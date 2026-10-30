package org.dynaroars.dig.axioms;

import java.io.*;
import java.lang.reflect.*;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.*;

/** Minimal dependency-free JSON-lines worker for DIG axiom evaluations. */
public final class Runner {
    private static final int PROTOCOL_VERSION = 1;
    private final Map<String, Map<String, Object>> types = new HashMap<>();
    private final Map<String, Operation> operations = new HashMap<>();
    private int outputLimit = 65_536;

    private record Operation(
        String id, String kind, String binding, List<String> inputs,
        String returnType, Set<Integer> mutates, Method method, Constructor<?> constructor
    ) {}

    private record Evaluated(Object value, Set<String> roots) {}

    public static void main(String[] args) throws Exception {
        new Runner().serve();
    }

    @SuppressWarnings("unchecked")
    private void serve() throws Exception {
        var reader = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
        var writer = new BufferedWriter(new OutputStreamWriter(System.out, StandardCharsets.UTF_8));
        String line;
        while ((line = reader.readLine()) != null) {
            Object parsed = Json.parse(line);
            if (!(parsed instanceof Map<?, ?>)) fail("message must be an object");
            Map<String, Object> request = (Map<String, Object>) parsed;
            if (number(request.get("protocol_version")).intValue() != PROTOCOL_VERSION) {
                fail("unsupported protocol version");
            }
            String message = string(request.get("message"));
            Map<String, Object> response = new LinkedHashMap<>();
            response.put("protocol_version", PROTOCOL_VERSION);
            if (message.equals("hello")) {
                configure((Map<String, Object>) request.get("config"));
                response.put("message", "hello");
                response.put("language", "java");
                response.put("capabilities", List.of("evaluate_terms"));
            } else if (message.equals("evaluate_batch")) {
                response.put("message", "batch_result");
                response.put("batch_id", request.get("batch_id"));
                List<Object> results = new ArrayList<>();
                for (Object item : (List<Object>) request.get("cases")) {
                    Map<String, Object> testCase = (Map<String, Object>) item;
                    Map<String, Object> result = new LinkedHashMap<>();
                    result.put("case_id", testCase.get("case_id"));
                    result.put("outcome", evaluateCase(testCase));
                    results.add(result);
                }
                response.put("results", results);
            } else if (message.equals("shutdown")) {
                response.put("message", "shutdown");
                write(writer, response);
                return;
            } else {
                fail("unknown message " + message);
            }
            write(writer, response);
        }
    }

    @SuppressWarnings("unchecked")
    private void configure(Map<String, Object> config) throws Exception {
        if (config == null) fail("hello requires config");
        if (config.get("output_limit_bytes") instanceof Number limit) {
            outputLimit = Math.max(0, limit.intValue());
        }
        for (Object item : (List<Object>) config.get("types")) {
            Map<String, Object> declaration = (Map<String, Object>) item;
            types.put(string(declaration.get("id")), declaration);
        }
        for (Object item : (List<Object>) config.get("operations")) {
            Map<String, Object> declaration = (Map<String, Object>) item;
            String id = string(declaration.get("id"));
            String kind = string(declaration.get("kind"));
            String binding = string(declaration.get("binding"));
            List<String> inputs = new ArrayList<>();
            if (declaration.get("receiver_type") != null) {
                inputs.add(string(declaration.get("receiver_type")));
            }
            for (Object type : (List<Object>) declaration.get("parameter_types")) {
                inputs.add(string(type));
            }
            Set<Integer> mutates = new TreeSet<>();
            for (Object index : (List<Object>) declaration.get("mutates")) {
                mutates.add(number(index).intValue());
            }
            Executable executable = resolve(binding, kind);
            operations.put(id, new Operation(
                id, kind, binding, inputs,
                declaration.get("return_type") == null ? null : string(declaration.get("return_type")),
                mutates,
                executable instanceof Method method ? method : null,
                executable instanceof Constructor<?> constructor ? constructor : null
            ));
        }
    }

    private static Executable resolve(String binding, String kind) throws Exception {
        int hash = binding.indexOf('#');
        int open = binding.indexOf('(', hash + 1);
        int close = binding.lastIndexOf(')');
        if (hash < 1 || open < hash || close < open) fail("invalid Java binding " + binding);
        Class<?> owner = classFor(binding.substring(0, hash));
        String name = binding.substring(hash + 1, open);
        String body = binding.substring(open + 1, close).trim();
        Class<?>[] parameters;
        if (body.isEmpty()) {
            parameters = new Class<?>[0];
        } else {
            String[] names = body.split(",");
            parameters = new Class<?>[names.length];
            for (int i = 0; i < names.length; i++) parameters[i] = classFor(names[i].trim());
        }
        if (kind.equals("constructor")) return owner.getConstructor(parameters);
        Method method = owner.getMethod(name, parameters);
        method.setAccessible(true);
        return method;
    }

    private static Class<?> classFor(String name) throws ClassNotFoundException {
        return switch (name) {
            case "boolean" -> boolean.class;
            case "byte" -> byte.class;
            case "short" -> short.class;
            case "int" -> int.class;
            case "long" -> long.class;
            case "float" -> float.class;
            case "double" -> double.class;
            case "char" -> char.class;
            default -> {
                if (name.endsWith("[]")) {
                    yield Array.newInstance(classFor(name.substring(0, name.length() - 2)), 0).getClass();
                }
                yield Class.forName(name);
            }
        };
    }

    @SuppressWarnings("unchecked")
    private Map<String, Object> evaluateCase(Map<String, Object> testCase) throws Exception {
        long started = System.nanoTime();
        Map<String, Object> recipe = (Map<String, Object>) testCase.get("recipe");
        Map<String, Object> roots = new LinkedHashMap<>();
        Map<String, String> rootTypes = new HashMap<>();
        Map<String, Evaluated> variables = new HashMap<>();
        Set<String> mutated = new TreeSet<>();
        for (Object item : (List<Object>) recipe.get("roots")) {
            Map<String, Object> root = (Map<String, Object>) item;
            String id = string(root.get("id"));
            String type = string(root.get("type_id"));
            roots.put(id, construct(type, root.get("value")));
            rootTypes.put(id, type);
        }
        for (Object item : (List<Object>) recipe.get("variables")) {
            Map<String, Object> variable = (Map<String, Object>) item;
            String type = string(variable.get("type_id"));
            int index = number(variable.get("index")).intValue();
            String root = string(variable.get("root_id"));
            variables.put(type + "\0" + index, new Evaluated(roots.get(root), Set.of(root)));
        }

        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        var stdout = new BoundedOutput(outputLimit);
        var stderr = new BoundedOutput(outputLimit);
        String status;
        Object returnValue = null;
        Object exception = null;
        try {
            System.setOut(new PrintStream(stdout, true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(stderr, true, StandardCharsets.UTF_8));
            Evaluated result = evaluate(
                (Map<String, Object>) testCase.get("term"), variables, roots, mutated
            );
            returnValue = snapshot(string(((Map<String, Object>) testCase.get("term")).get("type_id")), result.value());
            status = "returned";
        } catch (InvocationTargetException wrapped) {
            Throwable cause = wrapped.getCause();
            status = "threw";
            Map<String, Object> detail = new LinkedHashMap<>();
            detail.put("class", cause.getClass().getName());
            detail.put("payload", String.valueOf(cause.getMessage()));
            exception = detail;
        } catch (Throwable target) {
            status = "threw";
            Map<String, Object> detail = new LinkedHashMap<>();
            detail.put("class", target.getClass().getName());
            detail.put("payload", String.valueOf(target.getMessage()));
            exception = detail;
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }

        Set<String> observed = new TreeSet<>(mutated);
        Object requested = testCase.get("observe_roots");
        if (requested instanceof List<?> values) {
            for (Object value : values) observed.add(string(value));
        }
        Map<String, Object> observations = new LinkedHashMap<>();
        for (String id : observed) {
            Map<String, Object> observation = new LinkedHashMap<>();
            observation.put("observer_id", types.get(rootTypes.get(id)).getOrDefault("snapshot", "builtin-json-v1"));
            observation.put("value", snapshot(rootTypes.get(id), roots.get(id)));
            observations.put(id, observation);
        }
        Map<String, Object> outcome = new LinkedHashMap<>();
        outcome.put("status", status);
        outcome.put("return_value", returnValue);
        outcome.put("observations_by_root", observations);
        outcome.put("aliases", List.of());
        outcome.put("exception", exception);
        outcome.put("stdout", stdout.result());
        outcome.put("stderr", stderr.result());
        outcome.put("elapsed_ms", Math.max(0, (System.nanoTime() - started) / 1_000_000));
        return outcome;
    }

    @SuppressWarnings("unchecked")
    private Evaluated evaluate(
        Map<String, Object> term,
        Map<String, Evaluated> variables,
        Map<String, Object> roots,
        Set<String> mutated
    ) throws Exception {
        String kind = string(term.get("kind"));
        if (kind.equals("variable")) {
            return variables.get(string(term.get("type_id")) + "\0" + number(term.get("index")).intValue());
        }
        if (kind.equals("constant")) return new Evaluated(term.get("value"), Set.of());
        Operation operation = operations.get(string(term.get("operation_id")));
        List<Evaluated> children = new ArrayList<>();
        for (Object child : (List<Object>) term.get("children")) {
            children.add(evaluate((Map<String, Object>) child, variables, roots, mutated));
        }
        Object[] arguments = new Object[children.size() - (operation.kind().equals("instance_method") ? 1 : 0)];
        int offset = operation.kind().equals("instance_method") ? 1 : 0;
        for (int i = 0; i < arguments.length; i++) {
            Class<?> expected = operation.method() != null
                ? operation.method().getParameterTypes()[i]
                : operation.constructor().getParameterTypes()[i];
            arguments[i] = convert(children.get(i + offset).value(), expected);
        }
        Object result;
        if (operation.constructor() != null) {
            result = operation.constructor().newInstance(arguments);
        } else {
            Object receiver = offset == 1 ? children.get(0).value() : null;
            result = operation.method().invoke(receiver, arguments);
        }
        for (int index : operation.mutates()) mutated.addAll(children.get(index).roots());
        Map<String, Object> projection = (Map<String, Object>) term.get("projection");
        if (string(projection.get("kind")).equals("post_state")) {
            return children.get(number(projection.get("input_index")).intValue());
        }
        Set<String> resultRoots = new TreeSet<>();
        for (var entry : roots.entrySet()) if (result == entry.getValue()) resultRoots.add(entry.getKey());
        return new Evaluated(result, resultRoots);
    }

    private Object construct(String typeId, Object encoded) throws Exception {
        Class<?> type = classFor(string(types.get(typeId).get("java_class")));
        if (Stack.class.isAssignableFrom(type)) {
            Stack<Object> stack = new Stack<>();
            for (Object item : (List<?>) encoded) stack.add(item instanceof Long value ? value.intValue() : item);
            return stack;
        }
        if (List.class.isAssignableFrom(type)) return new ArrayList<>((List<?>) encoded);
        if (Set.class.isAssignableFrom(type)) return new LinkedHashSet<>((List<?>) encoded);
        return convert(encoded, type);
    }

    private static Object convert(Object value, Class<?> expected) {
        if (value == null || expected.isInstance(value)) return value;
        if (expected.isArray() && value instanceof List<?> values) {
            Object array = Array.newInstance(expected.getComponentType(), values.size());
            for (int i = 0; i < values.size(); i++) {
                Array.set(array, i, convert(values.get(i), expected.getComponentType()));
            }
            return array;
        }
        if (value instanceof Number number) {
            if (expected == int.class || expected == Integer.class) return number.intValue();
            if (expected == long.class || expected == Long.class) return number.longValue();
            if (expected == double.class || expected == Double.class) return number.doubleValue();
            if (expected == float.class || expected == Float.class) return number.floatValue();
            if (expected == short.class || expected == Short.class) return number.shortValue();
            if (expected == byte.class || expected == Byte.class) return number.byteValue();
        }
        return value;
    }

    private Object snapshot(String typeId, Object value) {
        return encode(value);
    }

    private static Object encode(Object value) {
        if (value == null || value instanceof Boolean || value instanceof String) return value;
        if (value instanceof Byte || value instanceof Short || value instanceof Integer || value instanceof Long) return value;
        if (value instanceof Float number) return number.doubleValue();
        if (value instanceof Double) return value;
        if (value instanceof Character) return value.toString();
        if (value.getClass().isArray()) {
            List<Object> result = new ArrayList<>();
            for (int i = 0; i < Array.getLength(value); i++) result.add(encode(Array.get(value, i)));
            return result;
        }
        if (value instanceof Collection<?> collection) {
            List<Object> result = new ArrayList<>();
            for (Object child : collection) result.add(encode(child));
            if (value instanceof Set<?>) result.sort(Comparator.comparing(Json::write));
            return result;
        }
        if (value instanceof Map<?, ?> map) {
            Map<String, Object> result = new TreeMap<>();
            for (var entry : map.entrySet()) result.put(String.valueOf(entry.getKey()), encode(entry.getValue()));
            return result;
        }
        return String.valueOf(value);
    }

    private static void write(BufferedWriter writer, Map<String, Object> value) throws IOException {
        writer.write(Json.write(value));
        writer.newLine();
        writer.flush();
    }

    private static String string(Object value) {
        if (!(value instanceof String text)) throw new IllegalArgumentException("expected string");
        return text;
    }

    private static Number number(Object value) {
        if (!(value instanceof Number number)) throw new IllegalArgumentException("expected number");
        return number;
    }

    private static void fail(String message) {
        throw new IllegalArgumentException(message);
    }

    private static final class BoundedOutput extends OutputStream {
        private final int limit;
        private final ByteArrayOutputStream prefix = new ByteArrayOutputStream();
        private final MessageDigest digest;
        private long count;

        BoundedOutput(int limit) throws Exception {
            this.limit = limit;
            this.digest = MessageDigest.getInstance("SHA-256");
        }

        @Override
        public void write(int value) {
            byte single = (byte) value;
            digest.update(single);
            count++;
            if (prefix.size() < limit) prefix.write(value);
        }

        @Override
        public void write(byte[] values, int offset, int length) {
            digest.update(values, offset, length);
            count += length;
            int remaining = Math.max(0, limit - prefix.size());
            prefix.write(values, offset, Math.min(remaining, length));
        }

        Map<String, Object> result() {
            Map<String, Object> result = new LinkedHashMap<>();
            result.put("sha256", HexFormat.of().formatHex(digest.digest()));
            result.put("bytes", count);
            result.put("truncated", count > prefix.size());
            return result;
        }
    }

    /** Small JSON implementation sufficient for the bounded protocol value model. */
    private static final class Json {
        private final String source;
        private int position;

        private Json(String source) { this.source = source; }

        static Object parse(String source) {
            Json parser = new Json(source);
            Object value = parser.value();
            parser.space();
            if (parser.position != source.length()) fail("trailing JSON input");
            return value;
        }

        static String write(Object value) {
            StringBuilder output = new StringBuilder();
            append(output, value);
            return output.toString();
        }

        private Object value() {
            space();
            if (position >= source.length()) fail("unexpected end of JSON");
            return switch (source.charAt(position)) {
                case '{' -> object();
                case '[' -> array();
                case '"' -> string();
                case 't' -> literal("true", true);
                case 'f' -> literal("false", false);
                case 'n' -> literal("null", null);
                default -> number();
            };
        }

        private Map<String, Object> object() {
            position++;
            Map<String, Object> result = new LinkedHashMap<>();
            space();
            if (take('}')) return result;
            do {
                space();
                String key = string();
                space();
                require(':');
                result.put(key, value());
                space();
            } while (take(','));
            require('}');
            return result;
        }

        private List<Object> array() {
            position++;
            List<Object> result = new ArrayList<>();
            space();
            if (take(']')) return result;
            do { result.add(value()); space(); } while (take(','));
            require(']');
            return result;
        }

        private String string() {
            require('"');
            StringBuilder result = new StringBuilder();
            while (position < source.length()) {
                char current = source.charAt(position++);
                if (current == '"') return result.toString();
                if (current != '\\') { result.append(current); continue; }
                char escaped = source.charAt(position++);
                switch (escaped) {
                    case '"', '\\', '/' -> result.append(escaped);
                    case 'b' -> result.append('\b');
                    case 'f' -> result.append('\f');
                    case 'n' -> result.append('\n');
                    case 'r' -> result.append('\r');
                    case 't' -> result.append('\t');
                    case 'u' -> {
                        result.append((char) Integer.parseInt(source.substring(position, position + 4), 16));
                        position += 4;
                    }
                    default -> fail("invalid JSON escape");
                }
            }
            fail("unterminated JSON string");
            return null;
        }

        private Object number() {
            int start = position;
            if (take('-')) {}
            while (position < source.length() && Character.isDigit(source.charAt(position))) position++;
            boolean decimal = false;
            if (take('.')) {
                decimal = true;
                while (position < source.length() && Character.isDigit(source.charAt(position))) position++;
            }
            if (position < source.length() && (source.charAt(position) == 'e' || source.charAt(position) == 'E')) {
                decimal = true;
                position++;
                if (position < source.length() && (source.charAt(position) == '+' || source.charAt(position) == '-')) position++;
                while (position < source.length() && Character.isDigit(source.charAt(position))) position++;
            }
            String token = source.substring(start, position);
            return decimal ? Double.valueOf(token) : Long.valueOf(token);
        }

        private Object literal(String token, Object value) {
            if (!source.startsWith(token, position)) fail("invalid JSON literal");
            position += token.length();
            return value;
        }

        private void space() {
            while (position < source.length() && Character.isWhitespace(source.charAt(position))) position++;
        }

        private boolean take(char expected) {
            if (position < source.length() && source.charAt(position) == expected) {
                position++;
                return true;
            }
            return false;
        }

        private void require(char expected) {
            if (!take(expected)) fail("expected '" + expected + "'");
        }

        @SuppressWarnings("unchecked")
        private static void append(StringBuilder output, Object value) {
            if (value == null) { output.append("null"); return; }
            if (value instanceof Boolean || value instanceof Number) { output.append(value); return; }
            if (value instanceof String text) {
                output.append('"');
                for (int i = 0; i < text.length(); i++) {
                    char current = text.charAt(i);
                    switch (current) {
                        case '"' -> output.append("\\\"");
                        case '\\' -> output.append("\\\\");
                        case '\n' -> output.append("\\n");
                        case '\r' -> output.append("\\r");
                        case '\t' -> output.append("\\t");
                        default -> {
                            if (current < 0x20) output.append(String.format("\\u%04x", (int) current));
                            else output.append(current);
                        }
                    }
                }
                output.append('"');
                return;
            }
            if (value instanceof Map<?, ?> map) {
                output.append('{');
                boolean first = true;
                for (var entry : map.entrySet()) {
                    if (!first) output.append(',');
                    first = false;
                    append(output, String.valueOf(entry.getKey()));
                    output.append(':');
                    append(output, entry.getValue());
                }
                output.append('}');
                return;
            }
            if (value instanceof Iterable<?> iterable) {
                output.append('[');
                boolean first = true;
                for (Object child : iterable) {
                    if (!first) output.append(',');
                    first = false;
                    append(output, child);
                }
                output.append(']');
                return;
            }
            throw new IllegalArgumentException("unsupported JSON value " + value.getClass());
        }
    }
}
