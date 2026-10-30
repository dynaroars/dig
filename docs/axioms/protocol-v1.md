# Axiom worker protocol version 1

Workers exchange UTF-8 JSON Lines over stdin/stdout. One JSON object occupies one
line, is at most 1 MiB by default, and contains `protocol_version`, `message`, and a
message-specific payload. Non-protocol target output is captured by the worker and
must never be written to the protocol stream.

The parent sends `hello` first and the worker must answer `hello` before receiving a
batch. Unknown versions, messages, fields, operation IDs, type IDs, or case IDs are
protocol errors. A batch receives exactly one terminal `batch_result`; missing or
duplicate case IDs invalidate the whole batch.

```json
{"protocol_version":1,"message":"hello","language":"java","run_id":"run-01"}
{"protocol_version":1,"message":"hello","language":"java","capabilities":["evaluate_terms"]}
```

## Terms

Term encodings are structural and use stable manifest IDs:

```json
{"kind":"variable","type_id":"stack","index":0}
{"kind":"constant","type_id":"item","value":0}
{"kind":"call","operation_id":"pop","projection":{"kind":"return"},"type_id":"item","children":[{"kind":"call","operation_id":"push","projection":{"kind":"post_state","input_index":0},"type_id":"stack","children":[{"kind":"variable","type_id":"stack","index":0},{"kind":"variable","type_id":"item","index":0}]}]}
```

The operation declaration, not the term, is authoritative about effects and passing
modes. A call projects either its operation return or the post-state of one declared
mutated input. A `null` return type is represented only in operation declarations;
void calls have no return projection but can be composed through a post-state
projection.

## Recipes and aliases

A recipe is data, not executable source. Each root is constructed once, and variables
reference root IDs. Reusing a root ID preserves an alias.

```json
{
  "recipe_id": "discovery-0001",
  "roots": [
    {"id": "r0", "type_id": "stack", "generator_id": "stack-recipes-v1", "value": [1, 2]},
    {"id": "r1", "type_id": "item", "generator_id": "small-int-v1", "value": 3}
  ],
  "variables": [
    {"type_id": "stack", "index": 0, "root_id": "r0"},
    {"type_id": "item", "index": 0, "root_id": "r1"}
  ]
}
```

Recipe root and variable arrays are sorted by ID and `(type_id, index)` respectively.
Map-like encoded values use lexicographically sorted encoded keys; sets are encoded as
tagged, sorted arrays. Non-finite floats use explicit tags and never JSON `NaN`.

## Evaluation

The parent batches independent term evaluations over fixed recipes:

```json
{"protocol_version":1,"message":"evaluate_batch","batch_id":"b1","cases":[{"case_id":"c1","recipe":{"recipe_id":"discovery-0001","roots":[],"variables":[]},"term":{"kind":"variable","type_id":"item","index":0}}]}
```

Each case yields one outcome:

```json
{
  "status": "returned",
  "return_value": 3,
  "observations_by_root": {"r0": {"observer_id": "stack-snapshot-v1", "value": [1, 2]}},
  "aliases": [],
  "exception": null,
  "stdout": {"sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "bytes": 0, "truncated": false},
  "stderr": {"sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "bytes": 0, "truncated": false},
  "elapsed_ms": 1
}
```

`status` is one of `returned`, `threw`, `timed_out`, `crashed`, `protocol_error`, or
`unsupported`. Exactly one of `return_value` or a non-null `exception` is meaningful:
`return_value` is present for `returned` (including JSON `null`); `exception` is
present for `threw` and contains `class` plus an adapter-normalized `payload`.
Infrastructure statuses may include a bounded `detail` but never count as a pass.

Workers sort outcomes by input case order. Digests cover all emitted target bytes,
including bytes beyond the captured prefix. Timing is evidence metadata and is
excluded from semantic signatures and normalized deterministic output.

## Shutdown

The parent may send `shutdown`; the worker answers `shutdown` after flushing results.
EOF, worker disappearance, malformed JSON, an oversized line, or target text on the
protocol stream is a protocol failure. The parent kills and replaces an unresponsive
worker after the recorded batch deadline.
