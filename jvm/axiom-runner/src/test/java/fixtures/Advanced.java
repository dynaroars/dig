package fixtures;

public final class Advanced {
    private Advanced() {}

    public static int overloaded(int value) {
        return value + 1;
    }

    public static String overloaded(String value) {
        return value + "!";
    }

    public static int[] reverse(int[] values) {
        int[] result = values.clone();
        for (int left = 0, right = result.length - 1; left < right; left++, right--) {
            int temporary = result[left];
            result[left] = result[right];
            result[right] = temporary;
        }
        return result;
    }
}
