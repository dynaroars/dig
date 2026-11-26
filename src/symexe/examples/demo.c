// MiniC uses mathematical integers and treats initialized declarations as assignments.
int x = input;

if (x > 0) {
  int y = x + 1;
  assert(y != 0);
} else {
  int y = x - 1;
  assert(y != 0);
}
