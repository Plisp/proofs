unsigned int expF(unsigned int x, unsigned int n)
{
  if (n == 0) {
    return 1;
  }
  unsigned int y = 1;
  while (n > 1) {
    if (n%2 != 0) {
      y = x * y;
      n = n - 1;
    }
    x = x * x;
    n = n / 2;
  }
  return x * y;
}
