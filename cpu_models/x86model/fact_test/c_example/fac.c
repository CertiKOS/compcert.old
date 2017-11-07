int fac(int n)
{
  int v = 0;

  if (n == 0) {
    v = 1;
  } else {
    v = n * fac(n-1);
  }

  return v;
}

int gv = 0;

int main()
{
  gv = fac(4);
  return gv;
}
