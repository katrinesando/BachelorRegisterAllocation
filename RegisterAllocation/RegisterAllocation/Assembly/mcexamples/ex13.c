// micro-C example 13 -- optimization of andalso and orelse

void main(int n) {
  int y;
  y = 1889;
  while (y < n) {
    y = y + 1;
    if (And(y % 4 == 0,Or(y % 100 != 0, y % 400 == 0)))
      print y;
  }
}

int And(int a, int b)
{
  //print a;
  //print b;
  if (a == 0)
  {
    return 0;
  }
  if (b == 0)
  {
    return 0;
  }
  return 1;
}

int Or(int a, int b)
{
  //print a;
  //print b;
  if (a != 0)
  {
    return 1;
  }
  if (b != 0)
  {
    return 1;
  }
  return 0;
}
