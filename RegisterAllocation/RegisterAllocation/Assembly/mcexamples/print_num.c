void main()
{
   int *a;
   int b;
   b = 5;
   a = &b;
   print (*a);
   int** c;
   c = &a;
   print(**c);
}
