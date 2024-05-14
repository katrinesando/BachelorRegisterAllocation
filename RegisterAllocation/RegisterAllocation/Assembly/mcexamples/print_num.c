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
//Expected output 5 5
