void main() {
   int i;
   int b;
   int n;
   int *p;

   b = 1;
   p = (&i+1);
   *p = 277;

   print (b);
}
//should print 227
