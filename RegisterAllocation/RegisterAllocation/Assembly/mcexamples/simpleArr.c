//local simpel arithmetic
void main()
{
   int b;
   int arr[5];
   arr[2]=3;
   arr[0+1]=7883;
   print (arr[2]);
   print (arr[0+1]);
   b = 27;
   print (b);
   
   //arr[1]=2;
   *(arr+1) = 3;
   print arr[1];
   /* *arr = 198;
   print arr[0];*/
}
//should print 3 1
