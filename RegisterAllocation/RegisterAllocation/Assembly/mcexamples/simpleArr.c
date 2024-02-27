//local simpel arithmetic
void main()
{
   int arr[5];
   arr[0]=1;
   *(arr+1) = 3;
   print arr[1];
   print arr[0];
   *arr = 198;
   print arr[0];
}
//should print 3 1
//prints 3 769
