
void main() {
   int arr[5]; 
   *(arr+1) = 3; //first index arr[0]=3
   print (arr[1]); //expect 3
}