// micro-C example 11 

//find median of arrays
void main(int num) {
	
	int n1;
	int n2;
	int arr1[100];
	int arr2[100];
	arr1[0] = 1;
	arr1[1] = 12;
	arr1[2] = 15;
	arr1[3] = 26;
	arr1[4] = 38;
  
	arr2[0] = 2;
	arr2[1] = 13;
	arr2[2] = 17;
	arr2[3] = 30;
	arr2[4] = 45;
	
	n1 = 5;
	n2 = 5/2;
	// n2 = 0;
	// while (n2 <= 100) {
	// 	arr1[n2] = n2;
	// 	n2 = n2+1;
	// }
	// n2 = 0;
	// n1 = 3;
	// while (n2 <= 100) {
	// 	n1 = n2*n1;
	// 	arr2[n2] = n1;
	// 	n2 = n2+1;
	// }
	// n1 = 100;
	print (median(arr1, arr2, n1));
	
}

int median(int a1[], int a2[], int n)
{
	int count;
	int i;
	int j;
	int median1;
	int median2;
    
	i = j = count = 0;
	median1 = median2 = -1;
	while (count <= n)
	{
		if (i == n)
		{
			median1 = median2;
			median2 = a2[0];
		}
		if(j == n)
		{
			median1 = median2;
			median2 = a1[0];
		}
		if(a1[i] <=  a2[j])
		{
			median1 = median2; //store prev med
			median2 = a1[i];
			i = i+1;
		}else
		{
			median1 = median2; //store prev med
			median2 = a2[j];
			j = j+1;
		}
		count = count +1;
	}
	return (median1 + median2) /2;
}