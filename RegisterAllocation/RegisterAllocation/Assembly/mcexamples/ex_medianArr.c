// micro-C example 11 

//find median of arrays

void main() {
	int arr1[100];
	int arr2[100];
	int n1;
	int n2;
	arr1[1] = 1;
	arr1[2] = 12;
	arr1[3] = 15;
	arr1[4] = 26;
	arr1[5] = 38;
    
	arr2[1] = 2;
	arr2[2] = 13;
	arr2[3] = 17;
	arr2[4] = 30;
	arr2[5] = 45;

	n1 = 5;
	n2 = 5/2;

	if (n1 == n2)
	{
		printi (median(arr1, arr2, n1));
	}
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
			i++;
		}else
		{
			median1 = median2; //store prev med
			median2 = a2[j];
			j++;
		}
		count++;
	}
	return (median1 + median2) /2;
}