#include <stdio.h>
void main(){
    int a;
    int *b;
    a = 2;
    b = &a;
    printf ("%d", *b);
}
