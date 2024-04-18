//This code stress tests the compiler. It should not compile if there is no register allocation.
//Which is the case as of writting the code. 

void main() {
    int n;
    n = 20; 
    int complex;
    complex = n + (n + (n + (n + (n + (n + (n + (n +(n+(n+(n+(n+(n+(n+(n+n)))))))))))))); //Too complex of an expression
    print n; 
   //complex = n + (n + n); 
    print complex;
}
