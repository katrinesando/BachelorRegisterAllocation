//This code stress tests the compiler. It should not compile if there is no register allocation.
//Which is the case as of writting the code. 

void main() {
    int complex;
    complex = 1 + 2 + 3 + 4 + 5; //Too complex of an expression
}
