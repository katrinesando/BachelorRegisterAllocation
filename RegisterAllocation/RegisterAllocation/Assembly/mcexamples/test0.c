void main(int i) {
    int r;
    r = 3;
    test0(r);
}

void test0(int n) {
    int e = 0;
    while(e != 1001){
    
        while(n % 2 == 0 || n > 0)
        {
            int p;
            p = (10*n) + (n/n+(n/2));
            n = p / 4;
        }
        e = e+1;   
    }
    print(n);
}


