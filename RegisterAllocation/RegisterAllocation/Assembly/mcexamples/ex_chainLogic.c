void main(int n, int m)
{
    int i;
    i = 5;
    if(Or(1+2,3+4)){
        print i;
    }
}

int And(int a, int b)
{
    if (a == 0)
    {
        return 0;
    }
    if (b == 0)
    {
        return 0;
    }
    return 1;
}

int Or(int a, int b)
{
    print a;
    print b;
    if (a != 0)
    {
        
        return 1;
    }
    if (b != 0)
    {
        
        return 1;
    }
    return 0;
}
