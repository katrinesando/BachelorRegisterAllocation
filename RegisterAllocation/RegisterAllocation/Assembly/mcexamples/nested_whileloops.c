void main(int n)
{
    print test3(n);
}

int one()
{
    return 1;
}
int return69()
{
    int counter;
    counter = 0;

    while(counter != 69)
    {
        counter = counter + one();
    }
    return counter;
    
}

int test3(int n)
{
    int x;
    x = 0;
    int y;
    y = 0;
    int z;
    z = 0;
    int a;
    a = 0;
    int b;
    b = 0;
    int counter;
    counter = 0;
    while(x!=n)
    {
        x = x+1;
        while(y!=n)
        {
            y = y+1;
            while(z!=n)
            {
                z = z+1;
                while(a!=n)
                {
                    a = a+1;
                    while(b!=n)
                    {
                        counter = counter + return69();
                        b = b+1;
                    }
                }
            }
        }
    }
    return counter;
}