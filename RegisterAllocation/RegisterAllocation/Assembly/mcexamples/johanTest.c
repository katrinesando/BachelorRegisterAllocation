void main()
{
    print test3();
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

int test3()
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
    while(x!=6)
    {
        x = x+1;
        while(y!=6)
        {
            y = y+1;
            while(z!=6)
            {
                z = z+1;
                while(a!=6)
                {
                    a = a+1;
                    while(b!=6)
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
