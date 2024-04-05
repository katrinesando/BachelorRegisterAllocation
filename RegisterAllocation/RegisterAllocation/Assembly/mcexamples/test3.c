void main()
{
    print test3();
}

int nut()
{
    return 1;
}
int megacoomer()
{
    int amountofnut;
    amountofnut = 0;

    while(amountofnut != 69)
    {
        amountofnut = amountofnut + nut();
    }
    return amountofnut;
    
}

int test3()
{
    int x;
    x = 5;
    int y;
    y = 5;
    int z;
    z = 5;
    int a;
    a = 5;
    int b;
    b = 5;
    int counter;
    counter = 0;
    while(x!=6)
    {
        x = x-1;
        while(y!=6)
        {
            y = y-1;
            while(z!=6)
            {
                z = z-1;
                while(a!=6)
                {
                    a = a-1;
                    while(b!=6)
                    {
                        counter = counter + megacoomer();
                        b = b-1;
                    }
                }
            }
        }
    }
    return counter;
}