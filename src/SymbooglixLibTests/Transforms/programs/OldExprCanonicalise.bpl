var g:int;
var h:int;

procedure main()
modifies g, h;
ensures g > old(g + 1);
{
    var temp:int;
    call temp := foo();
    call temp := bar();
}

procedure foo() returns (r:int);
modifies g;
ensures r == old(g);
ensures g > old(g + old(2));

procedure bar() returns (r:int)
modifies g;
ensures r == old(g);
ensures g > old(g + old(g)) + old(g);
{
    var temp:int;
    var local:int;
    local := 0;
    g := 5;
    temp := old(g + local);
    if (temp > 0)
    {
        g := g + old(g + h +17) + h;
    }
    else
    {
        g := g + old(old(old(g))) + 19;
    }
    r := old(g);
}
