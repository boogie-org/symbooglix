var g:int;
var h:int;

procedure main()
modifies g;
ensures g > old(g + 1);
{
    var temp:int;
    assert {:symbooglix_bp "check_old_g"} true;
    call temp := foo();
}

procedure foo() returns (r:int)
modifies g;
ensures r == old(g);
ensures g > old(g + old(2));
{
    assert {:symbooglix_bp "check_old_g"} true;
    g := old(g) + 3;
    r := old(g);
}
