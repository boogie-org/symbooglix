var g:int;
var g2:int;

procedure main()
modifies g,g2;
{
    var a:int;
    a := 15;
    call g := bar();
    assert {:symbooglix_bp "checkg"} true;
    assert g == 2;

    call g2 := bar2();
    assert {:symbooglix_bp "checkg2"} true;
    assert g2 == 3;
}

procedure bar() returns(r:int)
{
    r := 2;
}

procedure bar2() returns(t:int);
ensures t == 3;
