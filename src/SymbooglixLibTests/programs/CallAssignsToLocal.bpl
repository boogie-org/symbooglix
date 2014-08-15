procedure main()
{
    var a:int;
    var b:int;
    call a := bar();
    assert {:symbooglix_bp "checka"} true;
    assert a == 2;

    call b := bar2();
    assert {:symbooglix_bp "checkb"} true;
    assert b == 3;
}

procedure bar() returns(r:int)
{
    r := 2;
}

procedure bar2() returns(t:int);
ensures t == 3;
