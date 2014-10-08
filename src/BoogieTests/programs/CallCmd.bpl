procedure main()
{
    var x:int;
    call x := foo();
    call x := bar();
}

procedure foo() returns(r:int)
{
    r := 0;
}

procedure bar() returns(r:int);
ensures r == 0;
