procedure main()
{
    var x:int;
    assume x <= 0;
    call x:= foo(x);
}

procedure foo(a:int) returns (r:int)
requires a > 0;
{
    r := a + 1;
}
