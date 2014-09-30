procedure main()
{
    var x:int;
    call x:= foo(x);
}

procedure foo(a:int) returns (r:int)
requires a > 0; // This can fail or succeed when called from main
{
    r := a + 1;
}
