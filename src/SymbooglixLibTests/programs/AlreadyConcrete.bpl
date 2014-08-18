procedure main()
{
    call foo(4);
}

procedure foo(x:int)
requires x == 4;
{
    assert true;
}
