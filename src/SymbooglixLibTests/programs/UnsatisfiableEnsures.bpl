procedure main()
{
    var x:int;
    assume x <= 20;
    call x := foo(x);
    assert x <= 20;
}

procedure foo(x:int) returns (r:int);
ensures x == r;
ensures r > 20; // This can't be satisfied given the previous ensures
