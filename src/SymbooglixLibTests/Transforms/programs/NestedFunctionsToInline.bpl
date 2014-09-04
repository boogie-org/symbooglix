function {:inline} foo(a:int, b:int) returns(int)
{
    a + b
}

function {:inline} bar(x:int) returns(int)
{
    x + 1
}

procedure main(v:int)
{
    // Should inline to v + 1 + v + 1 + 1
    assert foo (bar(v), bar(bar(v))) == 12;
}
