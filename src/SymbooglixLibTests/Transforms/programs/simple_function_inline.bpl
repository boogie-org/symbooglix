function {:inline true} foo(x:int) returns(bool)
{
    x == 0
}

function {:inline true} bar(x:int) returns(bool)
{
    if x > 0 then foo(x) else foo(x-1)
}

const v:int;
axiom( foo(v) );


procedure main(x:int)
requires foo(x) && false <==> foo(x);
ensures foo(x) <==> foo(x);
{
    assert foo(x);
}
