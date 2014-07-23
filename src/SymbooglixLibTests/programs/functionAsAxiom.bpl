function foo(x:int) returns(bool);
// the ``:bool`` is a TypeCoercion
axiom(forall x:int :: foo(x):bool <==> x > 0);

procedure main(y:int)
{
    assert foo(5);
}
