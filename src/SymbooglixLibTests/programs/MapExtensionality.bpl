procedure main()
{
    var a:[int]int;
    var b:[int]int;

    assume (forall x:int :: a[x] == b[x]);
    assert a == b;

    
    a[0], b[0] := 12, 12;
    assert a == b;
    assert (forall x:int :: (a[x] == b[x])) <==> a==b;
}

