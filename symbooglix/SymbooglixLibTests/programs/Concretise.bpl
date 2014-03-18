var x:bv8;
var y:bv8;

procedure main()
{
    var a:bv8;
    assert {:symbooglix_bp "entry" } true;
    a := 1bv8;
    x := 2bv8;
    assert {:symbooglix_bp "now_concrete"} true;
}