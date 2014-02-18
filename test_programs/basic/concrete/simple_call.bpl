function {:bvbuiltin "bvadd"} bv16add(bv16,bv16) returns(bv16);

procedure main() returns (r:bv16)
{
    var a:bv8;
    var b:bv16;
    var result:bv16;
    a := 1bv8;
    b := 2bv16;
    call result := h(a,b);
    assert result == bv16add(a++a, b);
}

procedure h(a:bv8, b:bv16) returns (r:bv16)
{
   r := a++a; 
   r := bv16add(r, b);
}
