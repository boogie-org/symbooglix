procedure main() returns (r:bv8);

// Bitvector functions
function {:bvBuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvBuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

implementation main() returns (r:bv8)
{
    var a:bv8;
    var b:bv8;
    a := 1bv8;
    b := 2bv8;
    r := bv8add(a,b);
    assert bv8ugt(r, 0bv8); // FIXME: Boogie can't verify
}
