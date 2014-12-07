// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out --goto-assume-look-ahead=1 %s 2>&1 | %OutputCheck %s
// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} bv8ult(bv8,bv8) returns(bool);

procedure main(a:bv8, N:bv8) returns (r:bv8)
requires a == 0bv8;
requires N == 10bv8;
{
    var counter:bv8;
    counter := 0bv8;
    r := a;

    while(bv8ult(counter, N))
    {
        r := bv8add(r, 2bv8);
        counter := bv8add(counter, 1bv8);
    }

    assert r == 20bv8;
}

// CHECK-L: State 0: Terminated without error
