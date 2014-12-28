// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out --goto-assume-look-ahead=0 %s 2>&1 | %OutputCheck %s
function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);
procedure main(arg:bv8) returns (result:bv8)
{
    assume bv8ugt(arg, 0bv8);
    if ( arg == 0bv8)
    {
        result := 1bv8;
        // CHECK-NOT-L: The following assertion failed
        assert false;
    }
    else
    {
        result := 2bv8;
    }

    assert result == 2bv8;

}
// CHECK-L: State 1: Terminated without error
