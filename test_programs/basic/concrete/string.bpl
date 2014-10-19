// RUN: %rmdir %t.symbooglix-out
// RUN: %symbooglix --output-dir %t.symbooglix-out %s | %OutputCheck %s

// Model a string as a map of integers to 8-bit vectors
// where the value corresponds to ascii
type string = [int]bv8;

// Checks string is null terminated
function {:inline true} validStr(s:string) returns(bool)
{
    (exists x:int :: (x >= 0) && (s[x] == 0bv8))
}


procedure {:inline 1} strLen(s:string) returns(length:int)
requires validStr(s);
ensures length >= 0;
{
    length := 0;
    while (s[length] != 0bv8)
    // FIXME: Need loop invariants to prove this correct
    {
        length := length +1;
    }
}

procedure main()
{
    var myString:string;
    var length:int;

    // Write our string
    myString[0] := 48bv8; // 'H'
    myString[1] := 49bv8; // 'I'

    myString[2] := 0bv8; // '\0' Null terminate

    // Will fail if we forgot to null terminate
    assert validStr(myString);

   call length := strLen(myString);
   assert length == 2;
   // CHECK-L: State 0: Terminated without error at ${CHECKFILE_ABS_PATH}:${LINE:+1} return;
}
