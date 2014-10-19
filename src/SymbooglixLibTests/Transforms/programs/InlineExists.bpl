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
}
