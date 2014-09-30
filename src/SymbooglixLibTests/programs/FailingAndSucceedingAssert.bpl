procedure main()
{
    var x:int;
    assume x >= 0;
    // The constant folder shouldn't be able to catch this.
    // This assert can fail but can succeed is x happens to be 0
    assert x <= 0;
}
