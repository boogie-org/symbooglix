procedure main()
{
    var x:int;
    assume x > 0;
    // The constant folder shouldn't be able to catch this.
    assert x < 0;
}
