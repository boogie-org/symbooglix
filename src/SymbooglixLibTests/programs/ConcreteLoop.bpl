procedure main()
{
    var counter:int;
    var value:int;
    var old_value:int;

    counter := 0;

    old_value := value;
    
    while (counter < 3)
    {
        counter := counter +1;
        value := value +2;
    }

    // After leaving the loop the ExecutionState
    // will have ExplicitBranchDepth 4 because
    // the loop head is executed one more time
    // than the loop bound

    assert old_value + 6 == value;
}
