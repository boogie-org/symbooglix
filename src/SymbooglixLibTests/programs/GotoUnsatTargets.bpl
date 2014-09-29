procedure main()
{
    var x:int;
    x := 5;

    goto B1, B2, B3;

    // None of these paths are feasible
    B1:
        assume x == 10;
        return;

    B2:
        assume x == 17;
        return;

    B3:
        assume x == 20;
        return;
}
