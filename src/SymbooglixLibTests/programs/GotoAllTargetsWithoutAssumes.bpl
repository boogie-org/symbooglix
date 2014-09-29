procedure main()
{
    var x:int;
    assume x > 0;

    goto B1, B2, B3;

    // All of these paths are feasible
    B1:
        x := 5;
        return;

    B2:
        x := 15;
        return;

    B3:
        x := 25;
        return;
}
