procedure main()
{
    var x:int;
    assume x > 0;

    goto B1, B2, B3, B4;

    B1:
        // Infeasible path
        assume x < 0;
        return;

    B2:
        x := 15;
        assert {:symbooglix_bp "followed"} true;
        return;

    B3:
        // Feasible path
        assume x > 0;
        x := 25;
        assert {:symbooglix_bp "followed"} true;
        return;

    B4:
        // Feasible path
        x := 20;
        assert {:symbooglix_bp "followed"} true;
        return;
}
