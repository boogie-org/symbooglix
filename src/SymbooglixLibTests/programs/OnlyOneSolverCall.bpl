procedure main(x:int)
requires x > 5;
{
    // This won't be a solver call
    assert {:symbooglix_bp "before_assert" } true;

    // This should only require a single call to the solver
    // ∃ X :: (X > 5) ∧ ¬ (X > 4)
    // This is unsatisfiable meaning the assertion will
    // always succeed so we don't need to compute
    // ∃ X :: (X > 5) ∧ (X > 4)
    assert x > 4;

    // This won't be a solver call
    assert {:symbooglix_bp "after_assert" } true;
}
