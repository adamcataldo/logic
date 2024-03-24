using Test
using Logic

@testset "Logic Tests" begin
    @testset "parseprop tests" begin
        expr = "(¬A ∨ B) ∧ (C ⟹ D) ⟺ E"
        actual = parseprop(expr)
        expected = Iff(
            And(
                Or(
                    Not(Variable(:A)),
                    Variable(:B)
                ),
                Implies(
                    Variable(:C),
                    Variable(:D)
                )
            ),
            Variable(:E)
        )
        @test expected == actual
    end

    @testset "proposition tests" begin
        expr = "(¬A ∨ B) ∧ (C ⟹ D) ⟺ E"
        expected = parseprop(expr)
        actual = @proposition (¬A ∨ B) ∧ (C ⟹ D) ⟺ E
        @test expected == actual
        withxor = @proposition A ∧ B ⊕ C ∨ D
        expectedparse = Or(
            Xor(
                And(
                    Variable(:A),
                    Variable(:B)
                ),
                Variable(:C)
            ),
            Variable(:D)
        )
        @test expectedparse == withxor
    end

    @testset "evaluate tests" begin
        prop = @proposition A ∧ B
        @test evaluate(prop, Dict(:A => true, :B => false)) == false
    end

    @testset "istautology tests" begin
        prop1 = @proposition A ∨ (¬A)
        @test istautology(prop1) == true
        prop2 = @proposition A ∧ (¬A)
        @test istautology(prop2) == false
    end

    @testset "logicallyimplies (⟹) tests" begin
        a = @proposition A ∧ (A ⟹ B)
        b = @proposition B
        @test (a ⟹ b) == true
        c = @proposition ¬B
        @test (a ⟹ c) == false
    end

    @testset "logicallyequivalent (⟺) tests" begin
        a = @proposition A ∨ A
        b = @proposition A
        @test (a ⟺ b) == true
        c = @proposition B
        @test (a ⟺ c) == false
    end

    @testset "iscontradiction tests" begin
        prop1 = @proposition A ∨ (¬A)
        @test iscontradiction(prop1) == false
        prop2 = @proposition A ∧ (¬A)
        @test iscontradiction(prop2) == true
    end

    @testset "substitue tests" begin
        prop = @proposition A ∧ (A ∨ B) ⟹ (A ∨ B)
        match = @proposition (A ∨ B)
        replacement = @proposition (¬C)
        expected = @proposition A ∧ (¬C) ⟹ (¬C)
        actual = substitute(prop, match, replacement)
        @test expected == actual
    end

    @testset "minparens tests" begin
        prop = @proposition (¬A ∨ B) ∧ (C ⟹ D) ⟺ E
        expected = "(¬A ∨ B) ∧ (C ⟹ D) ⟺ E"
        actual = minparens(prop)
        @test expected == actual
    end

    @testset "polish tests" begin
        prop = @proposition ((¬A) ∧ (B ⟹ (¬D)))
        expected = "∧ ¬ A ⟹ B ¬ D"
        actual = polish(prop)
        @test expected == actual
    end

    @testset "parseandpolish tests" begin
        expr = "∧ ¬ A ⟹ B ¬ D"
        expected = @proposition ((¬A) ∧ (B ⟹ (¬D)))
        actual = parsepolish(expr)
        @test expected == actual
    end

end