using Test
using Logic

@testset "Logic Tests" begin
    @testset "parseprop tests" begin
        @test parseprop(:(A)) == Variable(:A)
        @test parseprop(:(¬N)) == Not(Variable(:N))
        @test parseprop(:(C ∨ D)) == Or(Variable(:C), Variable(:D))
        @test parseprop(:(C ∧ D)) == And(Variable(:C), Variable(:D))
        @test parseprop(:(C ⟹ D)) == Implies(Variable(:C), Variable(:D))
        @test parseprop(:(C ⟺ D)) == Iff(Variable(:C), Variable(:D))
        expected = Or(And(Variable(:A), Variable(:B)), Not(Variable(:A)))
        prop = :((A ∧ B) ∨ (¬A))
        @test parseprop(prop) == expected
    end

    @testset "propsosition tests" begin
        prop = @proposition A ∧ B
        @test prop == And(Variable(:A), Variable(:B))
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

end