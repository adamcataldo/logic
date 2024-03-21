import Base: ==, show, isidentifier

abstract type Proposition end

# Define types for logic connectives
struct And <: Proposition
    left::Proposition
    right::Proposition
end

==(x::And, y::And)::Bool = (x.left == y.left) && (x.right == y.right)

show(io::IO, l::And) = print(io, "($(l.left) ∧ $(l.right))")

struct Or <: Proposition
    left::Proposition
    right::Proposition
end

==(x::Or, y::Or)::Bool = (x.left == y.left) && (x.right == y.right)

show(io::IO, l::Or) = print(io, "($(l.left) ∨ $(l.right))")


struct Not <: Proposition
    expr::Proposition
end

==(x::Not, y::Not)::Bool = x.expr == y.expr

show(io::IO, l::Not) = print(io, "(¬$(l.expr))")

struct Implies <: Proposition
    left::Proposition
    right::Proposition
end

==(x::Implies, y::Implies)::Bool = (x.left == y.left) && (x.right == y.right)

show(io::IO, l::Implies) = print(io, "($(l.left) ⟹  $(l.right))")

struct Iff <: Proposition
    left::Proposition
    right::Proposition
end

==(x::Iff, y::Iff)::Bool = (x.left == y.left) && (x.right == y.right)

show(io::IO, l::Iff) = print(io, "($(l.left) ⟺  $(l.right))")

# Define a type for statement variables
struct Variable <: Proposition
    name::Symbol
end

==(x::Variable, y::Variable)::Bool = x.name == y.name

show(io::IO, l::Variable) = print(io, string(l.name))

function parseprop(expr::Union{Symbol, Expr})::Proposition
    if expr isa Symbol
        if !isidentifier(expr)
            error("invalid identifier $expr")
        end
        return Variable(expr)
    elseif expr.head == :call
        if length(expr.args) == 2 && expr.args[1] == :¬
            return Not(parseprop(expr.args[2]))
        elseif length(expr.args) == 3
            if expr.args[1] == :∨
                return Or(parseprop(expr.args[2]), parseprop(expr.args[3]))
            elseif expr.args[1] == :∧
                return And(parseprop(expr.args[2]), parseprop(expr.args[3]))
            elseif expr.args[1] == :⟹
                return Implies(parseprop(expr.args[2]), parseprop(expr.args[3]))
            elseif expr.args[1] == :⟺
                return Iff(parseprop(expr.args[2]), parseprop(expr.args[3]))
            end
        end
    end
    error("failed to parse expression: $expression")
end

macro proposition(exp)
    return parseprop(:( $exp ))
end

const Assignment = Dict{Symbol, Bool}

function evaluate(prop::T, assign::Assignment)::Bool where T <: Proposition
    if prop isa Variable
        return assign[prop.name]
    elseif prop isa Not
        return !evaluate(prop.expr, assign)
    elseif prop isa And
        return evaluate(prop.left, assign) && evaluate(prop.right, assign)
    elseif prop isa Or
        return evaluate(prop.left, assign) || evaluate(prop.right, assign)
    elseif prop isa Implies
        return !evaluate(prop.left, assign) || evaluate(prop.right, assign)
    elseif prop isa Iff
        return evaluate(prop.left, assign) == evaluate(prop.right, assign)
    end
    error("unrecognized proposition type $(typeof(prop))")
end

function getvars(prop::T)::Set{Symbol} where T <: Proposition
    if prop isa Variable
        return Set([prop.name])
    elseif prop isa Not
        return getvars(prop.expr)
    elseif prop isa And
        return union(getvars(prop.left), getvars(prop.right))
    elseif prop isa Or
        return union(getvars(prop.left), getvars(prop.right))
    elseif prop isa Implies
        return union(getvars(prop.left), getvars(prop.right))
    elseif prop isa Iff
        return union(getvars(prop.left), getvars(prop.right))
    end
    error("unrecognized proposition type $(typeof(prop))")
end

function istautology(prop::T) where T <: Proposition
    vars = [v for v in getvars(prop)]
    n = length(vars)
    assignments = falses(2^n, n)
    for i in 1:2^n
        for j in 1:n
            assignments[i, j] = (i-1) & (1 << (n-j)) != 0
        end
    end
    for i in 1:2^n
        assign = Dict(zip(vars, assignments[i, :]))
        if !(evaluate(prop, assign))
            return false
        end
    end
    return true
end

export Proposition
export And
export Or
export Not
export Implies
export Iff
export Variable
export parseprop
export @proposition
export Assignment
export evaluate
export istautology
