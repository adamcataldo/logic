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

function logicallyimplies(a::T, b::S)::Bool where {T<:Proposition, S<:Proposition}
    istautology(Implies(a, b))
end

function ⟹(a::T, b::S)::Bool where {T<:Proposition, S<:Proposition}
    logicallyimplies(a, b)
end

function logicallyequivalent(a::T, b::S)::Bool where {
    T<:Proposition, 
    S<:Proposition
}
    istautology(Iff(a, b))
end

function ⟺(a::T, b::S)::Bool where {T<:Proposition, S<:Proposition}
    logicallyequivalent(a, b)
end

function iscontradiction(a::T)::Bool where T <: Proposition
    istautology(Not(a))
end

function substitute(prop::T, match::U, replacement::V)::Proposition where {
    T<:Proposition,
    U<:Proposition,
    V<:Proposition
}
    if prop == match
        return replacement
    elseif prop isa Not
        return Not(substitute(prop.expr, match, replacement))
    elseif prop isa Or
        return Or(
            substitute(prop.left, match, replacement), 
            substitute(prop.right, match, replacement)
        )
    elseif prop isa And
        return And(
            substitute(prop.left, match, replacement),
            substitute(prop.right, match, replacement)
        )
    elseif prop isa Implies
        return Implies(
            substitute(prop.left, match, replacement), 
            substitute(prop.right, match, replacement)
        )
    elseif prop isa Iff
        return Iff(
            substitute(prop.left, match, replacement), 
            substitute(prop.right, match, replacement)
        )
    else
        return prop
    end
end

struct Nil <: Proposition end

function isstronger(a::Proposition, b::Proposition)::Bool
    precedence = Dict(
        Nil => 0,
        Iff => 1,
        Implies => 2,
        Or => 3,
        And => 4,
        Not => 5,
        Variable => 6
    )
    precedence[typeof(a)] > precedence[typeof(b)]
end

function _minparens(prop::Proposition, parent::Proposition)::String
    base = ""
    if prop isa Variable
        base = string(prop.name)
    elseif prop isa Not
        base = "¬" * _minparens(prop.expr, prop)
    elseif prop isa And
        base = _minparens(prop.left, prop) * " ∧ " * _minparens(prop.right, prop)
    elseif prop isa Or
        base = _minparens(prop.left, prop) * " ∨ " * _minparens(prop.right, prop)
    elseif prop isa Implies
        base = _minparens(prop.left, prop) * " ⟹ " * _minparens(prop.right, prop)
    elseif prop isa Iff
        base = _minparens(prop.left, prop) * " ⟺ " * _minparens(prop.right, prop)
    else
        error("invalid proposition type $(typeof(prop))")
    end
    if isstronger(prop, parent)
        return base
    else
        return "($base)"
    end
end

function minparens(prop::Proposition)::String
    _minparens(prop, Nil())
end

function _polish(prop::Proposition)::String
    if prop isa Variable
        return string(prop.name) * " "
    elseif prop isa Not
        return "¬ " * _polish(prop.expr)
    elseif prop isa And
        return "∧ " * _polish(prop.left) * _polish(prop.right)
    elseif prop isa Or
        return "∨ " * _polish(prop.left) * _polish(prop.right)
    elseif prop isa Implies
        return "⟹ " * _polish(prop.left) * _polish(prop.right)
    elseif prop isa Iff
        return "⟺ " * _polish(prop.left) * _polish(prop.right)
    else
        error("invalid proposition type $(typeof(prop))")
    end  
end

function polish(prop::Proposition)::String
    rstrip(_polish(prop))
end

export Assignment
export evaluate
export istautology
export logicallyimplies
export ⟹
export logicallyequivalent
export ⟺
export iscontradiction
export substitute
export minparens
export polish