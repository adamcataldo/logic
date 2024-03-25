const Assignment = Dict{Symbol, Bool}

function evaluate(prop::Variable, assign::Assignment)::Bool
    assign[prop.name]
end

function evaluate(prop::Not, assign::Assignment)::Bool
    !evaluate(prop.expr, assign)
end

function evaluate(prop::And, assign::Assignment)::Bool
    evaluate(prop.left, assign) && evaluate(prop.right, assign)
end

function evaluate(prop::Nand, assign::Assignment)::Bool
    evaluate(prop.left, assign) ⊼ evaluate(prop.right, assign)
end

function evaluate(prop::Xor, assign::Assignment)::Bool
    evaluate(prop.left, assign) ⊻ evaluate(prop.right, assign)
end

function evaluate(prop::Or, assign::Assignment)::Bool
    evaluate(prop.left, assign) || evaluate(prop.right, assign)
end

function evaluate(prop::Nor, assign::Assignment)::Bool
    evaluate(prop.left, assign) ⊽ evaluate(prop.right, assign)
end
function evaluate(prop::Implies, assign::Assignment)::Bool
    !evaluate(prop.left, assign) || evaluate(prop.right, assign)
end

function evaluate(prop::Iff, assign::Assignment)::Bool
    evaluate(prop.left, assign) == evaluate(prop.right, assign)
end

function getvars(prop::Variable)::Set{Symbol}
    Set([prop.name])
end

function getvars(prop::Not)::Set{Symbol}
    getvars(prop.expr)
end

function getvars(prop::BinaryProposition)::Set{Symbol}
    union(getvars(prop.left), getvars(prop.right))
end

function truthtable(numvars::Int64)::Matrix{Bool}
    n = numvars
    assignments = falses(2^n, n)
    for i in 1:2^n
        for j in 1:n
            assignments[i, j] = (i-1) & (1 << (n-j)) != 0
        end
    end
    assignments
end

function istautology(prop::T) where T <: Proposition
    vars = [v for v in getvars(prop)]
    n = length(vars)
    assignments = truthtable(n)
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

function substitute(prop::Variable, match::U, replacement::V)::Proposition where {
    U<:Proposition,
    V<:Proposition
}
    if prop == match
        return replacement
    else
        return prop
    end
end

function substitute(prop::Not, match::U, replacement::V)::Proposition where {
    U<:Proposition,
    V<:Proposition
}
    if prop == match
        return replacement
    else
        return Not(substitute(prop.expr, match, replacement))
    end
end

function substitute(prop::BinaryProposition, match::U, replacement::V)::Proposition where {
    U<:Proposition,
    V<:Proposition
}
    if prop == match
        return replacement
    else
        return typeof(prop)(
            substitute(prop.left, match, replacement), 
            substitute(prop.right, match, replacement)
        )
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

function maybeparen(base::String, prop::Proposition, parent::Proposition)::String
    if isstronger(prop, parent)
        return base
    else
        return "($base)"
    end
end

function _minparens(prop::Variable, parent::Proposition)::String
    base = string(prop.name)
    maybeparen(base, prop, parent)
end

function _minparens(prop::Not, parent::Proposition)::String
    base = "¬" * _minparens(prop.expr, prop)
    maybeparen(base, prop, parent)
end

#Fixme:: handle binary propositions

function _minparens(prop::And, parent::Proposition)::String
    base = _minparens(prop.left, prop) * " ∧ " * _minparens(prop.right, prop)
    maybeparen(base, prop, parent)
end

function _minparens(prop::Xor, parent::Proposition)::String
    base = _minparens(prop.left, prop) * " ⊕ " * _minparens(prop.right, prop)
    maybeparen(base, prop, parent)
end

function _minparens(prop::Or, parent::Proposition)::String
    base = _minparens(prop.left, prop) * " ∨ " * _minparens(prop.right, prop)
    maybeparen(base, prop, parent)
end

function _minparens(prop::Implies, parent::Proposition)::String
    base = _minparens(prop.left, prop) * " ⟹ " * _minparens(prop.right, prop)
    maybeparen(base, prop, parent)
end

function _minparens(prop::Iff, parent::Proposition)::String
    base = _minparens(prop.left, prop) * " ⟺ " * _minparens(prop.right, prop)
    maybeparen(base, prop, parent)
end

function minparens(prop::Proposition)::String
    _minparens(prop, Nil())
end

function _polish(prop::Variable)::String
    string(prop.name) * " "
end

function _polish(prop::Not)::String
    "¬ " * _polish(prop.expr)
end

function _polish(prop::BinaryProposition)::String
    "$(symbol(prop)) " * _polish(prop.left) * _polish(prop.right)
end

function polish(prop::Proposition)::String
    rstrip(_polish(prop))
end

function gensymbols(n::Int64)::Vector{Symbol}
    syms = Symbol[]
    for i in 1:n
        num = i
        str = ""
        while num > 0
            mod = (num - 1) % 26
            str = Char('A' + mod) * str
            num = (num - mod) ÷ 26
        end
        push!(syms, Symbol(str))
    end
    return syms
end

function fromfunction(fun::Function)::Proposition
    n = length(methods(fun)[1].sig.parameters) - 1
    if n == 0
        if fun()
            return Or(Variable(:A), Not(Variable(:A)))
        else
            return And(Variable(:A), Not(Variable(:A)))
        end
    end
    assignments = truthtable(n)
    symbols = gensymbols(n)
    terms = Proposition[]
    for assignment in eachrow(assignments)
        if fun(assignment...)
            conjuncts = map(a -> a[1] ? Variable(a[2]) : Not(Variable(a[2])), zip(assignment, symbols))
            term = reduce(And, conjuncts)
            push!(terms, term)
        end
    end
    if isempty(terms)
        return And(Variable(:A), Not(Variable(:A)))
    end
    reduce(Or, terms)
end

function fromtruthtable(inputs::Matrix{Bool}, outputs::Vector{Bool})::Proposition
    (rows, n) = size(inputs)
    if (rows != 2^n)
        error("should be $(2^n) rows but found $rows")
    end
    if length(outputs) != 2^n
        error("should be $(2^n) outputs but found $(length(outputs))")
    end
    symbols = gensymbols(n)
    terms = Proposition[]
    for (i, output) in enumerate(outputs)
        if output
            row = inputs[i, :]
            conjuncts = map(a -> a[1] ? Variable(a[2]) : Not(Variable(a[2])), zip(row, symbols))
            term = reduce(And, conjuncts)
            push!(terms, term)
        end
    end
    if isempty(terms)
        return And(Variable(:A), Not(Variable(:A)))
    end
    reduce(Or, terms)
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
export deduce
export fromfunction
export fromtruthtable