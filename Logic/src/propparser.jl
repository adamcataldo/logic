import Base: ==, show, isidentifier

# Define the token types and the lexer function
abstract type Token end

struct Neg <: Token end
struct Wedge <: Token end
struct Mid <: Token end
struct Oplus <: Token end
struct Vee <: Token end
struct DArrow <: Token end
struct RArrow <: Token end
struct LRArrow <: Token end
struct LParen <: Token end
struct RParen <: Token end
struct Ident <: Token
    name::String
end

==(x::Neg, y::Neg)::Bool = true
==(x::Wedge, y::Wedge)::Bool = true
==(x::Mid, y::Mid)::Bool = true
==(x::Oplus, y::Oplus)::Bool = true
==(x::Vee, y::Vee)::Bool = true
==(x::DArrow, y::DArrow)::Bool = true
==(x::RArrow, y::RArrow)::Bool = true
==(x::LRArrow, y::LRArrow)::Bool = true
==(x::LParen, y::RParen)::Bool = true
==(x::RParen, y::RParen)::Bool = true
==(x::Ident, y::Ident)::Bool = x.name == y.name

show(io::IO, l::Token) = print(io, "$(typeof(l))")

function lexer(input::String)::Vector{<:Token}
    # Token definitions
    tokens = Dict(
        '¬' => Neg(),
        '∧' => Wedge(),
        '|' => Mid(),
        '⊕' => Oplus(),
        '∨' => Vee(),
        '↓' => DArrow(),
        '⟹' => RArrow(),
        '⟺' => LRArrow(),
        '(' => LParen(),
        ')' => RParen()
    )
    
    # Initialize variables
    result = Token[]
    curident = ""

    # Helper function to add identifiers
    flushident!() = begin
        if !isempty(curident)
            push!(result, Ident(curident))
            curident = ""
        end
    end

    # Process each character
    for char in input
        if char in keys(tokens)
            flushident!()
            push!(result, tokens[char])
        elseif !isspace(char)
            curident *= char
        else
            flushident!()
        end
    end

    # Flush the last identifier if present
    flushident!()

    return result
end

abstract type Proposition end

struct Variable <: Proposition
    name::Symbol
end

struct Not <: Proposition
    expr::Proposition
end

abstract type BinaryProposition <: Proposition end;

struct And <: BinaryProposition
    left::Proposition
    right::Proposition
end

struct Nand <: BinaryProposition
    left::Proposition
    right::Proposition
end

struct Xor <: BinaryProposition
    left::Proposition
    right::Proposition
end

struct Or <: BinaryProposition
    left::Proposition
    right::Proposition
end

struct Nor <: BinaryProposition
    left::Proposition
    right::Proposition
end

struct Implies <: BinaryProposition
    left::Proposition
    right::Proposition
end

struct Iff <: BinaryProposition
    left::Proposition
    right::Proposition
end

function symbol(prop::BinaryProposition)::String
    error("not impliemented for $(typeof(prop))")
end

==(x::Variable, y::Variable)::Bool = x.name == y.name
==(x::Not, y::Not)::Bool = x.expr == y.expr
==(x::BinaryProposition, y::BinaryProposition)::Bool = (x.left == y.left) && (x.right == y.right)

function symbol(prop::And)::String
    "∧"
end

function symbol(prop::Nand)::String
    "|"
end

function symbol(prop::Xor)::String
    "⊕"
end

function symbol(prop::Or)::String
    "∨"
end

function symbol(prop::Nor)::String
    "↓"
end

function symbol(prop::Implies)::String
    "⟹"
end

function symbol(prop::Iff)::String
    "⟺"
end

show(io::IO, l::Variable) = print(io, string(l.name))
show(io::IO, l::Not) = print(io, "(¬$(l.expr))")
show(io::IO, l::BinaryProposition) = print(io, "($(l.left) $(symbol(l)) $(l.right))")

function parseexpr(tokens, pos=1)::Tuple{Proposition, Int}
    expr, pos = parseiff(tokens, pos)
    return expr, pos
end

function parseiff(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parseimplies(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == LRArrow
        pos += 1
        right, pos = parseimplies(tokens, pos)
        left = Iff(left, right)
    end
    return left, pos
end

function parseimplies(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parseor(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == RArrow
        pos += 1
        right, pos = parseor(tokens, pos)
        left = Implies(left, right)
    end
    return left, pos
end

function parseor(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parsenor(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == Vee
        pos += 1
        right, pos = parsenor(tokens, pos)
        left = Or(left, right)
    end
    return left, pos
end

function parsenor(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parsexor(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == DArrow
        pos += 1
        right, pos = parsexor(tokens, pos)
        left = Nor(left, right)
    end
    return left, pos
end

function parsexor(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parsenand(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == Oplus
        pos += 1
        right, pos = parsenand(tokens, pos)
        left = Xor(left, right)
    end
    return left, pos
end

function parsenand(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parseand(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == Mid
        pos += 1
        right, pos = parseand(tokens, pos)
        left = Nand(left, right)
    end
    return left, pos
end

function parseand(tokens, pos)::Tuple{Proposition, Int}
    left, pos = parsenot(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == Wedge
        pos += 1
        right, pos = parsenot(tokens, pos)
        left = And(left, right)
    end
    return left, pos
end

function parsenot(tokens, pos)::Tuple{Proposition, Int}
    if pos <= length(tokens) && typeof(tokens[pos]) == Neg
        pos += 1
        expr, pos = parsenot(tokens, pos)
        return Not(expr), pos
    else
        return parseprimary(tokens, pos)
    end
end

function parseprimary(tokens, pos)::Tuple{Proposition, Int}
    if typeof(tokens[pos]) == Ident
        var = Variable(Symbol(tokens[pos].name))
        pos += 1
        return var, pos
    elseif typeof(tokens[pos]) == LParen
        pos += 1
        expr, pos = parseexpr(tokens, pos)
        if typeof(tokens[pos]) != RParen
            error("Expected ')'")
        end
        pos += 1
        return expr, pos
    else
        error("Unexpected token")
    end
end

function parseproptokens(tokens::Vector{<:Token})::Proposition
    expr, pos = parseexpr(tokens)
    if pos <= length(tokens)
        error("Extra tokens after valid expression")
    end
    return expr
end

function parseprop(str::String)::Proposition
    parseproptokens(lexer(str))
end

macro proposition(exp)
    return :( parseprop(string($(QuoteNode(exp)))) )
end

function _parsepolish(tokens::Vector{<:Token}, i::Int64)::Tuple{Proposition, Int64}
    if i > length(tokens)
        error("invalid statement form")
    end
    next = tokens[i]
    if next isa Ident
        return Variable(Symbol(next.name)), i+1
    elseif next isa Neg
        expr, pos = _parsepolish(tokens, i+1)
        return Not(expr), pos
    elseif next isa Wedge
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return And(left, right), pos
    elseif next isa Mid
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return Nand(left, right), pos
    elseif next isa Oplus
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return Xor(left, right), pos
    elseif next isa Vee
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return Or(left, right), pos
    elseif next isa DArrow
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return Nor(left, right), pos
    elseif next isa RArrow
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return Implies(left, right), pos
    elseif next isa LRArrow
        left, pos = _parsepolish(tokens, i+1)
        right, pos = _parsepolish(tokens, pos)
        return Iff(left, right), pos
    else
        error("unable to process token $next")
    end
end

function parsepolish(str::String)::Proposition
    tokens = lexer(str)
    _parsepolish(tokens, 1)[1]
end

export Proposition
export And
export Nand
export Xor
export Or
export Nor
export Not
export Implies
export Iff
export Variable
export parseprop
export @proposition
export parsepolish
export symbol