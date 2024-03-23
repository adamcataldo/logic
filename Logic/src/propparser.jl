import Base: ==, show, isidentifier

# Define the token types and the lexer function
abstract type Token end

struct Neg <: Token end
struct Vee <: Token end
struct Wedge <: Token end
struct RArrow <: Token end
struct LRArrow <: Token end
struct LParen <: Token end
struct RParen <: Token end
struct Ident <: Token
    name::String
end

==(x::Neg, y::Neg)::Bool = true
==(x::Vee, y::Vee)::Bool = true
==(x::Wedge, y::Wedge)::Bool = true
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
        '∨' => Vee(),
        '∧' => Wedge(),
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

# Define types for logic connectives
struct And <: Proposition
    left::Proposition
    right::Proposition
end

struct Or <: Proposition
    left::Proposition
    right::Proposition
end

struct Not <: Proposition
    expr::Proposition
end

struct Implies <: Proposition
    left::Proposition
    right::Proposition
end

struct Iff <: Proposition
    left::Proposition
    right::Proposition
end

struct Variable <: Proposition
    name::Symbol
end

==(x::And, y::And)::Bool = (x.left == y.left) && (x.right == y.right)
==(x::Or, y::Or)::Bool = (x.left == y.left) && (x.right == y.right)
==(x::Not, y::Not)::Bool = x.expr == y.expr
==(x::Implies, y::Implies)::Bool = (x.left == y.left) && (x.right == y.right)
==(x::Iff, y::Iff)::Bool = (x.left == y.left) && (x.right == y.right)
==(x::Variable, y::Variable)::Bool = x.name == y.name

show(io::IO, l::And) = print(io, "($(l.left) ∧ $(l.right))")
show(io::IO, l::Or) = print(io, "($(l.left) ∨ $(l.right))")
show(io::IO, l::Not) = print(io, "(¬$(l.expr))")
show(io::IO, l::Implies) = print(io, "($(l.left) ⟹ $(l.right))")
show(io::IO, l::Iff) = print(io, "($(l.left) ⟺ $(l.right))")
show(io::IO, l::Variable) = print(io, string(l.name))

function parseexpr(tokens, pos=1)
    expr, pos = parseiff(tokens, pos)
    return expr, pos
end

function parseiff(tokens, pos)
    left, pos = parseimplies(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == LRArrow
        pos += 1
        right, pos = parseimplies(tokens, pos)
        left = Iff(left, right)
    end
    return left, pos
end

function parseimplies(tokens, pos)
    left, pos = parseor(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == RArrow
        pos += 1
        right, pos = parseor(tokens, pos)
        left = Implies(left, right)
    end
    return left, pos
end

function parseor(tokens, pos)
    left, pos = parseand(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == Vee
        pos += 1
        right, pos = parseand(tokens, pos)
        left = Or(left, right)
    end
    return left, pos
end

function parseand(tokens, pos)
    left, pos = parsenot(tokens, pos)
    while pos <= length(tokens) && typeof(tokens[pos]) == Wedge
        pos += 1
        right, pos = parsenot(tokens, pos)
        left = And(left, right)
    end
    return left, pos
end

function parsenot(tokens, pos)
    if pos <= length(tokens) && typeof(tokens[pos]) == Neg
        pos += 1
        expr, pos = parsenot(tokens, pos)
        return Not(expr), pos
    else
        return parseprimary(tokens, pos)
    end
end

function parseprimary(tokens, pos)
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

export Proposition
export And
export Or
export Not
export Implies
export Iff
export Variable
export parseprop
export @proposition