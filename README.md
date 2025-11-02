# ShiTT2

[English](README.md) | [中文](README-zh.md)

A dependently-typed language with indexed inductive types supported. 

> __Note.__ This project is based on András Kovács' [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) ((04-implicit-args)[https://github.com/AndrasKovacs/elaboration-zoo/tree/master/04-implicit-args]).

## Features

### Inherited from elaboration-zoo
- [x] Dependent types
- [x] Bidirectional type checking 
- [x] Type in Type
- [x] Meta variables and implict arugments (pattern unification)

### My works
- [x] Indexed data types
- [x] Dependent pattern matching
- [x] Mutual inductive types
- [x] Mutual recursive
- [x] Inductive-inductive types
- [x] Inductive-recursive types
- [x] Coverage checking
- [x] Soundness
- [ ] Termination checking
- [ ] Positivity checking
- [ ] Universe polymorphism
- [ ] Consistency

If you only want to know how to implement indexed data types and do not care about metavariable solving, you can check my previous work [dependent-pattern-matching](http://github.com/KonjacSource/dependent-pattern-matching).

## Example

This is prelude definitions hard-coded in `app/Main.hs`.

```lean
data Nat where
| zero : Nat
| suc  : Nat -> Nat

data Id : {A : U} (x y : A) -> U where
| refl : {A : U} (x : A) -> Id x x

data Vec : (A : U) -> Nat -> U where
| vnil : {A : U} -> Vec A zero
| vcons : {A : U} {n : Nat} -> A -> Vec A n -> Vec A (suc n)

def add : Nat -> Nat -> Nat
| zero    n = n
| (suc m) n = suc (add m n)

def symm : {A : U} {x y : A} -> Id x y -> Id y x
| (refl x) = refl x

def trans : {A : U} {x : A} (y : A) {z : A} -> Id x y -> Id y z -> Id x z
| y (refl x) (refl x1) = refl x

def append : {A : U} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (add n m)
| vnil         ys = ys
| (vcons x xs) ys = vcons x (append xs ys)


def J : (A : U) (P : (x : A) (y : A) -> Id x y -> U) 
        (m : (x : A) -> P x x (refl x))
        (a : A) (b : A) (p : Id a b) -> P a b p
| A P m a b (refl x) = m x
```

This is an example for inductive-inductive / inductive-recursive types

```lean
mutual 

  data Ctx : U 
  data Ty : U 
  data Tm : (G : Ctx) -> Ty -> U
  data Ix : Ctx -> U
  def lookup : {G : Ctx} -> Ix G -> Ty 

begin

  data Ctx 
  | empty : Ctx
  | extend : (G : Ctx) -> Ty -> Ctx

  data Ty 
  | top : Ty 
  | arr : Ty -> Ty -> Ty

  data Tm 
  | tt : {G : Ctx} -> Tm G top
  | lam : {G : Ctx} {A B : Ty} -> (Tm (extend G A) B) -> Tm G (arr A B)
  | app : {G : Ctx} {A B : Ty} -> (Tm G (arr A B)) -> (Tm G A) -> Tm G B
  | var : {G : Ctx} (i : Ix G) -> Tm G (lookup i)

  data Ix 
  | iz : {G : Ctx} {A : Ty} -> Ix (extend G A)
  | is : {G : Ctx} {A : Ty} -> Ix G -> Ix (extend G A)

  def lookup
  | {extend G A} iz = A 
  | {G} (is i) = lookup i

end

-- Example 

-- G1 = top, top -> top
def G1 : Ctx = extend (extend empty top) (arr top top)

def tm1 : Tm G1 top = 
  app (var {G1} iz) tt
```


## Usage 

You can use repl to interact with this project.

```
system> stack repl
ghci> repl 
repl> :h  
Available commands:
  :h           - show this help message
  :q           - quit
  :l <file>    - load a file
  :metas       - display unsolved metas
  :func <name> - display function definition
  :t <expr>    - typecheck expression
  :nf <expr>   - typecheck expression and print its normal form
```

Or compile this project and use command argument "repl" to start repl.

Note. use `printcxt[e]` or `sorry` in a term to print the context.