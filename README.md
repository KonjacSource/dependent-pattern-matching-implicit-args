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

We can use those definitions to prove the soundness of STLC.

```lean
data Val : {A : Ty} -> Tm empty A -> U where
| vlam : {A B : Ty} (t : Tm (extend empty A) B) -> Val (lam t)
| vtt  :  Val tt

-- Substitution from empty context. 
data Sub : Ctx -> Ctx -> U where
| sempty : {G : Ctx} -> Sub G empty
| sid    : {G : Ctx} -> Sub G G
| sextend : {D G : Ctx} {A : Ty} -> Sub D G -> Tm D A -> Sub D (extend G A)
| sshift : {D G : Ctx} -> Sub D G -> (A : Ty) -> Sub (extend D A) (extend G A)

def fromEmp : {G : Ctx} {A : Ty} -> Tm empty A -> Tm G A
| {empty} t = t
| {extend G B} t = wk (fromEmp t)

def applySub : {D G : Ctx} {A : Ty} -> Sub D G -> Tm G A -> Tm D A
| sempty t = fromEmp t
| sid t = t
| g tt = tt
| g (lam t) = lam (applySub (sshift g _) t)
| g (app t1 t2) = app (applySub g t1) (applySub g t2)
| (sextend g a) (var iz) = a
| (sextend g a) (var (is i)) = applySub g (var i)
| (sextend g a) (wk t) = applySub g t
| (sshift g A) (var iz) = var iz
| (sshift g A) (var (is i)) = wk (applySub g (var i))
| (sshift g A) (wk t) = wk (applySub g t)

-- Automatally have preservation.
data step1 : {A : Ty} -> Tm empty A -> Tm empty A -> U where
| stApp : {A B : Ty} (t1 : Tm (extend empty A) B) (t2 : Tm empty A) -> step1 (app (lam t1) t2) (applySub (sextend sid t2) t1)
| stApp1 : {A B : Ty} (t1 T1 : Tm empty (arr A B)) (t2 : Tm empty A) -> step1 t1 T1 -> step1 (app t1 t2) (app T1 t2)
| stApp2 : {A B : Ty} (t1 : Tm empty (arr A B)) (t2 T2 : Tm empty A) -> step1 t2 T2 -> step1 (app t1 t2) (app t1 T2)

data Progress : {A : Ty} -> Tm empty A -> U where
| prStep : {A : Ty} (t T : Tm empty A) -> step1 t T -> Progress t
| prDone : {A : Ty} (t : Tm empty A) -> Val t -> Progress t 

-- Progress 
def progress : {A : Ty} (t : Tm empty A) -> Progress t
| tt = prDone tt vtt
| (lam t) = prDone (lam t) (vlam t)
| (var x) = absurd x
| (app t1 t2) =
    match progress t1 with 
    | (prStep t1 T1 st1) = prStep _ _ (stApp1 t1 T1 t2 st1)
    | (prDone t1 (vlam t)) = prStep _ _ (stApp t t2)
    end
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

# Reference

- András Kovács. [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
- Ulf Norell. [Towards a practical programming language based on dependent type theory](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf)