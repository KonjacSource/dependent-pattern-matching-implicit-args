# dependent-pattern-matching-implicit-args

[English](README.md) | [中文](README-zh.md)

一个支持归纳类型族的依赖类型语言。

> __注意.__ 本项目基于 András Kovács 的 [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo) ((04-implicit-args)[https://github.com/AndrasKovacs/elaboration-zoo/tree/master/04-implicit-args])。

## 特性

### 继承自 elaboration-zoo
- [x] 依赖类型
- [x] 双向类型检查 
- [x] Type in Type
- [x] 元变量与隐式参数

### 我的工作
- [x] 归纳类型族
- [x] 依赖模式匹配
- [x] 互归纳类型
- [x] 互递归函数
- [x] 归纳归纳类型
- [x] 归纳递归类型
- [ ] 覆盖性检查
- [ ] 终止性检查

如果你只关心如何实现索引数据类型且不关心元变量求解，可以参考我之前的项目 [dependent-pattern-matching](http://github.com/KonjacSource/dependent-pattern-matching)。

## 示例

以下是硬编码在 `app/Main.hs` 中的 prelude 定义。

```agda
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


```

## 用法 

你可以使用 repl 与本项目进行交互。

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

或者编译本项目并使用命令参数 "repl" 启动 repl。

注意：在项中使用 `printcxt[e]` 或 `sorry` 来打印上下文。