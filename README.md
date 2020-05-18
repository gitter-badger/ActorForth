# Reimplementation of ActorForth in Haskell

ActorForth is Open Source software covered under BSD license (see
LICENSE.txt).  If you contribute to this project then you guarantee
that you have the right to contribute your content & IP, will abide by
said license and do assign an unlimited, universal, non-exclusive
license to the copyright holder and anyone else who agrees to abide by
the license.

## Haskell
Currently the type checker and type inferencer is implemented for
proof of concept.

### Examples
- `1 2 +`
```
λ> solve defaultWords (assembleP [LitI 1, LitI 2, Cmd "add"])
Right (T "Int" :- Bot)
```

- `3 False swap`
```
λ> solve defaultWords (assembleP [LitI 3, LitB False, Cmd "swap"])
Right (T "Int" :- (T "Bool" :- Bot))
```

- `1 False +`
```
λ> solve defaultWords (assembleP [LitI 1, LitB False, Cmd "add"])
Left "Failed to unify Int and Bool"
```

- `swap drop +`
```
λ> solve defaultWords (assembleP [assembleF [Cmd "swap", Cmd "drop", Cmd "add"]])
Right ((T "Int" :- (TV "t2" :- (T "Int" :- TV "t1"))) :->
       (T "Int" :- TV "t1") :- Bot)
```


## Python Notes
Run ./setup under a python 3.7+ virtual environment for best results.

Then run ./interpret  samples/fundamentals01.a4 to see it run a simple script.

Run ./interpret by itself to get the repl.

See [ActorForthDefinition](docs/ActorForthDefinition.md) for a quick overview of how the language works.

Experiments implementing an Actor-style programming language on top of
a stack-based processor will be forthcoming as the system is
developed.
