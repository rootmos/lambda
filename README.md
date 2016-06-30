# lambda

`lambda` is a personal pet project of mine to learn [Lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus)
and to play with [Church encodings](https://en.wikipedia.org/wiki/Church_encoding).
And of course, to code in lovely Haskell :)

The greatest heights the project has reached is to calculate:
```
lambda> (plus 7 4)
11
```
where under the hood:
* `7` and `4` are Church encoded numerals, ie `(\f.(\x.(f (f (f (f x))))))` represents 4 and so on, and
* `plus` is the predefined function:
```
lambda> :d plus
(λm.(λn.(λf.(λx.(m f (n f x))))))
```
Conversion happens from these predefined values and simplified using [reductions](https://en.wikipedia.org/wiki/Lambda_calculus#Reduction),
after which the resulting expression is reversely tested for equivalence with any predefined expressions.

All predefined functions can be found by:
```
lambda> :p
id := (λx.x)
true := (λa.(λb.a))
false := (λa.(λb.b))
if := (λp.(λa.(λb.(p a b))))
plus := (λm.(λn.(λf.(λx.(m f (n f x))))))
```
