---
layout: post
title: Arithmetic Overflows
date: 2017-01-05
author: Ranjit Jhala
published: true
comments: true
tags: basic
demo: refinements101.hs
---


## This is a subtitle

* Here is some text that is *bold* and some that is _italic_.
* Here is some text that is *bold* and some that is _italic_.
* Here is some text that is *bold* and some that is _italic_.

## And now for some code

This is a function called `incr`:

```haskell
{-@ incr :: x:Nat -> {v:Nat | v > x} @-}
incr :: Int -> Int
incr x = x + 1
```

This is a function called `decr`:

\begin{code}
{-@ incr :: x:Nat -> {v:Nat | v > x} @-}
incr :: Int -> Int
incr x = x + 1
\end{code}

and that is it.
