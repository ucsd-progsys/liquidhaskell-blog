---
layout: post
title: Splitting and Splicing Intervals (Part 1)
date: 2017-12-15
comments: true
author: Ranjit Jhala
published: true
tags: reflection, abstract-refinements
demo: IntervalSets.hs
---

[Joachim Breitner](https://twitter.com/nomeata?lang=en)
wrote a [cool post][nomeata-intervals] describing a
library for representing sets of integers
as _sorted lists of intervals_, and how
they were able to formally verify the
code by translating it to Coq using
their [nifty new tool][hs-to-coq].

* First, lets just see how plain refinement types
  let us specify the key "goodness" invariant,
  and check it automatically.

* Next, we'll see how LH's new "type-level computation"
  abilities let us specify and check "correctness",
  and even better, understand _why_ the code works.

(Click here to [demo][demo])

<!-- more -->

<br>
<br>
<br>

<div class="row-fluid">
  <div class="span12 pagination-centered">
  <img src="https://ucsd-progsys.github.io/liquidhaskell-blog/static/img/escher-helix.jpg"
       alt="Ribbons" width="300">
       <br>
       <br>
       <br>
       Escher's Ribbons.
       <br>
       <br>
       <br>
  </div>
</div>

<div class="hidden">

<pre><span class=hs-linenum>52: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--short-names"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>53: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--exact-data-con"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>54: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-adt"</span>         <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>55: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--prune-unsorted"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>56: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--higherorder"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>57: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>58: </span>
<span class=hs-linenum>59: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>60: </span>
<span class=hs-linenum>61: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Interval</span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>I</span>
<span class=hs-linenum>62: </span>  <span class='hs-layout'>{</span> <span class='hs-varid'>from</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>63: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>to</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>64: </span>  <span class='hs-layout'>}</span> <span class='hs-keyword'>deriving</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(Show Interval)</span><span class='hs-conid'>Show</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>65: </span>
</pre>
</div>

Encoding Sets as Intervals
--------------------------

The key idea underlying the intervals data structure, is that
we can represent sets of integers like:

```haskell
{ 7, 1, 10, 3, 11, 2, 9, 12, 4}
```

by first *ordering* them into a list

```haskell
[ 1, 2, 3, 4, 7, 9, 10, 11, 12 ]
```

and then *partitioning* the list into compact intervals

```haskell
[ (1, 5), (7, 8), (9, 13) ]
```

That is,

1. Each interval `(from, to)` corresponds to the set
   `{from,from+1,...,to-1}`.

2. Ordering ensures there is a canonical representation
   that simplifies interval operations.

Making Illegal Intervals Unrepresentable
----------------------------------------

We require that the list of intervals be
"sorted, non-empty, disjoint and non-adjacent".
Lets follow the slogan of _make-illegal-values-unrepresentable_
to see how we can encode the legality constraints with refinements.

**A Single Interval**

We can ensure that each interval is **non-empty** by
refining the data type for a single interval to specify
that the `to` field must be strictly bigger than the `from`
field:


<pre><span class=hs-linenum>115: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Interval</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>I</span>
<span class=hs-linenum>116: </span>      <span class='hs-layout'>{</span> <span class='hs-varid'>from</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>117: </span>      <span class='hs-layout'>,</span> <span class='hs-varid'>to</span>   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>from</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>v</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>118: </span>      <span class='hs-layout'>}</span>
<span class=hs-linenum>119: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Now, LH will ensure that we can only construct *legal*,
non-empty `Interval`s


<pre><span class=hs-linenum>126: </span><a class=annot href="#"><span class=annottext>Interval</span><span class='hs-definition'>goodItv</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>10</span> <span class='hs-num'>20</span>
<span class=hs-linenum>127: </span><a class=annot href="#"><span class=annottext>Interval</span><span class='hs-definition'>badItv</span></a>  <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>20</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>10</span></span>     <span class='hs-comment'>-- ILLEGAL: empty interval!</span>
</pre>

**Many Intervals**

We can represent arbitrary sets as a *list of* `Interval`s:


<pre><span class=hs-linenum>135: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Intervals</span> <span class='hs-layout'>{</span> <span class='hs-varid'>itvs</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Interval</span><span class='hs-keyglyph'>]</span> <span class='hs-layout'>}</span>
</pre>

The plain Haskell type doesn't have enough teeth to
enforce legality, specifically, to ensure *ordering*
and the absence of *overlaps*. Refinements to the rescue!

First, we specify a *lower-bounded* `Interval` as:


<pre><span class=hs-linenum>145: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>LbInterval</span> <span class='hs-conid'>N</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Interval</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>N</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>from</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Intuitively, an `LbInterval n` is one that starts (at or) after `n`.

Next, we use the above to define an *ordered list*
of lower-bounded intervals:


<pre><span class=hs-linenum>154: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>LbInterval</span> <span class='hs-conid'>N</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>vHd</span> <span class='hs-varid'>vTl</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>to</span> <span class='hs-varid'>vHd</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>from</span> <span class='hs-varid'>vTl</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
</pre>

The signature above uses an [abstract-refinement][abs-ref]
to capture the legality requirements.

1. An `OrdInterval N` is a list of `Interval` that are
   lower-bounded by `N`, and

2. In each sub-list, the head `Interval` `vHd` *precedes*
   each in the tail `vTl`.

Legal Intervals
---------------

We can now describe legal `Intervals` simply as:


<pre><span class=hs-linenum>172: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Intervals</span> <span class='hs-layout'>{</span> <span class='hs-varid'>itvs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-num'>0</span> <span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

LH will now ensure that illegal `Intervals` are not representable.


<pre><span class=hs-linenum>178: </span><a class=annot href="#"><span class=annottext>Intervals</span><span class='hs-definition'>goodItvs</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:[{v : Interval | 0 &lt;= Intervals.from v}] -&gt; {v : Intervals | Intervals.itvs v == x1
                                                                     &amp;&amp; lqdc##$select v == x1
                                                                     &amp;&amp; v == Intervals.Intervals x1} | v == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-keyglyph'>[</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>1</span> <span class='hs-num'>5</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>7</span> <span class='hs-num'>8</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>9</span> <span class='hs-num'>13</span><span class='hs-keyglyph'>]</span>  <span class='hs-comment'>-- LEGAL</span>
<span class=hs-linenum>179: </span>
<span class=hs-linenum>180: </span><a class=annot href="#"><span class=annottext>Intervals</span><span class='hs-definition'>badItvs1</span></a>  <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:[{v : Interval | 0 &lt;= Intervals.from v}] -&gt; {v : Intervals | Intervals.itvs v == x1
                                                                     &amp;&amp; lqdc##$select v == x1
                                                                     &amp;&amp; v == Intervals.Intervals x1} | v == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>[</span></span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>7</span></span><span class=hs-error><span class='hs-layout'>,</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>5</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>8</span></span><span class=hs-error><span class='hs-keyglyph'>]</span></span>          <span class='hs-comment'>-- ILLEGAL: overlap!</span>
<span class=hs-linenum>181: </span><a class=annot href="#"><span class=annottext>Intervals</span><span class='hs-definition'>badItvs2</span></a>  <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:[{v : Interval | 0 &lt;= Intervals.from v}] -&gt; {v : Intervals | Intervals.itvs v == x1
                                                                     &amp;&amp; lqdc##$select v == x1
                                                                     &amp;&amp; v == Intervals.Intervals x1} | v == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>[</span></span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>5</span></span><span class=hs-error><span class='hs-layout'>,</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>9</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>13</span></span><span class=hs-error><span class='hs-layout'>,</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>7</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>8</span></span><span class=hs-error><span class='hs-keyglyph'>]</span></span>  <span class='hs-comment'>-- ILLEGAL: disorder!</span>
</pre>

Do the types _really_ capture the legality requirements?
In the original code, Breitner described goodness as a
recursively defined predicate that takes an additional
_lower bound_ `lb` and returns `True` iff the representation
was legal:


<pre><span class=hs-linenum>191: </span><span class='hs-definition'>goodLIs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Interval</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>192: </span><a class=annot href="#"><span class=annottext>x1:{v : Int | v &gt;= 0} -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; {v : Bool | v}</span><span class='hs-definition'>goodLIs</span></a> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span>              <span class='hs-keyglyph'>=</span> <span class='hs-conid'>True</span>
<span class=hs-linenum>193: </span><span class='hs-definition'>goodLIs</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f</span> <span class='hs-varid'>t</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>Bool</span><span class='hs-varid'>lb</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; x2:Bool -&gt; {v : Bool | v &lt;=&gt; x1
                                             &amp;&amp; x2} | v == GHC.Classes.&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; f &lt; t}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>t</span> <a class=annot href="#"><span class=annottext>{v : x1:Bool -&gt; x2:Bool -&gt; {v : Bool | v &lt;=&gt; x1
                                             &amp;&amp; x2} | v == GHC.Classes.&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>x1:{v : Int | v &gt;= 0} -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; {v : Bool | v}</span><span class='hs-varid'>goodLIs</span></a> <span class='hs-varid'>t</span> <span class='hs-varid'>is</span>
</pre>

We can check that our type-based representation is indeed
legit by checking that `goodLIs` returns `True` whenever it
is called with a valid of `OrdIntervals`:


<pre><span class=hs-linenum>201: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>goodLIs</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>is</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v :</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>| v }</span> <span class='hs-keyword'>@-}</span>
</pre>


Algorithms on Intervals
-----------------------

We represent legality as a type, but is that _good for_?
After all, we could, as seen above, just as well have written a
predicate `goodLIs`? The payoff comes when it comes to _using_
the `Intervals` e.g. to implement various set operations.

For example, here's the code for _intersecting_ two sets,
each represented as intervals. We've made exactly one
change to the function implemented by Breitner: we added
the extra lower-bound parameter `lb` to the recursive `go`
to make clear that the function takes two `OrdIntervals lb`
and returns an `OrdIntervals lb`.


<pre><span class=hs-linenum>221: </span><span class='hs-definition'>intersect</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span>
<span class=hs-linenum>222: </span><a class=annot href="#"><span class=annottext>Intervals -&gt; Intervals -&gt; Intervals</span><span class='hs-definition'>intersect</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:[{v : Interval | 0 &lt;= Intervals.from v}] -&gt; {v : Intervals | Intervals.itvs v == x1
                                                                     &amp;&amp; lqdc##$select v == x1
                                                                     &amp;&amp; v == Intervals.Intervals x1} | v == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] | v == go}</span><span class='hs-varid'>go</span></a> <span class='hs-num'>0</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>223: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>224: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>225: </span>    <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>226: </span>    <span class='hs-varid'>go</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>227: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f1</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f2</span> <span class='hs-varid'>t2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>228: </span>      <span class='hs-comment'>-- reorder for symmetry</span>
<span class=hs-linenum>229: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t1 &lt; t2}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>t2</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>230: </span>      <span class='hs-comment'>-- disjoint</span>
<span class=hs-linenum>231: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; f1 &gt;= t2}</span><span class='hs-varid'>f1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &gt;= x2}</span><span class='hs-varop'>&gt;=</span></a> <span class='hs-varid'>t2</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>232: </span>      <span class='hs-comment'>-- subset</span>
<span class=hs-linenum>233: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t1 == t2}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 == x2}</span><span class='hs-varop'>==</span></a> <span class='hs-varid'>t2</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f'</span> <span class='hs-varid'>t2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>234: </span>      <span class='hs-comment'>-- overlapping</span>
<span class=hs-linenum>235: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; f2 &lt; f1}</span><span class='hs-varid'>f2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>f1</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f'</span> <span class='hs-varid'>t2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>236: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>237: </span>      <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{v : Int | v == (if f1 &gt; f2 then f1 else f2)}</span><span class='hs-varid'>f'</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == (if x1 &gt; x2 then x1 else x2)}</span><span class='hs-varid'>max</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span>
</pre>

Internal vs External Verification
----------------------------------

By representing legality **internally** as a refinement type,
as opposed to **externally** as predicate (`goodLIs`) we have
exposed enough information about the structure of the values
that LH can _automatically_ chomp through the above code to
guarantee that we haven't messed up the invariants.

To appreciate the payoff, compare to the effort needed
to verify legality using the external representation
used in the [hs-to-coq proof][intersect-good].

The same principle and simplification benefits apply to both the `union`


<pre><span class=hs-linenum>256: </span><span class='hs-definition'>union</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span>
<span class=hs-linenum>257: </span><a class=annot href="#"><span class=annottext>Intervals -&gt; Intervals -&gt; Intervals</span><span class='hs-definition'>union</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:[{v : Interval | 0 &lt;= Intervals.from v}] -&gt; {v : Intervals | Intervals.itvs v == x1
                                                                     &amp;&amp; lqdc##$select v == x1
                                                                     &amp;&amp; v == Intervals.Intervals x1} | v == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] | v == go}</span><span class='hs-varid'>go</span></a> <span class='hs-num'>0</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>258: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>259: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>260: </span>    <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>[Interval]</span><span class='hs-varid'>is</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>is</span>
<span class=hs-linenum>261: </span>    <span class='hs-varid'>go</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>is</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>is</span>
<span class=hs-linenum>262: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f1</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f2</span> <span class='hs-varid'>t2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>263: </span>      <span class='hs-comment'>-- reorder for symmetry</span>
<span class=hs-linenum>264: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t1 &lt; t2}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt; x2}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>265: </span>      <span class='hs-comment'>-- disjoint</span>
<span class=hs-linenum>266: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; f1 &gt; t2}</span><span class='hs-varid'>f1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &gt; x2}</span><span class='hs-varop'>&gt;</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>i2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>267: </span>      <span class='hs-comment'>-- overlapping</span>
<span class=hs-linenum>268: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f'</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>269: </span>      <span class='hs-keyword'>where</span>
<span class=hs-linenum>270: </span>        <a class=annot href="#"><span class=annottext>{v : Int | v == (if f1 &lt; f2 then f1 else f2)}</span><span class='hs-varid'>f'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Int | v == (if x1 &lt; x2 then x1 else x2)}</span><span class='hs-varid'>min</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span>
</pre>

and the `subtract` functions too:


<pre><span class=hs-linenum>276: </span><span class='hs-definition'>subtract</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span>
<span class=hs-linenum>277: </span><a class=annot href="#"><span class=annottext>Intervals -&gt; Intervals -&gt; Intervals</span><span class='hs-definition'>subtract</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{v : x1:[{v : Interval | 0 &lt;= Intervals.from v}] -&gt; {v : Intervals | Intervals.itvs v == x1
                                                                     &amp;&amp; lqdc##$select v == x1
                                                                     &amp;&amp; v == Intervals.Intervals x1} | v == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] | v == go}</span><span class='hs-varid'>go</span></a> <span class='hs-num'>0</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>278: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>279: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>280: </span>    <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>[Interval]</span><span class='hs-varid'>is</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>is</span>
<span class=hs-linenum>281: </span>    <span class='hs-varid'>go</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-keyword'>_</span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>282: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f1</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f2</span> <span class='hs-varid'>t2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>283: </span>      <span class='hs-comment'>-- i2 past i1</span>
<span class=hs-linenum>284: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t1 &lt;= f2}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f2</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t1</span> <span class='hs-varid'>is1</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>285: </span>      <span class='hs-comment'>-- i1 past i2</span>
<span class=hs-linenum>286: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t2 &lt;= f1}</span><span class='hs-varid'>t2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f1</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>287: </span>      <span class='hs-comment'>-- i1 contained in i2</span>
<span class=hs-linenum>288: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; f2 &lt;= f1}</span><span class='hs-varid'>f2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f1</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t1 &lt;= t2}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-varid'>is1</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>289: </span>      <span class='hs-comment'>-- i2 covers beginning of i1</span>
<span class=hs-linenum>290: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; f2 &lt;= f1}</span><span class='hs-varid'>f2</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f1</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>291: </span>      <span class='hs-comment'>-- -- i2 covers end of i1</span>
<span class=hs-linenum>292: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{v : Bool | v &lt;=&gt; t1 &lt;= t2}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>x1:Int -&gt; x2:Int -&gt; {v : Bool | v &lt;=&gt; x1 &lt;= x2}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>f2</span> <span class='hs-varid'>is1</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>293: </span>      <span class='hs-comment'>-- i2 in the middle of i1</span>
<span class=hs-linenum>294: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>x1:Int -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}] -&gt; [{v : Interval | x1 &lt;= Intervals.from v}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>f2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{v : x1:Int -&gt; x2:{v : Int | x1 &lt; v} -&gt; {v : Interval | Intervals.to v == x2
                                                        &amp;&amp; Intervals.from v == x1
                                                        &amp;&amp; lqdc##$select v == x2
                                                        &amp;&amp; lqdc##$select v == x1
                                                        &amp;&amp; v == Intervals.I x1 x2} | v == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
</pre>


both of which require [non-trivial][union-good] [proofs][subtract-good]
in the _external style_. (Of course, its possible those proofs can be
simplified.)

Summing Up (and Looking Ahead)
------------------------------

I hope the above example illustrates why _"making illegal states"_
unrepresentable is a great principle for engineering code _and_ proofs.

That said, notice that with [hs-to-coq][nomeata-intervals], Breitner
was able to go _far beyond_ the above legality requirement: he was able
to specify and verify the far more important (and difficult) property
that the above is a _correct_ implementation of a Set library.

Is it even _possible_, let alone _easier_ to do that with LH?

[demo]:              http://goto.ucsd.edu/~rjhala/liquid/haskell/demo/#?demo=IntervalSets.hs
[intersect-good]:    https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L370-L439
[union-good]:        https://github.com/antalsz/hs-to-coq/blob/b7efc7a8dbacca384596fc0caf65e62e87ef2768/examples/intervals/Proofs_Function.v#L319-L382
[subtract-good]:     https://github.com/antalsz/hs-to-coq/blob/8f84d61093b7be36190142c795d6cd4496ef5aed/examples/intervals/Proofs.v#L565-L648
[abs-ref]:           /tags/abstract-refinements.html
[hs-to-coq]:         https://github.com/antalsz/hs-to-coq
[nomeata-intervals]: https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it
