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
  <img src="https://ucsd-progsys.github.io/liquidhaskell-blog/static/img/ribbon.png"
       alt="Ribbons" height="150">
  </div>
</div>


<div class="hidden">

<pre><span class=hs-linenum>46: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--short-names"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>47: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--exact-data-con"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>48: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-adt"</span>         <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>49: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--prune-unsorted"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>50: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--higherorder"</span>    <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>51: </span><span class='hs-keyword'>{-@</span> <span class='hs-conid'>LIQUID</span> <span class='hs-str'>"--no-termination"</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>52: </span>
<span class=hs-linenum>53: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>54: </span>
<span class=hs-linenum>55: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Interval</span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>I</span>
<span class=hs-linenum>56: </span>  <span class='hs-layout'>{</span> <span class='hs-varid'>from</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>57: </span>  <span class='hs-layout'>,</span> <span class='hs-varid'>to</span>   <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>58: </span>  <span class='hs-layout'>}</span> <span class='hs-keyword'>deriving</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>(Show Interval)</span><span class='hs-conid'>Show</span></a><span class='hs-layout'>)</span>
<span class=hs-linenum>59: </span>
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


<pre><span class=hs-linenum>109: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Interval</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>I</span>
<span class=hs-linenum>110: </span>      <span class='hs-layout'>{</span> <span class='hs-varid'>from</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span>
<span class=hs-linenum>111: </span>      <span class='hs-layout'>,</span> <span class='hs-varid'>to</span>   <span class='hs-keyglyph'>::</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>|</span> <span class='hs-varid'>from</span> <span class='hs-varop'>&lt;</span> <span class='hs-varid'>v</span> <span class='hs-layout'>}</span>
<span class=hs-linenum>112: </span>      <span class='hs-layout'>}</span>
<span class=hs-linenum>113: </span>  <span class='hs-keyword'>@-}</span>
</pre>

Now, LH will ensure that we can only construct *legal*,
non-empty `Interval`s


<pre><span class=hs-linenum>120: </span><a class=annot href="#"><span class=annottext>Interval</span><span class='hs-definition'>goodItv</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##740 : lq_tmp$x##741:Int -&gt; lq_tmp$x##742:{lq_tmp$x##737 : Int | lq_tmp$x##741 &lt; lq_tmp$x##737} -&gt; {lq_tmp$x##738 : Interval | Intervals.to lq_tmp$x##738 == lq_tmp$x##742
                                                                                                                                         &amp;&amp; Intervals.from lq_tmp$x##738 == lq_tmp$x##741
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##738 == lq_tmp$x##742
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##738 == lq_tmp$x##741
                                                                                                                                         &amp;&amp; (is$Intervals.I lq_tmp$x##738 &lt;=&gt; true)
                                                                                                                                         &amp;&amp; lq_tmp$x##738 == Intervals.I lq_tmp$x##741 lq_tmp$x##742
                                                                                                                                         &amp;&amp; lq_tmp$x##738 == Intervals.I lq_tmp$x##741 lq_tmp$x##742} | lq_tmp$x##740 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>10</span> <span class='hs-num'>20</span>
<span class=hs-linenum>121: </span><a class=annot href="#"><span class=annottext>Interval</span><span class='hs-definition'>badItv</span></a>  <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##762 : lq_tmp$x##763:Int -&gt; lq_tmp$x##764:{lq_tmp$x##759 : Int | lq_tmp$x##763 &lt; lq_tmp$x##759} -&gt; {lq_tmp$x##760 : Interval | Intervals.to lq_tmp$x##760 == lq_tmp$x##764
                                                                                                                                         &amp;&amp; Intervals.from lq_tmp$x##760 == lq_tmp$x##763
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##760 == lq_tmp$x##764
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##760 == lq_tmp$x##763
                                                                                                                                         &amp;&amp; (is$Intervals.I lq_tmp$x##760 &lt;=&gt; true)
                                                                                                                                         &amp;&amp; lq_tmp$x##760 == Intervals.I lq_tmp$x##763 lq_tmp$x##764
                                                                                                                                         &amp;&amp; lq_tmp$x##760 == Intervals.I lq_tmp$x##763 lq_tmp$x##764} | lq_tmp$x##762 == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>20</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>10</span></span>     <span class='hs-comment'>-- ILLEGAL: empty interval!</span>
</pre>

**Many Intervals**

We can represent arbitrary sets as a *list of* `Interval`s:


<pre><span class=hs-linenum>129: </span><span class='hs-keyword'>data</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Intervals</span> <span class='hs-layout'>{</span> <span class='hs-varid'>itvs</span> <span class='hs-keyglyph'>::</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Interval</span><span class='hs-keyglyph'>]</span> <span class='hs-layout'>}</span>
</pre>

The plain Haskell type doesn't have enough teeth to
enforce legality, specifically, to ensure *ordering*
and the absence of *overlaps*. Refinements to the rescue!

First, we specify a *lower-bounded* `Interval` as:


<pre><span class=hs-linenum>139: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>LbInterval</span> <span class='hs-conid'>N</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>{</span><span class='hs-varid'>v</span><span class='hs-conop'>:</span><span class='hs-conid'>Interval</span> <span class='hs-keyglyph'>|</span> <span class='hs-conid'>N</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>from</span> <span class='hs-varid'>v</span><span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

Intuitively, an `LbInterval n` is one that starts (at or) after `n`.

Next, we use the above to define an *ordered list*
of lower-bounded intervals:


<pre><span class=hs-linenum>148: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>type</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-conid'>N</span> <span class='hs-keyglyph'>=</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>LbInterval</span> <span class='hs-conid'>N</span><span class='hs-keyglyph'>]</span><span class='hs-varop'>&lt;</span><span class='hs-layout'>{</span><span class='hs-keyglyph'>\</span><span class='hs-varid'>vHd</span> <span class='hs-varid'>vTl</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>to</span> <span class='hs-varid'>vHd</span> <span class='hs-varop'>&lt;=</span> <span class='hs-varid'>from</span> <span class='hs-varid'>vTl</span><span class='hs-layout'>}</span><span class='hs-varop'>&gt;</span> <span class='hs-keyword'>@-}</span>
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


<pre><span class=hs-linenum>166: </span><span class='hs-keyword'>{-@</span> <span class='hs-keyword'>data</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>Intervals</span> <span class='hs-layout'>{</span> <span class='hs-varid'>itvs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-num'>0</span> <span class='hs-layout'>}</span> <span class='hs-keyword'>@-}</span>
</pre>

LH will now ensure that illegal `Intervals` are not representable.


<pre><span class=hs-linenum>172: </span><a class=annot href="#"><span class=annottext>Intervals</span><span class='hs-definition'>goodItvs</span></a>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##950 : lq_tmp$x##952:[{lq_tmp$x##945 : Interval | 0 &lt;= Intervals.from lq_tmp$x##945}] -&gt; {lq_tmp$x##949 : Intervals | Intervals.itvs lq_tmp$x##949 == lq_tmp$x##952
                                                                                                                                &amp;&amp; lqdc##$select##Intervals.Intervals##1 lq_tmp$x##949 == lq_tmp$x##952
                                                                                                                                &amp;&amp; (is$Intervals.Intervals lq_tmp$x##949 &lt;=&gt; true)
                                                                                                                                &amp;&amp; lq_tmp$x##949 == Intervals.Intervals lq_tmp$x##952
                                                                                                                                &amp;&amp; lq_tmp$x##949 == Intervals.Intervals lq_tmp$x##952} | lq_tmp$x##950 == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-keyglyph'>[</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##784 : lq_tmp$x##785:Int -&gt; lq_tmp$x##786:{lq_tmp$x##781 : Int | lq_tmp$x##785 &lt; lq_tmp$x##781} -&gt; {lq_tmp$x##782 : Interval | Intervals.to lq_tmp$x##782 == lq_tmp$x##786
                                                                                                                                         &amp;&amp; Intervals.from lq_tmp$x##782 == lq_tmp$x##785
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##782 == lq_tmp$x##786
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##782 == lq_tmp$x##785
                                                                                                                                         &amp;&amp; (is$Intervals.I lq_tmp$x##782 &lt;=&gt; true)
                                                                                                                                         &amp;&amp; lq_tmp$x##782 == Intervals.I lq_tmp$x##785 lq_tmp$x##786
                                                                                                                                         &amp;&amp; lq_tmp$x##782 == Intervals.I lq_tmp$x##785 lq_tmp$x##786} | lq_tmp$x##784 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>1</span> <span class='hs-num'>5</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##806 : lq_tmp$x##807:Int -&gt; lq_tmp$x##808:{lq_tmp$x##803 : Int | lq_tmp$x##807 &lt; lq_tmp$x##803} -&gt; {lq_tmp$x##804 : Interval | Intervals.to lq_tmp$x##804 == lq_tmp$x##808
                                                                                                                                         &amp;&amp; Intervals.from lq_tmp$x##804 == lq_tmp$x##807
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##804 == lq_tmp$x##808
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##804 == lq_tmp$x##807
                                                                                                                                         &amp;&amp; (is$Intervals.I lq_tmp$x##804 &lt;=&gt; true)
                                                                                                                                         &amp;&amp; lq_tmp$x##804 == Intervals.I lq_tmp$x##807 lq_tmp$x##808
                                                                                                                                         &amp;&amp; lq_tmp$x##804 == Intervals.I lq_tmp$x##807 lq_tmp$x##808} | lq_tmp$x##806 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>7</span> <span class='hs-num'>8</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##828 : lq_tmp$x##829:Int -&gt; lq_tmp$x##830:{lq_tmp$x##825 : Int | lq_tmp$x##829 &lt; lq_tmp$x##825} -&gt; {lq_tmp$x##826 : Interval | Intervals.to lq_tmp$x##826 == lq_tmp$x##830
                                                                                                                                         &amp;&amp; Intervals.from lq_tmp$x##826 == lq_tmp$x##829
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##826 == lq_tmp$x##830
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##826 == lq_tmp$x##829
                                                                                                                                         &amp;&amp; (is$Intervals.I lq_tmp$x##826 &lt;=&gt; true)
                                                                                                                                         &amp;&amp; lq_tmp$x##826 == Intervals.I lq_tmp$x##829 lq_tmp$x##830
                                                                                                                                         &amp;&amp; lq_tmp$x##826 == Intervals.I lq_tmp$x##829 lq_tmp$x##830} | lq_tmp$x##828 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-num'>9</span> <span class='hs-num'>13</span><span class='hs-keyglyph'>]</span>  <span class='hs-comment'>-- LEGAL</span>
<span class=hs-linenum>173: </span>
<span class=hs-linenum>174: </span><a class=annot href="#"><span class=annottext>Intervals</span><span class='hs-definition'>badItvs1</span></a>  <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##1088 : lq_tmp$x##1090:[{lq_tmp$x##1083 : Interval | 0 &lt;= Intervals.from lq_tmp$x##1083}] -&gt; {lq_tmp$x##1087 : Intervals | Intervals.itvs lq_tmp$x##1087 == lq_tmp$x##1090
                                                                                                                                     &amp;&amp; lqdc##$select##Intervals.Intervals##1 lq_tmp$x##1087 == lq_tmp$x##1090
                                                                                                                                     &amp;&amp; (is$Intervals.Intervals lq_tmp$x##1087 &lt;=&gt; true)
                                                                                                                                     &amp;&amp; lq_tmp$x##1087 == Intervals.Intervals lq_tmp$x##1090
                                                                                                                                     &amp;&amp; lq_tmp$x##1087 == Intervals.Intervals lq_tmp$x##1090} | lq_tmp$x##1088 == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>[</span></span><span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##976 : lq_tmp$x##977:Int -&gt; lq_tmp$x##978:{lq_tmp$x##973 : Int | lq_tmp$x##977 &lt; lq_tmp$x##973} -&gt; {lq_tmp$x##974 : Interval | Intervals.to lq_tmp$x##974 == lq_tmp$x##978
                                                                                                                                         &amp;&amp; Intervals.from lq_tmp$x##974 == lq_tmp$x##977
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##974 == lq_tmp$x##978
                                                                                                                                         &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##974 == lq_tmp$x##977
                                                                                                                                         &amp;&amp; (is$Intervals.I lq_tmp$x##974 &lt;=&gt; true)
                                                                                                                                         &amp;&amp; lq_tmp$x##974 == Intervals.I lq_tmp$x##977 lq_tmp$x##978
                                                                                                                                         &amp;&amp; lq_tmp$x##974 == Intervals.I lq_tmp$x##977 lq_tmp$x##978} | lq_tmp$x##976 == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>7</span></span><span class=hs-error><span class='hs-layout'>,</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##998 : lq_tmp$x##999:Int -&gt; lq_tmp$x##1000:{lq_tmp$x##995 : Int | lq_tmp$x##999 &lt; lq_tmp$x##995} -&gt; {lq_tmp$x##996 : Interval | Intervals.to lq_tmp$x##996 == lq_tmp$x##1000
                                                                                                                                          &amp;&amp; Intervals.from lq_tmp$x##996 == lq_tmp$x##999
                                                                                                                                          &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##996 == lq_tmp$x##1000
                                                                                                                                          &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##996 == lq_tmp$x##999
                                                                                                                                          &amp;&amp; (is$Intervals.I lq_tmp$x##996 &lt;=&gt; true)
                                                                                                                                          &amp;&amp; lq_tmp$x##996 == Intervals.I lq_tmp$x##999 lq_tmp$x##1000
                                                                                                                                          &amp;&amp; lq_tmp$x##996 == Intervals.I lq_tmp$x##999 lq_tmp$x##1000} | lq_tmp$x##998 == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>5</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>8</span></span><span class=hs-error><span class='hs-keyglyph'>]</span></span>          <span class='hs-comment'>-- ILLEGAL: overlap!</span>
<span class=hs-linenum>175: </span><a class=annot href="#"><span class=annottext>Intervals</span><span class='hs-definition'>badItvs2</span></a>  <span class='hs-keyglyph'>=</span> <span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##1280 : lq_tmp$x##1282:[{lq_tmp$x##1275 : Interval | 0 &lt;= Intervals.from lq_tmp$x##1275}] -&gt; {lq_tmp$x##1279 : Intervals | Intervals.itvs lq_tmp$x##1279 == lq_tmp$x##1282
                                                                                                                                     &amp;&amp; lqdc##$select##Intervals.Intervals##1 lq_tmp$x##1279 == lq_tmp$x##1282
                                                                                                                                     &amp;&amp; (is$Intervals.Intervals lq_tmp$x##1279 &lt;=&gt; true)
                                                                                                                                     &amp;&amp; lq_tmp$x##1279 == Intervals.Intervals lq_tmp$x##1282
                                                                                                                                     &amp;&amp; lq_tmp$x##1279 == Intervals.Intervals lq_tmp$x##1282} | lq_tmp$x##1280 == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-keyglyph'>[</span></span><span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##1114 : lq_tmp$x##1115:Int -&gt; lq_tmp$x##1116:{lq_tmp$x##1111 : Int | lq_tmp$x##1115 &lt; lq_tmp$x##1111} -&gt; {lq_tmp$x##1112 : Interval | Intervals.to lq_tmp$x##1112 == lq_tmp$x##1116
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1112 == lq_tmp$x##1115
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1112 == lq_tmp$x##1116
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1112 == lq_tmp$x##1115
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1112 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1112 == Intervals.I lq_tmp$x##1115 lq_tmp$x##1116
                                                                                                                                                &amp;&amp; lq_tmp$x##1112 == Intervals.I lq_tmp$x##1115 lq_tmp$x##1116} | lq_tmp$x##1114 == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>1</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>5</span></span><span class=hs-error><span class='hs-layout'>,</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##1136 : lq_tmp$x##1137:Int -&gt; lq_tmp$x##1138:{lq_tmp$x##1133 : Int | lq_tmp$x##1137 &lt; lq_tmp$x##1133} -&gt; {lq_tmp$x##1134 : Interval | Intervals.to lq_tmp$x##1134 == lq_tmp$x##1138
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1134 == lq_tmp$x##1137
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1134 == lq_tmp$x##1138
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1134 == lq_tmp$x##1137
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1134 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1134 == Intervals.I lq_tmp$x##1137 lq_tmp$x##1138
                                                                                                                                                &amp;&amp; lq_tmp$x##1134 == Intervals.I lq_tmp$x##1137 lq_tmp$x##1138} | lq_tmp$x##1136 == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>9</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>13</span></span><span class=hs-error><span class='hs-layout'>,</span></span><span class=hs-error> </span><span class=hs-error><a class=annot href="#"><span class=annottext>{lq_tmp$x##1158 : lq_tmp$x##1159:Int -&gt; lq_tmp$x##1160:{lq_tmp$x##1155 : Int | lq_tmp$x##1159 &lt; lq_tmp$x##1155} -&gt; {lq_tmp$x##1156 : Interval | Intervals.to lq_tmp$x##1156 == lq_tmp$x##1160
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1156 == lq_tmp$x##1159
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1156 == lq_tmp$x##1160
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1156 == lq_tmp$x##1159
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1156 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1156 == Intervals.I lq_tmp$x##1159 lq_tmp$x##1160
                                                                                                                                                &amp;&amp; lq_tmp$x##1156 == Intervals.I lq_tmp$x##1159 lq_tmp$x##1160} | lq_tmp$x##1158 == Intervals.I}</span><span class='hs-conid'>I</span></a></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>7</span></span><span class=hs-error> </span><span class=hs-error><span class='hs-num'>8</span></span><span class=hs-error><span class='hs-keyglyph'>]</span></span>  <span class='hs-comment'>-- ILLEGAL: disorder!</span>
</pre>

Do the types _really_ capture the legality requirements?
In the original code, Breitner described goodness as a
recursively defined predicate that takes an additional
_lower bound_ `lb` and returns `True` iff the representation
was legal:


<pre><span class=hs-linenum>185: </span><span class='hs-definition'>goodLIs</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyglyph'>[</span><span class='hs-conid'>Interval</span><span class='hs-keyglyph'>]</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Bool</span>
<span class=hs-linenum>186: </span><a class=annot href="#"><span class=annottext>lq_tmp$x##6334:{lq_tmp$x##0 : Int | lq_tmp$x##0 &gt;= 0} -&gt; lq_tmp$x##6335:[{lq_tmp$x##11 : Interval | lq_tmp$x##6334 &lt;= Intervals.from lq_tmp$x##11}] -&gt; {v : Bool | v}</span><span class='hs-definition'>goodLIs</span></a> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span>              <span class='hs-keyglyph'>=</span> <span class='hs-conid'>True</span>
<span class=hs-linenum>187: </span><span class='hs-definition'>goodLIs</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f</span> <span class='hs-varid'>t</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##6422 : Bool | lq_tmp$x##6422 &lt;=&gt; ds_d2nn &lt;= f##a134}</span><span class='hs-varid'>lb</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##6427:{lq_tmp$x##6432 : Int^"lq_tmp$x##6431" | $k_##6430[VV##6429:=lq_tmp$x##6432][lq_tmp$x##6426:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##6428:{lq_tmp$x##6432 : Int^"lq_tmp$x##6431" | $k_##6430[VV##6429:=lq_tmp$x##6432][lq_tmp$x##6426:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##6422 : Bool | lq_tmp$x##6422 &lt;=&gt; lq_tmp$x##6427 &lt;= lq_tmp$x##6428}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##6491 : lq_tmp$x##6492:Bool -&gt; lq_tmp$x##6493:Bool -&gt; {lq_tmp$x##6489 : Bool | lq_tmp$x##6489 &lt;=&gt; lq_tmp$x##6492
                                                                                                            &amp;&amp; lq_tmp$x##6493} | lq_tmp$x##6491 == GHC.Classes.&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>{lq_tmp$x##6442 : Bool | lq_tmp$x##6442 &lt;=&gt; f##a134 &lt; t##a135}</span><span class='hs-varid'>f</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##6447:{lq_tmp$x##6452 : Int^"lq_tmp$x##6451" | $k_##6450[VV##6449:=lq_tmp$x##6452][lq_tmp$x##6446:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##6448:{lq_tmp$x##6452 : Int^"lq_tmp$x##6451" | $k_##6450[VV##6449:=lq_tmp$x##6452][lq_tmp$x##6446:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##6442 : Bool | lq_tmp$x##6442 &lt;=&gt; lq_tmp$x##6447 &lt; lq_tmp$x##6448}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>t</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##6481 : lq_tmp$x##6482:Bool -&gt; lq_tmp$x##6483:Bool -&gt; {lq_tmp$x##6479 : Bool | lq_tmp$x##6479 &lt;=&gt; lq_tmp$x##6482
                                                                                                            &amp;&amp; lq_tmp$x##6483} | lq_tmp$x##6481 == GHC.Classes.&amp;&amp;}</span><span class='hs-varop'>&amp;&amp;</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##6334:{lq_tmp$x##0 : Int | lq_tmp$x##0 &gt;= 0} -&gt; lq_tmp$x##6335:[{lq_tmp$x##11 : Interval | lq_tmp$x##6334 &lt;= Intervals.from lq_tmp$x##11}] -&gt; {v : Bool | v}</span><span class='hs-varid'>goodLIs</span></a> <span class='hs-varid'>t</span> <span class='hs-varid'>is</span>
</pre>

We can check that our type-based representation is indeed
legit by checking that `goodLIs` returns `True` whenever it
is called with a valid of `OrdIntervals`:


<pre><span class=hs-linenum>195: </span><span class='hs-keyword'>{-@</span> <span class='hs-varid'>goodLIs</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Nat</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-varid'>is</span><span class='hs-conop'>:</span><span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-keyword'>{v :</span> <span class='hs-conid'>Bool</span> <span class='hs-keyword'>| v }</span> <span class='hs-keyword'>@-}</span>
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


<pre><span class=hs-linenum>215: </span><span class='hs-definition'>intersect</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span>
<span class=hs-linenum>216: </span><a class=annot href="#"><span class=annottext>lq_tmp$x##1290:Intervals -&gt; lq_tmp$x##1291:Intervals -&gt; Intervals</span><span class='hs-definition'>intersect</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##2340 : lq_tmp$x##2342:[{lq_tmp$x##2335 : Interval | 0 &lt;= Intervals.from lq_tmp$x##2335}] -&gt; {lq_tmp$x##2339 : Intervals | Intervals.itvs lq_tmp$x##2339 == lq_tmp$x##2342
                                                                                                                                     &amp;&amp; lqdc##$select##Intervals.Intervals##1 lq_tmp$x##2339 == lq_tmp$x##2342
                                                                                                                                     &amp;&amp; (is$Intervals.Intervals lq_tmp$x##2339 &lt;=&gt; true)
                                                                                                                                     &amp;&amp; lq_tmp$x##2339 == Intervals.Intervals lq_tmp$x##2342
                                                                                                                                     &amp;&amp; lq_tmp$x##2339 == Intervals.Intervals lq_tmp$x##2342} | lq_tmp$x##2340 == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##2314 : lq_tmp$x##2317:Int -&gt; lq_tmp$x##2318:[{lq_tmp$x##2300 : Interval | lq_tmp$x##2317 &lt;= Intervals.from lq_tmp$x##2300}] -&gt; lq_tmp$x##2319:[{lq_tmp$x##2304 : Interval | lq_tmp$x##2317 &lt;= Intervals.from lq_tmp$x##2304}] -&gt; [{lq_tmp$x##2308 : Interval | lq_tmp$x##2317 &lt;= Intervals.from lq_tmp$x##2308}] | lq_tmp$x##2314 == go##a23U}</span><span class='hs-varid'>go</span></a> <span class='hs-num'>0</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>217: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>218: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>219: </span>    <a class=annot href="#"><span class=annottext>lq_tmp$x##1338:Int -&gt; lq_tmp$x##1339:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##1340:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-keyword'>_</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>220: </span>    <span class='hs-varid'>go</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-keyword'>_</span> <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>221: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f1</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f2</span> <span class='hs-varid'>t2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>222: </span>      <span class='hs-comment'>-- reorder for symmetry</span>
<span class=hs-linenum>223: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##1637 : Bool | lq_tmp$x##1637 &lt;=&gt; t1##a23Y &lt; t2##a242}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##1642:{lq_tmp$x##1647 : Int^"lq_tmp$x##1646" | $k_##1645[lq_tmp$x##1641:=GHC.Classes.$fOrdInt][VV##1644:=lq_tmp$x##1647]} -&gt; lq_tmp$x##1643:{lq_tmp$x##1647 : Int^"lq_tmp$x##1646" | $k_##1645[lq_tmp$x##1641:=GHC.Classes.$fOrdInt][VV##1644:=lq_tmp$x##1647]} -&gt; {lq_tmp$x##1637 : Bool | lq_tmp$x##1637 &lt;=&gt; lq_tmp$x##1642 &lt; lq_tmp$x##1643}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>t2</span>   <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##1338:Int -&gt; lq_tmp$x##1339:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##1340:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>224: </span>      <span class='hs-comment'>-- disjoint</span>
<span class=hs-linenum>225: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##1664 : Bool | lq_tmp$x##1664 &lt;=&gt; f1##a23X &gt;= t2##a242}</span><span class='hs-varid'>f1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##1669:{lq_tmp$x##1674 : Int^"lq_tmp$x##1673" | $k_##1672[lq_tmp$x##1668:=GHC.Classes.$fOrdInt][VV##1671:=lq_tmp$x##1674]} -&gt; lq_tmp$x##1670:{lq_tmp$x##1674 : Int^"lq_tmp$x##1673" | $k_##1672[lq_tmp$x##1668:=GHC.Classes.$fOrdInt][VV##1671:=lq_tmp$x##1674]} -&gt; {lq_tmp$x##1664 : Bool | lq_tmp$x##1664 &lt;=&gt; lq_tmp$x##1669 &gt;= lq_tmp$x##1670}</span><span class='hs-varop'>&gt;=</span></a> <span class='hs-varid'>t2</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##1338:Int -&gt; lq_tmp$x##1339:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##1340:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>226: </span>      <span class='hs-comment'>-- subset</span>
<span class=hs-linenum>227: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##1691 : Bool | lq_tmp$x##1691 &lt;=&gt; t1##a23Y == t2##a242}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##1696:{lq_tmp$x##1701 : Int^"lq_tmp$x##1700" | $k_##1699[lq_tmp$x##1695:=GHC.Classes.$fEqInt][VV##1698:=lq_tmp$x##1701]} -&gt; lq_tmp$x##1697:{lq_tmp$x##1701 : Int^"lq_tmp$x##1700" | $k_##1699[lq_tmp$x##1695:=GHC.Classes.$fEqInt][VV##1698:=lq_tmp$x##1701]} -&gt; {lq_tmp$x##1691 : Bool | lq_tmp$x##1691 &lt;=&gt; lq_tmp$x##1696 == lq_tmp$x##1697}</span><span class='hs-varop'>==</span></a> <span class='hs-varid'>t2</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##1983 : lq_tmp$x##1984:Int -&gt; lq_tmp$x##1985:{lq_tmp$x##1980 : Int | lq_tmp$x##1984 &lt; lq_tmp$x##1980} -&gt; {lq_tmp$x##1981 : Interval | Intervals.to lq_tmp$x##1981 == lq_tmp$x##1985
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1981 == lq_tmp$x##1984
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1981 == lq_tmp$x##1985
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1981 == lq_tmp$x##1984
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1981 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1981 == Intervals.I lq_tmp$x##1984 lq_tmp$x##1985
                                                                                                                                                &amp;&amp; lq_tmp$x##1981 == Intervals.I lq_tmp$x##1984 lq_tmp$x##1985} | lq_tmp$x##1983 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f'</span> <span class='hs-varid'>t2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##1338:Int -&gt; lq_tmp$x##1339:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##1340:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>228: </span>      <span class='hs-comment'>-- overlapping</span>
<span class=hs-linenum>229: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##1718 : Bool | lq_tmp$x##1718 &lt;=&gt; f2##a241 &lt; f1##a23X}</span><span class='hs-varid'>f2</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##1723:{lq_tmp$x##1728 : Int^"lq_tmp$x##1727" | $k_##1726[VV##1725:=lq_tmp$x##1728][lq_tmp$x##1722:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##1724:{lq_tmp$x##1728 : Int^"lq_tmp$x##1727" | $k_##1726[VV##1725:=lq_tmp$x##1728][lq_tmp$x##1722:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##1718 : Bool | lq_tmp$x##1718 &lt;=&gt; lq_tmp$x##1723 &lt; lq_tmp$x##1724}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>f1</span>   <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##1859 : lq_tmp$x##1860:Int -&gt; lq_tmp$x##1861:{lq_tmp$x##1856 : Int | lq_tmp$x##1860 &lt; lq_tmp$x##1856} -&gt; {lq_tmp$x##1857 : Interval | Intervals.to lq_tmp$x##1857 == lq_tmp$x##1861
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1857 == lq_tmp$x##1860
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1857 == lq_tmp$x##1861
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1857 == lq_tmp$x##1860
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1857 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1857 == Intervals.I lq_tmp$x##1860 lq_tmp$x##1861
                                                                                                                                                &amp;&amp; lq_tmp$x##1857 == Intervals.I lq_tmp$x##1860 lq_tmp$x##1861} | lq_tmp$x##1859 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f'</span> <span class='hs-varid'>t2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##1338:Int -&gt; lq_tmp$x##1339:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##1340:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##1869 : lq_tmp$x##1870:Int -&gt; lq_tmp$x##1871:{lq_tmp$x##1866 : Int | lq_tmp$x##1870 &lt; lq_tmp$x##1866} -&gt; {lq_tmp$x##1867 : Interval | Intervals.to lq_tmp$x##1867 == lq_tmp$x##1871
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1867 == lq_tmp$x##1870
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1867 == lq_tmp$x##1871
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1867 == lq_tmp$x##1870
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1867 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1867 == Intervals.I lq_tmp$x##1870 lq_tmp$x##1871
                                                                                                                                                &amp;&amp; lq_tmp$x##1867 == Intervals.I lq_tmp$x##1870 lq_tmp$x##1871} | lq_tmp$x##1869 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>230: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##1338:Int -&gt; lq_tmp$x##1339:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##1340:[{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##1338 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##1745 : lq_tmp$x##1746:Int -&gt; lq_tmp$x##1747:{lq_tmp$x##1742 : Int | lq_tmp$x##1746 &lt; lq_tmp$x##1742} -&gt; {lq_tmp$x##1743 : Interval | Intervals.to lq_tmp$x##1743 == lq_tmp$x##1747
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##1743 == lq_tmp$x##1746
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##1743 == lq_tmp$x##1747
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##1743 == lq_tmp$x##1746
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##1743 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##1743 == Intervals.I lq_tmp$x##1746 lq_tmp$x##1747
                                                                                                                                                &amp;&amp; lq_tmp$x##1743 == Intervals.I lq_tmp$x##1746 lq_tmp$x##1747} | lq_tmp$x##1745 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>231: </span>      <span class='hs-keyword'>where</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##1627 : Int^"lq_tmp$x##1626" | $k_##1625[lq_tmp$x##1622:=f1##a23X][lq_tmp$x##1621:=GHC.Classes.$fOrdInt][lq_tmp$x##1623:=f2##a241][VV##1624:=lq_tmp$x##1627]
                                         &amp;&amp; lq_tmp$x##1627 == (if f1##a23X &gt; f2##a241 then f1##a23X else f2##a241)}</span><span class='hs-varid'>f'</span></a>    <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##1622:{lq_tmp$x##1627 : Int^"lq_tmp$x##1626" | $k_##1625[lq_tmp$x##1621:=GHC.Classes.$fOrdInt][VV##1624:=lq_tmp$x##1627]} -&gt; lq_tmp$x##1623:{lq_tmp$x##1627 : Int^"lq_tmp$x##1626" | $k_##1625[lq_tmp$x##1621:=GHC.Classes.$fOrdInt][VV##1624:=lq_tmp$x##1627]} -&gt; {lq_tmp$x##1627 : Int^"lq_tmp$x##1626" | $k_##1625[lq_tmp$x##1621:=GHC.Classes.$fOrdInt][VV##1624:=lq_tmp$x##1627]
                                                                                                                                                                                                                                                                                                                     &amp;&amp; lq_tmp$x##1627 == (if lq_tmp$x##1622 &gt; lq_tmp$x##1623 then lq_tmp$x##1622 else lq_tmp$x##1623)}</span><span class='hs-varid'>max</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span>
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


<pre><span class=hs-linenum>250: </span><span class='hs-definition'>union</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span>
<span class=hs-linenum>251: </span><a class=annot href="#"><span class=annottext>lq_tmp$x##2351:Intervals -&gt; lq_tmp$x##2352:Intervals -&gt; Intervals</span><span class='hs-definition'>union</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3123 : lq_tmp$x##3125:[{lq_tmp$x##3118 : Interval | 0 &lt;= Intervals.from lq_tmp$x##3118}] -&gt; {lq_tmp$x##3122 : Intervals | Intervals.itvs lq_tmp$x##3122 == lq_tmp$x##3125
                                                                                                                                     &amp;&amp; lqdc##$select##Intervals.Intervals##1 lq_tmp$x##3122 == lq_tmp$x##3125
                                                                                                                                     &amp;&amp; (is$Intervals.Intervals lq_tmp$x##3122 &lt;=&gt; true)
                                                                                                                                     &amp;&amp; lq_tmp$x##3122 == Intervals.Intervals lq_tmp$x##3125
                                                                                                                                     &amp;&amp; lq_tmp$x##3122 == Intervals.Intervals lq_tmp$x##3125} | lq_tmp$x##3123 == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##3097 : lq_tmp$x##3100:Int -&gt; lq_tmp$x##3101:[{lq_tmp$x##3083 : Interval | lq_tmp$x##3100 &lt;= Intervals.from lq_tmp$x##3083}] -&gt; lq_tmp$x##3102:[{lq_tmp$x##3087 : Interval | lq_tmp$x##3100 &lt;= Intervals.from lq_tmp$x##3087}] -&gt; [{lq_tmp$x##3091 : Interval | lq_tmp$x##3100 &lt;= Intervals.from lq_tmp$x##3091}] | lq_tmp$x##3097 == go##a247}</span><span class='hs-varid'>go</span></a> <span class='hs-num'>0</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>252: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>253: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>254: </span>    <a class=annot href="#"><span class=annottext>lq_tmp$x##2399:Int -&gt; lq_tmp$x##2400:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##2401:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>[{lq_tmp$x##11 : Interval | ds_d2mb &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>is</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>is</span>
<span class=hs-linenum>255: </span>    <span class='hs-varid'>go</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-varid'>is</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>is</span>
<span class=hs-linenum>256: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f1</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f2</span> <span class='hs-varid'>t2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>257: </span>      <span class='hs-comment'>-- reorder for symmetry</span>
<span class=hs-linenum>258: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##2680 : Bool | lq_tmp$x##2680 &lt;=&gt; t1##a24d &lt; t2##a24h}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##2685:{lq_tmp$x##2690 : Int^"lq_tmp$x##2689" | $k_##2688[VV##2687:=lq_tmp$x##2690][lq_tmp$x##2684:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##2686:{lq_tmp$x##2690 : Int^"lq_tmp$x##2689" | $k_##2688[VV##2687:=lq_tmp$x##2690][lq_tmp$x##2684:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##2680 : Bool | lq_tmp$x##2680 &lt;=&gt; lq_tmp$x##2685 &lt; lq_tmp$x##2686}</span><span class='hs-varop'>&lt;</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##2399:Int -&gt; lq_tmp$x##2400:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##2401:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span>
<span class=hs-linenum>259: </span>      <span class='hs-comment'>-- disjoint</span>
<span class=hs-linenum>260: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##2707 : Bool | lq_tmp$x##2707 &lt;=&gt; f1##a24c &gt; t2##a24h}</span><span class='hs-varid'>f1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##2712:{lq_tmp$x##2717 : Int^"lq_tmp$x##2716" | $k_##2715[VV##2714:=lq_tmp$x##2717][lq_tmp$x##2711:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##2713:{lq_tmp$x##2717 : Int^"lq_tmp$x##2716" | $k_##2715[VV##2714:=lq_tmp$x##2717][lq_tmp$x##2711:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##2707 : Bool | lq_tmp$x##2707 &lt;=&gt; lq_tmp$x##2712 &gt; lq_tmp$x##2713}</span><span class='hs-varop'>&gt;</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>i2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##2399:Int -&gt; lq_tmp$x##2400:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##2401:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>261: </span>      <span class='hs-comment'>-- overlapping</span>
<span class=hs-linenum>262: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span>  <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##2399:Int -&gt; lq_tmp$x##2400:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##2401:[{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##2399 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##2734 : lq_tmp$x##2735:Int -&gt; lq_tmp$x##2736:{lq_tmp$x##2731 : Int | lq_tmp$x##2735 &lt; lq_tmp$x##2731} -&gt; {lq_tmp$x##2732 : Interval | Intervals.to lq_tmp$x##2732 == lq_tmp$x##2736
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##2732 == lq_tmp$x##2735
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##2732 == lq_tmp$x##2736
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##2732 == lq_tmp$x##2735
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##2732 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##2732 == Intervals.I lq_tmp$x##2735 lq_tmp$x##2736
                                                                                                                                                &amp;&amp; lq_tmp$x##2732 == Intervals.I lq_tmp$x##2735 lq_tmp$x##2736} | lq_tmp$x##2734 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f'</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>263: </span>      <span class='hs-keyword'>where</span>
<span class=hs-linenum>264: </span>        <a class=annot href="#"><span class=annottext>{lq_tmp$x##2670 : Int^"lq_tmp$x##2669" | $k_##2668[lq_tmp$x##2664:=GHC.Classes.$fOrdInt][VV##2667:=lq_tmp$x##2670][lq_tmp$x##2665:=f1##a24c][lq_tmp$x##2666:=f2##a24g]
                                         &amp;&amp; lq_tmp$x##2670 == (if f1##a24c &lt; f2##a24g then f1##a24c else f2##a24g)}</span><span class='hs-varid'>f'</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##2665:{lq_tmp$x##2670 : Int^"lq_tmp$x##2669" | $k_##2668[lq_tmp$x##2664:=GHC.Classes.$fOrdInt][VV##2667:=lq_tmp$x##2670]} -&gt; lq_tmp$x##2666:{lq_tmp$x##2670 : Int^"lq_tmp$x##2669" | $k_##2668[lq_tmp$x##2664:=GHC.Classes.$fOrdInt][VV##2667:=lq_tmp$x##2670]} -&gt; {lq_tmp$x##2670 : Int^"lq_tmp$x##2669" | $k_##2668[lq_tmp$x##2664:=GHC.Classes.$fOrdInt][VV##2667:=lq_tmp$x##2670]
                                                                                                                                                                                                                                                                                                                     &amp;&amp; lq_tmp$x##2670 == (if lq_tmp$x##2665 &lt; lq_tmp$x##2666 then lq_tmp$x##2665 else lq_tmp$x##2666)}</span><span class='hs-varid'>min</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span>
</pre>

and the `subtract` functions too:


<pre><span class=hs-linenum>270: </span><span class='hs-definition'>subtract</span> <span class='hs-keyglyph'>::</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>Intervals</span>
<span class=hs-linenum>271: </span><a class=annot href="#"><span class=annottext>lq_tmp$x##3134:Intervals -&gt; lq_tmp$x##3135:Intervals -&gt; Intervals</span><span class='hs-definition'>subtract</span></a> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-conid'>Intervals</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##4655 : lq_tmp$x##4657:[{lq_tmp$x##4650 : Interval | 0 &lt;= Intervals.from lq_tmp$x##4650}] -&gt; {lq_tmp$x##4654 : Intervals | Intervals.itvs lq_tmp$x##4654 == lq_tmp$x##4657
                                                                                                                                     &amp;&amp; lqdc##$select##Intervals.Intervals##1 lq_tmp$x##4654 == lq_tmp$x##4657
                                                                                                                                     &amp;&amp; (is$Intervals.Intervals lq_tmp$x##4654 &lt;=&gt; true)
                                                                                                                                     &amp;&amp; lq_tmp$x##4654 == Intervals.Intervals lq_tmp$x##4657
                                                                                                                                     &amp;&amp; lq_tmp$x##4654 == Intervals.Intervals lq_tmp$x##4657} | lq_tmp$x##4655 == Intervals.Intervals}</span><span class='hs-conid'>Intervals</span></a> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##4629 : lq_tmp$x##4632:Int -&gt; lq_tmp$x##4633:[{lq_tmp$x##4615 : Interval | lq_tmp$x##4632 &lt;= Intervals.from lq_tmp$x##4615}] -&gt; lq_tmp$x##4634:[{lq_tmp$x##4619 : Interval | lq_tmp$x##4632 &lt;= Intervals.from lq_tmp$x##4619}] -&gt; [{lq_tmp$x##4623 : Interval | lq_tmp$x##4632 &lt;= Intervals.from lq_tmp$x##4623}] | lq_tmp$x##4629 == go##a24m}</span><span class='hs-varid'>go</span></a> <span class='hs-num'>0</span> <span class='hs-varid'>is1</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>272: </span>  <span class='hs-keyword'>where</span>
<span class=hs-linenum>273: </span>    <span class='hs-keyword'>{-@</span> <span class='hs-varid'>go</span> <span class='hs-keyglyph'>::</span> <span class='hs-varid'>lb</span><span class='hs-conop'>:</span><span class='hs-conid'>Int</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyglyph'>-&gt;</span> <span class='hs-conid'>OrdIntervals</span> <span class='hs-varid'>lb</span> <span class='hs-keyword'>@-}</span>
<span class=hs-linenum>274: </span>    <a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-keyword'>_</span> <a class=annot href="#"><span class=annottext>[{lq_tmp$x##11 : Interval | ds_d2lu &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>is</span></a> <span class='hs-conid'>[]</span> <span class='hs-keyglyph'>=</span> <span class='hs-varid'>is</span>
<span class=hs-linenum>275: </span>    <span class='hs-varid'>go</span> <span class='hs-keyword'>_</span> <span class='hs-conid'>[]</span> <span class='hs-keyword'>_</span>  <span class='hs-keyglyph'>=</span> <span class='hs-conid'>[]</span>
<span class=hs-linenum>276: </span>    <span class='hs-varid'>go</span> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f1</span> <span class='hs-varid'>t1</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-keyglyph'>@</span><span class='hs-layout'>(</span><span class='hs-conid'>I</span> <span class='hs-varid'>f2</span> <span class='hs-varid'>t2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>277: </span>      <span class='hs-comment'>-- i2 past i1</span>
<span class=hs-linenum>278: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3452 : Bool | lq_tmp$x##3452 &lt;=&gt; t1##a24r &lt;= f2##a24u}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##3457:{lq_tmp$x##3462 : Int^"lq_tmp$x##3461" | $k_##3460[lq_tmp$x##3456:=GHC.Classes.$fOrdInt][VV##3459:=lq_tmp$x##3462]} -&gt; lq_tmp$x##3458:{lq_tmp$x##3462 : Int^"lq_tmp$x##3461" | $k_##3460[lq_tmp$x##3456:=GHC.Classes.$fOrdInt][VV##3459:=lq_tmp$x##3462]} -&gt; {lq_tmp$x##3452 : Bool | lq_tmp$x##3452 &lt;=&gt; lq_tmp$x##3457 &lt;= lq_tmp$x##3458}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f2</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t1</span> <span class='hs-varid'>is1</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>279: </span>      <span class='hs-comment'>-- i1 past i2</span>
<span class=hs-linenum>280: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3479 : Bool | lq_tmp$x##3479 &lt;=&gt; t2##a24v &lt;= f1##a24q}</span><span class='hs-varid'>t2</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##3484:{lq_tmp$x##3489 : Int^"lq_tmp$x##3488" | $k_##3487[VV##3486:=lq_tmp$x##3489][lq_tmp$x##3483:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##3485:{lq_tmp$x##3489 : Int^"lq_tmp$x##3488" | $k_##3487[VV##3486:=lq_tmp$x##3489][lq_tmp$x##3483:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##3479 : Bool | lq_tmp$x##3479 &lt;=&gt; lq_tmp$x##3484 &lt;= lq_tmp$x##3485}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f1</span>  <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-layout'>(</span><span class='hs-varid'>i1</span><span class='hs-conop'>:</span><span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>281: </span>      <span class='hs-comment'>-- i1 contained in i2</span>
<span class=hs-linenum>282: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3506 : Bool | lq_tmp$x##3506 &lt;=&gt; f2##a24u &lt;= f1##a24q}</span><span class='hs-varid'>f2</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##3511:{lq_tmp$x##3516 : Int^"lq_tmp$x##3515" | $k_##3514[VV##3513:=lq_tmp$x##3516][lq_tmp$x##3510:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##3512:{lq_tmp$x##3516 : Int^"lq_tmp$x##3515" | $k_##3514[VV##3513:=lq_tmp$x##3516][lq_tmp$x##3510:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##3506 : Bool | lq_tmp$x##3506 &lt;=&gt; lq_tmp$x##3511 &lt;= lq_tmp$x##3512}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f1</span><span class='hs-layout'>,</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3907 : Bool | lq_tmp$x##3907 &lt;=&gt; t1##a24r &lt;= t2##a24v}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##3912:{lq_tmp$x##3917 : Int^"lq_tmp$x##3916" | $k_##3915[VV##3914:=lq_tmp$x##3917][lq_tmp$x##3911:=GHC.Classes.$fOrdInt]} -&gt; lq_tmp$x##3913:{lq_tmp$x##3917 : Int^"lq_tmp$x##3916" | $k_##3915[VV##3914:=lq_tmp$x##3917][lq_tmp$x##3911:=GHC.Classes.$fOrdInt]} -&gt; {lq_tmp$x##3907 : Bool | lq_tmp$x##3907 &lt;=&gt; lq_tmp$x##3912 &lt;= lq_tmp$x##3913}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>lb</span> <span class='hs-varid'>is1</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
<span class=hs-linenum>283: </span>      <span class='hs-comment'>-- i2 covers beginning of i1</span>
<span class=hs-linenum>284: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3934 : Bool | lq_tmp$x##3934 &lt;=&gt; f2##a24u &lt;= f1##a24q}</span><span class='hs-varid'>f2</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##3939:{lq_tmp$x##3944 : Int^"lq_tmp$x##3943" | $k_##3942[lq_tmp$x##3938:=GHC.Classes.$fOrdInt][VV##3941:=lq_tmp$x##3944]} -&gt; lq_tmp$x##3940:{lq_tmp$x##3944 : Int^"lq_tmp$x##3943" | $k_##3942[lq_tmp$x##3938:=GHC.Classes.$fOrdInt][VV##3941:=lq_tmp$x##3944]} -&gt; {lq_tmp$x##3934 : Bool | lq_tmp$x##3934 &lt;=&gt; lq_tmp$x##3939 &lt;= lq_tmp$x##3940}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>f1</span> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>t2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##4226 : lq_tmp$x##4227:Int -&gt; lq_tmp$x##4228:{lq_tmp$x##4223 : Int | lq_tmp$x##4227 &lt; lq_tmp$x##4223} -&gt; {lq_tmp$x##4224 : Interval | Intervals.to lq_tmp$x##4224 == lq_tmp$x##4228
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##4224 == lq_tmp$x##4227
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##4224 == lq_tmp$x##4228
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##4224 == lq_tmp$x##4227
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##4224 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##4224 == Intervals.I lq_tmp$x##4227 lq_tmp$x##4228
                                                                                                                                                &amp;&amp; lq_tmp$x##4224 == Intervals.I lq_tmp$x##4227 lq_tmp$x##4228} | lq_tmp$x##4226 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span>
<span class=hs-linenum>285: </span>      <span class='hs-comment'>-- -- i2 covers end of i1</span>
<span class=hs-linenum>286: </span>      <span class='hs-keyglyph'>|</span> <a class=annot href="#"><span class=annottext>{lq_tmp$x##3961 : Bool | lq_tmp$x##3961 &lt;=&gt; t1##a24r &lt;= t2##a24v}</span><span class='hs-varid'>t1</span></a> <a class=annot href="#"><span class=annottext>lq_tmp$x##3966:{lq_tmp$x##3971 : Int^"lq_tmp$x##3970" | $k_##3969[lq_tmp$x##3965:=GHC.Classes.$fOrdInt][VV##3968:=lq_tmp$x##3971]} -&gt; lq_tmp$x##3967:{lq_tmp$x##3971 : Int^"lq_tmp$x##3970" | $k_##3969[lq_tmp$x##3965:=GHC.Classes.$fOrdInt][VV##3968:=lq_tmp$x##3971]} -&gt; {lq_tmp$x##3961 : Bool | lq_tmp$x##3961 &lt;=&gt; lq_tmp$x##3966 &lt;= lq_tmp$x##3967}</span><span class='hs-varop'>&lt;=</span></a> <span class='hs-varid'>t2</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##4112 : lq_tmp$x##4113:Int -&gt; lq_tmp$x##4114:{lq_tmp$x##4109 : Int | lq_tmp$x##4113 &lt; lq_tmp$x##4109} -&gt; {lq_tmp$x##4110 : Interval | Intervals.to lq_tmp$x##4110 == lq_tmp$x##4114
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##4110 == lq_tmp$x##4113
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##4110 == lq_tmp$x##4114
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##4110 == lq_tmp$x##4113
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##4110 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##4110 == Intervals.I lq_tmp$x##4113 lq_tmp$x##4114
                                                                                                                                                &amp;&amp; lq_tmp$x##4110 == Intervals.I lq_tmp$x##4113 lq_tmp$x##4114} | lq_tmp$x##4112 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span><span class='hs-layout'>)</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>f2</span> <span class='hs-varid'>is1</span> <span class='hs-layout'>(</span><span class='hs-varid'>i2</span><span class='hs-conop'>:</span><span class='hs-varid'>is2</span><span class='hs-layout'>)</span><span class='hs-layout'>)</span>
<span class=hs-linenum>287: </span>      <span class='hs-comment'>-- i2 in the middle of i1</span>
<span class=hs-linenum>288: </span>      <span class='hs-keyglyph'>|</span> <span class='hs-varid'>otherwise</span> <span class='hs-keyglyph'>=</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##3988 : lq_tmp$x##3989:Int -&gt; lq_tmp$x##3990:{lq_tmp$x##3985 : Int | lq_tmp$x##3989 &lt; lq_tmp$x##3985} -&gt; {lq_tmp$x##3986 : Interval | Intervals.to lq_tmp$x##3986 == lq_tmp$x##3990
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##3986 == lq_tmp$x##3989
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##3986 == lq_tmp$x##3990
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##3986 == lq_tmp$x##3989
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##3986 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##3986 == Intervals.I lq_tmp$x##3989 lq_tmp$x##3990
                                                                                                                                                &amp;&amp; lq_tmp$x##3986 == Intervals.I lq_tmp$x##3989 lq_tmp$x##3990} | lq_tmp$x##3988 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>f1</span> <span class='hs-varid'>f2</span> <span class='hs-conop'>:</span> <a class=annot href="#"><span class=annottext>lq_tmp$x##3182:Int -&gt; lq_tmp$x##3183:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; lq_tmp$x##3184:[{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}] -&gt; [{lq_tmp$x##11 : Interval | lq_tmp$x##3182 &lt;= Intervals.from lq_tmp$x##11}]</span><span class='hs-varid'>go</span></a> <span class='hs-varid'>f2</span> <span class='hs-layout'>(</span><a class=annot href="#"><span class=annottext>{lq_tmp$x##3998 : lq_tmp$x##3999:Int -&gt; lq_tmp$x##4000:{lq_tmp$x##3995 : Int | lq_tmp$x##3999 &lt; lq_tmp$x##3995} -&gt; {lq_tmp$x##3996 : Interval | Intervals.to lq_tmp$x##3996 == lq_tmp$x##4000
                                                                                                                                                &amp;&amp; Intervals.from lq_tmp$x##3996 == lq_tmp$x##3999
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##2 lq_tmp$x##3996 == lq_tmp$x##4000
                                                                                                                                                &amp;&amp; lqdc##$select##Intervals.I##1 lq_tmp$x##3996 == lq_tmp$x##3999
                                                                                                                                                &amp;&amp; (is$Intervals.I lq_tmp$x##3996 &lt;=&gt; true)
                                                                                                                                                &amp;&amp; lq_tmp$x##3996 == Intervals.I lq_tmp$x##3999 lq_tmp$x##4000
                                                                                                                                                &amp;&amp; lq_tmp$x##3996 == Intervals.I lq_tmp$x##3999 lq_tmp$x##4000} | lq_tmp$x##3998 == Intervals.I}</span><span class='hs-conid'>I</span></a> <span class='hs-varid'>t2</span> <span class='hs-varid'>t1</span> <span class='hs-conop'>:</span> <span class='hs-varid'>is1</span><span class='hs-layout'>)</span> <span class='hs-varid'>is2</span><span class='hs-layout'>)</span>
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
