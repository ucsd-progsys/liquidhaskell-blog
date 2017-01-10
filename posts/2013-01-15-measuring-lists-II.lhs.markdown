---
layout: post
title: Measuring Lists II
date: 2013-01-05 16:12
author: Ranjit Jhala
published: false 
comments: true
tags: basic
demo: lenQuicksort.hs
---

The [last note][listlen1] we saw how to measure the length of a list
and use it to write **safe** versions of potentially unsafe operations
like `head` and `tail` and `foldr1`, all of which require non-empty lists.

Of course, having done all the work needed to reason about lengths, 
we can also specify and verify properties that *relate* the lengths
of different lists.

<!-- more -->

Basic Operations: Map, Filter, Reverse
--------------------------------------


<pre><span class=hs-linenum>27: </span><span class='hs-keyword'>module</span> <span class='hs-conid'>List2</span> <span class='hs-keyword'>where</span>
<span class=hs-linenum>28: </span>
<span class=hs-linenum>29: </span><a class=annot href="#"><span class=annottext>forall a. {VV : a | false}</span><span class='hs-definition'>x</span></a> <span class='hs-keyglyph'>=</span> <a class=annot href="#"><span class=annottext>[(Char)] -&gt; {VV : a | false}</span><span class='hs-varid'>error</span></a> <a class=annot href="#"><span class=annottext>{VV : [(Char)] | (len([VV]) &gt;= 0)}</span><span class='hs-str'>"TODO"</span></a>
</pre>
Less Basic: Append, Zip, Take 
-----------------------------

A Short Example: Insertion/Quick Sort
-------------------------------------




