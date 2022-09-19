# LiquidHaskell Blog

*Note:* This blog is now deprecated. You're probably looking for the latest version of the Liquid Haskell site, which can be found [in the main LH repository](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/docs).

LiquidHaskell is a static verifier for Haskell, based on **Liquid Types**

See [about](about.md) for more details.

## Build

To add a new post:

1. Write a `.lhs` file with the name `YEAR-MONTH-DAY-TITLE.lhs` 
e.g. [see this example](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/docs/blog/2017-12-15-splitting-and-splicing-intervals-I.lhs)

2. Generate the `.markdown` file. 

3. Copy the `.markdown` file in `posts/`

4. Rebuild and upload.

Here are the four steps:

```
cd blogpost/
cat > YEAR-MONTH-DAY-TITLE.lhs
stack exec -- liquid YEAR-MONTH-DAY-TITLE.lhs
cp blogpost/.liquid/YEAR-MONTH-DAY.lhs.markdown /path/to/liquidhaskell-blog/posts/
make upload
```

## TODO

+ DONE?: Disqus (?)
+ DONE: [Tags](https://javran.github.io/posts/2014-03-01-add-tags-to-your-hakyll-blog.html)
- [Teasers](https://jaspervdj.be/hakyll/tutorials/using-teasers-in-hakyll.html)
