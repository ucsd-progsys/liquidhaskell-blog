function swizzle(name){
    $(function() {
        var divName  = "#" + name;
        var animName = "/liquidhaskell-blog/static/img/" + name + ".gif";
        var statName = "/liquidhaskell-blog/static/img/" + name + ".png";
        $(divName).hover(
            function() {
                $(this).attr("src", animName);
            },
            function() {
                $(this).attr("src", statName);
            }
        );
    });
};

var z0 = swizzle("splash-head");
var z1 = swizzle("splash-unstutter");
var z2 = swizzle("splash-vectorsum");
var z3 = swizzle("splash-dotproduct");
var z4 = swizzle("splash-fib");
var z5 = swizzle("splash-merge");
var z6 = swizzle("splash-ups");
var z7 = swizzle("splash-insertsort");
var z8 = swizzle("splash-assocthm");
var z9 = swizzle("splash-assocpf");
