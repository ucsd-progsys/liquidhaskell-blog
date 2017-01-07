site:
	stack build
	stack exec -- homepage rebuild

upload: blog
	cp -r _site/* $(GHPAGE)
	cd $(GHPAGE) && git add . && git commit -a -m "update page" && git push origin gh-pages

clean:
	rm -rf *.hi *.o .*.swp .*.swo website _site/ _cache/
