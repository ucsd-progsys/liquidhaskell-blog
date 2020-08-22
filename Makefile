site:
	stack build --fast
	stack exec -- blog rebuild

upload: site 
	cp -r _site/* docs/ 
	git add docs && git commit -a -m "update page" && git push origin master 

clean:
	rm -rf *.hi *.o .*.swp .*.swo website _site/ _cache/
