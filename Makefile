site: site.hs
	ghc --make site

run: site
	./site rebuild && ./site preview

.PHONY: run
