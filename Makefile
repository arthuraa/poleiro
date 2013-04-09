all: site
	./site build

site: site.hs
	ghc --make -fwarn-unused-imports site

run: site
	./site rebuild && ./site preview

deploy:
	./deploy.sh

.PHONY: run deploy
