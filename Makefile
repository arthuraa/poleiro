all: site
	./site build

site: site.hs
	ghc --make -fwarn-unused-imports site

run: site
	./site watch

deploy:
	./deploy.sh

clean: site
	./site clean

.PHONY: run deploy clean
