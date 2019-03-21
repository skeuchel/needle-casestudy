DIRS := ${shell find . \( ! -name . -prune ! -name .git -prune \) -type d -print}

all:
	-for d in $(DIRS); do (cd $$d; $(MAKE)); done
clean:
	-for d in $(DIRS); do (cd $$d; $(MAKE) clean ); done
infra:
	-${for file in $(find . -name \*.infra); do infra $file > $(dirname $file)/$(basename $file .infra).v; done}

.PHONY: all clean infra
