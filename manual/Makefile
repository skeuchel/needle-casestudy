DIRS := ${shell find . \( ! -name . -prune ! -name .git -prune \) -type d -print}

all:
	-for d in $(DIRS); do (cd $$d; $(MAKE)); done
clean:
	-for d in $(DIRS); do (cd $$d; $(MAKE) clean ); done

.PHONY: all clean
