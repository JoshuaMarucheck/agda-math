AGDAI := $(shell find $(SRC_DIRS) -name '*.agdai')

.PHONY: clean
clean:
	rm $(AGDAI)