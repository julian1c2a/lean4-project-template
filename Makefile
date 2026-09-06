# Makefile for Lean 4 projects
# Usage: make <target>
# Requires: bash, lake, git

.PHONY: build clean rebuild sorry docsync docsync-quick status lock unlock list init new root update-toolchain help

## Build the project
build:
	lake build

## Clean build artifacts
clean:
	lake clean

## Clean and rebuild
rebuild: clean build

## Check for sorry statements
sorry:
	@bash check-sorry.bash

## Comprueba que la documentacion cuadra con el codigo (AI-GUIDE §27)
docsync:
	@bash check-doc-sync.bash

## Idem, sin lake build (para iterar rapido)
docsync-quick:
	@bash check-doc-sync.bash --quick

## Show project status: locked files + sorry count
status:
	@echo "=== Lock Status ==="
	@bash git-lock.bash list
	@echo ""
	@echo "=== Sorry Status ==="
	@bash check-sorry.bash || true

## Lock a file: make lock FILE=ProjectName/Module.lean
lock:
	@[ -n "$(FILE)" ] || (echo "Usage: make lock FILE=ProjectName/Module.lean" && exit 1)
	@bash git-lock.bash lock $(FILE)

## Unlock a file: make unlock FILE=ProjectName/Module.lean
unlock:
	@[ -n "$(FILE)" ] || (echo "Usage: make unlock FILE=ProjectName/Module.lean" && exit 1)
	@bash git-lock.bash unlock $(FILE)

## List all locked files
list:
	@bash git-lock.bash list

## Initialize lock system (install git hook)
init:
	@bash git-lock.bash init

## Create a new module: make new NAME=Algebra/Ring
new:
	@[ -n "$(NAME)" ] || (echo "Usage: make new NAME=ModuleName" && exit 1)
	@bash new-module.bash $(NAME)

## Regenerate root module file
root:
	@bash gen-root.bash

## Update Lean toolchain: make update-toolchain [VERSION=v4.31.0]
update-toolchain:
	@bash update-toolchain.bash $(VERSION)

## Show this help
help:
	@echo "Available targets:"
	@grep -E '^## ' Makefile | sed 's/^## /  /'
