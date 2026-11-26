.PHONY: check full all paper lean figures
check:
	python3 scripts/verify.py --mode quick
full:
	python3 scripts/verify.py --mode full
all:
	python3 scripts/verify.py --mode all
paper:
	python3 scripts/build_paper.py
lean:
	python3 lean/verify.py --check-inventory lean/inventory.json
figures:
	python3 scripts/render_figures.py
