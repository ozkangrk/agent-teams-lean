# Paper build (Claude's code). `make` regenerates numbers, bibliography and PDF from the experiment records.
.PHONY: all data bib paper clean
all: data bib paper
data:
	python3 -I scripts/build_data.py > /dev/null
bib:
	python3 -I scripts/build_bib.py
paper:
	cd paper && tectonic -X compile main.tex --keep-logs
clean:
	rm -f paper/main.pdf paper/main.log paper/main.blg
