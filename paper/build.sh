#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")/.."
mkdir -p output/pdf
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf paper/coven-meyerowitz-t2.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf paper/coven-meyerowitz-t2.tex
