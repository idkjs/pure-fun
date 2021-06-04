#!/bin/bash
# for i in $(find . -not -path "*node_modules*" -type f \( -name "*.re" -o -name "*.rei" \))
# do
#   ./node_modules/.bin/bsrefmt --in-place $i
# done

#!/bin/sh
filenames=$(find . -iname '*.ml' | grep -v node_modules | grep -v _opam/ | grep -v _build | grep -v _esy | grep -v .melane.eobjs)
len=${#filenames[@]}
echo "$len"
echo "$filenames"
# for filename in $filenames; do refmt --parse ml --print re "$filename" > "${filename%.ml}.re"; done;


filenames=$(find . -iname '*.mli' | grep -v node_modules | grep -v _opam/ | grep -v _build | grep -v _esy | grep -v .melane.eobjs)
len=${#filenames[@]}
echo "$len"
echo "$filenames"
# for filename in $filenames; do refmt --parse ml --print re "$filename" > "${filename%.mli}.rei"; done;
# filenames=$(find "$(pwd)" -name "*.rei")
# len=${#filenames[@]}
# echo "$len"
# echo "$filenames"
# for filename in $filenames; do rm "$filename"; done;
# exit 0
filenames=$(find . -iname '*.ml'| grep -v node_modules | grep -v _opam/ | grep -v _build && find . -iname '*.mli'| grep -v node_modules | grep -v _opam | grep -v _build)
len=${#filenames[@]}
echo "$len"
echo "$filenames"
for filename in $filenames; do rm "$filename"; done;
