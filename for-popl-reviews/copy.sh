#!/usr/bin/env bash

outputdir="review"
prefix="../formalizations/guarded-cubical/"
ToRemove=("Experiments" "_build")

rm -r $outputdir
mkdir $outputdir

cp "README.md" ${outputdir}
cp -r ${prefix} ${outputdir}"/code"

for name in "${ToRemove[@]}"; do
  echo "removing directory $name"
  rm -r ${outputdir}"/code/"${name}
done

rm ${outputdir}"/code/Semantics/GuardedResults/ToposOfTrees.agda"