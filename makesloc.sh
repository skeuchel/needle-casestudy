#!/bin/bash

CASESTUDY=$PWD

function coqwc2 () {
  # cat $* | grep -v '^Require' | grep -v '^Set' | coqwc | tail -n 1 | awk '{print ($1+$2)}'
  cat $* | coqwc | tail -n 1 | awk '{print ($1+$2)}'
}

function calc () {

  SPEC="SpecSyntax.v SpecSemantics.v DeclarationEvaluation.v"
  BPSPEC="BoilerplateFunctions.v"
  BPSYNTAX="BoilerplateSyntax.v"
  BPSEMANTICS="BoilerplateSemantics.v"
  METATHEORY="MetaTheory.v"
  BP="$BPSPEC $BPSYNTAX $BPSEMANTICS"
  ALL="$SPEC $METATHEORY $BP"

  echo "Spec             " $(coqwc2 $SPEC *.knot 2> /dev/null)
  echo "BP Spec          " $(coqwc2 $BPSPEC      2> /dev/null)
  echo "BP Syntax        " $(coqwc2 $BPSYNTAX    2> /dev/null)
  echo "BP Semantics     " $(coqwc2 $BPSEMANTICS 2> /dev/null)
  echo "Metatheory       " $(coqwc2 $METATHEORY  2> /dev/null)
  BOILERPLATE=$(coqwc2 $BP 2> /dev/null)
  TOTAL=$(coqwc2 $ALL *.knot 2> /dev/null)
  echo "BOILERPLATE:      $BOILERPLATE"
  echo "TOTAL:            $TOTAL"
}

function go () {
    for dir in $DIRS
    do
	echo
	cd $CASESTUDY/$dir
	echo "---- $dir ----" | sed -e 's/$/                               /' | cut -c1-30 | tee sloc.txt
	calc | sed -e 's/$/                               /' | cut -c1-30 | tee -a sloc.txt
    done
}

DIRS="
  manual/stlc     needle/stlc
  manual/stlcprod needle/stlcprod
  manual/f        needle/f
  manual/fexists  needle/fexists
  manual/fprod    needle/fprod
  manual/fseqlet  needle/fseqlet
  manual/fsub     needle/fsub
  manual/fsubprod needle/fsubprod
  manual/lomega   needle/lomega
  manual/fomega   needle/fomega
  "

function slocs () {
    for dir in $DIRS
    do
	echo -n $CASESTUDY/$dir/sloc.txt " "
    done
}

function pa () {
    while (( "$#" )); do
        paste $1 $2
        echo ""
        shift
        shift
    done
}

go
pa $(slocs) | sed -e 's/ *$//' > $CASESTUDY/sloc.txt
