#! /bin/bash
set -e

# generate the version file
scripts/set_version.sh

TARGET=src/goblint
FLAGS="-cflag -annot -tag bin_annot -X webapp -no-links -use-ocamlfind -j 8 -no-log -ocamlopt opt -cflag -g"
OCAMLBUILD=ocamlbuild
EXCLUDE="_build|goblint.ml|apronDomain|poly"

ocb() {
  $OCAMLBUILD $FLAGS $*
}

opam_build() {
  eval `opam config env`
  opam update
  opam install ocamlfind batteries xml-light ppx_distr_guards ppx_monadic ppx_import ppx_deriving ppx_deriving_yojson camlp4 mongo # camlp4 needed for mongo
  # opam's cil is too old
  opam pin -y add cil "https://github.com/goblint/cil.git"
  # unpin once deriving show with_path is available in opam version
  # opam pin add ppx_deriving https://github.com/whitequark/ppx_deriving.git
}

rule() {
  case $1 in
    clean)   rm -rf goblint goblint.byte arinc doclist.odocl $TARGET.ml;
             ocb -clean
             ;;
    opt | nat*)
             ocb -no-plugin $TARGET.native &&
             cp _build/$TARGET.native goblint
             ;;
    debug)  ocb -tag debug $TARGET.d.byte &&
             cp _build/$TARGET.d.byte goblint.byte
             ;;
    warn)    # be pedantic and show all warnings
             $OCAMLBUILD $FLAGS -no-plugin -cflags "-w +a" $TARGET.native && # copied b/c passing a quoted argument to a function does not work
             cp _build/$TARGET.native goblint
             ;;
    # gprof (run only generates gmon.out). use: gprof goblint
    profile) ocb -tag profile $TARGET.p.native &&
             cp _build/$TARGET.p.native goblint
             ;;
    # gprof & ocamlprof (run also generates ocamlprof.dump). use: ocamlprof src/goblint.ml
    ocamlprof) ocb -ocamlopt ocamloptp $TARGET.p.native &&
             cp _build/$TARGET.p.native goblint
             ;;
    doc*)    rm -rf doc;
             ls src/**/*.ml | egrep -v $EXCLUDE  | sed 's/.*\/\(.*\)\.ml/\1/' > doclist.odocl;
             ocb -ocamldoc ocamldoc -docflags -charset,utf-8,-colorize-code,-keep-code doclist.docdir/index.html;
             rm doclist.odocl;
             ln -sf _build/doclist.docdir doc
             ;;
    tag*)    otags -vi `find src/ -iregex [^.]*\.mli?`;;
    poly)    echo "open ApronDomain" >> $TARGET.ml
             echo "open Poly" >> $TARGET.ml
             ocb -no-plugin -package apron -package apron.polkaMPQ -package apron.octD $TARGET.native &&
             cp _build/$TARGET.native goblint
             ;;
    arinc)   ocb src/mainarinc.native &&
             cp _build/src/mainarinc.native arinc
             ;;
    npm)     if test ! -e "webapp/package.json"; then
                git submodule update --init --recursive webapp
             fi
             cd webapp && npm install && npm start
             ;;
    jar)     if test ! -e "g2html/build.xml"; then
                git submodule update --init --recursive g2html
             fi
             cd g2html && ant jar && cd .. &&
             cp g2html/g2html.jar .
             ;;
    dep*)    OPAMYES=1 opam_build;;
    setup)   echo "Make sure you have the following installed: opam >= 1.2.2, m4, patch, autoconf, git"
             opam init --comp=4.04.0
             opam_build
             ;;
    dev)     echo "Installing opam packages for development..."
             opam install utop merlin ocp-indent
             echo "Be sure to adjust your vim/emacs config!"
             echo "Installing Pre-commit hook..."
             cd .git/hooks; ln -s ../../scripts/hooks/pre-commit; cd -
             echo "Installing gem parallel (not needed for ./scripts/update_suite.rb -s)"
             sudo gem install parallel
             ;;
    watch)   fswatch --event Updated -e $TARGET.ml src/ | xargs -n1 -I{} make
             ;;
    header*) curl -L -O https://github.com/goblint/linux-headers/archive/master.tar.gz
             tar xf master.tar.gz && rm master.tar.gz
             rm -rf linux-headers && mv linux-headers-master linux-headers
             cp linux-headers/include/linux/compiler-gcc5.h linux-headers/include/linux/compiler-gcc6.h
             cp linux-headers/include/linux/compiler-gcc5.h linux-headers/include/linux/compiler-gcc7.h
             ;;
    test)    ./scripts/update_suite.rb;;
    testci)  ruby scripts/update_suite.rb -s -d;;
    *)       echo "Unknown action '$1'. Try clean, opt, debug, profile, byte, or doc.";;
  esac; }

ls -1 src/**/*.ml | egrep -v $EXCLUDE | perl -pe 's/.*\/(.*)\.ml/open \u$1/g' > $TARGET.ml
echo "open Maingoblint" >> $TARGET.ml

if [ $# -eq 0 ]; then
  rule nat
else
  while [ $# -gt 0 ]; do
    rule $1;
    shift
  done
fi

