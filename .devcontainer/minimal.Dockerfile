#FROM bcpierce00/cis5000:8.17.1
FROM coqorg/coq:8.18.0-ocaml-4.14.2-flambda


ARG OPAM_PACKAGES="vscoq-language-server"
RUN /bin/bash --login -o pipefail -c opam update -y && opam install -y -j ${NJOBS} ${OPAM_PACKAGES} && opam clean -y -a -c -s --logs && eval $(opam env) &&     ln -s 4.14.2+flambda .opam/default # buildkit
