(lang dune 3.6)

(using dune_site 0.1)

(cram enable)

(generate_opam_files true)

(license LGPL-3.0-only)

(authors "Kakadu@pm.me")

(maintainers "Kakadu")

(bug_reports "FIXME")

(homepage "FIXME")

(name MiniML)

(package
 (name MiniML)
 (synopsis "A MiniML interpreter")
 (description
  "FIXME. A longer description, for example, which are the most interesing features being supported, etc.")
 (version 0.1)
 (sites
  (lib plugins))
 (depends
  dune
  dune-site
  (angstrom
   (= 0.16.0))
  (ocaml
   (>= 4.14))
  (ppx_inline_test :with-test)
  ppx_expect
  ppx_show
  (llvm
   (>= 16.0.0))
  ctypes-foreign ; needed for LLVM
  ppx_blob
  (ocamlgraph
   (>= 2.1.0))
  (odoc :with-doc)
  (ocamlformat :build)
  base))
