import Lean
open Lean Meta Meta.Simp

initialize globalSimpExt : SimpExtension ←
  registerSimpAttr `euclid_simp "\
    The `euclid_simp` attribute registers simp lemmas to be used when proving
    that global/constant definitions successfully evaluate."
