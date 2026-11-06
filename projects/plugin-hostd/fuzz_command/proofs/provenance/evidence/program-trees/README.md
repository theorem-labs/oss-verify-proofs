# Program trees: our decoder and its recipes

The unit's libc proofs `lib/CJ/RL/GX/G_sn_write.v`, `lib/CJ/RL/GX/G_vsnprintf.v`, `lib/CJ/RL/GXA/G_sn_write.v` and
`lib/CJ/RL/GXA/G_vsnprintf.v` each hold a program tree: the `Definition` of an `RStep.ptree` made of `PNode` and
`PJ_<op>` lines. Each tree is a fact of the unit's pinned images: the build checks it against the image's bytes.

`ptree_emit.py` is our own decoder for this form. It reads the function's bytes from a pinned image, decodes every
32-bit word into the `PJ_<op>` notation of `lib/CJ/RL/Reloc/RProgNotJ.v`, writes calls out of the function and
address pairs as terms over the Definition's parameters, and lays the tree out in leaves of ten instructions. It
refuses (exit 2, nothing written) a word it cannot write as a notation, an external address it is not given a name
for, and any argument or output that holds a string of its deny list. `resolve_keys.py` carries each key of the
tree's `PROGAT_CODE_` line through the unit's key map to the image, and names the symbol at each address.

Each `.recipe` gives the exact commands, the sha256 of every input (images, unstripped twins, key maps, the decoder)
and of the output. On each of the four pins, the decoder's output is byte-equal to the committed tree in all four
files, measured 2026-10-31. A second run gives the same bytes.
