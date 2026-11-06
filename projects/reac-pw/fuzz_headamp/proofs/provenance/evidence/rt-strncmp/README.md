# rt-strncmp: the strncmp interceptor's runtime proofs, relocated from plugin-hostd/fuzz_command

Each file lists one row per numeral that the relocation changed, with the old and new value, the symbol both values
name in their own image, and the decision.

| file | covers |
| --- | --- |
| reloc-rt.tsv | image A, files under lib/A/Rt/ (fuzz_command.asan -> fuzz_headamp.asan) |
| reloc-bz.tsv | image A, files under lib/A/Bz/ (fuzz_command.asan -> fuzz_headamp.asan) |
| derive-B-rt.tsv | image B, the lib/AU/Rt/ twins derived from image A (fuzz_headamp.asan -> fuzz_headamp.asan-ubsan) |
| derive-B-bz.tsv | image B, the lib/AU/Bz/ twins derived from image A |
