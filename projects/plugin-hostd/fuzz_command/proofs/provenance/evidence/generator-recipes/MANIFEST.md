# provenance/evidence/generator-recipes: the recipes of four generated files of plugin-hostd/fuzz_command and the generators that write them

Each recipe names, for one file, the generator that wrote it (file name, sha256), its inputs (sha256) and arguments, the result of running that generator again on those inputs, and the command of the copy of record in scripts/ that now writes the file and its provenance line.

| file | sha256 | role |
|---|---|---|
| lib-A-RT_IImgA.v.recipe | 656fd621753add189e24118ba4e8f20d4c99a332b759c9f62693e48a2a1e6c78 | the recipe of lib/A/RT_IImgA.v line 2 (image A, fuzz_command.asan): the generator that wrote lines 3-129 (sha256, git blob, what it is), its inputs with sha256, the regeneration with it, the copy of record's command and result |
| lib-B-RT_IImgA.v.recipe | 3d380992d3cf630658ee10703eb9e21179148dcf24d18c657f8294ff6424cae2 | the same for lib/B/RT_IImgA.v line 2 (image B, fuzz_command.asan-ubsan) |
| lib-A-Rt-RtDtorTbl.v.recipe | 316ad28528151f36c4c673db7a9440391f3507ed259e8e3a4428a10281be1401 | the recipe of lib/A/Rt/RtDtorTbl.v lines 11-12, the BEGIN marker of its asan_globals table (image A): the generator that wrote lines 11-199, its argument and input, the regeneration with it, the copy of record's command and result |
| lib-B-Rt-RtDtorTbl.v.recipe | 8d29a0ab643fae12fda95fa33c926ebf1a160970412319b34f430f1668cdd7f6 | the same for lib/B/Rt/RtDtorTbl.v lines 11-12 (image B) |
| scripts/cmdimga.py | 9be672203137e48bf9a611399c79475cc02efb3aa35e5d6ef77a7cf3bcc935b6 | copy of record of the image-table generator of lib/A/RT_IImgA.v and lib/B/RT_IImgA.v: it writes each file's line 2 and every line after it (lines 3-132) |
| scripts/gen_dtor_tbl.py | 8aa0a4ab6d2a52c3cd486947022dab4601f525e5efa34cedba65695277df2fa0 | copy of record of the asan_globals table generator of lib/A/Rt/RtDtorTbl.v and lib/B/Rt/RtDtorTbl.v: it writes each file's lines 11-199 |
