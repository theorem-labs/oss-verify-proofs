# reac-pw/fuzz_segconf image A: interceptor layer - index of evidence

This directory holds the interceptor (library-wrapper) layer's evidence for image A (ASan build).
Image: pin sha256 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8; unstripped twin sha256 4362701197e4cecdb46108f7694774021f7b8d5e7bd85cfe200fa90ad7a63c32.

- `INTERFACE-A-interceptors.md`: the accepted interface: one row per wrapper the program calls, with its contract name and its closing.
- `PATHMAP.tsv`: every file of this layer COPIED from a released or donor tree (`<unit path>\thub:<commit>:<donor path>`); files written for this unit have no row.

## Closings

Every closing except row 13 is in `Section closed` with `Context {fx : YK11.FPState} {rc : YM05.RunCeil}`, `Variable B : asyms`, `Hypothesis HB : SegBSyms B` only;
`AR_laws` comes from `YG0q.AR_laws_ok tfibsegs B`. Print Assumptions of each: the PrimInt63 / PrimString / PrimArray primitives and
`FunctionalExtensionality.functional_extensionality_dep` only.

| row | function | theorem | file (unit-relative) | walk source |
|---|---|---|---|---|
| 3 | strtol | `seg_strtol0_closed (+ seg_strtol0_digits_closed)` | lib/A/Rt/RtLStrtol0.v | new walk files lib/A/Bz/A/I_strtolfix0.v, I_strtol0w.v |
| 4 | snprintf | `seg_snprintf_closed, seg_rtformat_closed` | lib/A/Rt/RtFSnprintfSeg.v | new |
| 5 | vsnprintf | `seg_vsnprintf_closed` | lib/A/Rt/RtFSnprintfSeg.v | new |
| 6 | strchr | `seg_strchr_closed` | lib/A/Rt/RtLStrchr.v | walks relocated from omx-clap-core/fuzz_manifest |
| 7 | strncasecmp | `seg_strncasecmp_closed` | lib/A/Rt/RtLStrncasecmp.v | walks relocated from omx-clap-core/fuzz_manifest |
| 8 | strstr | `seg_strstr_closed` | lib/A/Rt/RtLStrstr.v | walks relocated from omx-clap-core/fuzz_manifest |
| 9 | isalnum | `seg_isalnum_closed` | lib/A/Rt/RtLIsalnum.v | walks relocated from omx-clap-core/fuzz_manifest |
| 10 | strcasecmp | `seg_strcasecmp_closed` | lib/A/Rt/RtLStrcasecmp.v | new |
| 11 | strrchr | `seg_strrchr_closed` | lib/A/Rt/RtLStrrchr.v | walk copied from plugin-hostd/fuzz_reply (unreleased) |
| 12 | strncpy | `seg_strncpy_closed` | lib/A/Rt/RtLStrncpy.v | new |
| 1 | strncmp | `seg_strncmp_closed` | lib/A/Rt/SegRtClosed.v | walks relocated from plugin-hostd/fuzz_command |
| 2 | strspn | `seg_strspn_closed` | lib/A/Rt/SegRtClosed.v | walks relocated from plugin-hostd/fuzz_command |
| 14 | __asan_stack_malloc_5 | `seg_stack_malloc5_closed` | lib/A/Rt/SegRtClosed.v | walks relocated from plugin-hostd/fuzz_command |
| 16 | strlen | `seg_strlen_closed` | lib/A/Rt/SegRtClosed.v | walks relocated from plugin-hostd/fuzz_command |
| 17 | strcmp | `seg_strcmp_closed` | lib/A/Rt/SegRtClosed.v | walks relocated from plugin-hostd/fuzz_command |
| 20 | memchr | `seg_memchr_closed` | lib/A/Rt/SegRtClosed.v | walks relocated from plugin-hostd/fuzz_command |
| 19 | bcmp | `seg_bcmp_closed` (re-export of the frame's AE2s.bcmp_icpt_contract, lib/A/AE2s.v:712) | lib/A/Rt/SegRtClosed.v | frame closing |
| 13 | calloc | `seg_acalloc_closed` (one premise beyond HB: `forall t, as_dhash B t = tfib_dhash t`, the depot-hash equality AFem.tfib_depot_ok needs; SegBSyms fixes the hash of two traces only) and `seg_acalloc_closed_segB` (at the image's record AD2l.SegB, no premise) | lib/A/Rt/RtLCalloc.v | thin walk relocated from libreac/fuzz_decode, Allocate family from omx-clap-core/fuzz_state, YCbpCalloc.v converted from libreac/fuzz_decode |

lib/A/Rt/SegRtClosed.v also re-exports every closing above. Row 15 (__asan_stack_free_5) is closed in a later commit of this layer.

## Tools run (registry name and sha)

- relocation of the fuzz_command interceptor files: port_core 7a74e72920e6 (primary), alreloc a5c53bb2bed4 (cross-check); dry-run diff port_core 83f5203d2a2f;
- relocation of the calloc walk and Allocate family: port_core 7a74e72920e6 (primary), alreloc a5c53bb2bed4 (cross-check); dry-run diff port_core d9e0589898fd; code identity cmpkit 86da41d3ef68;
  value checks port_addr_check 3d2eee813cce (--fail-on-flags, A = asan), roundconst gate v2 32b39f3b34e9.
- names scan of record: ossv-binscan 807be47c4034, exceptions 957a82b968a0.

## Run records (internal record, not shipped)

The verbatim run text of this layer (run scripts, logs, overrides, patches, per-row tables, tool sha256 lists, review reports) is kept
in the internal record: commit 72eb1296d954 (records/interceptors/, 106 files), commit f252a3dc75cb (records/interceptors/measurements/, 4 files)
commit eacec177d236 (records/interceptors/closings/, 3 files)
commit 8838802efbe0 (records/interceptors/calloc/, 118 files)
and commit 936becf778e6 (records/interceptors/relocation-checks/, 33 files + ALIASES.txt naming 23 files of that run already recorded byte for byte).
Each file is listed below with its sha256; the same list is the record's MANIFEST.

| record path | sha256 |
|---|---|
| records/interceptors/INTERFACE-A-interceptors.md | 2e7a8959b22bc93d60e40ac36b270dd83b4409b5f87b67cebf1ce055581c1c1a |
| records/interceptors/manifest-string-walks/PATHMAP.tsv | 15e8a5cae2bac3b409997e7c5d2b56b49de719ef0ffd6e54ef2c003d7dc09fca |
| records/interceptors/manifest-string-walks/RELOC.md | 437cd7728fd8d06c3fe959c89a830dc69b44e54ef9a5388363cd5cf0035e2f09 |
| records/interceptors/manifest-string-walks/alreloc.log | 92e19ca69fddb2d220a5e7e0c4f0ef1864c3479a58b7ce0f66c1e95cb92588e7 |
| records/interceptors/manifest-string-walks/dirs.patch | 9af270d2fbeee2da801123276d23efbd60590bd17d7467c1ee780c01a512c944 |
| records/interceptors/manifest-string-walks/dirs.tsv | 65703222e92589eefe062f75e0577ffd706fc6a737658cbe96f7a745a75bec7e |
| records/interceptors/manifest-string-walks/fix_dirs_fm.py | 64219c79714c1cfae63a73a1cea2bd2ae7f46598487f5105ea9623a9a37031a6 |
| records/interceptors/manifest-string-walks/fm-files.txt | ac721585bbb59fde167dee91fea3bd4eb40cc646c4d97fc1f1927daf3afdbd87 |
| records/interceptors/manifest-string-walks/measure_aglob.py | 933a1f909df58a7c2c10e4646d3efd1ebeb592d7ccdebdc5e6c8e3f17f1d64ac |
| records/interceptors/manifest-string-walks/overrides.tsv | 7cba43a0e56305c6805666ec60ddd6531d7cd5968e7b7093e141379581d01675 |
| records/interceptors/manifest-string-walks/port_core-review.tsv | 96aa5bb0ec814e021495c8f542315a8728419b5630a3ae4db1465360f6b3ef33 |
| records/interceptors/manifest-string-walks/port_core-run3.log | b7e913b72df9c5e8d5c065d9ae466b2bfa69942a46c51316999608d4286498e5 |
| records/interceptors/manifest-string-walks/port_core-versions.txt | 71734cfdf646a6653377d7bea3b27fd46de918f15ebedd01c5ae2ce03507b41e |
| records/interceptors/manifest-string-walks/run.sh | bc4c25904fe36e5fcc55e6419f03e1503733aaa1ab9f53afb2201710b23fe005 |
| records/interceptors/manifest-string-walks/sample220-check.txt | c6b8bf597c283cb0eed80b83ece3f9821b166e51b4494164da63405e9201b099 |
| records/interceptors/manifest-string-walks/tool-sha256.txt | ef182562d9fd7b88415ba51c3c300bcb241fe2a17900f1dff0a40de0dfdd7b4d |
| records/interceptors/manifest-string-walks/xcheck.tsv | 87fcf31c3e769addaf8bd877cfd163bf3c44cdaf813b38d348ea0a37df6a95d9 |
| records/interceptors/printf/closing.txt | d0cc6f2e6f70a5d7ffe95ae10be08549648dc93d4396a8ca0d9d2013f24199b2 |
| records/interceptors/printf/tools/SegGxaSeam.v.post | 0437704903e385ccbd4703c09a99505914b4e4f2d1f88152db3234e3bafbc9e9 |
| records/interceptors/printf/tools/SegGxaSeam.v.pre | 6598dd325885a15a30a93aa20e42e4287c37975e47a5b8023ba098439f894501 |
| records/interceptors/printf/tools/gen_seg_seam.py | 89a3f2d6af8d44af21b08641ff1c859fe527af4a36b352d03e772fc67742cb7d |
| records/interceptors/printf/tools/to_cmd.sh | 35fd63ae848db3f734202b9d7d4e2bd1b5c3ff22dfdf75ed6e60f9734381ffc8 |
| records/interceptors/relocation/PATHMAP.tsv | 18665d332d2ed07cdd9c9db2593d27e975f7b3d7098965d9387e347a6231d025 |
| records/interceptors/relocation/README.md | bc889a452fce760d081454c0d3f1468be17ccd894783422b3f35f577b710fd9d |
| records/interceptors/relocation/aexact.tsv | 9115af80b0e32beaba147f9a37fa275e13286b738662d0965a4bece4c0a54dcf |
| records/interceptors/relocation/commit-files.txt | 33c943efe6579af079a6c9a8ee4d42c6e2221ab3ba3522f93ea375812f1f84f2 |
| records/interceptors/relocation/dirs.tsv | 681234a90712076a5f8119b3bae4f02af296baa72e5f3adae735855c5549487d |
| records/interceptors/relocation/dropped-to-a3.txt | 5b133eed53312c8e72aa03a5a15aa41ee07ba91688245fff12a460f721e02d76 |
| records/interceptors/relocation/files-A.txt | cb54747ad8f8f0ae2e5095df957c6d70ef0f38707c8f321bde822eb578e03e88 |
| records/interceptors/relocation/files.txt | cf413275b392eeb54bbc5e882a78108a63b1e097f638c8e68fdd68712bc33177 |
| records/interceptors/relocation/keys.tsv | 4960a492a02b490044a4ba339921630342dbbb2e61949a63c47d747d17e10789 |
| records/interceptors/relocation/ledger.tsv | 0f66bec746ee47a2433a68dbdda21079bae510f36bac01db8bbcda3a57cbd116 |
| records/interceptors/relocation/open-rows.tsv | 55de394e0716868cb5946c434cb903b153697fe77a8348b8958c3196b119fa1d |
| records/interceptors/relocation/out-of-tree.sha256 | 6a22e352f74c6a9de7c58ee11dfee9a5ac23e266590628f3d62986da08dd776a |
| records/interceptors/relocation/overrides.in | 556432bb149c1b233865e7d332ffd2064b6a3097b7fbc16514141ba3c7f0d2e6 |
| records/interceptors/relocation/patches/no-strcpy-strcat-atoi.patch | 5f18120f035f53875eaef100106b6eb33a956baf7bf7f1ca5151cc934eb3ecf3 |
| records/interceptors/relocation/run-d9e0.sh | d2f1b6ac6586fd6f19145ca67a96f46147559bcb85e90ba349a5068453cf0208 |
| records/interceptors/relocation/run.sh | 84a7aaafdd175d7504c7562dee742a83551f8b8fb3a30be43d160a83fd1d4e06 |
| records/interceptors/relocation/scripts/check_agree.py | 0dea300616e0df92c5cbf3e371f65f622456c192ae44269431045845c68906dd |
| records/interceptors/relocation/scripts/check_aiv.py | 4f557d4a025e9b3e3ac2c8fb3b1185a24c66306cbeda9fdcaadcb4da1b476994 |
| records/interceptors/relocation/scripts/check_counts.py | 04f7fe68896dfa905d8ddfb476781821be5bb85f80e2a7ae5dceff8108b84936 |
| records/interceptors/relocation/scripts/check_defs.py | 377bc501ab57394529938514df5ed9ab14bddfc0a15058931e61162986c13e5c |
| records/interceptors/relocation/scripts/check_dirs.py | 4874d29fd4baeb3fec17934ccff38f91cae1e4a69426235565640977aeac9b91 |
| records/interceptors/relocation/scripts/checks.py | 143d407c60a72480f79bc5ad87def63bd4172b16824632b530a99e4f9969eb79 |
| records/interceptors/relocation/scripts/decide.py | 7362970a90f921acdc91f285e3eb4958b2a93be8e28add54b31f2590e7ccd71c |
| records/interceptors/relocation/scripts/fix_dirs.py | be86bb1dc120605e1a9db38d95ddca1f875391c881504af547d308a55337a499 |
| records/interceptors/relocation/scripts/keys.py | f1379aa8af9854aa3127dd10a20d552e1beda8f221a136580714caccd9ce139d |
| records/interceptors/relocation/scripts/mkoverrides.py | afd7082cd4a38b53a09ab85f60c849811c488caee244116693d214ccc56375db |
| records/interceptors/relocation/scripts/mksyms.py | bb7940865e527f1f97c21c7049ad420add7251e6c871317d5a4fe43e39939a4a |
| records/interceptors/relocation/scripts/req_check.py | 82cfc63643f9c3c4f32ba2c7a5939629cc6f961d73258256491533a222e33f53 |
| records/interceptors/relocation/scripts/verify_aexact.py | e3f11264bae242f325a97fd741cf0a528e44ad7d4491fb61194854474ee68f3a |
| records/interceptors/relocation/tables/83f5-difflist.tsv | 546529d8e1f0a7ad68245125a5e4f69d5fdfeeb05884b526977de3eaa4d8d6ac |
| records/interceptors/relocation/tables/ab1w-merged.tsv | 30ecbe2a1234b04ad58ad754eff30cc58cde74027b1442cc498970b3a180bf50 |
| records/interceptors/relocation/tables/agree-independent.tsv | 54075ac6f4e07639c965654c3dd3121b7dc15c066d5502de9bb85c7ed22d7a79 |
| records/interceptors/relocation/tables/agree.tsv | 26719f7ef2fde8d0f7d877df9879f8126fd5459620c679d64388986655b83d38 |
| records/interceptors/relocation/tables/cellcheck.tsv | cefd201fca01bc7097ddfa2a21ff3216ecf77632e5ae78e24c4145bde9c9e6b3 |
| records/interceptors/relocation/tables/cellgates.txt | 18d8ae0c4789158787875686bf76b67e3c795baf805cc418fb0a22811a56e345 |
| records/interceptors/relocation/tables/cells.tsv | c11d682cb0a0efbf20576ee19117d97bd88cf5f1531df8eb3bf7f36d77db3205 |
| records/interceptors/relocation/tables/check.tsv | 97bbeaf5c2420105787943d32fd19800942460ca8e66db1ac78e08485e866d1a |
| records/interceptors/relocation/tables/counts.tsv | 1bffae867a4e409135f3a9243773a2952c62a279e3759876f0354253476c5cc1 |
| records/interceptors/relocation/tables/d9e0-difflist.tsv | 57b2cfc99d7a64c5ff2e70a841e6695b04153e500c4f75e3eaac3537c8dfc0ba |
| records/interceptors/relocation/tables/decimals-left.tsv | 2fa880a2474630ef658b94fee07430014e4f94ff21bd9ac2fff320859fdab104 |
| records/interceptors/relocation/tables/decimals.tsv | 0c6701920ee4f69182cf2cb05584a90dfdec8da93b56943d1ae3f75db2074493 |
| records/interceptors/relocation/tables/differs.tsv | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| records/interceptors/relocation/tables/gate.tsv | e01cbd224cd48d71da9c018331ac6a6b2e2a1d5a77b12cc1efc243bc1cdfe433 |
| records/interceptors/relocation/tables/geometry.tsv | e94ea3f5f4a8404b93d061b91445418093633ca814d40fe86776f3d200ffc8b1 |
| records/interceptors/relocation/tables/got-check.tsv | f93fb51795512729d6ac901abdb093c43d69e0cd2d7d48ddf4b995d7152376d7 |
| records/interceptors/relocation/tables/got.tsv | a8403cdc0b1c926237e8aa6a5f806f12b7bf9e9612d03bd13cc5706b1b226c14 |
| records/interceptors/relocation/tables/hypothesis-values.tsv | 16782477fbba88b1fa13cbc2c6be11b2698a0b271214d3026c7119d6bb532daf |
| records/interceptors/relocation/tables/kept.txt | 01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b |
| records/interceptors/relocation/tables/names.tsv | f836309db120dd180a0d9ab67b989d0dace1fc1eedf3a263d6b9e99e76b0e89a |
| records/interceptors/relocation/tables/no-twin.tsv | ccc2def33eb0d779c85ff1ff1c4b52d60eaeef7e4e120bbbd7084df957cc0c90 |
| records/interceptors/relocation/tables/nonA.tsv | 37a9805bf36b326511a9dff95d8646522bec1362b072e88ad858a87d9a408a57 |
| records/interceptors/relocation/tables/overrides.tsv | 69503ebb4b3ffd0f9db87029f23b5279381b8ac7e84fb44b9d7b038c2a187912 |
| records/interceptors/relocation/tables/rc-ctrl.tsv | 17bf51db97c6bd5e4ac2cfd43b2ae826246299050fdd9fde6a9f4e814c582914 |
| records/interceptors/relocation/tables/rc-kept.tsv | d6dfe6330b71eaab2bee0bcaefff3b8241b7b961e2836237f47d9e5d063b69c1 |
| records/interceptors/relocation/tables/rc-moved.tsv | 8f1fe399580f38bc2afc5f98b05d92a0486760addf4e4a7f7fddf43a5ca78d2b |
| records/interceptors/relocation/tables/required.tsv | d0434e7082ebf7ecaf754108ff6bdd13b2f52b620e4177247ff65297f2da8559 |
| records/interceptors/relocation/tables/rowaddr.tsv | dd0f925ffc3e3fd5aadd11828b96b08abb7129aec3ec9392e6255bf24ecf8f4f |
| records/interceptors/relocation/tables/slots.tsv | 0b9f6ace057c043d4b151ec43575ee117587b5d71f8a8e5ff782953e0f7b0e3b |
| records/interceptors/relocation/tables/stmt.tsv | 9a5f65536993246eb2f5adc5e30fafd8e647cccf961c2d09805c6747a7f9901e |
| records/interceptors/relocation/tables/trampolines.tsv | a09d0e55b9cc3f6150e1607b951379c88384a851f79f1b974dd1fd921d40de1c |
| records/interceptors/relocation/tables/versions.txt | 71734cfdf646a6653377d7bea3b27fd46de918f15ebedd01c5ae2ce03507b41e |
| records/interceptors/relocation/tables/vocab.tsv | 30cb5753335bf6c1e7f4266e850d841ad5768f022aaf6bb5f95caf8b71473697 |
| records/interceptors/strncpy/METHOD.md | 8959dca22fe2a7178a955b644583586174d702290a5714c705136030dc199e33 |
| records/interceptors/strrchr/PATHMAP.tsv | 635b7dd955b4ea062baf9912fbf13851762df8c3d136ebe00bc80042601aef3e |
| records/interceptors/strrchr/reloc/B-moddirs.patch | 58cac35bfc2814b529a7265d419a7eaea056a5efe5abe14f4a6da267f9c0d8b6 |
| records/interceptors/strrchr/reloc/RELOC.md | 7e0277c92baa3acb597142d1d19d7e428964b34bf4203d11cd5b16ecafbc9021 |
| records/interceptors/strrchr/reloc/altA.sh | b553746ba5cb5dc8a7cb7fed20e96feebfe094dc58a7951899dfb52ac0a54727 |
| records/interceptors/strrchr/reloc/altB.sh | 901fc4e597119fa6958c1918abe2dd5d0b12919acd78ec463eb0e5961df50df6 |
| records/interceptors/strrchr/reloc/checks.out | c547168351154856fe2a0ca13851a17002fa0262b7324e9a836a826abc1b7684 |
| records/interceptors/strrchr/reloc/checks.py | d020d2a6d0e4a8713dc0a3f0c6db138d2ddc8e86e4659ef4c04f3e38c670dac8 |
| records/interceptors/strrchr/reloc/disagreements.tsv | 4fe62a7ee094a525e79ff7ea874290a0baae8b9fedc4ea5566355413a25e8eb8 |
| records/interceptors/strrchr/reloc/filesA.txt | e37eaad5c3652e8562f428912868581161b54300c5a0ae957f1b5762acaf5412 |
| records/interceptors/strrchr/reloc/filesB.txt | 644c697c48ad30e7a4d2fd0c93132bb04aa2e2fb28d89f714dc9c32c766d2620 |
| records/interceptors/strrchr/reloc/ledger.tsv | 0b66c0849c4a590f0cc92b67f2e868fec6eeb2428b606823c4be9d3fbd616c0e |
| records/interceptors/strrchr/reloc/mksyms_reply.py | 526c8d181821f86e313cd11ec92eb87c8e0921129b8dee2c4e03f75817373cf6 |
| records/interceptors/strrchr/reloc/numerals.tsv | 5ad2f570634d55b62f202b88efb493bfb8136196bc4aca7cde64b17ce246520f |
| records/interceptors/strrchr/reloc/out.sha256 | f4c6a0d3134159474a2e604ab5a1abf4fcd2a4315b752d16f876250926c8c998 |
| records/interceptors/strrchr/reloc/overlay-from-fm-stage-out.sha256 | 2985fac1c143722865e67f866285c4b6cf5784cdfece370a0ed1c0337076d7c9 |
| records/interceptors/strrchr/reloc/overlay-from-pc-stage-out.sha256 | 4971a6c5d5d7ba79c53b153a737e3132a85e84dc36bde6cd0c8aa632dfd7d17b |
| records/interceptors/strrchr/reloc/runA.sh | 5471f93e2b3c52d3dab1d4ef9a8f1fbcd06831612ed3b1944bdfbca5e5c06724 |
| records/interceptors/strrchr/reloc/runB.sh | 6a2fe5c01b5c4d3d0dc8ab35e554cab4b255b52b8857f160a21db6eed0924124 |
| records/interceptors/strrchr/reloc/vocab.tsv | 16c04dc4bb4430e5f6ef24910268a4c8aaee61aef944670102e9fc9e79679ffb |
| records/interceptors/reviews/ctrreview.md | 57e482a595bda1b65f4aad8849c2f90c32fb1a0812cb9e3723c8e637d25f700c |
| records/interceptors/reviews/pfreview.md | ef57763bee0515fb2eaaca76b33edd51e200962e576517bdf6c4ad0b21067648 |
| records/interceptors/measurements/callsites.asan.tsv | 704ffff206b5fe92fc9cf27eb4b8ea7e0fe03d0488babaf15d3a2b3132216a4b |
| records/interceptors/measurements/sites.md | ae7d3353ce4c9924faceaa598d2103b907d65e044c157cabe867400feac34d53 |
| records/interceptors/measurements/callocplan.md | 7a3106749b34370a7af304d77745a40b11a39d3f4d739d0f5206a121ffd981f0 |
| records/interceptors/measurements/pfdesign.md | 1eae8f5667f83911adf3a7a60863e9750d81a49235dea23dd1b0d5a5a17c8f16 |
| records/interceptors/closings/memchr-window.txt | cf83654158cca2adcb35401dd4b7a07aa46f5335be101a113c5cf6c961f5e1fc |
| records/interceptors/closings/memchr_window.py | be60bc47a88c5537ba176d97449e1a4dc6bb7346d537ebe7573afc9320a4a035 |
| records/interceptors/closings/req_closure.py | b051a4a806c033477dddf677726b4a11be3304a41f4519d051b0c920087d3fc6 |
| records/interceptors/calloc/PATHMAP.tsv | fd0782ba8a668e1a1081074f5ee6172706874ce96e3ba13a9100feae88c6a9f2 |
| records/interceptors/calloc/YCbpCalloc-CONVERT.md | 3a3df604d5a3eb29b7d9eb70690619e8ab5c04256e929f4102a44a2da08ad8db |
| records/interceptors/calloc/ag/PATHMAP.tsv | aae4b9504424f1a7dad87fb1b5db3eb89247db71fd4f89f85dc07f21b219311c |
| records/interceptors/calloc/ag/RELOC.md | 4b56580e149d08795bf7622afc2fc3e423a5274bdc3f67c24a9ad0f40943e4b8 |
| records/interceptors/calloc/ag/alreloc-compare.tsv | fa49e63161f4b0d131e7c048222e9dabf74179aeadc724d0b981063f9baa0e8d |
| records/interceptors/calloc/ag/alt.sh | e86cb3fc36fc8ab0891994ac2a0f370679bfbbb4d1df296e7908367bb9450e7c |
| records/interceptors/calloc/ag/cells.tsv | 9637e63bd480c3c63d88d40afa6414c30c441e471502d605efd95147ceb39518 |
| records/interceptors/calloc/ag/checks.out | 09607ddac310c0ea9d8ac5dd174499320cbba50bbf98f452ff6700e570d7fe9d |
| records/interceptors/calloc/ag/checks.py | 954b8b9139b236eedd240d05f662bc8e4f1a4d33dba6d8cc32ef2470b4261ac9 |
| records/interceptors/calloc/ag/d9e0-vs-7a74.diff | 13ca004142cfa9e66738cc66ad71de0ba4dd255d7da260f043aa6057c26260a0 |
| records/interceptors/calloc/ag/disagreements.tsv | ed50098ec2195b5339bbb2f8689e086114f1691f012ae01ce840c8adbc3aff87 |
| records/interceptors/calloc/ag/files.txt | a1d8dc5558843d46b5c62047a3b0d6fb4df8d146428252345d112d5103081dc2 |
| records/interceptors/calloc/ag/ledger.tsv | 91a80affec3c84633f30e969cd2c6ce37936d32450293d8befa6a8fc0c86c4fd |
| records/interceptors/calloc/ag/mksyms_fs.py | 26867a236c76eeb92e0f1b72fea83768d525a161b8cb19f6c0ac1fc709a0bf18 |
| records/interceptors/calloc/ag/numerals.tsv | 500e9981864f206223c0f974ad448dd151573e6f2191990bec1d23ed205af657 |
| records/interceptors/calloc/ag/out.sha256 | 142d55f329829edb7ae5df58076924494d542764f392e8691a08129266aac03f |
| records/interceptors/calloc/ag/overlay-from-fuzz_command.sha256 | 19ac5b6f20bdcb6ecbfec4e7439f02b402741cec61d368ddbe0a245b3cd479ac |
| records/interceptors/calloc/ag/overrides.tsv | 0b30c8f963111cd63de7dfd5c4a209f558b23a97355146b82e5fe2a0c6e37e8a |
| records/interceptors/calloc/ag/rebase-edits.patch | 72e541895850b4144dc235fcac8933cea45a659b735a9fe83a49d9cb4b7d64bd |
| records/interceptors/calloc/ag/rebase-uses.tsv | feead00165f65a1c50b7ded5994bcb5d9bf6a620f9a0c788af4a8309acc3ad59 |
| records/interceptors/calloc/ag/require-ygalloc.patch | efe5d42e5b8b6124173da4d8d23c82124de38d114819c764f1f89961746f3c29 |
| records/interceptors/calloc/ag/run.sh | 67c81f39002297f213d419cc670b22dbf424781c953b9c808f80d5037c191fe9 |
| records/interceptors/calloc/ag/vocab.tsv | d8766c3e5499105c20658bab7234fecfe6f8fdd5b7579ea3710e137e16b4de6c |
| records/interceptors/calloc/walk/PATHMAP.tsv | aee8df994b53c6df1eba2e9dcaba14cf27e60fe2f0fd73484f66b5f3757dc197 |
| records/interceptors/calloc/walk/reloc/HYPOTHESES.md | 91126f885a55fe92790d8a06ae8610faf23c8bcd490424dcd7d39258b7035f8f |
| records/interceptors/calloc/walk/reloc/RELOC.md | 87f4eafd232c44b1e2ff2572ce97ba258b4f116aab1e587b9958fddbe93ceafe |
| records/interceptors/calloc/walk/reloc/about.out | b14a21db2f18cbb2539b4ff2f8b81bd7a87cf838c29f80492ba5f274eaa7cfa3 |
| records/interceptors/calloc/walk/reloc/about.sh | 4a2e6f89b3e779cb98e84ce0916345b41ef18a9f5b1e418f3784a402c612566a |
| records/interceptors/calloc/walk/reloc/alt1.sh | b202dee9ac357192fa74622fa4549f0363b5c89e651938cbc7fe8db04229522e |
| records/interceptors/calloc/walk/reloc/checks.out | b5a324185f3bd27b6844f1b1858921b167de80381936803c790b99b17cec47b4 |
| records/interceptors/calloc/walk/reloc/checks.py | 8f813d826d037064a44f8c8b46050589f61224bcf6972cc4d2d3bde147cb7cf4 |
| records/interceptors/calloc/walk/reloc/closure-DecodeCallocTop.txt | f3fc5961171cbd8d5024625ed29ec167d6d289472887026cbd29eb1fd27be12e |
| records/interceptors/calloc/walk/reloc/conv.patch | c94865ee56e420bad003f9ac79b4b8268b03b0e0fb2b7066a3b3a06820859f7f |
| records/interceptors/calloc/walk/reloc/disagreements.tsv | 3c611fa4dbcc1435f38674e043486f0a186655e050a7502a358ac3a4c31396a2 |
| records/interceptors/calloc/walk/reloc/files1.txt | a1fe89b5483ce3c40e2ae113730c190724a4816e1fd995c015722ca97b18cbf7 |
| records/interceptors/calloc/walk/reloc/handnum.tsv | 68baa1c4b442ad767740be11a4651f3be961efca05e427376f52dc6be8b3330f |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN11__sanitizer10StackTrace12GetCurrentPcEv.fuzz_segconf.asan.s | 61ab6952f8209900d7d7b8e8971d29d3b8c3753340f7de7ba6e52afe6a8b4d25 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj.fuzz_segconf.asan.s | bdc263e5754a9cb0e4450332c33d4b95c277d7b8816e73395fec9c1e6a3653cd |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj.fuzz_segconf.asan.s | fe28ade5458df6c6d6f409a8b4a674610667dc830022505bd0eac0d3d948e642 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN11__sanitizer18BufferedStackTrace6UnwindEjmmPvmmb.fuzz_segconf.asan.s | 929ba4b063d145c642a4c815d370baa7a5f699601d537dad05b9be13ee1d387b |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan10AsanInitedEv.fuzz_segconf.asan.s | 6dbadc170b67ba0c6bd0cf99125c2cc6431e7f3d730a9d1113cb1c3461296b5d |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan10AsanTSDGetEv.fuzz_segconf.asan.s | 28a94a808439d9b2a34b883ecc431503840d32e64cc49508e7b727474cfb5642 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan10AsanThread12stack_bottomEv.fuzz_segconf.asan.s | 25c077ff98cf21a4d8e5ac943825512d7fe9ae8a44463f05ba03befdeef56586 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan10AsanThread9stack_topEv.fuzz_segconf.asan.s | 65a574c24ce111424bda866228f459937b2e8887be92a50f969811209f53be61 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan16GetCurrentThreadEv.fuzz_segconf.asan.s | 6403aedc88dab4a0dfc50f73ebb6de050c5b0323da1988d11b1955d861db0ca3 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan18TryAsanInitFromRtlEv.fuzz_segconf.asan.s | 818de8c4d080a6b1ae1aea4e99b44d70b481ad4bf400afadf8de96fdcd6152a0 |
| records/interceptors/calloc/walk/reloc/hyp-dis/_ZN6__asan20GetMallocContextSizeEv.fuzz_segconf.asan.s | b4f4d34d35432de2dac098d6017df2e484c22bc0330e1ba52c8e16ca379cd696 |
| records/interceptors/calloc/walk/reloc/hyp-dis/___interceptor_calloc.fuzz_segconf.asan.s | d5f4dd0cac8135e581c07fe03c008079b69261166c13f6ff03efbcc97f357c81 |
| records/interceptors/calloc/walk/reloc/hyp-dis/__init_tls.fuzz_segconf.asan.s | 3bcd70f423b526edf04cac9ee81edd5ad2d76120f02c9336db8ee2d78c59f04a |
| records/interceptors/calloc/walk/reloc/hyp-dis/__interceptor_trampoline_calloc.fuzz_segconf.asan.s | cd1474f890080007a071a68647af1224c8fc67b0d76bd1b0bb4a5800e9a6c90c |
| records/interceptors/calloc/walk/reloc/hyp-dis/memset.fuzz_segconf.asan.s | ac9cd6cdf2d529434a340bfa8ce3d1f5917af9e5655af0fbe03bc94d1fe114ad |
| records/interceptors/calloc/walk/reloc/hyp-dis/pthread_getspecific.fuzz_segconf.asan.s | 6f3ac19b9652bda3c13ab63500d7368d84c8b96d3a594bf7cff04d3b3b24838c |
| records/interceptors/calloc/walk/reloc/ledger.tsv | 5d62c7c076d0bf791da6807e84572b6121a9b079ee61a86d62e5e0c48dd48e8d |
| records/interceptors/calloc/walk/reloc/logs/alt1.log | dd224ea4ecf866bc9a7150067fa17b879db0ac6d2729b23529b90a070d0368b1 |
| records/interceptors/calloc/walk/reloc/logs/cb-build-20261030T194520Z.log | e71f63c1fc2dbc5723e840583521328d85cd2e1fecac9fc078e1d0537e9d1709 |
| records/interceptors/calloc/walk/reloc/logs/cb-build-20261030T194855Z.log | dbde31e11dac926138397ad2c3d7ca16bd93b1a9eaef27dc2d79a9ce89bbd883 |
| records/interceptors/calloc/walk/reloc/logs/cb-build-af5f9fdc0576.out | d2faeca7f8bd5fe74ccdd5a8ba6b217a3f521530ff87b550b1a9bda0b367e3f7 |
| records/interceptors/calloc/walk/reloc/logs/run1.log | b2b76cbcecc58b130f092eef3508a3c4bb919209ed88a9074ef459b23f5bcf2d |
| records/interceptors/calloc/walk/reloc/logs/run3.log | 4a56573cae8ecd773726a65c0df4a4e50260160d404766745f3464f276a318d8 |
| records/interceptors/calloc/walk/reloc/mksyms_decode.out | b14609a52222b4ce0b9b3918737f639a19b0e54c9423c6d31e9032c4b01f0c0e |
| records/interceptors/calloc/walk/reloc/mksyms_decode.py | f2109370a2ad81460d3617652443039e584596e06d821b89be511ccfcc232751 |
| records/interceptors/calloc/walk/reloc/numerals.tsv | ad77bce2ab691f7614e0ba7149a9c9fa632d7d52c5ab217baebf9336033d4c34 |
| records/interceptors/calloc/walk/reloc/out.sha256 | 0fc1326d6e35034f09d91155ba0d2a1a66f14b17a6d6375e275eda51e03a260a |
| records/interceptors/calloc/walk/reloc/overrides.tsv | 81eabfc27ea9424d6f03303b3d7cad2c30f04ec9825afbd9c7aa94c199b9ad29 |
| records/interceptors/calloc/walk/reloc/run1.sh | d88b76b81d13e6c3b0149d2ec58f0fc17484f2aa34b8a35066492c2b3acca7b2 |
| records/interceptors/calloc/walk/reloc/tables-work1/cellcheck.tsv | f5f649c27c47fd2576300a636fa9301730a9ac0046a16d8c1e56da045bc01342 |
| records/interceptors/calloc/walk/reloc/tables-work1/check.tsv | 2e76af029676cd6582142235715703f2fd0a806d90c4deec4c5b463cddf98e72 |
| records/interceptors/calloc/walk/reloc/tables-work1/fixed.tsv | 8d0caf6cd677316cc17904d6120a49d23fea2fe62532c691a24dd26466fdc51a |
| records/interceptors/calloc/walk/reloc/tables-work1/got.tsv | e319a349b5ff8382f5538f09cdfb1654004a83ae993f3695cddc0f157b82583a |
| records/interceptors/calloc/walk/reloc/tables-work1/names.tsv | 19c495dbd04dc047de66b3ec6d12768f42aa36750c71ff649719d0ef02a23e72 |
| records/interceptors/calloc/walk/reloc/tables-work1/no-twin.tsv | 54d638479e7e6df1cff5e8f4fccc79b0f9b26bbf9400f28d41cc528c7e46121e |
| records/interceptors/calloc/walk/reloc/tables-work1/nonA.tsv | c30ae51e8c5d083e6389847106b7f91a08844a921f9f4b09717993801fb1bebf |
| records/interceptors/calloc/walk/reloc/tables-work1/required.tsv | c5fe22891d083e576c0681a40a8f52271f3b8b40288f4dbc3cf13884b24b14a6 |
| records/interceptors/calloc/walk/reloc/tables-work1/review.tsv | cc5cb4a33753f1ff199a278c3c0b19bc298bd76805f6c6bf0ab324bfec9ea2dd |
| records/interceptors/calloc/walk/reloc/tables-work1/versions.txt | 71734cfdf646a6653377d7bea3b27fd46de918f15ebedd01c5ae2ce03507b41e |
| records/interceptors/calloc/walk/reloc/tables-work3/cellcheck.tsv | 4e8046fac4be89b6f97c8075b95e68940b0c725bfab444b484042e77a6561178 |
| records/interceptors/calloc/walk/reloc/tables-work3/check.tsv | f94bb9281110092a84187696248a8a67843b2054de031971d309d309f424c855 |
| records/interceptors/calloc/walk/reloc/tables-work3/fixed.tsv | 8d0caf6cd677316cc17904d6120a49d23fea2fe62532c691a24dd26466fdc51a |
| records/interceptors/calloc/walk/reloc/tables-work3/got.tsv | e319a349b5ff8382f5538f09cdfb1654004a83ae993f3695cddc0f157b82583a |
| records/interceptors/calloc/walk/reloc/tables-work3/names.tsv | 766cfc5d8e290f7beca55dce4f9712120d6c3a3d1a00a8ae41ca48072326e3c9 |
| records/interceptors/calloc/walk/reloc/tables-work3/no-twin.tsv | 54d638479e7e6df1cff5e8f4fccc79b0f9b26bbf9400f28d41cc528c7e46121e |
| records/interceptors/calloc/walk/reloc/tables-work3/nonA.tsv | c30ae51e8c5d083e6389847106b7f91a08844a921f9f4b09717993801fb1bebf |
| records/interceptors/calloc/walk/reloc/tables-work3/overrides.tsv | 69e684eda5448c73122a276e9b876acfc0f5a396081d89f2165b93e35fb8de6e |
| records/interceptors/calloc/walk/reloc/tables-work3/patches.log | b83bcdd26948c0dcca8c580af07d9715daa76a9cae0e379a357316f54e7a1d7e |
| records/interceptors/calloc/walk/reloc/tables-work3/required.tsv | dbfa1811ab1e69ad15d1e8e99517bbd0dae8982e65893f7f59be6fdd18aea2ae |
| records/interceptors/calloc/walk/reloc/tables-work3/review.tsv | f720e7a8c6a66d88bf95ffa844fd630f07bb0b4f9e96b9854b61f180db947e24 |
| records/interceptors/calloc/walk/reloc/tables-work3/versions.txt | 71734cfdf646a6653377d7bea3b27fd46de918f15ebedd01c5ae2ce03507b41e |
| records/interceptors/calloc/walk/reloc/vocab.tsv | dfda75b341af209f282720e7d4ee5475b6092d8be09e66cacd38fc6a5924203b |
| records/interceptors/calloc/walk/reloc2/RELOC2.md | 02d466f8e22d98819fe761cd900bbfb7d61432790a96eade9c6e8c7dd55619ac |
| records/interceptors/calloc/walk/reloc2/about2.out | a6392cfcebc56e369d2bf049b72b644d427c751fba39ea6fa5576a9ad8603e87 |
| records/interceptors/calloc/walk/reloc2/about2.sh | 119f7638c373a66c97d028daa047a73ace551429f7019156059a7666507bd1f1 |
| records/interceptors/calloc/walk/reloc2/alt2.sh | fccd8a338fabc4bc94eaecd4082140a7af21ffc05aafa7ca6698aed103a203d9 |
| records/interceptors/calloc/walk/reloc2/checks-a.out | d5ac1ccae22cb0bdcd3d62f8de74850fa2fab3521150f0ac52985e479597f8db |
| records/interceptors/calloc/walk/reloc2/checks-b.out | f9ee957430c0fe920adea302f1e18a89e363fc10006752b24fdd60779c4a2acc |
| records/interceptors/calloc/walk/reloc2/convP-a.patch | 1e32ea7d9c7a64111f898e8c670e192019a14a688e52cd327a3699c17167bdb8 |
| records/interceptors/calloc/walk/reloc2/convP-b.patch | 5200bf4f172cf3e1ec56bb1301f9982db445e99f98744087b7a7d947e278f7aa |
| records/interceptors/calloc/walk/reloc2/files2.txt | 57043bd76db79de3f701c146fdf84b1960d60fbe27e342a757af25638cb09756 |
| records/interceptors/calloc/walk/reloc2/handnum-a.tsv | ec50b5afba00d44efdaf3f5015958b692f4920986b32f3d9b06059f70eaa9f2c |
| records/interceptors/calloc/walk/reloc2/handnum-b.tsv | ec50b5afba00d44efdaf3f5015958b692f4920986b32f3d9b06059f70eaa9f2c |
| records/interceptors/calloc/walk/reloc2/ledger-a.tsv | 8fd73c00fa37b5d3354085eaf8ca64a62eabef3c9312472f76460f854e0e09c7 |
| records/interceptors/calloc/walk/reloc2/ledger-b.tsv | 73c99088def8e8c7ef146e13bb6ce78c9708a486b39bb7e1c6fb50da4e042aae |
| records/interceptors/calloc/walk/reloc2/logs/alt2.log | 0012236276aadfcb04f05dce6cd99734aed0ca600b32c9ce82694323b31dce55 |
| records/interceptors/calloc/walk/reloc2/logs/cb-build-20261030T200812Z.log | 0cff1850186080c1a9290c5fd25f304f6aa83bf1a0705a777be742e98b5a1833 |
| records/interceptors/calloc/walk/reloc2/logs/cb-build-20261030T231701Z.log | ee2f5e948edee170105ef203bd62d7734357f43485f25995b6948dee1190c24c |
| records/interceptors/calloc/walk/reloc2/logs/cb-build-20261030T232122Z.log | 9e5a49f76fcddfab52ccdaaa819a39c1268e7cc9f74afba9cd453c2797777eb0 |
| records/interceptors/calloc/walk/reloc2/logs/cb-build-9cc685db399.out | 99c95a98f04ed3b3e0e734fd8863d27ab31994c9b21231f9a14203caa852dcfc |
| records/interceptors/calloc/walk/reloc2/logs/runP1.log | 8b1b4a56f799abd92a6efcb86d06cf700a11739638d6dd1786da08a9a8301851 |
| records/interceptors/calloc/walk/reloc2/numerals-a.tsv | 831fc438a7eea7a3c0127d67a32d5cfb801ba9366d71d36f863b7a8011938982 |
| records/interceptors/calloc/walk/reloc2/numerals-b.tsv | f951140183cd9be2099f2ce7688d35e8bbb9b3aa21dbba7024a0817db2ffb140 |
| records/interceptors/calloc/walk/reloc2/tables-workP1/cellcheck.tsv | 20564f0ee394423184c7843ad74e840675c9803f03554e0f7be35dc1189bfbe7 |
| records/interceptors/calloc/walk/reloc2/tables-workP1/check.tsv | df73a8cb2c48af3fe1ed5764ddcc61ca00683aa9bb636688f55005386089925c |
| records/interceptors/calloc/walk/reloc2/tables-workP1/got.tsv | 95aae41fecf38adbd6ff4cf797487cc90b53c98675317e22063d56b1f613d6c0 |
| records/interceptors/calloc/walk/reloc2/tables-workP1/names.tsv | b1ebafdd788f1770c6ae1803f33153cfbab22d201214d96ef52731f661b46fad |
| records/interceptors/calloc/walk/reloc2/tables-workP1/required.tsv | 9669deea865a727beca3ab51a0d5c017abbe8f9eddf338264ac6428eccda03fe |
| records/interceptors/calloc/walk/reloc2/tables-workP1/review.tsv | 765f8a5b9425f7c651fe4acea72a0d22e08ddacbf6aa9d3e48cf24185b970c73 |
| records/interceptors/calloc/walk/reloc2/tables-workP1/versions.txt | 71734cfdf646a6653377d7bea3b27fd46de918f15ebedd01c5ae2ce03507b41e |
| records/interceptors/calloc/walk/reloc2/vocab-a.tsv | 4dd2a2712e39e571f001e8217b887855597c0b7b284891b3e520a93ff324a0dd |
| records/interceptors/calloc/walk/reloc2/vocab-b.tsv | c54d8c0436698acb04071957e8ecbad11e96190898bef4bdcce2dfb748f108c9 |
| records/interceptors/relocation-checks/INDEX.md | e0e4b082eef0a752a2e26488fa94e2d6e8bf9f25ac44980aaff15926daf93cba |
| records/interceptors/relocation-checks/RUN.md | 298449c431d7048c4e0a4e0a34b2737b78d3c0255ae64b84917d04683b7c3b77 |
| records/interceptors/relocation-checks/audit_mkaf.py | 01e57b981366f0235b0d828c36e74acb400bf126ee2a0fbe086ba38db2c35075 |
| records/interceptors/relocation-checks/check_agree.py | fa5f9460a4c32864ccb1a2f6dbf5bfbce122ffc7a1680cbde0cffe0dd8d468bb |
| records/interceptors/relocation-checks/check_bounds.py | bab93f8286a0f6ddb40f692c607dc28e981a5dfb269a835bee70636d81ed54dc |
| records/interceptors/relocation-checks/check_counts.py | bfd473b9e1efefc525f03b7539c7acd1e1a19b20965ac3e926b55674024bea23 |
| records/interceptors/relocation-checks/check_defs.py | 807661cabab3d3d6717ee6f9da556e3a727fa884fa3a5ef829e1dee29304963b |
| records/interceptors/relocation-checks/check_dirs.py | bf7320fa0d6b47d45f9e902779f3f1b81c2fdadaa31684a31b299d121b965fc3 |
| records/interceptors/relocation-checks/check_geom.py | 199f8a06d4fbb8aa0fa21cf2f106e062f72881afd2dc76a23687d5db7f8567f4 |
| records/interceptors/relocation-checks/check_words.py | f6871249c805c185d1b34c023cb36b32f048eeadd15e31d2b2d3b00a2cc31710 |
| records/interceptors/relocation-checks/checks.py | 2645851417eb60d0809ddab6a48c81d72432b08f070bd29fbaf80f8a32f076f8 |
| records/interceptors/relocation-checks/decide.py | 2bd6e1fe76b8ffbeb87ebdf1d5a1d0aede1783b1109a4ecc77b1e7ae0fb6fe7e |
| records/interceptors/relocation-checks/fix_dirs.py | 36771f2c8e741253bc2186fa70b823125c294d271b9d849280e92408b82330f5 |
| records/interceptors/relocation-checks/keys.py | 569b9a2a931272a27d5cbae49cfc2d8a6a9f898a2b23852e5035ff85d4477874 |
| records/interceptors/relocation-checks/mkoverrides.py | c4281a79ee9e0bb698f311defcbda2e23725bcffb5928d28d90a76ca01382c98 |
| records/interceptors/relocation-checks/mksyms.py | 598ae431682ca6f9d6156c8fcfd961c5f012d26b585aa8c43f0f6f80f86b50f3 |
| records/interceptors/relocation-checks/req_check.py | 5ac4aae03103f266deee49b9f11fdc39d825ff0294f6853279dc8ad6c770c2de |
| records/interceptors/relocation-checks/run-83f5.sh | 29b8fae14dd50f07031a35916465e5532c35e25aea2a1ddcf5b16507e29f841f |
| records/interceptors/relocation-checks/run-d9e0.sh | b52e11e6e1d0ea49ce22519e6a1f1077d6afa972aa0e54a2a9b5bba26f90ad09 |
| records/interceptors/relocation-checks/run.sh | 9c8616370206a27243bbf36cbbee4d01acf781c337afb25ba2a427ee534fc6f6 |
| records/interceptors/relocation-checks/samefile.py | c435ec8ed134dbcf5b3522d4297b0399044ffad90a776541cde271b58633bc7a |
| records/interceptors/relocation-checks/sanitize.py | ff55759087c2223ed7e2c3e45f585e798048d8cb76a19605feae59c616bb4c46 |
| records/interceptors/relocation-checks/tables/alreloc.log | ebe2c597d4c4df1fd98769604408f5e9528da66d0a6f770b5691183987954ff9 |
| records/interceptors/relocation-checks/tables/ledger.tsv | b4c4739af98ad127d79978d8ed7dab7370f2e5f615205719f210d785e4c7d12a |
| records/interceptors/relocation-checks/tables/mkaf.tsv | 845c765507491775f5de9199cd61b652f14942870f8f61260a9eab32dc4abbc9 |
| records/interceptors/relocation-checks/tables/named-cells.tsv | 6951ae501ac0416be892fba1451c634381236da14380c2e26c459b8c56a6acf2 |
| records/interceptors/relocation-checks/tables/pac0d24 | 9e1564d2cbee1f91023d65763cafa61fc30f4b63e66aef45cb504a7891504254 |
| records/interceptors/relocation-checks/tables/pac0d24-summary.log | c8cadfaf197a33d7984bfed297d3afd85ff190d4ec19c5548338a40ec81c07ec |
| records/interceptors/relocation-checks/tables/run5.log | aa9afe5251889a715308ec62f7eb9d6e5744f23b862ec56381f39bdf18754b46 |
| records/interceptors/relocation-checks/tables/samefile.tsv | 23d03448619f7e6e0d247c851d40a7b54fb3dfb856de9250f8e2dc26c906873b |
| records/interceptors/relocation-checks/tables/section-bounds.tsv | 1f94d348bcd29cf0eaae2cc3403ff11ccf8b09fd4091e8a9bf23438ce74b0694 |
| records/interceptors/relocation-checks/tables/words.tsv | 2dbea602b9c2650df7c099c2a50aece3c5bb7742302fb87208ac59f8a26dd817 |
| records/interceptors/relocation-checks/verify_aexact.py | 72b92a30095b617bfe92ee0c70612edce13a0b8e644f1ee2efe37ff26dd3ca1c |
| records/interceptors/relocation-checks/ALIASES.txt | c0379f8c2d0eba1f471a30038e6266e4accbb887407eb89abd7792b751d79684 |

## Generated file

lib/A/SegGxaSeam.v is generated by records/interceptors/printf/tools/gen_seg_seam.py from the tree's relocated lib/A/FMgxaSeam.v and
the header records/interceptors/printf/tools/SegGxaSeam.v.pre. In the tree, line 7 of the header cites the generator by its record
path; the recorded .pre file names its earlier in-tree path at that line. That citation is the only difference.
