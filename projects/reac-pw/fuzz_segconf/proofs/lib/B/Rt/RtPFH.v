(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/B/Rt/RtPFH.v (donor image sha256 bbe55d24d096), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* fuzz_manifest's (fm's) runtime layer, program part (proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Base.v), cut
   to what the GXA snprintf route names, at fuzz_command.asan:
   the route's files Require FMH_Base for six names only (measured over the Require closure of FMsnprintfFmI and
   FMgxaSeamInv): PC_snprintf, FM_GOT_canary, FM_canary (here) and bytes_at,
   rom_viewN, rom_viewO (the statement base RtBzHBase.v, re-exported). fm's other entries, windows, format table and
   program statics (FMPstat, ManifestModel) are not used by the route and are left out. The route keeps fm's names;
   the values are this image's, the same numbers RtAPI.v names PC_snprintf, A_SSP_GOT and A_SSP_GUARD. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Export RtBzHBase.
Local Open Scope Z_scope.

(* the snprintf trampoline of fuzz_command.asan (nm: __interceptor_trampoline_snprintf) *)
Definition PC_snprintf : Z := 0x43af0.
(* the stack-protector cells musl's vsnprintf / vfprintf / printf_core / pad read: the GOT word (ld s2 at 0x9aeec)
   and __stack_chk_guard, which it holds *)
Definition FM_GOT_canary : Z := 0xa3e98.
Definition FM_canary : Z := 0x5ff838.
