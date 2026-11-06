(* fuzz_manifest's (fm's) runtime layer, program part (proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Base.v), cut
   to what the GXA snprintf route names, at fuzz_command.asan:
   the route's files Require FMH_Base for six names only (measured over the Require closure of FMsnprintfFmI and
   FMgxaSeamInv): PC_snprintf, FM_GOT_canary, FM_canary (here) and bytes_at,
   rom_viewN, rom_viewO (the statement base RtBzHBase.v, re-exported). fm's other entries, windows, format table and
   program statics (FMPstat, ManifestModel) are not used by the route and are left out. The route keeps fm's names;
   the values are this image's, the same numbers RtAPI.v names PC_snprintf, A_SSP_GOT and A_SSP_GUARD. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Export RtBzHBase.
Local Open Scope Z_scope.

(* the snprintf trampoline of fuzz_command.asan (nm: __interceptor_trampoline_snprintf) *)
Definition PC_snprintf : Z := 0x43a64.
(* the stack-protector cells musl's vsnprintf / vfprintf / printf_core / pad read: the GOT word (ld s2 at 0x9b390)
   and __stack_chk_guard, which it holds *)
Definition FM_GOT_canary : Z := 0xa36d8.
Definition FM_canary : Z := 0x5ff078.
