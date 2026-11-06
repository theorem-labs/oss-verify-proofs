(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfFm.v (cold/port-fm-rtprintf-param 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfFm.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfFm.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* fm.asan's snprintf over the shared contract (FMsnprintfShared.v sh_asnprintf_realizesU), composed from the four walks:
   __wrap_snprintf / __interceptor_snprintf (FMsnprintfSnp.v snp_ok) -> __interceptor_vsnprintf (FMsnprintfSvsni.v
   svsni_ok) -> musl vsnprintf (FMsnprintfSvsn.v svsn_ok) -> __interceptor_vfprintf (FMsnprintfSvfi.v svfi_ok) ->
   musl vfprintf (the seam, a hypothesis in the GXA-route form sh_avfprintf_icpt_realizesUx), with ASan's
   printf_common and the FILE memset as hypotheses. Generic in the format family FF and in the windows: the seam's Kv,
   printf_common's Kp, and the top's K >= fm_glue_img + Kv; the stack-protector cells are fm's (musl vsnprintf reads
   its GOT slot by a PC-relative load). New file. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfFm.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfFm.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfFm.v keeps its donor's comment text) is kept as lib/A/FMsnprintfFm.v writes it. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require FMsnprintfSnp FMsnprintfSvsni FMsnprintfSvsn FMsnprintfSvfi.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm.asan's glue depth: the top's sp down to musl vfprintf's entry sp ---- *)
(* MEASURED from fm.asan (the frame offsets of FMsnprintfGI.v, RtPrintf's pinned chain): __interceptor_snprintf's frame 0x60,
   __interceptor_vsnprintf's 0x870, musl vsnprintf's 0x130, __interceptor_vfprintf's 0x30 *)
Definition fm_glue_img : Z := 0xa30.
Lemma fm_glue_img_parts : fm_glue_img = 0x60 + 0x870 + 0x130 + 0x30.
Proof. reflexivity. Qed.
(* GXA's released musl vfprintf window: VF_DEPTH = VFA_DEPTH 368 + PC_DEPTH 5184 (fuzz_reply
   lib/CJ/RL/GXA/G_printf_core_common.v:141, G_vfprintf_snf.v:54, origin/ossv/recipes 568db058c1d) *)
Definition GXA_VF_DEPTH : Z := 5552.
(* on the GXA route the top's window is at least 8160 (= 2256 to musl vsnprintf + VSN_DEPTH 5904); 2 * ESTACK fits *)
Lemma fm_K_min_gxa : fm_glue_img + GXA_VF_DEPTH = 8160.
Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem fm_snprintf_shared : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall FF img_lo img_hi cr Kp Kv K,
  ff_stable64 FF -> ff_mono FF -> ESTACK <= Kv -> Kp <= Kv -> fm_glue_img + Kv <= K ->
  sh_apcommon_realizesUz tfibsegs B FF Kp cr A_PCOM ->
  aintrin_realizesU B OSet W_MEMSET ->
  sh_avfprintf_icpt_realizesUx tfibsegs B FF Kv FM_GOT_canary FM_canary img_lo img_hi cr A_SNW A_VFP ->
  sh_asnprintf_realizesU tfibsegs B FF K FM_GOT_canary FM_canary img_lo img_hi cr PC_snprintf.
Proof.
intros B LAWS TB FF img_lo img_hi cr Kp Kv K STAB MONO HE HKp HK APC AMS AVFP.
set (gc := FM_GOT_canary) in *. set (gv := FM_canary) in *.
unfold fm_glue_img in HK.
assert (VFI : sh_avfprintf_icpt_realizesUx tfibsegs B FF (0x30 + Kv) gc gv img_lo img_hi cr A_SNW A_VFPI).
{ apply (FMsnprintfSvfi.svfi_ok B LAWS TB FF gc gv img_lo img_hi cr Kp Kv (0x30 + Kv));
    first [assumption | lia]. }
assert (VSN : sh_avsnprintf_realizesUa tfibsegs B FF (0x160 + Kv) gc gv img_lo img_hi cr A_VSN).
{ apply (FMsnprintfSvsn.svsn_ok B LAWS FF STAB MONO (0x160 + Kv) (0x30 + Kv) gc gv img_lo img_hi cr);
    first [assumption | reflexivity | lia]. }
assert (VSNI : sh_avsnprintf_icpt_realizesUa tfibsegs B FF (0x9d0 + Kv) gc gv img_lo img_hi cr A_VSNI).
{ apply (FMsnprintfSvsni.svsni_ok B LAWS TB FF STAB MONO gc gv img_lo img_hi cr (0x9d0 + Kv) (0x160 + Kv) Kp);
    first [assumption | lia]. }
apply (FMsnprintfSnp.snp_ok B LAWS TB FF gc gv img_lo img_hi cr (0x9d0 + Kv) K);
  first [assumption | lia].
Qed.
End c.
