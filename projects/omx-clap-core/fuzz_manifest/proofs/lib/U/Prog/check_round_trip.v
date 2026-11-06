From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem Ledger ManifestB names_c as_ruled_c snprintf_c strlen_c plain_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import crt_glue.
Import ListNotations.
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Theorem check_round_trip_holds :
  (forall fx', @names_contract fx' rc B API) ->
  (forall fx', @as_ruled_contract fx' rc B API) ->
  (forall fx', @malloc_contract fx' rc B API) ->
  (forall fx', @free_contract fx' rc B API) ->
  snprintf_contract -> strlen_contract -> plain_contract ->
  statics_facts B -> statics_free B MR -> errno_low B -> ManifestB.ctx_owned B MR -> guard_syms B ->
  statics_noerrno B -> malloc_syms_omx B -> YL01.AllocExtra B MR -> block_slack_present B API ->
  check_round_trip_contract B API.
Proof.
  intros NAMES ASR MAL FRE SNP STRL PLN SFA SF ERR CTX GS SNE MSO AX BSP.
  unfold check_round_trip_contract.
  intros L A regs mem md b u us Lam peak cnt fail SEG PRE INIT SPt FRM RA GC CU UH LEN IMG CS LG QT RES CAP BY0 BYU.
  destruct UH as (ua & uk & UB & UL & UR).
  exact (crt_all B API NAMES ASR MAL FRE SFA SF ERR CTX GS SNE MSO AX BSP L A regs mem md b u us Lam peak cnt fail ua uk
    SEG PRE RA CU UB UL UR LEN IMG LG QT CS SNP STRL PLN CAP BY0 BYU RES FRM INIT SPt).
Qed.

End P.
