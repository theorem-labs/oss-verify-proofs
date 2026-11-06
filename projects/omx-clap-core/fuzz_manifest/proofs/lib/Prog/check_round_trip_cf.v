From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import
ManifestModel ManifestMem Ledger ManifestB names_c as_ruled_c snprintf_c strlen_c plain_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import names_c_cf as_ruled_c_cf check_round_trip_c_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_glue_cf.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free (agreement) twin of check_round_trip_holds (check_round_trip.v): the cut-free contracts of names,
   as_ruled, malloc and free, the agreement limit law, and the premises of the original. *)
Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Theorem check_round_trip_cf_holds :
  (forall fx', @names_contract_cf fx' rc B API) ->
  (forall fx', @as_ruled_contract_cf fx' rc B API) ->
  (forall fx', @malloc_contract_cf fx' rc B API) ->
  (forall fx', @free_contract_cf fx' rc B API) ->
  (forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md)) ->
  snprintf_contract -> strlen_contract -> plain_contract ->
  statics_facts B -> statics_free B MR -> errno_low B -> ManifestB.ctx_owned B MR -> guard_syms B ->
  statics_noerrno B -> malloc_syms_omx B -> YL01.AllocExtra B MR -> block_slack_present B API ->
  check_round_trip_contract_cf B API.
Proof.
  intros NCF ACF MCF FCF LIMLAW SNP STRL PLN SFA SF ERR CTX GS SNE MSO AX BSP.
  unfold check_round_trip_contract_cf.
  intros L A regs mem md b u us Lam peak cnt fail SEG PRE INIT SPt FRM RA GC CU UH LEN IMG CS LG QT RES CAP BY0 BYU.
  destruct UH as (ua & uk & UB & UL & UR).
  exact (crt_all_cf B API NCF ACF MCF FCF LIMLAW SFA SF ERR CTX GS SNE MSO AX BSP L A regs mem md b u us Lam peak cnt
    fail ua uk SEG PRE RA CU UB UL UR LEN IMG LG QT CS SNP STRL PLN CAP BY0 BYU RES FRM INIT SPt).
Qed.

End P.
