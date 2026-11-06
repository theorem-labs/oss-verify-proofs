(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): the GXA walk of musl vfprintf on link's memory
   FILE (lib/CJ/RL/GXA/LinkVfMfA.v vfprintf_mf_a_proof) at link's image record RecAsanVfA.N_img_asan_vf, the record the
   donors' seam runs at (FMgxaSeamCall.v seam_vfprintf_a).

   vfprintf_mf_a_proof is proved over an abstract image record; every image fact it takes (the code of musl vfprintf
   and __towrite, the near-call and symbol facts, printf_core's code and tables, __fwritex's code) is one of
   RT_IImgA_ok.v's lemmas at N_img_asan_vf, carried here by instance resolution as RT_gxa_inst.v carries them for
   vfprintf_snf_a_closed.  Its three callee theorems are:
   - printf_core with a sink (printf_core_a_all): RT_gxa_inst.fm_printf_core_a_all;
   - printf_core's first pass (printf_core1_a_stmt): G_printf_core.printf_core1_a_proof;
   - __fwritex's room arm (fwritex_room_stmt): G_fwritex_room.fwritex_room_ok from the memcpy contract.
   What is left open is what FMgxaSeamCall.v leaves open: the three interceptor call contracts (memcpy, memset,
   strnlen) and their readiness predicates.  No function is walked here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import
SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Import Prelim Monad FmtFp StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require Import
G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg GRoTab.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts G_pop_arg_x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require Import
AsanFacts SetCall StrnlenCall CopyCall VfprintfCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require Import G_fwritex_room G_printf_core G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require Import LinkMfSinkA LinkVfMfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import IInst RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import RT_IImgA_ok RT_gxa_inst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMgxaSeamCall.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance N_img_asan_vf.

(* the image facts, as instances (RT_gxa_inst.v's list) *)
#[local] Existing Instances
  fr_CODE_vfprintf fr_RB_vfprintf fr_RN_printf_core fr_RN_lockfile fr_RN_towrite fr_RN_unlockfile
  fr_RN_stack_chk_fail fr_CODE_towrite fr_RB_towrite
  fr_CODE_sn_write fr_RS_snw fr_RB_snw fr_RN_snw_memcpy
  fr_CODE_fwritex fr_RB_fwritex fr_RN_fwritex_memcpy
  fr_CODE_printf_core fr_RB_printf_core fr_RO_10884
  fr_RN_B_fwritex fr_RN_B_pop_arg fr_RN_B_fmt_fp fr_RN_B_errno_location fr_RN_B_strerror
  fr_RN_B_strnlen fr_RN_B_wctomb fr_RN_B_pad fr_RN_B_memset fr_RN_B_stack_chk_fail
  fr_RS_K_109cc fr_RS_K_10884 fr_RS_K_1029e fr_RS_K_103b3 fr_RS_K_10964 fr_RS_K_10b9c
  fr_RO_states0 fr_RO_pfx fr_RQ_pfx_lo fr_RQ_pfx_got fr_RO_xdigits fr_RO_states
  fr_RS_got_ssp fr_RS_34288 fr_RS_35000 fr_RL0_0 fr_RL0_1 fr_RL1_0
  fr_CODE_pop_arg fr_RB_pop_arg fr_RO_10984 fr_RN_B_extenddftf2 fr_RS_K_10984
  fr_CODE_extenddftf2 fr_RB_extenddftf2
  fr_pop_arg_contract fr_pop_arg_x_contract.

Section C.
(* the three interceptor call contracts, with their readiness predicates (as FMgxaSeamCall.v takes them) *)
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.
Hypothesis SPEC_memcpy : @memcpy_stack_contract N_img_asan_vf copy_ready.
Hypothesis SPEC_memset : @memset_stack_contract N_img_asan_vf set_ready.
Hypothesis SPEC_strnlen : @strnlen_stack_contract N_img_asan_vf strn_ready.

(* __fwritex's room arm at link's image *)
Lemma mf_fwritex_room_ok : @fwritex_room_stmt N_img_asan_vf copy_ready.
Proof. eapply fwritex_room_ok. exact SPEC_memcpy. Qed.

(* printf_core's first pass at link's image *)
Lemma mf_printf_core1_ok : forall INV' : (word -> option byte) -> Prop, @printf_core1_a_stmt N_img_asan_vf INV'.
Proof. exact printf_core1_a_proof. Qed.

(* musl vfprintf on link's memory FILE, in CJ's evt form, at N_img_asan_vf, for any invariant INV the guard carries *)
Theorem link_vfprintf_mf_a_closed : forall INV : (word -> option byte) -> Prop,
  @vfprintf_mf_a_stmt N_img_asan_vf set_ready strn_ready copy_ready INV.
Proof.
  intros INV. pose proof mf_fwritex_room_ok as FROOM.
  exact (vfprintf_mf_a_proof set_ready strn_ready copy_ready INV
           (fm_printf_core_a_all set_ready strn_ready SPEC_memset SPEC_strnlen) mf_printf_core1_ok).
Qed.

(* the seam's instance: the invariant the walk threads is FMgxaSeamCall.SEAM_INV (True) *)
Definition seam_vfprintf_mf_a :
  @vfprintf_mf_a_stmt N_img_asan_vf set_ready strn_ready copy_ready FMgxaSeamCall.SEAM_INV :=
  link_vfprintf_mf_a_closed FMgxaSeamCall.SEAM_INV.

End C.
