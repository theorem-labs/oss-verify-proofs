(* GXA's closed ASan printf-core theorems INSTANTIATED on the pinned fuzz_reply.asan.  R4Printf wrote this file and
   it was still compiling when the lane stopped; finished here in the shape a Theorem Labs lane's Gxa prover settled on
   (a working branch efa2842e125, fm's RT_gxa_inst.v fm_vsnprintf_x_proof), with the image facts given as
   EXPLICIT arguments in the declaration order rather than searched for by `first [...]` - the search is what did
   not finish (each candidate is tried against a goal whose type needs the symbol map evaluated).

   The image facts are RT_IImgA_ok.v's, all proved by vm_compute at the instances of RT_IImgA.v, and the pop_arg /
   pop_arg_x call contracts are RT_IImgA_ok.v's closed theorems (so pop_arg, pop_arg_x and __extenddftf2 are NOT
   hypotheses).  What stays a hypothesis is exactly what is not musl's printf core, each with who closes it:
     SPEC_memcpy / SPEC_memset : GXA's interceptor call contracts at the trampolines 0x52724 / 0x52720 (in an ASan
       build musl calls memcpy / memset through the interceptors).  PfCalls brings them.
     SPEC_strnlen : the trampoline 0x42190; closed by RT_gxa_calls.v strnlen_stack_contract_A (R4Printf).
     VF : musl vsnprintf's call into the vfprintf INTERCEPTOR (trampoline 0x421d0), which runs printf_common and
       then REAL(vfprintf) = musl vfprintf 0x92d08.  Closed by RT_pf_vf.v vf_icpt_ok from fr_vfprintf_guarded here.
   The second instance A_img_vsn is where musl vsnprintf is read, because its vfprintf call target is the
   interceptor trampoline and not musl vfprintf's body (RT_IImgA.v:98-107). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr ITree Nodes PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec Require Import Prelim Monad FmtFp StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex G_pad G_fmt_fp_lib G_pop_arg GRoTab.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require ProgAt3.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.ProgAt3.ProgAt2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import Printf_model Printf_zfacts G_pop_arg_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX Require Import G_towrite G_vfprintf_snf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require Import AsanFacts SetCall StrnlenCall CopyCall VfprintfCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require G_printf_core_common.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require Import G_sn_write G_fwritex_w G_fwritex_room G_printf_core.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require Import G_vfprintf_snf G_printf_snfsink G_vfprintf_snf_closed.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require G_vsnprintf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_IImgA RT_IImgA_ok.
Import ListNotations.
Open Scope Z_scope.

Section S.
(* musl vfprintf's body, printf_core, sn_write, __fwritex at A_img (musl vfprintf 0x92d08) *)
Variable copy_ready : mem -> Z -> Z -> Z -> Z -> Prop.
Hypothesis SPEC_memcpy : @memcpy_stack_contract A_img copy_ready.
Variable set_ready : mem -> Z -> Z -> Z -> Prop.
Hypothesis SPEC_memset : @memset_stack_contract A_img set_ready.
Variable strn_ready : mem -> Z -> Z -> Z -> list byte -> Prop.
Hypothesis SPEC_strnlen : @strnlen_stack_contract A_img strn_ready.
Variable INV : mem -> Prop.

Definition fr_vfprintf_guarded :=
  @G_vfprintf_snf_closed.vfprintf_snf_a_guarded_closed A_img
    fr_CODE_vfprintf fr_RB_vfprintf fr_RN_printf_core fr_RN_towrite fr_CODE_towrite
    fr_CODE_sn_write fr_RS_snw fr_RB_snw fr_RN_snw_memcpy fr_CODE_fwritex fr_RB_fwritex
    fr_RN_fwritex_memcpy fr_CODE_printf_core fr_RB_printf_core fr_RO_10884
    fr_RN_B_fwritex fr_RN_B_pop_arg fr_RN_B_fmt_fp fr_RN_B_errno_location fr_RN_B_strerror
    fr_RN_B_strnlen fr_RN_B_wctomb fr_RN_B_pad fr_RN_B_memset fr_RN_B_stack_chk_fail
    fr_RS_K_109cc fr_RS_K_10884 fr_RS_K_1029e fr_RS_K_103b3 fr_RS_K_10964 fr_RS_K_10b9c
    fr_RO_states0 fr_RO_pfx fr_RQ_pfx_lo fr_RQ_pfx_got fr_RO_xdigits fr_RO_states
    fr_RS_got_ssp fr_RS_34288 fr_RS_35000 fr_RL0_0 fr_RL0_1 fr_RL1_0
    copy_ready SPEC_memcpy set_ready SPEC_memset strn_ready SPEC_strnlen
    fr_pop_arg_contract fr_pop_arg_x_contract INV.

End S.

(* GXA's UNGUARDED closed musl vfprintf at A_img, under a Theorem Labs lane's name and parameter order (fm's RT_gxa_inst.v:57
   fm_vfprintf_snf_a_closed, a working branch 3242941dc96), so the relocated seam file
   FMgxaSeamCall.v (seam_vfprintf_a) resolves it by path.  The image facts are fr_vfprintf_guarded's, given
   explicitly in the same order; G_vfprintf_snf_closed.v:108 and :117 close one Section Img and run the same
   tactic. *)
Definition fm_vfprintf_snf_a_closed
  (copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop)
  (set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop)
  (strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop)
  (INV : (word -> option byte) -> Prop)
  (SPEC_memcpy : @memcpy_stack_contract A_img copy_ready)
  (SPEC_memset : @memset_stack_contract A_img set_ready)
  (SPEC_strnlen : @strnlen_stack_contract A_img strn_ready)
  : @vfprintf_snf_a_stmt A_img (snf_out_ready copy_ready) set_ready strn_ready copy_ready INV :=
  @G_vfprintf_snf_closed.vfprintf_snf_a_closed A_img
    fr_CODE_vfprintf fr_RB_vfprintf fr_RN_printf_core fr_RN_towrite fr_CODE_towrite
    fr_CODE_sn_write fr_RS_snw fr_RB_snw fr_RN_snw_memcpy fr_CODE_fwritex fr_RB_fwritex
    fr_RN_fwritex_memcpy fr_CODE_printf_core fr_RB_printf_core fr_RO_10884
    fr_RN_B_fwritex fr_RN_B_pop_arg fr_RN_B_fmt_fp fr_RN_B_errno_location fr_RN_B_strerror
    fr_RN_B_strnlen fr_RN_B_wctomb fr_RN_B_pad fr_RN_B_memset fr_RN_B_stack_chk_fail
    fr_RS_K_109cc fr_RS_K_10884 fr_RS_K_1029e fr_RS_K_103b3 fr_RS_K_10964 fr_RS_K_10b9c
    fr_RO_states0 fr_RO_pfx fr_RQ_pfx_lo fr_RQ_pfx_got fr_RO_xdigits fr_RO_states
    fr_RS_got_ssp fr_RS_34288 fr_RS_35000 fr_RL0_0 fr_RL0_1 fr_RL1_0
    copy_ready SPEC_memcpy set_ready SPEC_memset strn_ready SPEC_strnlen
    fr_pop_arg_contract fr_pop_arg_x_contract INV.

Section V.
(* musl vsnprintf at A_img_vsn: its vfprintf call lands on the interceptor trampoline 0x421d0 *)
Variable set_ready : mem -> Z -> Z -> Z -> Prop.
Variable vf_ready : vf_guard.
Hypothesis SPEC_memset : @memset_stack_contract A_img_vsn set_ready.
Hypothesis VF : @vfprintf_guarded_stmt A_img_vsn vf_ready.

(* the six global facts G_vsnprintf.v:128-133 takes, checked at A_img_vsn itself by vm_compute (IInst.v `inst`),
   so that no fact proved at A_img has to be converted across the two symbol maps *)
Lemma frv_RS_got_ssp : RelSym (@sym A_img_vsn 0x22e18). Proof. inst. Qed.
Lemma frv_RS_snw : RelSym (@sym A_img_vsn K_SN_WRITE). Proof. inst. Qed.
Lemma frv_RS_34288 : RelSym (@sym A_img_vsn 0x34288). Proof. inst. Qed.
Lemma frv_RS_35000 : RelSym (@sym A_img_vsn 0x35000). Proof. inst. Qed.
Lemma frv_RL0_0 : ZFact (@sym A_img_vsn 0x22e18 + 8 <= @sym A_img_vsn 0x34288). Proof. inst. Qed.
Lemma frv_RL0_1 : ZFact (@sym A_img_vsn 0x34288 + 8 <= @sym A_img_vsn 0x35000). Proof. inst. Qed.

Definition fr_vsnprintf_x : @G_vsnprintf.vsnprintf_x_stmt A_img_vsn set_ready vf_ready :=
  @G_vsnprintf.vsnprintf_x_proof A_img_vsn
    fr_CODE_vsnprintf fr_RB_vsnprintf fr_RN_vsn_memset fr_RN_vsn_vfprintf
    frv_RS_got_ssp frv_RS_snw frv_RS_34288 frv_RS_35000 frv_RL0_0 frv_RL0_1 fr_RQ_vsn_22e18
    set_ready vf_ready SPEC_memset VF.

End V.
