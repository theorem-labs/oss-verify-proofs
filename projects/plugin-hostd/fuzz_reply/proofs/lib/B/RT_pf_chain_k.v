(* Image B twin of lib/A/RT_pf_chain_k.v at 2c1f180a413 (sha256 f51644ef6751; internal record): module paths lib.A -> lib.B; no image numeral (CHAINKB-numerals.tsv sha256 86a76b0550d0; internal record). *) (* The evt-level snprintf chain at fuzz_reply.asan-ubsan, KEEP-FX: RT_pf_stmt_k.v snprintf_icpt_stmt_k (no frm0 premise;
   the post returns at the caller's F and fc) with every Section hypothesis of its pieces discharged.
   Copy of lib/A/RT_pf_chain.v:9-48 at d49bd1db505 (sha256 959fbd3afd54; internal record), retargeted to GXAK:
     RT_pf_snf_k.v snprintf_icpt_ok_k  <- RT_pf_vsn_body_k.v vsnprintf_icpt_ok_body_k  <- RT_pf_vsn_k.v vsnprintf_icpt_ok_k
       <- RT_gxa_inst_k.v fr_vsnprintf_x_k (the keep-FP twin's musl vsnprintf at A_img_vsn, GXAK/G_vsnprintf.v
          vsnprintf_x_proof; memset at RT_gxa_calls_mem.v)
       <- RT_pf_vf_k.v vf_icpt_ok_k <- RT_gxa_inst_k.v fr_vfprintf_guarded_k (the twin's guarded musl vfprintf at
          A_img, GXAK/G_vfprintf_snf_closed.v vfprintf_snf_a_guarded_closed; memcpy / memset at RT_gxa_calls_mem.v,
          strnlen at RT_gxa_calls.v, pop_arg / pop_arg_x at RT_IImgA_ok_k.v).
   The only variable left is the store invariant INV, which the evt -> SRr bridge chooses.

   THE GUARD is written over the RELEASED names (GXA/G_vfprintf_snf.v vf_ready_a, GXA/G_printf_snfsink.v
   snf_out_ready), the form the SRr bridge states (RT_pf_snp_srr.v VFB_GUARD on a working branch
   95c831b7e5e); the twin's closed body carries the twin's copies, and RT_gxak_eq.v vf_ready_a_eq /
   snf_out_ready_eq rewrite one into the other.  snprintf_chain_closed_k_seam is the theorem at the bridge's
   invariant FMgxaSeamCall.SEAM_INV, in the bridge's text. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxak_eq.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FMgxaSeamCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls_mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_inst_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_snf_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vsn_body_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vsn_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vf_k.
Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module VFCK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXAK.VfprintfCall.
Module GSA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_snfsink.
Module GVA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_IImgA.
Module EQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxak_eq.
Module SC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FMgxaSeamCall.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Module GM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls_mem.
Module GIK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_inst_k.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Module PSK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt_k.
Module PNK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_snf_k.
Module PBK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vsn_body_k.
Module PVK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vsn_k.
Module PFK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_vf_k.

Section Chain.
Variable INV : (word -> option byte) -> Prop.

(* the twin's guarded musl vfprintf body at A_img, under reply's three interceptor contracts *)
Definition fr_VFB_k := GIK.fr_vfprintf_guarded_k GM.copy_ready GM.memcpy_stack_contract_A GM.set_ready
  GM.memset_stack_contract_A GC.strn_ready GC.strnlen_stack_contract_A INV.

(* its guard, over the released names *)
Definition fr_vfb_k : VFC.vf_guard :=
  @GVA.vf_ready_a RTA.A_img (@GSA.snf_out_ready RTA.A_img GM.copy_ready) GM.set_ready GC.strn_ready GM.copy_ready
    INV.

Lemma fr_VFB_k_released : @VFCK.vfprintf_guarded_stmt RTA.A_img fr_vfb_k.
Proof.
  pose proof fr_VFB_k as VFB. rewrite EQ.vf_ready_a_eq, EQ.snf_out_ready_eq in VFB. exact VFB.
Qed.

Theorem snprintf_chain_closed_k : PSK.snprintf_icpt_stmt_k GM.set_ready (PS.vf_ready_icpt fr_vfb_k).
Proof.
  apply (PNK.snprintf_icpt_ok_k GM.set_ready (PS.vf_ready_icpt fr_vfb_k)).
  apply (PBK.vsnprintf_icpt_ok_body_k GM.set_ready (PS.vf_ready_icpt fr_vfb_k)).
  apply (PVK.vsnprintf_icpt_ok_k GM.set_ready (PS.vf_ready_icpt fr_vfb_k)).
  apply (GIK.fr_vsnprintf_x_k GM.set_ready (PS.vf_ready_icpt fr_vfb_k) GM.memset_stack_contract_Avsn).
  exact (PFK.vf_icpt_ok_k fr_vfb_k fr_VFB_k_released).
Qed.
End Chain.

(* at the SRr bridge's invariant, with the guard in the bridge's text (RT_pf_snp_srr.v VFB_GUARD) *)
Corollary snprintf_chain_closed_k_seam :
  PSK.snprintf_icpt_stmt_k GM.set_ready
    (PS.vf_ready_icpt
       (@GVA.vf_ready_a RTA.A_img (@GSA.snf_out_ready RTA.A_img GM.copy_ready) GM.set_ready GC.strn_ready GM.copy_ready
          SC.SEAM_INV)).
Proof. exact (snprintf_chain_closed_k SC.SEAM_INV). Qed.
