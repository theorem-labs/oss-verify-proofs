(* Copy of lib/A/RT_pf_vsn_body.v:11-57 at d49bd1db505 (sha256 94d3a16c2833; internal record), retargeted to RT_pf_stmt_k.v's keep-fx
   statements.
   ___interceptor_vsnprintf at fuzz_reply.asan entered at its BODY 0x464e0
   (PF_ICPT_VSNPRINTF), where ___interceptor_snprintf calls it, jumping past the trampoline __wrap_vsnprintf 0x421d4
   (PF_WRAP_VSNPRINTF).  RT_pf_stmt_k.v vsnprintf_icpt_stmt_k at the body, from the same statement at the trampoline
   (RT_pf_vsn_k.v proves that one; here it is the Section hypothesis VSNT).  No function is walked here:
   - the trampoline is one instruction, `j 464e0`: R4Printf's relocated I_snprintfw.v vsn_tramp_mstep (Qed);
   - one step forward past it: RT_pf_kit.v pf_evt_fwd, which needs the post NOT to hold at the trampoline state.
     The post (RT_pf_stmt_k.v vsnprintf_k_post) fixes the state's pc to `ret_pc ra`, so it holding there would mean
     `ret_pc ra = __wrap_vsnprintf` - exactly what the statement's last premise excludes.
   The proof is RT_pf_vsn_body.v's: the statement has one premise fewer (no frm0) and the post no FP witnesses.
   Everything here is at ONE instance, A_img: no fact crosses to A_img_vsn. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.K Require Import I_snprintfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pf_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt_k.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_kit.
Import ListNotations.
Open Scope Z_scope.

Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module PSK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt_k.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_kit.

Section IcptBody.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.   (* RT_pf_stmt_k.v's `mem -> Z -> Z -> Z -> Prop` *)
Variable vf_ready : VFC.vf_guard.
Hypothesis VSNT : PSK.vsnprintf_icpt_stmt_k set_ready vf_ready PF_WRAP_VSNPRINTF.

Theorem vsnprintf_icpt_ok_body_k : PSK.vsnprintf_icpt_stmt_k set_ready vf_ready PF_ICPT_VSNPRINTF.
Proof.
  unfold PSK.vsnprintf_icpt_stmt_k. intros until o. cbv zeta.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28
    H29 H30 H31 H32 H33 H34 H35 NE.
  (* the same call at the trampoline: the hypothesis, at the same instance A_img, premise for premise *)
  pose proof (VSNT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m D n A VA dn junkd fmt slots args lo canary r o
                H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28
                H29 H30 H31 H32 H33 H34 H35 NE) as T.
  apply PK.cj_bz_evt in T.
  apply GC.bz_cj_evt.
  unfold PF_ICPT_VSNPRINTF. unfold PF_WRAP_VSNPRINTF in T.
  (* `j 464e0`, one step forward; the post cannot hold at the trampoline: its pc would be ret_pc ra *)
  refine (PK.pf_evt_fwd _ _ _ T (vsn_tramp_mstep _ F fc m) _).
  unfold not, PSK.vsnprintf_k_post.
  intros (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ & _).
  apply NE. unfold PF_WRAP_VSNPRINTF. exact (eq_sym (f_equal ms_pc_val EQ)).
Qed.

End IcptBody.
