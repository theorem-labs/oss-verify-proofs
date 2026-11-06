(* Image B twin of lib/A/RT_pf_vsn_body.v at d49bd1db505: module paths lib.A -> lib.B; 4 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* ___interceptor_vsnprintf at fuzz_reply.asan-ubsan entered at its BODY 0x46538 (PF_ICPT_VSNPRINTF), where
   ___interceptor_snprintf calls it, jumping past the trampoline __wrap_vsnprintf 0x4222c (PF_WRAP_VSNPRINTF).
   RT_pf_stmt.v vsnprintf_icpt_stmt at the body, from the same statement at the trampoline (RT_pf_vsn.v proves that
   one; here it is the Section hypothesis VSNT).  No function is walked here:
   - the trampoline is one instruction, `j 46538`: R4Printf's relocated I_snprintfw.v vsn_tramp_mstep (Qed);
   - one step forward past it: RT_pf_kit.v pf_evt_fwd, which needs the post NOT to hold at the trampoline state.
     The post (GXA's vsnprintf_x_post) fixes the state's pc to `ret_pc ra`, so it holding there would mean
     `ret_pc ra = __wrap_vsnprintf` - exactly what the statement's last premise excludes.
   The goal is CJ's evt and the step lemma is Bz's; the two cross with RT_gxa_calls.v bz_cj_evt and RT_pf_kit.v
   cj_bz_evt.  Everything here is at ONE instance, A_img: no fact crosses to A_img_vsn. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.K Require Import I_snprintfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_kit.
Import ListNotations.
Open Scope Z_scope.

Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module GVS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_gxa_calls.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_stmt.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_pf_kit.

Section IcptBody.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.   (* RT_pf_stmt.v's `mem -> Z -> Z -> Z -> Prop` *)
Variable vf_ready : VFC.vf_guard.
Hypothesis VSNT : PS.vsnprintf_icpt_stmt set_ready vf_ready PF_WRAP_VSNPRINTF.

Theorem vsnprintf_icpt_ok_body : PS.vsnprintf_icpt_stmt set_ready vf_ready PF_ICPT_VSNPRINTF.
Proof.
  unfold PS.vsnprintf_icpt_stmt. intros until o. cbv zeta.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28
    H29 H30 H31 H32 H33 H34 H35 H36 NE.
  (* the same call at the trampoline: the hypothesis, at the same instance A_img, premise for premise *)
  pose proof (VSNT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m D n A VA dn junkd fmt slots args lo canary r o
                H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28
                H29 H30 H31 H32 H33 H34 H35 H36 NE) as T.
  apply PK.cj_bz_evt in T.
  apply GC.bz_cj_evt.
  unfold PF_ICPT_VSNPRINTF. unfold PF_WRAP_VSNPRINTF in T.
  (* `j 46538`, one step forward; the post cannot hold at the trampoline: its pc would be ret_pc ra *)
  refine (PK.pf_evt_fwd _ _ _ T (vsn_tramp_mstep _ F fc m) _).
  unfold not, GVS.vsnprintf_x_post.
  intros (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' & EQ & _).
  apply NE. unfold PF_WRAP_VSNPRINTF. exact (eq_sym (f_equal ms_pc_val EQ)).
Qed.

End IcptBody.
