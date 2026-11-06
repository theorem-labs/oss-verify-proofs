(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MState Mem Frame Exec FP RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Ghost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import B1G_mc B1G_defs B1G_vcs B1G_cert B1G_ok B1G_mcb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Lemma B1G_vc_okH : forall d c, SG.gvc_list B1G_GV c = true -> SG.vc_holds SG (s1_gp d) c.
Proof. intros d c H. exact (SG.gvc_list_ok SG (s1_gp d) B1G_GV c (B1G_GV_ok d) H). Qed.

Definition B1G_hints : list (list ST.xhint) :=
  [[ST.XH [(16%nat, EMd M_MUL (ELit 16) (EVar 1)); (17%nat, EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 1)) (ELit (0x7fff8000 - 1024)))] [] []]].

Lemma b1g_certH : SP.pcheckH SG s1_gfp (SG.gvc_list B1G_GV) B1G B1G_IT 4000 true B1G_hints = true.
Proof. exact (SP.pcheck_pcheckH SG s1_gfp (SG.gvc_list B1G_GV) B1G B1G_IT 4000 true B1G_hints b1g_cert). Qed.

(* [comment removed for export] *)
Definition B1G_cnd {rc : runConstT} (AI : AMallocIface) (LB : list ablock) (E : env) : Prop :=
  SP.wins_client (B1B.hmC AI LB) E (SP.p_W B1G).

Lemma B1G_cnd_g {rc : runConstT} : forall AI LB E E2, SP.gagree (SP.p_G B1G) E E2 -> eb E = eb E2 -> B1G_cnd AI LB E -> B1G_cnd AI LB E2.
Proof.
  intros AI LB E E2 Hg Hb H. unfold B1G_cnd, SP.wins_client in *. apply Forall_forall. intros w Hw.
  assert (Hc : SP.win_closed (SP.p_G B1G) w = true) by (revert w Hw; apply forallb_forall; vm_compute; reflexivity).
  rewrite <- (SP.win_den_gagree (SP.p_G B1G) E E2 w Hg Hb Hc). exact (proj1 (Forall_forall _ _) H w Hw).
Qed.

Section S.
Context {rc : runConstT}.
Variable AI : AMallocIface.
Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
Hypothesis MEMCPY : asan_memcpy_stmt.
Variable d : list Z.

Notation hmH := (B1B.hmH AI L RNGh st LB).
Notation hmA := (B1B.hmA AI LB).
Notation hmC := (B1B.hmC AI LB).

Theorem b1g_soundH : forall T E M rom ms, In T (SP.p_tm B1G ++ SP.p_xt B1G) -> rom = seg_rom bsegs -> SX.aw_genuine E (SP.p_A B1G) ->
  B1G_cnd AI LB E -> hmH M -> ST.tm_okF SG T E M rom ms -> SG.gholds (s1_gp d) E M (ST.t_ghost T) ->
  exists ms', ExecF.mstepsF SG (SX.fp_of (SP.p_A B1G) E) ms ms' /\ SP.prun_postH SG (s1_gp d) hmH hmA B1G E M rom ms'.
Proof.
  intros T E M rom ms HinT HRom HAG HCnd HHM HT HG.
  exact (SP.pcheck_soundH SG (s1_gp d) s1_gfp (SG.gvc_list B1G_GV) (s1_gp_frame d) (B1G_vc_okH d) hmH hmA hmC B1B.hmR
           (B1B.HMC_sub AI LB) (B1B.HMF AI L RNGh st LB) B1G B1G_IT 4000 true B1G_hints (B1G_cnd AI LB) b1g_certH
           (SP.itab_ranges_sound SG _) ltac:(intros TA [])
           ltac:(intros Sm [<-|[]]; exact (B1B.mcb_ok AI L RNGh st LB MEMCPY d))
           (B1G_cnd_g AI LB) ltac:(intros E0 H0; exact H0) ltac:(intros E0 _ w Hw; destruct Hw) ltac:(intros; constructor)
           T E M rom ms HinT HRom HAG HCnd HHM HT HG).
Qed.

(* [comment removed for export] *)
Theorem b1g_summ_okH : SP.summ_okH SG (s1_gp d) hmH hmA hmC B1B.hmR
  (SP.SUMX (SP.p_G B1G) T0 (SP.p_ex B1G) (SP.p_W B1G) (SP.p_A B1G) (SP.p_PS B1G) false).
Proof.
  exact (SP.summ_of_pcheckH SG (s1_gp d) s1_gfp (SG.gvc_list B1G_GV) (s1_gp_frame d) (B1G_vc_okH d) hmH hmA hmC B1B.hmR
           (B1B.HMC_sub AI LB) (B1B.HMF AI L RNGh st LB) B1G B1G_IT 4000 true B1G_hints T0 b1g_certH
           (SP.itab_ranges_sound SG _) eq_refl eq_refl ltac:(intros TA [])
           ltac:(intros Sm [<-|[]]; exact (B1B.mcb_ok AI L RNGh st LB MEMCPY d)) ltac:(left; reflexivity)).
Qed.

(* [comment removed for export] *)
Theorem b1g_evtH : forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  rom = seg_rom bsegs -> SX.aw_genuine E (SP.p_A B1G) -> B1G_cnd AI LB E -> hmH m ->
  rfull R -> regs_ok E (ST.t_regs T0) R -> know_ok SG E m (ST.t_know T0) -> SG.gholds (s1_gp d) E m (ST.t_ghost T0) ->
  mem_inv SG m -> frm0 fc ->
  ExecF.evtF SG (SX.fp_of (SP.p_A B1G) E) (SLib.xpostH SG (s1_gp d) hmH hmA B1G E m rom) (MS R F (Z_to_bv 64 (ST.t_pc T0)) fc None m rom).
Proof.
  intros E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
  exact (SLib.prog_evtH SG (s1_gp d) s1_gfp (SG.gvc_list B1G_GV) (s1_gp_frame d) (B1G_vc_okH d) hmH hmA hmC B1B.hmR
           (B1B.HMC_sub AI LB) (B1B.HMF AI L RNGh st LB) B1G B1G_IT 4000 true B1G_hints T0 (B1G_cnd AI LB) b1g_certH
           (SP.itab_ranges_sound SG _) ltac:(intros TA [])
           ltac:(intros Sm [<-|[]]; exact (B1B.mcb_ok AI L RNGh st LB MEMCPY d))
           (B1G_cnd_g AI LB) ltac:(intros E0 H0; exact H0) ltac:(intros E0 _ w Hw; destruct Hw) ltac:(intros; constructor)
           ltac:(left; reflexivity) E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ).
Qed.
End S.
Print Assumptions b1g_soundH.
Print Assumptions b1g_summ_okH.
Print Assumptions b1g_evtH.
