(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths changed; 166 of its 215 lines of code are new or changed and 3804 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/joined_byte.v; 39 of its 104 lines of code are new or changed and 150 lines of the source are left out. *)
(* lib/B/Prog/joined_byteF_on.v -- route (C): the proofs of the _on forms of image B's joined_byte (entry 0x836ac),
   whose statements are in joined_byte_c_on.v.  joined_byteF.v is FROZEN (a Theorem Labs lane FROZEN-INTERFACES.md:37 (a working note, not in this delivery)), so by
   ASSIGN.md:79 (a working note, not in this delivery) these proofs are in this separate file and joined_byteF.v stays unchanged apart from comment text.  Writer:
   a Theorem Labs lane.  rule 24: no function proved.

   joined_byte_holds_F_on is the script of joined_byte_holds_F (joined_byteF.v:161-243 at 6c3b15fd429) with two
   changes: (1) the shadow_rw premise is not introduced (the old script introduced it as HSW and cleared it unused at
   :181); (2) the tail jb_tail_on is joined_byteF.v's jb_tail plus the post's last conjunct, closed from the munch of
   the frame, wmono and HWs (the frame is apart from the shadow) by jbF_shadow_rw_on_munch.  That lemma is the proof of
   B.ShadowRwOnT.fl_shadow_rw_on, restated here: Requiring B.ShadowRwOnT takes this file's Require closure in the unit
   from 41 to 192 files, among them the B.Bz.Lib twins of Lib.Exec / Lib.Mem / Lib.Step / Lib.MState (DUP families for
   ctrlgate); with B.ShadowRwOn only, the closure reaches no family.  joined_byte_holds_on follows by
   joined_byte_contract_on_of_F_on. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcRecLib RcLeafLib RcAsan RcAsanLib RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT joined_byte_c.
(* StepF's step (evtF goals) shadows Step's (evt goals); joined_byteF's tactics after it, as in joined_byteF.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import joined_byte_c_on joined_byteF.
Import ListNotations.
Open Scope Z_scope.

(* joined_byteF.v:47's hook (Local there, so set again here): the shadow loads' access goals go through acc_hintF. *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

(* shadow_rw_on survives writes apart from the shadow (the proof of B.ShadowRwOnT.fl_shadow_rw_on; see the header). *)
Lemma jbF_shadow_rw_on_munch : forall P W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall x, in_shadow x -> outside W x) -> B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' H Hm Hw HW a Hp Ha. destruct (H a Hp Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  exists b. pose proof (rt_shadow_bound _ Ha) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Ha.
Qed.

(* joined_byteF.v's jb_tail, plus the post's last conjunct (forall P, shadow_rw_on P m -> shadow_rw_on P m'). *)
Local Ltac jb_tail_on X RX SH RDb m m1 MU WM WVS ST FR S HWs :=
  chk_core X RX (Z_to_bv 5 12) SH pre_sr;
  step; clear RDb; step; step; step;
  release_frame FR ST (bv_unsigned S);
  apply evtF_done; cbv beta; do 7 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|];
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WVS)|];
  split; [exact ST|];
  intros P HP; exact (jbF_shadow_rw_on_munch P _ _ _ HP MU WM HWs).

Theorem joined_byte_holds_F_on : joined_byte_contract_F_on.
Proof.
  unfold joined_byte_contract_F_on, JOINED_BYTE, JOINED_BYTE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    i nb b Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE HAN HAB HW RFR RGOT RCELL RN RB RSN RSB.
  subst a2.
  unfold GOT_CELL_K, CELL_K in RGOT, RCELL. unfold shadow_addr in RSN, RSB.
  assert (Ri : 9 <= i <= 10) by lia.
  pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. unfold inr64 in R0, R1.
  pose proof (byte_range nb) as Bn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (HWs : forall x, in_shadow x -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] x)
    by (intros x Hx; apply HW; right; right; exact Hx).
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (jbF_app m _ _ HAN) as AN. pose proof (jbF_app m _ _ HAB) as AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (WVS : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; apply (rc_wv_stk rsegs m lo (bv_unsigned sp)); [exact ST | lia]).
  clear HCE HW.
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  pose proof (jbF_addr_munch _ m m1 _ _ HAN MU HWs) as HAN1.
  pose proof (jbF_addr_munch _ m m1 _ _ HAB MU HWs) as HAB1.
  clear HRT HRT1 HAN HAB.
  (* +0x08 andi, +0x0c bnez: T1 (p mod 4 = 0) *)
  step. rewrite rcl_land3, Hal.
  step. jb_if false.
  (* +0x10 auipc, +0x14 ld (the GOT cell), +0x18 ld (the shadow offset) *)
  step. step. step.
  (* +0x1c addi a3 = p + 4; +0x20 .. +0x2c and 0x83740 .. 0x83744: the check of the load of nb *)
  pose proof (jbF_shadow m1 _ HAN1) as SH1.
  assert (RX1 : 0 <= bv_unsigned a0 + 4 < 2^64) by lia.
  step.
  chk_core (bv_unsigned a0 + 4) RX1 (Z_to_bv 5 16) SH1 pre_sr.
  (* +0x30 lbu a3 = nb; +0x34 bgeu a2,a3 *)
  pose proof (jbF_rd rsegs m1 (bv_unsigned a0 + 4) nb (bv_unsigned a0 + 4) HN eq_refl) as RDn.
  step. clear RDn RN RSN.
  step.
  destruct (Z.ltb_spec i (bv_unsigned nb)) as [E | E].
  - (* body path: i < nb *)
    assert (EJ : jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i = bv_unsigned a0 + 5 + i)
      by (unfold jb_addr; rewrite (proj2 (Z.ltb_lt _ _) E); reflexivity).
    rewrite EJ in HB, HAB1, AB, RB, RSB. clear EJ DB.
    jb_if false.
    (* +0x38 addi a0 = p + 5; +0x3c not a1; +0x40 bltu a1,a2: T2 *)
    step. step.
    step. rewrite (jbF_not (bv_unsigned a0 + 5) i) by lia. cbv iota.
    (* +0x44 add a0 = p + 5 + i; +0x48 j 0x8371c *)
    step. step.
    pose proof (jbF_shadow m1 _ HAB1) as SH2.
    assert (RX2 : 0 <= bv_unsigned a0 + 5 + i < 2^64) by lia.
    pose proof (jbF_rd rsegs m1 (bv_unsigned a0 + 5 + i) b (bv_unsigned a0 + 5 + i) HB eq_refl) as RDb.
    jb_tail_on (bv_unsigned a0 + 5 + i) RX2 SH2 RDb m m1 MU WM WVS ST FR sp HWs.
  - (* last path: nb <= i *)
    pose proof (Hq E) as Hq0.
    assert (EJ : jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i
                 = i - bv_unsigned nb + 9 + bv_unsigned a1)
      by (unfold jb_addr; rewrite (proj2 (Z.ltb_ge _ _) E); lia).
    rewrite EJ in HB, HAB1, AB, RB, RSB. clear EJ DB.
    jb_if true.
    (* +0x4c subw a2 = i - nb; +0x50 addiw a0 = 9 + i - nb *)
    step. rewrite (unsigned_lit i) by lia. rewrite jbF_zxb. rewrite (jbF_swrap (i - bv_unsigned nb)) by lia.
    step. rewrite (unsigned_lit (i - bv_unsigned nb)) by lia. rewrite (jbF_swrap (i - bv_unsigned nb + 9)) by lia.
    (* +0x54 add a0 = t = q + (9 + i - nb); +0x58 bltu t,q: T3 *)
    step.
    step. jb_if false.
    (* +0x5c snez, +0x60 seqz, +0x64 xor, +0x68 beqz: T4 *)
    step. step. step.
    step. rewrite rc_ubchk by (try rewrite unsigned_lit by lia; lia). cbv iota.
    (* +0x6c beqz a1: T5 *)
    step. rewrite (rc_neq0w a1) by lia. cbv iota.
    pose proof (jbF_shadow m1 _ HAB1) as SH2.
    assert (RX2 : 0 <= i - bv_unsigned nb + 9 + bv_unsigned a1 < 2^64) by lia.
    pose proof (jbF_rd rsegs m1 _ b _ HB eq_refl) as RDb.
    jb_tail_on (i - bv_unsigned nb + 9 + bv_unsigned a1) RX2 SH2 RDb m m1 MU WM WVS ST FR sp HWs.
Qed.

(* The _on contract as a corollary of the footprint form (joined_byte_contract_on_of_F_on, RNG_all). *)
Theorem joined_byte_holds_on : joined_byte_contract_on.
Proof. exact (joined_byte_contract_on_of_F_on joined_byte_holds_F_on). Qed.
