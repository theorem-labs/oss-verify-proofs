(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 2169 of its 2293 lines of code are new or changed and 887 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F30.v, with its module paths and module names changed; 801 of its 920 lines of code are new or changed and 2174 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/X12.v, with its module paths and module names changed; 154 of its 271 lines of code are new or changed and 803 lines of the source are left out. *)
(* rule 24: no function proved.
   Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
     image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
       sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
     source runs: lib/B/Prog/Seg/X12.v x12_store_evt (:303), x12_b_evt (:360), x12_a_evt (:393),
       x12_x2_evt (:503) at a working branch 3803efccea0
       (blob 9385278636c06c8f9da345e5de1b118e2e6f17b4);
     tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
           lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
     compare: x12_store_evt_of_F, x12_b_evt_of_F, x12_x2_evt_of_F (evtF_evt + rng_all) re-derive the source
       statements verbatim.  x12_a_evt calls the memchr wrapper and is split at that call and carries no callee
       contract: x12_a_pre_F re-runs X12.v:442-449 (0x82eac ld a0,176(s1); lbu a0,20(a0); beqz not taken;
       ld a0,176(s1); addi a0,a0,3; li a2,17; li a1,0; jal 42ab0), stopping AT the wrapper entry 0x42ab0 with
       ra = the return pc 0x82ecc.  x12_a_evt has no post stretch: the wrapper returns at 0x82ecc, which is the
       run's own Q.  No `_F` steps through a callee, and the MemNorm.evt_normalize of X12.v:457 wraps the
       wrapper call alone, so no stretch here crosses it. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require X12.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* local copies of X12.v's byte-read and store_ok helpers (X12.v:89, :97, :105) *)
Lemma x12f_rd_le8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_ov_read rsegs m a (le8 v) 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH.
Qed.

Lemma x12f_rd_b1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn [length]; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH.
Qed.

Lemma x12f_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m lo hi a (H0 & H1 & H) Ha.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with a by lia. exact (proj1 (H a Ha)). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1 WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* Resolve a branch condition c to b from H : c = b (X12.v:284 x12_br).  StepF's if_true_by / if_false_by
   leave one goal too few here: `replace` closes its side goal by assumption when H is in context. *)
Ltac x12f_br b H :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

(* store_ok of the byte at Sh + off, out of the shadow window ST (X12.v:291, on the evtF goal). *)
Ltac x12f_st ST Sh off :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa (Sh + off)) 1 = true)
        by (apply (x12f_stk_store_ok _ _ _ _ ST); lia)
  end.

(* ------------------------------------------------------------------ the shared shadow-fill block (no call)
   0x82ed0 - 0x82f2c: li a0,-8; twenty sb a0,off(s3) (offsets 352 353 354 360 361 362 363 364 348 349 350 351
   339 340 346 347 328 336 337 338); ld s8,48(s1); ld s9,40(s1).
   Writes the shadow bytes [Sh + 328, Sh + 365); reads [A + 40, A + 56). *)
Lemma x12_store_evt_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A Sh vS vF : Z),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 Sh ->
    stk rsegs m Sh (Sh + 392) ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 vS)) ->
    bytes_at rsegs m (A + 40) (le8 (Z_to_bv 64 vF)) ->
    0 <= Sh -> Sh + 392 <= 2 ^ 64 -> Sh + 392 <= A -> A + 56 <= 2 ^ 64 ->
    rng RNG (Sh + 328) 37 -> rng RNG (A + 40) 16 ->
    evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3v s4 s5 s6 s7 (Z_to_bv 64 vS) (Z_to_bv 64 vF) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 536364) fc None m' (seg_rom rsegs)
         /\ munch [(Sh + 328, Sh + 365)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' Sh (Sh + 392))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536272) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A Sh vS vF -> -> ST H48 H40 HSh0 HSh1 HShA HAb RSH RA.
  pose proof (munch_refl [(Sh + 328, Sh + 365)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  x12f_st ST Sh 352. step. store_done.
  x12f_st ST Sh 353. step. store_done.
  x12f_st ST Sh 354. step. store_done.
  x12f_st ST Sh 360. step. store_done.
  x12f_st ST Sh 361. step. store_done.
  x12f_st ST Sh 362. step. store_done.
  x12f_st ST Sh 363. step. store_done.
  x12f_st ST Sh 364. step. store_done.
  x12f_st ST Sh 348. step. store_done.
  x12f_st ST Sh 349. step. store_done.
  x12f_st ST Sh 350. step. store_done.
  x12f_st ST Sh 351. step. store_done.
  x12f_st ST Sh 339. step. store_done.
  x12f_st ST Sh 340. step. store_done.
  x12f_st ST Sh 346. step. store_done.
  x12f_st ST Sh 347. step. store_done.
  x12f_st ST Sh 328. step. store_done.
  x12f_st ST Sh 336. step. store_done.
  x12f_st ST Sh 337. step. store_done.
  x12f_st ST Sh 338. step. store_done.
  pose proof (x12f_rd_le8 _ _ _ H48) as HR48.
  step.
  clear HR48.
  pose proof (x12f_rd_le8 _ _ _ H40) as HR40.
  step.
  clear HR40.
  apply evtF_done. cbv beta. eexists _.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* The auditor's compare lemma: X12.v:303 x12_store_evt verbatim, from x12_store_evt_F at RNG_all. *)
Lemma x12_store_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A Sh vS vF : Z),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 Sh ->
    stk rsegs m Sh (Sh + 392) ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 vS)) ->
    bytes_at rsegs m (A + 40) (le8 (Z_to_bv 64 vF)) ->
    0 <= Sh -> Sh + 392 <= 2 ^ 64 -> Sh + 392 <= A -> A + 56 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3v s4 s5 s6 s7 (Z_to_bv 64 vS) (Z_to_bv 64 vF) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 536364) fc None m' (seg_rom rsegs)
         /\ munch [(Sh + 328, Sh + 365)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' Sh (Sh + 392))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536272) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A Sh vS vF E1 E3 ST H48 H40 HSh0 HSh1 HShA HAb.
  apply (evtF_evt rsegs RNG_all).
  apply (x12_store_evt_F RNG_all ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7
           s8 s9 s10 s11 t3 t4 t5 t6 sp F fc m A Sh vS vF E1 E3 ST H48 H40 HSh0 HSh1 HShA HAb);
    apply rng_all; lia.
Qed.
Definition x12_store_evt_src_check : ltac:(let T := type of X12.x12_store_evt in exact T) := x12_store_evt_of_F.

(* ------------------------------------------------------------------ X1, taken branch (no call)
   0x82eac - 0x82ed0: ld a0,176(s1); lbu a0,20(a0); beqz a0,0x82ed0 taken (byte 20 of the identity record is 0).
   Reads [A + 176, A + 184) and the byte fr + 2708. *)
Lemma x12_b_evt_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 = 0 ->
    rng RNG (A + 176) 8 -> rng RNG (fr + 2708) 1 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 0) a1
                               a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 536272) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536236) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 -> H176 H20 Hb0 R176 R20.
  assert (HBz : zxb b20 = Z_to_bv 64 0).
  { apply bv_eq. rewrite kb_unsigned_zxb, Hb0. symmetry. apply LMS.unsigned_lit. lia. }
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = true) by (rewrite HBz; unfold bv_eqb; apply Z.eqb_refl).
  pose proof (x12f_rd_le8 _ _ _ H176) as HR176.
  step.
  pose proof (x12f_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12f_br true HB.
  apply evtF_done. cbv beta. rewrite HBz. reflexivity.
Qed.

(* The auditor's compare lemma: X12.v:360 x12_b_evt verbatim, from x12_b_evt_F at RNG_all. *)
Lemma x12_b_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 = 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 0) a1
                               a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 536272) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536236) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 E1 H176 H20 Hb0.
  pose proof H176 as (HA0 & HAL & _). rewrite length_le8 in HAL.
  pose proof H20 as (HF0 & HFL & _). cbn [length] in HFL.
  apply (evtF_evt rsegs RNG_all).
  apply (x12_b_evt_F RNG_all ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7
           s8 s9 s10 s11 t3 t4 t5 t6 sp F fc m A fr b20 E1 H176 H20 Hb0);
    apply rng_all; lia.
Qed.
Definition x12_b_evt_src_check : ltac:(let T := type of X12.x12_b_evt in exact T) := x12_b_evt_of_F.

(* ------------------------------------------------------------------ X2 (no call)
   0x82ecc - 0x82ed0: beqz a0,0x82fa4 (the abort pair) shown not taken, a0 <> 0.  Touches no memory. *)
Lemma x12_x2_evt_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z),
    a0w = Z_to_bv 64 q -> 0 < q < 2 ^ 64 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 536272) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536268) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m q -> Hq.
  assert (HB : bv_eqb (Z_to_bv 64 q) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !LMS.unsigned_lit in E by lia. lia. }
  step.
  x12f_br false HB.
  apply evtF_done. cbv beta. reflexivity.
Qed.

(* The auditor's compare lemma: X12.v:503 x12_x2_evt verbatim, from x12_x2_evt_F at RNG_all (the run touches no
   memory, so it has no rng premise). *)
Lemma x12_x2_evt_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z),
    a0w = Z_to_bv 64 q -> 0 < q < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 536272) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536268) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m q E0 Hq.
  apply (evtF_evt rsegs RNG_all).
  exact (x12_x2_evt_F RNG_all ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7
           s8 s9 s10 s11 t3 t4 t5 t6 sp F fc m q E0 Hq).
Qed.
Definition x12_x2_evt_src_check : ltac:(let T := type of X12.x12_x2_evt in exact T) := x12_x2_evt_of_F.

(* ------------------------------------------------------------------ X1, memchr-wrapper arm, split at the call
   0x82eac - 0x82ec8: ld a0,176(s1); lbu a0,20(a0); beqz NOT taken (byte 20 is non-zero); ld a0,176(s1);
   addi a0,a0,3; li a2,17; li a1,0; jal 42ab0 <memchr_wrap>.  Stops AT the wrapper entry with ra = 0x82ecc.
   Reads [A + 176, A + 184) (twice) and the byte fr + 2708. *)
Lemma x12_a_pre_F :
  forall (RNG : footprint)
         (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    rng RNG (A + 176) 8 -> rng RNG (fr + 2708) 1 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 536268) sp gp tp t0 t1 t2 s0 s1v
                               (Z_to_bv 64 (fr + 2691)) (Z_to_bv 64 0) (Z_to_bv 64 17) a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 273072) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536236) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 -> H176 Hfr0 HfrA H20 Hb20 R176 R20.
  pose proof FRAME_BYTES_val as HFBv.
  unfold APPMEM_END in HfrA.
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite kb_unsigned_zxb in E. rewrite LMS.unsigned_lit in E by lia. exact (Hb20 E). }
  pose proof (x12f_rd_le8 _ _ _ H176) as HR176.
  step.
  pose proof (x12f_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12f_br false HB.
  step. step. step. step. step.
  apply evtF_done. cbv beta.
  replace (Z_to_bv 64 (fr + 2688 + 3)) with (Z_to_bv 64 (fr + 2691)) by (f_equal; lia).
  reflexivity.
Qed.
