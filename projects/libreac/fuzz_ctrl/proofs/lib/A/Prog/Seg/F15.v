(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v, with its module paths, module names, addresses and numbers changed; 549 of its 668 lines of code are new or changed and 678 lines of the source are left out. *)
(* Segments F15 (0x82174 -> 0x82178) and F15b (0x82178 -> 0x821d0 / 0x822a0) of the entry function, in the slot
   framework (CUTST / FRA / LK / FLV / F16CARRY), against the push-5 cut set.  No call, no memory change.
   libreac v1.9.0 image (internal path): F15 is the v1.8 code at new addresses; F15b
   reads its three record pointers from the renumbered spills [A+96] / [A+88] / [A+80] (v1.8 [A+80] / [A+72] /
   [A+64]) and adds one load, 0x821cc `ld t0,112(s1)` (t0 := n of the FIRST state, which F16 reads).

   F15 (plan-asan 2 / section 2 row F15, first instruction):
     0x82174  bnez a0,82bf4   -- a0 is the compare result of the 72-byte record against its before-call copy.
                                 The cut 0x82174 carries [A+280] = 0, and [A+280] = b2z (t_sum_ok j) (F13/F14),
                                 so the turn's blocksum is not 0; with 50 <= len that makes fg_fr false, the
                                 fragment class FgNone, and the call left the record as it was: the compare
                                 result is 0, the branch is not taken and the error path is not reached.
   F15b (rows 59-62), from the cut 0x82178:
     0x82178  li   a0,1
     0x8217c  bne  s9,a0,822a0 -- s9 = fg_ret of the class (0 or 1).  s9 <> 1: exit cut 0x822a0.
     s9 = 1 (the class is FgClose, so t_rf j = 1 and FLV's conditional part gives [fr+272] = fragb fr + 19 and
     [fr+304] = f_pll):
     0x82180  ld   a0,272(s1) ; 0x82184 ld a2,0(a0)   -- a2 := [fr+272] = fragb fr + 19 = pl.
     0x82188  ld   a0,96(s1)                          -- a0 := fragb fr + 8.
     0x8218c  bltu a2,a0,82bf4 -- pl = (fragb fr + 8) + 11: not taken.
     0x82190  sub  a0,a2,a0    -- a0 := 11.
     0x82194  li   a1,64 ; 0x82198 bltu a1,a0,82bf4   -- 64 < 11 is false: not taken.
     0x8219c  ld   a1,264(s1) ; 0x821a0 ld a3,0(a1)   -- a3 := [fr+304] = f_pll = fg_T - 13.
     0x821a4  addi a1,a3,2 ; 0x821a8 li a4,64 ; 0x821ac sub a0,a4,a0  -- a0 := 53, a1 := f_pll + 2.
     0x821b0  bltu a0,a1,82bf4 -- the class is FgClose, so 14 <= fg_T <= 64, i.e. 1 <= f_pll <= 51 and
                                 f_pll + 2 <= 53: not taken.
     0x821b4  ld   a0,88(s1)   -- a0 := fragb fr + 19.
     0x821b8  bne  a2,a0,82bf4 -- pl = fragb fr + 19: not taken.
     0x821bc  li   a1,0 ; 0x821c0 addi a4,a3,5 ; 0x821c4 ld a0,80(s1) ; 0x821c8 mv a5,a0
                               -- the loop registers of the byte-sum loop at 0x821d0.
     0x821cc  ld   t0,112(s1)  -- t0 := [A+112] = fs_n of the FIRST state (FSj), the new last conjunct of the
                                 exit cut Inv_A821d0_at.
   The five branch targets 0x82bf4 are the error path; each test above shows it is not taken.  Both segments
   leave memory, the shadow map and the side stack unchanged, so FRA and every carried fact move by register
   equalities alone (the cuts' own registers: 2, 3, 4, 8, 9, 19, 21, 22, 23, 24, 25, 26). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F13 F14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* ---- arithmetic of the five tests and of the compare result. ---- *)

Lemma memcmp_self : forall bs n, (n <= length bs)%nat -> memcmp_model bs bs n = Some 0.
Proof.
  intros bs n. revert bs. induction n as [|n IH]; intros [|b bs] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* [A+280] = 0 is b2z (t_sum_ok j) = 0: either the frame is shorter than 50 bytes or its blocksum is not 0, and
   either way the fragment's first test fg_fr is false, so the class is FgNone and the call left the 72 record
   bytes as they were. *)
Lemma sum_ok_false_fr : forall g j, b2z (t_sum_ok (g_in g) j) = 0 ->
  fg_fr (flen g j) (t_g (g_in g) j) = false.
Proof.
  intros g j H. unfold b2z in H.
  destruct (t_sum_ok (g_in g) j) eqn:E; [discriminate|].
  unfold t_sum_ok, t_big in E. rewrite andb_false_iff in E.
  destruct E as [E|E].
  - unfold fg_fr, flen. rewrite E. reflexivity.
  - unfold fg_fr. rewrite E. apply andb_false_r.
Qed.

Lemma frcl_none : forall g j fr phi, fragb fr <> 0 -> phi <> 0 ->
  fr + 256 <> 0 -> fr + 272 <> 0 -> fr + 304 <> 0 ->
  fg_fr (flen g j) (t_g (g_in g) j) = false -> frcl g j fr phi = FgNone.
Proof.
  intros g j fr phi H1 H2 H3 H4 H5 HFR. unfold frcl.
  rewrite (rf_class_nn (fragb fr) phi (fr + 256) (fr + 272) (fr + 304)) by assumption.
  rewrite HFR. reflexivity.
Qed.

(* The FgClose class bounds the record's total length: fg_keep gives fg_T <= 64 and fg_close gives 14 <= fg_T,
   so f_pll = fg_T - 13 lies in [1, 51]. *)
Lemma close_T : forall f fr pa pp pn len st g, fg_class f fr pa pp pn len st g = FgClose ->
  14 <= fg_T st g <= 64.
Proof.
  intros f fr pa pp pn len st g H. unfold fg_class in H.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [discriminate|].
  destruct (negb (fg_fr len g)); [discriminate|].
  destruct (bat g 19 =? 1); [discriminate|].
  destruct (fg_keep st g) eqn:KEEP; cbn [negb] in H; [|discriminate].
  destruct (fg_close st g) eqn:CLOSE; cbn [negb] in H; [|discriminate].
  split; [|apply keep_T; exact KEEP].
  unfold fg_close in CLOSE. rewrite !andb_true_iff in CLOSE.
  destruct CLOSE as (CL & _). repeat (destruct CL as (CL & _)). apply Z.leb_le in CL. lia.
Qed.

Lemma pll_range : forall g j fr phi, frcl g j fr phi = FgClose ->
  1 <= f_pll (t_FG (g_in g) j) (t_g (g_in g) j) <= 51.
Proof.
  intros g j fr phi H. unfold f_pll.
  pose proof (close_T _ _ _ _ _ _ _ _ H) as HT. lia.
Qed.

(* The FgClose class passed the fragment test fg_fr, whose first conjunct is 50 <= len. *)
Lemma close_len : forall g j fr phi, frcl g j fr phi = FgClose -> 50 <= flen g j.
Proof.
  intros g j fr phi H. unfold frcl, fg_class in H.
  destruct ((fragb fr =? 0) || (phi =? 0) || (fr + 256 =? 0) || (fr + 272 =? 0) || (fr + 304 =? 0));
    [discriminate|].
  destruct (fg_fr (flen g j) (t_g (g_in g) j)) eqn:FR; cbn [negb] in H; [|discriminate].
  unfold fg_fr in FR. rewrite !andb_true_iff in FR.
  destruct FR as (FR & _). repeat (destruct FR as (FR & _)). apply Z.leb_le in FR. exact FR.
Qed.

(* ---- the branch conditions of the five tests. ---- *)

Lemma f15_ltu_false : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> y <= x ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy H. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.

Lemma f15_eqb_true : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x = y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y Hx Hy H. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_eq. lia. Qed.

Lemma f15_eqb_false : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy H. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma f15_sub_val : forall x y v, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v = x - y ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - bv_unsigned (Z_to_bv 64 y)) = Z_to_bv 64 v.
Proof. intros x y v Hx Hy ->. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

(* Replace the branch condition of the goal's `if` by a proved value and reduce. *)
Ltac f15_cond v tac :=
  match goal with
  | |- context [if ?c then _ else _] => replace c with v by (symmetry; tac)
  end; cbv iota.

(* Fold the `sub` of two carried values to the literal v. *)
Ltac f15_sub v :=
  match goal with
  | |- context [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ?x) - bv_unsigned (Z_to_bv 64 ?y))] =>
      rewrite (f15_sub_val x y v) by lia
  end.

(* Close the landing state: the register values differ from the cut's text only by `+ 0` (from `mv rd,rs`) and
   by closed arithmetic, which conversion settles. *)
Ltac f15_state :=
  apply evt_done;
  first [ reflexivity
        | (repeat match goal with
           | |- context [Z_to_bv 64 (?a + 0)] => replace (a + 0) with a by lia
           end); reflexivity ].

(* ---- the single-instruction run of F15: 0x82174 with a0 = 0, landing at 0x82178. ---- *)
Lemma f15_evt_dc :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0v = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82174) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m ->.
  step.
  f15_cond false ltac:(apply Bool.negb_false_iff; apply f15_eqb_true; lia).
  f15_state.
Qed.

(* ---- F15b, the s9 <> 1 arm: two instructions, landing at 0x822a0 with a0 = 1. ---- *)
Lemma f15_evt_c4 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
    s9v = Z_to_bv 64 r -> 0 <= r <= 1 -> r <> 1 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x822a0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m r -> Hr Hr1.
  step. step.
  f15_cond true ltac:(apply Bool.negb_true_iff; apply f15_eqb_false; lia).
  f15_state.
Qed.

(* ---- F15b, the s9 = 1 arm: the four checked tests, the loop set-up and (v1.9) the load of the FIRST length
   n = [A + 112] into t0 at 0x821cc, landing at 0x821d0. ---- *)
Lemma f15_evt_34 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A F Q N L Nf : Z),
    s1v = Z_to_bv 64 A -> s9v = Z_to_bv 64 1 ->
    0 <= F /\ F + 72 < 2 ^ 64 -> 0 <= Q /\ Q + 8 < 2 ^ 64 -> 0 <= N /\ N + 8 < 2 ^ 64 ->
    1 <= L <= 51 ->
    bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 Q)) ->
    bytes_at rsegs m (A + 264) (le8 (Z_to_bv 64 N)) ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 (F + 8))) ->
    bytes_at rsegs m (A + 88) (le8 (Z_to_bv 64 (F + 19))) ->
    bytes_at rsegs m (A + 80) (le8 (Z_to_bv 64 (F + 15))) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 Nf)) ->
    bytes_at rsegs m Q (le8 (Z_to_bv 64 (F + 19))) ->
    bytes_at rsegs m N (le8 (Z_to_bv 64 L)) ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp (Z_to_bv 64 Nf) t1 t2 s0 s1v (Z_to_bv 64 (F + 15)) (Z_to_bv 64 0)
                                (Z_to_bv 64 (F + 19)) (Z_to_bv 64 L) (Z_to_bv 64 (L + 5))
                                (Z_to_bv 64 (F + 15)) a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x821d0) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9v s10 s11 t3 t4 t5 t6
    Fr fc m A F Q N L Nf -> -> HF HQ HN HL H272 H264 H96 H88 H80 H112 HQv HNv.
  pose proof (rd8 m (A + 272) _ H272 (length_le8 _)) as R272.
  pose proof (rd8 m (A + 264) _ H264 (length_le8 _)) as R264.
  pose proof (rd8 m (A + 96) _ H96 (length_le8 _)) as R96.
  pose proof (rd8 m (A + 88) _ H88 (length_le8 _)) as R88.
  pose proof (rd8 m (A + 80) _ H80 (length_le8 _)) as R80.
  pose proof (rd8 m (A + 112) _ H112 (length_le8 _)) as R112.
  pose proof (rd8 m Q _ HQv (length_le8 _)) as RQ.
  pose proof (rd8 m N _ HNv (length_le8 _)) as RN.
  (* 0x82178 li a0,1 ; 0x8217c bne s9,a0 (s9 = 1): not taken *)
  step. step.
  f15_cond false ltac:(apply Bool.negb_false_iff; apply f15_eqb_true; lia).
  (* 0x82180 ld a0,272(s1) ; 0x82184 ld a2,0(a0) ; 0x82188 ld a0,96(s1) *)
  step. step. step.
  (* 0x8218c bltu a2,a0: pl = (F + 8) + 11, not taken *)
  step.
  f15_cond false ltac:(apply f15_ltu_false; lia).
  (* 0x82190 sub a0,a2,a0 = 11 *)
  step. f15_sub 11.
  (* 0x82194 li a1,64 ; 0x82198 bltu a1,a0: 64 < 11 false *)
  step. step.
  f15_cond false ltac:(apply f15_ltu_false; lia).
  (* 0x8219c ld a1,264(s1) ; 0x821a0 ld a3,0(a1) ; 0x821a4 addi a1,a3,2 ; 0x821a8 li a4,64 *)
  step. step. step. step.
  (* 0x821ac sub a0,a4,a0 = 53 (both operands are literals here, so the step normalizes it) *)
  step.
  (* 0x821b0 bltu a0,a1: 53 < L + 2 false (L <= 51) *)
  step.
  f15_cond false ltac:(apply f15_ltu_false; lia).
  (* 0x821b4 ld a0,88(s1) ; 0x821b8 bne a2,a0: pl = F + 19, not taken *)
  step. step.
  f15_cond false ltac:(apply Bool.negb_false_iff; apply f15_eqb_true; lia).
  (* 0x821bc li a1,0 ; 0x821c0 addi a4,a3,5 ; 0x821c4 ld a0,80(s1) ; 0x821c8 mv a5,a0 ; 0x821cc ld t0,112(s1) *)
  step. step. step. step. step.
  f15_state.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The Lib-evt -> SR bridge, as in F13 / F14: the segment's run starts at the CUTST config (registers through
   Regs6ss.mkR_of) and lands in a state satisfying K. *)
Lemma f15_run : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF', Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* A spill cell read at the cut's own spill base A (the base is pinned by register 9). *)
Lemma spill_at : forall regs m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & H9' & Hq) H9 HA0 HA1 Ho0 Ho1.
  assert (EA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    pose proof Hq as Hq'. unfold q64, bytes_at in Hq'. rewrite length_le8 in Hq'.
    destruct Hq' as (Hb1 & Hb2 & _).
    revert Hm Hb1 Hb2 HA0 HA1 Ho0 Ho1. change (2 ^ 64) with 18446744073709551616. intros.
    Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.
(* ---- transport of the carried facts across a register-only step (no memory change). ---- *)

Lemma spill_regs : forall regs regs' m off v,
  spill regs m off v -> getr regs' 9 = getr regs 9 -> spill regs' m off v.
Proof.
  intros regs regs' m off v (A & H9 & Hq) E9. exists A. split; [unfold rg in *; rewrite E9; exact H9 | exact Hq].
Qed.

Lemma lk_regs : forall g fr j regs regs' m,
  LK g fr j regs m -> getr regs' 21 = getr regs 21 -> LK g fr j regs' m.
Proof.
  intros g fr j regs regs' m (Hj & H21 & HO) E21.
  split; [exact Hj|]. split; [unfold rg in *; rewrite E21; exact H21 | exact HO].
Qed.

Lemma flv_regs : forall g fr j regs regs' m,
  FLV g fr j regs m -> getr regs' 9 = getr regs 9 -> FLV g fr j regs' m.
Proof.
  intros g fr j regs regs' m (F64 & F72 & F80 & F272 & F264 & Fc) E9.
  split; [eapply spill_regs; [exact F64 | exact E9]|].
  split; [eapply spill_regs; [exact F72 | exact E9]|].
  split; [eapply spill_regs; [exact F80 | exact E9]|].
  split; [eapply spill_regs; [exact F272 | exact E9]|].
  split; [eapply spill_regs; [exact F264 | exact E9] | exact Fc].
Qed.

Lemma f16carry_regs : forall g j fr phi A regs regs' m,
  F16CARRY g j fr phi A regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 20 = getr regs 20 ->
  getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  F16CARRY g j fr phi A regs' m.
Proof.
  intros g j fr phi A regs regs' m HC E9 E18 E20 E22 E23 E24.
  unfold F16CARRY, F17CARRY in *.
  destruct HC as (Hfok & HFS & Hidb & Haid & H144 & H23 & H22 & H24 & H18 & H20 & H232 & H192 & H136 & H120 &
    H176 & H152 & Hrest).
  split; [exact Hfok|].
  split.
  { exact (fsj_regs g fr j regs regs' m HFS E9). }
  split; [exact Hidb|]. split; [exact Haid|]. split; [exact H144|].
  split; [unfold rg in *; rewrite E23; exact H23|].
  split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E18; exact H18|].
  split; [unfold rg in *; rewrite E20; exact H20|].
  split; [exact H232|]. split; [exact H192|].
  split; [exact H136|]. split; [exact H120|]. split; [exact H176|].
  split; [eapply spill_regs; [exact H152 | exact E9] | exact Hrest].
Qed.

Lemma f14_tail_regs : forall g j fr phi regs regs' m A v w280,
  f14_tail g j fr phi regs m A v w280 ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 10 = getr regs 10 ->
  getr regs' 18 = getr regs 18 -> getr regs' 20 = getr regs 20 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 ->
  f14_tail g j fr phi regs' m A v w280.
Proof.
  intros g j fr phi regs regs' m A v w280 HT E2 E9 E10 E18 E20 E22 E23 E24 E25.
  assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite E2; reflexivity).
  unfold f14_tail in *.
  destruct HT as (H9 & H25 & H10 & HAC & HSW & HAb & Hwb & Hws & Hphifr & Hphisep & Hstk &
    H184 & H208 & H280 & HbL & HaL & HbR & HaR & HB1 & HB2 & HB3 & HB4 & HB5 & Hc256 & HFGM & HCAR).
  split; [unfold rg in *; rewrite E9; exact H9|].
  split; [unfold rg in *; rewrite E25; exact H25|].
  split; [unfold rg in *; rewrite E10; exact H10|].
  split; [exact HAC|]. split; [exact HSW|].
  split; [exact HAb|]. split; [exact Hwb|]. split; [exact Hws|].
  split; [exact Hphifr|].
  split; [rewrite Easp; exact Hphisep|].
  split; [rewrite Easp; exact Hstk|].
  split; [exact H184|]. split; [exact H208|]. split; [exact H280|].
  split; [exact HbL|]. split; [exact HaL|]. split; [exact HbR|]. split; [exact HaR|].
  split; [exact HB1|]. split; [exact HB2|]. split; [exact HB3|]. split; [exact HB4|]. split; [exact HB5|].
  split; [exact Hc256|]. split; [exact HFGM|].
  eapply f16carry_regs; [exact HCAR | exact E9 | exact E18 | exact E20 | exact E22 | exact E23 | exact E24].
Qed.

(* ---- The exit cut at 0x821d0 (the F16 entry, the turn closes a record) is the official Inv_A821d0_at of
   A/Prog/SlotInv.v (aslot push 11B). ---- *)

(* ---- The exit at 0x822a0 (the entry of seg_F17b) is the official Inv_A822a0_at of A/Prog/SlotInv.v (push 6c8):
   F15b's s9 <> 1 branch at 0x8217c reaches it on the short frame (flen < 50, empty frame included: the class is
   FgNone) and on the long frame whatever t_8819 is, so that text carries the a_size heap list, [A+240] by the
   8819 test, the record facts under `50 <= flen g j ->` and the compare operands under `t_8819 = true ->`. ---- *)

(* ---- facts read off FRA at either cut: the frame is app memory above AC.GT, and the spill base A of the cut
   (pinned by register 9) sits above the frame with its 416-byte save area below the entry sp. ---- *)
Lemma f15_frame : forall g fr phi j regs mem md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ AC.GT <= fr /\ 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64 /\
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 ->
     HIGHMEM_BEG <= A /\ fr + FRAME_BYTES <= A /\ A + 416 <= APPMEM_END /\ phi + flen g j <= A /\ phi + 50 <= A).
Proof.
  intros g fr phi j regs mem md HFRA.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hselq & Hfr24q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)).
  assert (Hframe : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
      split; [right; unfold APPMEM_END, HIGHMEM_BEG in *; lia | unfold AC.GT, HIGHMEM_BEG in *; lia].
    - intros a Ha. destruct (Hfs a Ha) as (FSa & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSa HAH Hw HFSr) as LWr1.
      pose proof (lwf_gt _ _ _ _ LWr1) as HG.
      pose proof (lwf_end _ _ _ _ LWr1) as Hend.
      pose proof (lwf_app _ _ _ _ LWr1) as Happ2.
      split; [exact (Happ2 a ltac:(lia)) | lia]. }
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; apply (Hframe a Ha)).
  assert (Hb1 : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA2b : 0 <= A2 < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  split; [exact Happ|].
  split; [apply (Hframe fr ltac:(lia))|].
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  split; [apply Hfrb|]. split; [apply Hfrb|].
  (* the record block of this turn is a live block (of AC.a_size len >= 1 bytes), so it ends below stklo, which
     is a megabyte below the entry sp S and hence below the spill base A (S - 4096 < sp <= A) *)
  assert (Hblk : phi + AC.a_size (flen g j) <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { pose proof (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
                (AC.a_size (flen g j)) HAH
                ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity)) as LWr2.
    pose proof (lwb_end _ _ _ _ _ _ LWr2) as Hend.
    exact Hend. }
  unfold AC.a_size in Hblk.
  intros A HA HAb.
  assert (EA : A2 = A) by (apply (rg_eq64 regs 9 A2 A Hr9) in HA; revert HA HA2b HAb;
                           change (2 ^ 64) with 18446744073709551616; intros;
                           Z.div_mod_to_equations; lia).
  subst A2.
  split; [lia|]. split; [exact Hfa|].
  split; [unfold APPMEM_END in *; lia|]. split; lia.
Qed.

(* ---- seg_F15 : 0x82174 -> 0x82178.  The compare result is 0, so the branch is not taken. ---- *)
Lemma seg_F15 : forall j : nat,
  Hat B APIf ra (Inv_A82178_at B APIf ra) j -> Hat B APIf ra (Inv_A82174_at B APIf ra) j.
Proof.
  intros j He0 g c HInv.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLV &
    vcmp & A & Hmm & HT & HIFS2).
  subst c. rewrite SEGS.
  pose proof HT as HT2. unfold f14_tail in HT2.
  destruct HT2 as (H9 & H25 & H10 & HAC0 & HSW0 & HAb & Hwb & Hws & Hphifr & Hphisep & Hstk &
    H184 & H208 & H280 & HbL & HaL & HbR & HaR & HB1 & HB2 & HB3 & HB4 & HB5 & Hc256 & HFGM & HCAR).
  destruct (f15_frame g fr phi j regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfr1 & HAbnd).
  destruct (HAbnd A H9 HAb) as (HAhi & HfrA & HA416 & Hphilen & Hphi50A).
  assert (Hfnz : fragb fr <> 0) by (unfold fragb, AC.GT in *; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hhalt : m_halted md = None).
  { destruct HFRA as (A2 & sp & s5 & _ & _ & _ & _ & HH & _). exact HH. }
  (* the fragment class is FgNone, so the record is unchanged and the compare result is 0 *)
  assert (Hv0 : vcmp = 0).
  { assert (HFR : fg_fr (flen g j) (t_g (g_in g) j) = false)
      by (apply (sum_ok_false_fr g j); lia).
    assert (HC : frcl g j fr phi = FgNone)
      by (apply (frcl_none g j fr phi); solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia | exact HFR]).
    unfold frrec in Hmm. rewrite HC in Hmm. cbn [fg_next] in Hmm.
    rewrite (memcmp_self (t_FG (g_in g) j) 72 ltac:(rewrite t_FG_length; lia)) in Hmm.
    injection Hmm as Hmm. lia. }
  subst vcmp.
  apply (f15_run regs (Z_to_bv 64 0x82174) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82178 /\ mem' = mem /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 10 = getr regs 10 /\ getr R0 20 = getr regs 20)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of. apply f15_evt_dc. unfold rg in H10; exact H10. }
    { intros ms' E.
      eexists _, (Z_to_bv 64 0x82178), mem. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity. }
  - intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er18 &
      Er22 & Er23 & Er24 & Er25 & Er10 & Er20) Hreg Hmat.
    subst pc' mem'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr10 : getr regs' 10 = getr regs 10) by (rewrite Hreg; exact Er10).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
        [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
      by exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem md md' HENT Hmat).
    assert (HIexit : Inv_A82178_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82178) mem (seg_rom rsegs)) md')).
    { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|].
      split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [exact (flsi_regs g j fr regs regs' mem HFLSI Fr9)|].
      split; [eapply lk_regs; [exact HLK | exact Fr21]|].
      split; [eapply flv_regs; [exact HFLV | exact Fr9]|].
      split; [|exact (ifs2_regs g fr j regs regs' mem HIFS2 Fr9)].
      exists A, 0, 0.
      eapply f14_tail_regs;
        [exact HT | exact Fr2 | exact Fr9 | exact Fr10 | exact Fr18 | exact Fr20 | exact Fr22 | exact Fr23
        | exact Fr24 | exact Fr25]. }
    pose proof (He0 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* ---- seg_F15b : 0x82178 -> {0x821d0, 0x822a0}. ---- *)
Lemma seg_F15b : forall j : nat,
  Hat B APIf ra (Inv_A821d0_at B APIf ra) j -> Hat B APIf ra (Inv_A822a0_at B APIf ra) j ->
  Hat B APIf ra (Inv_A82178_at B APIf ra) j.
Proof.
  intros j H34 Hc4 g c HInv.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLV &
    (A & v & w280 & HT) & HIFS2).
  subst c. rewrite SEGS.
  pose proof HT as HT2. unfold f14_tail in HT2.
  destruct HT2 as (H9 & H25 & H10 & HAC0 & HSW0 & HAb & Hwb & Hws & Hphifr & Hphisep & Hstk &
    H184 & H208 & H280 & HbL & HaL & HbR & HaR & HB1 & HB2 & HB3 & HB4 & HB5 & Hc256 & HFGM & HCAR).
  destruct (f15_frame g fr phi j regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfr1 & HAbnd).
  destruct (HAbnd A H9 HAb) as (HAhi & HfrA & HA416 & Hphilen & Hphi50A).
  assert (Hfnz : fragb fr <> 0) by (unfold fragb, AC.GT in *; lia).
  assert (Hphinz : phi <> 0) by (destruct HHB as (HH & _); exact HH).
  assert (Hhalt : m_halted md = None).
  { destruct HFRA as (A2 & sp & s5 & _ & _ & _ & _ & HH & _). exact HH. }
  assert (Hrr : 0 <= fg_ret (frcl g j fr phi) <= 1).
  { unfold frcl. apply fg_ret_range; solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia]. }
  assert (Htrf : t_rf (g_in g) j = fg_ret (frcl g j fr phi))
    by (apply (trf_of_frcl g j fr phi); solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia]).
  assert (HFGf : frrec g j fr phi = t_FGf (g_in g) j)
    by (apply (frrec_FGf g j fr phi); solve [exact Hfnz | exact Hphinz | unfold AC.GT in *; lia]).
  rewrite HFGf in HbR.
  destruct (Z.eq_dec (fg_ret (frcl g j fr phi)) 1) as [Hc|Hn].
  - (* the turn closes a record: the four tests pass and the run lands at the loop head 0x821d0 *)
    assert (HC : frcl g j fr phi = FgClose) by (apply ret1_close; exact Hc).
    pose proof (pll_range g j fr phi HC) as HL.
    (* the class passed fg_fr, so the frame has at least 50 bytes *)
    pose proof (close_len g j fr phi HC) as Hlen50.
    (* FLV's conditional part: [fr+272] = fragb fr + 19 and [fr+304] = f_pll *)
    destruct HFLV as (F80 & F88 & F96 & F272 & F264 & Fcond).
    destruct (Fcond ltac:(rewrite Htrf; exact Hc)) as (Hpp & Hpn).
    (* v1.9: the FIRST length n = [A+112] (FSb's second spill), which 0x821cc loads into t0 *)
    pose proof HIFS2 as HI2. unfold IFS2, FSj, FSb in HI2. destruct HI2 as (_ & _ & _ & S112 & _).
    (* the six spill cells, at the cut's own A *)
    pose proof (spill_at regs mem 80 _ A F80 H9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                 ltac:(lia) ltac:(lia)) as Q80.
    pose proof (spill_at regs mem 88 _ A F88 H9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                 ltac:(lia) ltac:(lia)) as Q88.
    pose proof (spill_at regs mem 96 _ A F96 H9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                 ltac:(lia) ltac:(lia)) as Q96.
    pose proof (spill_at regs mem 112 _ A S112 H9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                 ltac:(lia) ltac:(lia)) as Q112.
    pose proof (spill_at regs mem 272 _ A F272 H9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                 ltac:(lia) ltac:(lia)) as Q272.
    pose proof (spill_at regs mem 264 _ A F264 H9 ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
                 ltac:(lia) ltac:(lia)) as Q264.
    apply (f15_run regs (Z_to_bv 64 0x82178) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x821d0 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
         getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
         getr R0 10 = Z_to_bv 64 (fragb fr + 15) /\ getr R0 15 = Z_to_bv 64 (fragb fr + 15) /\
         getr R0 11 = Z_to_bv 64 0 /\ getr R0 12 = Z_to_bv 64 (fragb fr + 19) /\
         getr R0 13 = Z_to_bv 64 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) /\
         getr R0 14 = Z_to_bv 64 (f_pll (t_FG (g_in g) j) (t_g (g_in g) j) + 5) /\
         getr R0 5 = Z_to_bv 64 (fs_n (fst_at (g_in g) j)) /\
         getr R0 20 = getr regs 20)
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f15_evt_34 with (A := A) (F := fragb fr) (Q := fr + 272) (N := fr + 304)
          (L := f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) (Nf := fs_n (fst_at (g_in g) j)).
        - unfold rg in H9; exact H9.
        - unfold rg in H25; rewrite Hc in H25; exact H25.
        - unfold fragb in *; lia.
        - lia.
        - lia.
        - exact HL.
        - unfold q64 in Q272; exact Q272.
        - unfold q64 in Q264; exact Q264.
        - unfold q64 in Q96; exact Q96.
        - unfold q64 in Q88; exact Q88.
        - unfold q64 in Q80; exact Q80.
        - unfold q64 in Q112; exact Q112.
        - unfold q64 in Hpp; exact Hpp.
        - unfold q64 in Hpn; exact Hpn. }
      { intros ms' E.
        eexists _, (Z_to_bv 64 0x821d0), mem. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        repeat (split; [reflexivity|]). reflexivity. }
    + intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er18 &
        Er22 & Er23 & Er24 & Er10 & Er15 & Er11 & Er12 & Er13 & Er14 & Er5 & Er20) Hreg Hmat.
      subst pc' mem'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      (* push 14B: 0x821d0's heap list is hb1 phi (AC.a_size (flen g j)), as at 0x82178 *)
      assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md').
      { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
        by exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem md md' HENT Hmat).
      assert (HR9' : rg regs' 9 A) by (unfold rg; rewrite Fr9; unfold rg in H9; exact H9).
      assert (HCAR' : F16CARRY g j fr phi A regs' mem)
        by (eapply f16carry_regs;
            [exact HCAR | exact Fr9 | exact Fr18 | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr24]).
      assert (HIexit : Inv_A821d0_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x821d0) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA'|].
        split; [exact HENT'|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
        split; [exact (flsi_regs g j fr regs regs' mem HFLSI Fr9)|].
        split; [eapply lk_regs; [exact HLK | exact Fr21]|].
        split.
        { unfold FLV. split; [eapply spill_regs; [exact F80 | exact Fr9]|].
          split; [eapply spill_regs; [exact F88 | exact Fr9]|].
          split; [eapply spill_regs; [exact F96 | exact Fr9]|].
          split; [eapply spill_regs; [exact F272 | exact Fr9]|].
          split; [eapply spill_regs; [exact F264 | exact Fr9] | exact Fcond]. }
        split; [rewrite Htrf; exact Hc|].
        split; [unfold rg; rewrite Hreg; exact Er10|].
        split; [unfold rg; rewrite Hreg; exact Er15|].
        split; [unfold rg; rewrite Hreg; exact Er11|].
        split; [unfold rg; rewrite Hreg; exact Er12|].
        split; [unfold rg; rewrite Hreg; exact Er13|].
        split; [unfold rg; rewrite Hreg; exact Er14|].
        split; [exact HbR|].
        split; [exact HaR|].
        pose proof HCAR' as HCAR2. unfold F16CARRY in HCAR2.
        destruct HCAR2 as (Hfok & HFS & Hidb & Haid & H144 & HF17).
        split; [exact Hfok|]. split; [exact HFS|].
        split.
        { rewrite HC in HFGM. cbn [fg_mem] in HFGM. destruct HFGM as (_ & Hpa2 & _ & _).
          unfold u16. exact Hpa2. }
        split; [exact Hidb|]. split; [exact Haid|].
        exists A. split; [exact HR9'|].
        split; [exact H208|].
        split.
        { destruct Hc256 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb.
          apply bytes_at_app in Hb. destruct Hb as (Hb1 & _).
          unfold q64. exact Hb1. }
        split; [exact H144|]. split; [exact HF17|].
        split; [exact (ifs2_regs g fr j regs regs' mem HIFS2 Fr9)|].
        unfold rg; rewrite Hreg; exact Er5. }
      pose proof (H34 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
  - (* the turn does not close a record: the branch at 0x8217c is taken, landing at 0x822a0 *)
    assert (Hr0 : fg_ret (frcl g j fr phi) = 0) by lia.
    apply (f15_run regs (Z_to_bv 64 0x82178) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x822a0 /\ mem' = mem /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\ getr R0 18 = getr regs 18 /\
         getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
         getr R0 25 = getr regs 25 /\ getr R0 10 = Z_to_bv 64 1 /\ getr R0 20 = getr regs 20)
      (Post B APIf ra g)).
    + exact Hhalt.
    + eapply evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f15_evt_c4 with (r := fg_ret (frcl g j fr phi));
          [unfold rg in H25; exact H25 | exact Hrr | exact Hn]. }
      { intros ms' E.
        eexists _, (Z_to_bv 64 0x822a0), mem. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|].
        repeat (split; [reflexivity|]). reflexivity. }
    + intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er18 &
        Er22 & Er23 & Er24 & Er25 & Er10 & Er20) Hreg Hmat.
      subst pc' mem'.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
      assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
      assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
      assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
      assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
      assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
      assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
      assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
      assert (Fr10 : getr regs' 10 = Z_to_bv 64 1) by (rewrite Hreg; exact Er10).
      assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
      assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md').
      { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
          [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
        by exact (Tac_slot.ent_mat APIf g (hb1 phi (AC.a_size (flen g j))) mem md md' HENT Hmat).
      assert (HR9' : rg regs' 9 A) by (unfold rg; rewrite Fr9; unfold rg in H9; exact H9).
      assert (HCAR' : F16CARRY g j fr phi A regs' mem)
        by (eapply f16carry_regs;
            [exact HCAR | exact Fr9 | exact Fr18 | exact Fr20 | exact Fr22 | exact Fr23 | exact Fr24]).
      pose proof HCAR' as HC2. unfold F16CARRY, F17CARRY in HC2.
      destruct HC2 as (_ & _ & _ & _ & _ & C23 & C22 & C24 & C18 & C20 & C232 & C192 & C136 & C120 & C176 & C152 &
        Cw & C50 & C88).
      assert (Hadd50 : 50 <= flen g j -> addressable mem phi 50).
      { intros Hl. destruct HHB as (_ & Hadd). rewrite <- (Z.add_0_r phi).
        eapply addressable_sub; [exact Hadd | lia | lia | unfold AC.a_size; lia]. }
      (* the official F17b entry (SlotInv.Inv_A822a0_at, push 6c8) at turn j *)
      assert (HIexit : Inv_A822a0_at B APIf ra g j
                         (mkCfg (mkst regs' (Z_to_bv 64 0x822a0) mem (seg_rom rsegs)) md')).
      { exists phi, regs', mem, md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA'|].
        split; [exact HENT'|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
        split; [exact (flsi_regs g j fr regs regs' mem HFLSI Fr9)|].
        split; [eapply lk_regs; [exact HLK | exact Fr21]|].
        split; [exact C23|].
        split; [exact C22|].
        split; [intros Hl; destruct (C50 Hl) as (Crb & _ & _ & _); split; [exact (Hadd50 Hl) | exact Crb]|].
        split.
        { exists A. split; [exact HR9'|].
          split; [exact C232|]. split; [exact C192|].
          split; [exact C136|]. split; [exact C120|]. split; [exact C176|].
          split; [intros a Ha; lia|].
          split; [exact Cw|].
          split; [exact C24|].
          split; [|exact C88].
          intros Hl. destruct (C50 Hl) as (_ & _ & _ & CRI). split; [exact CRI|].
          split; [rewrite HaspEq; destruct Hphisep as [Hs|Hs];
                  [left; unfold BCMP_WRAP_K, REAC_CTRL_IDENTITY_FRAGMENT_K in *; lia | right; exact Hs]|].
          left; lia. }
        split; [exact C18|].
        split.
        { intros Hl. destruct (C50 Hl) as (_ & Cg & Cp & _).
          split; [exact Cg|]. split; [exact Cp | exact (t_phi_len g j)]. }
        split; [exact C152|].
        split; [unfold spill; exists A; split; [exact HR9' | rewrite <- Hws; exact H280]|].
        (* push 12: IFS3 at 0x822a0. The turn skips the fragment ingest (t_rf j <> 1), so the identity of turn
           S j is ID1 g j, the bytes IFS2 carries; the fragment record and the spills are IFS2's. *)
        (* push 13A: s4 = 1 - sum_ok is F17CARRY's, carried *)
        split; [|exact C20].
        unfold IFS2 in HIFS2. destruct HIFS2 as (HId1 & HFG1 & HFS1).
        unfold IFS3. split; [|split; [exact HFG1 | exact (fsj_regs g fr j regs regs' mem HFS1 Fr9)]].
        unfold IDj, IDb. rewrite (t_ID_S_skip g j ltac:(rewrite Htrf; exact Hn)). exact HId1. }
      pose proof (Hc4 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
