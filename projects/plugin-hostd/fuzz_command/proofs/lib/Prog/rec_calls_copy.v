(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 779 of its 856 lines of code are new or changed and 471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/rec_clear.v, with its module paths, addresses and numbers changed; 1564 of its 1647 lines of code are new or changed and 773 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_free.
Import ListNotations.
Open Scope Z_scope.

Lemma addr56c : forall c (i : nat), (i <= 16)%nat ->
  Z_to_bv 64 (c + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3))))
  = Z_to_bv 64 (c + 56 * Z.of_nat i).
Proof.
  intros c i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Section KA.
Variables (sw dw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32).
Variable n : nat.
Hypothesis HN : (n <= 16)%nat.
Hypothesis HSW : 2 ^ 20 <= bv_unsigned sw - 80.
Hypothesis HDW : bv_unsigned sw <= bv_unsigned dw.
Hypothesis HDN : bv_unsigned dw + 56 * Z.of_nat n <= 2 ^ 64.

Definition FRC : list cell :=
  [C8 s8_0; C8 s7_0; C8 s6_0; C8 s5_0; C8 s4_0; C8 s3_0; C8 s2_0; C8 s1_0; C8 s0_0; C8 ra0].

Definition st_head (Q : machine_state -> Prop) (i : nat) (m : word -> option byte) : Prop :=
  forall y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y28 y29 y30 y31,
    Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp y5 y6 y7 dw (Z_to_bv 64 0x33d10) y10
               (Z_to_bv 64 (Z.of_nat n)) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.of_nat i))
               (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
               y21 y22 y23 y24 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x156e4) fc None m (seg_rom rsegs)).

Definition st_call (Q : machine_state -> Prop) (i j : nat) (pw : word) (m : word -> option byte) : Prop :=
  forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    Q (MS (mkR (Z_to_bv 64 0x15720) (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp y5 y6 y7 dw (Z_to_bv 64 0x33d10) pw
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (Z.of_nat i))
               (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
               (Z_to_bv 64 (bv_unsigned dw + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j))
               (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j))
               (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j)) s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs)).

Definition st_ret (Q : machine_state -> Prop) (m : word -> option byte) : Prop :=
  forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    Q (MS (mkR ra0 sw gp tp y5 y6 y7 s0_0 s1_0 (Z_to_bv 64 (Z.of_nat n)) y11 y12 y13 y14 y15 y16 y17
               s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9 s10 s11 y28 y29 y30 y31)
          F (ret_pc ra0) fc None m (seg_rom rsegs)).

Lemma k_epi : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17
    x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 m,
  rw_cells rsegs m (bv_unsigned sw + -80) FRC -> st_ret Q m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (Z.of_nat n))
                       x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1574c) fc None m (seg_rom rsegs)).
Proof using HN HSW.
  intros Q x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 m FR HK.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp. unfold FRC in FR.
  do 13 step.
  replace (Z_to_bv 64 (bv_unsigned sw + -80 + 80)) with sw by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  apply evt_done.
  exact (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_tail_next : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24
    x28 x29 x30 x31 m (i : nat),
  (S i < n)%nat -> st_head Q (S i) m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 dw (Z_to_bv 64 0x33d10) x10
                       (Z_to_bv 64 (Z.of_nat n)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat i))
                       (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
                       x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1573c) fc None m (seg_rom rsegs)).
Proof using HN HSW HDW HDN.
  intros Q x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 m i Hi HK.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  do 4 step.
  rewrite rec_calls_free.lts_small by lia.
  replace (Z.of_nat i + 1 <? Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  apply evt_done.
  replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
  replace (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 56)) with (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat (S i)))
    by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i + 56))
    with (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat (S i))) by (f_equal; lia).
  exact (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_tail_last : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24
    x28 x29 x30 x31 m (i : nat),
  (S i = n)%nat -> rw_cells rsegs m (bv_unsigned sw + -80) FRC -> st_ret Q m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 dw (Z_to_bv 64 0x33d10) x10
                       (Z_to_bv 64 (Z.of_nat n)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat i))
                       (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
                       x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1573c) fc None m (seg_rom rsegs)).
Proof using HN HSW HDW HDN.
  intros Q x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 m i Hi FR HK.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  do 4 step.
  rewrite rec_calls_free.lts_small by lia.
  replace (Z.of_nat i + 1 <? Z.of_nat n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  eapply k_epi; [exact FR | exact HK].
Qed.

Lemma k_zero : forall (Q : machine_state -> Prop) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk,
  n = 0%nat ->
  rw_cells rsegs m (bv_unsigned sw + -80) [CB 80 junk] ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -80) FRC ->
     munch [(bv_unsigned sw + -80, bv_unsigned sw)] m m' -> wmono rsegs m m' -> st_ret Q m') ->
  evt rsegs Q (MS (mkR ra0 sw gp tp t0 t1 t2 s0_0 s1_0 dw a1 a2 a3 a4 a5 a6 a7
                       s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15698) fc None m (seg_rom rsegs)).
Proof using HN HSW.
  intros Q t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk Hn FR NC HK.
  pose proof (munch_refl [(bv_unsigned sw + -80, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step.
  rewrite rec_calls_free.sx32_small by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with false by (rewrite Hn; reflexivity). cbn [andb negb].
  eapply k_epi; [exact FR | exact (HK _ FR MU WM)].
Qed.

Lemma k_pro : forall (Q : machine_state -> Prop) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk,
  (0 < n)%nat ->
  rw_cells rsegs m (bv_unsigned sw + -80) [CB 80 junk] ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -80) FRC ->
     munch [(bv_unsigned sw + -80, bv_unsigned sw)] m m' -> wmono rsegs m m' -> st_head Q 0 m') ->
  evt rsegs Q (MS (mkR ra0 sw gp tp t0 t1 t2 s0_0 s1_0 dw a1 a2 a3 a4 a5 a6 a7
                       s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15698) fc None m (seg_rom rsegs)).
Proof using HN HSW HDW HDN.
  intros Q t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk Hn FR NC HK.
  pose proof (munch_refl [(bv_unsigned sw + -80, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  apply (rw_cells_split_CB rsegs _ _ [] 80%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step.
  rewrite rec_calls_free.sx32_small by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.of_nat n <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb].
  do 4 step.
  apply evt_done.
  replace (Z_to_bv 64 (bv_unsigned dw + 8)) with (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat 0)) by (f_equal; lia).
  exact (HK _ FR MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_head_call : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24
    x28 x29 x30 x31 m (i : nat) (fn len : Z) (pw : word) j1 j2,
  (i < n)%nat -> 0 <= fn < 2 ^ 31 -> 0 < len <= 6 ->
  rw_cells rsegs m (0x33d10 + 56 * Z.of_nat i + 72) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
  rw_cells rsegs m (0x33d60 + 56 * Z.of_nat i) [C8 pw] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [CB 4 j1; CB 4 j2] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
     munch [(bv_unsigned dw + 56 * Z.of_nat i, bv_unsigned dw + 56 * Z.of_nat i + 8)] m m' -> wmono rsegs m m' ->
     st_call Q i 0 pw m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 dw (Z_to_bv 64 0x33d10) x10
                       (Z_to_bv 64 (Z.of_nat n)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat i))
                       (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
                       x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x156e4) fc None m (seg_rom rsegs)).
Proof using HN HSW HDW HDN.
  intros Q x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 m i fn len pw j1 j2
    Hi Hfn Hl RF RA SL HK.
  assert (E7 : 0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat 0 = 0x33d60 + 56 * Z.of_nat i) by lia.
  assert (E8 : bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat 0 = bv_unsigned dw + 8 + 56 * Z.of_nat i) by lia.
  unfold st_call in HK. rewrite E7, E8 in HK. clear E7 E8.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  remember (0x33d60 + 56 * Z.of_nat i) as Y eqn:HY.
  pose proof (munch_refl [(X, X + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite addr56c by lia.
  do 2 step.
  rewrite !rec_calls_free.sx32_small by lia.
  step.
  rewrite addr56c by lia. rewrite <- HX.
  do 3 step.
  rewrite bv_lts_zero_l, (unsigned_lit len) by lia.
  replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (len <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb].
  do 5 step.
  apply evt_done.
  subst X Y.
  exact (HK _ SL MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_head_skip_next : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24
    x28 x29 x30 x31 m (i : nat) (fn : Z) j1 j2,
  (S i < n)%nat -> 0 <= fn < 2 ^ 31 ->
  rw_cells rsegs m (0x33d10 + 56 * Z.of_nat i + 72) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [CB 4 j1; CB 4 j2] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
     munch [(bv_unsigned dw + 56 * Z.of_nat i, bv_unsigned dw + 56 * Z.of_nat i + 8)] m m' -> wmono rsegs m m' ->
     st_head Q (S i) m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 dw (Z_to_bv 64 0x33d10) x10
                       (Z_to_bv 64 (Z.of_nat n)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat i))
                       (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
                       x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x156e4) fc None m (seg_rom rsegs)).
Proof using HN HSW HDW HDN.
  intros Q x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 m i fn j1 j2
    Hi Hfn RF SL HK.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  pose proof (munch_refl [(X, X + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite addr56c by lia.
  do 2 step.
  rewrite !rec_calls_free.sx32_small by lia.
  step.
  rewrite addr56c by lia. rewrite <- HX.
  do 3 step.
  rewrite bv_lts_zero_l, (unsigned_lit 0) by lia.
  replace (0 <? 0) with false by reflexivity. cbn [andb negb].
  eapply k_tail_next; [exact Hi|].
  subst X. exact (HK _ SL MU WM).
Qed.

Lemma k_head_skip_last : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24
    x28 x29 x30 x31 m (i : nat) (fn : Z) j1 j2,
  (S i = n)%nat -> 0 <= fn < 2 ^ 31 ->
  rw_cells rsegs m (bv_unsigned sw + -80) FRC ->
  rw_cells rsegs m (0x33d10 + 56 * Z.of_nat i + 72) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [CB 4 j1; CB 4 j2] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
     munch [(bv_unsigned dw + 56 * Z.of_nat i, bv_unsigned dw + 56 * Z.of_nat i + 8)] m m' -> wmono rsegs m m' ->
     st_ret Q m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 dw (Z_to_bv 64 0x33d10) x10
                       (Z_to_bv 64 (Z.of_nat n)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (Z.of_nat i))
                       (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i))
                       x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x156e4) fc None m (seg_rom rsegs)).
Proof using HN HSW HDW HDN.
  intros Q x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 m i fn j1 j2
    Hi Hfn FR RF SL HK.
  unfold FRC in FR.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  pose proof (munch_refl [(X, X + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite addr56c by lia.
  do 2 step.
  rewrite !rec_calls_free.sx32_small by lia.
  step.
  rewrite addr56c by lia. rewrite <- HX.
  do 3 step.
  rewrite bv_lts_zero_l, (unsigned_lit 0) by lia.
  replace (0 <? 0) with false by reflexivity. cbn [andb negb].
  eapply k_tail_last; [exact Hi | exact FR |].
  subst X. exact (HK _ SL MU WM).
Qed.

Definition st_after (pv : word) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (i j : nat)
    (m : word -> option byte) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -80)) gp tp x5 x6 x7 dw (Z_to_bv 64 0x33d10) pv x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i))
          (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned dw + 56 * Z.of_nat i))
          (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j))
          (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j)) s9 s10 s11 x28 x29 x30 x31)
     F (Z_to_bv 64 0x15720) fc None m (seg_rom rsegs).

Lemma k_after_call : forall (Q : machine_state -> Prop) pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    m (i j : nat) (fn len : Z) (pw : word) jj,
  (i < n)%nat -> Z.of_nat (S j) < len <= 6 ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
  rw_cells rsegs m (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [CB 8 jj] ->
  rw_cells rsegs m (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8) [C8 pw] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 pv] ->
     munch [(bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
             bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] m m' -> wmono rsegs m m' ->
     st_call Q i (S j) pw m') ->
  evt rsegs Q (st_after pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 i j m).
Proof using HN HSW HDW HDN.
  intros Q pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i j fn len pw jj Hi Hl SL AS RA HK.
  unfold st_after.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  remember (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Z8 eqn:HZ8.
  remember (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Y eqn:HY.
  pose proof (munch_refl [(Z8, Z8 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  rewrite rec_calls_free.sx32_small by lia.
  do 5 step.
  rewrite rec_calls_free.lts_small by lia.
  replace (Z.of_nat j + 1 <? len) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  do 2 step.
  apply evt_done.
  subst X Z8 Y.
  replace (Z_to_bv 64 (Z.of_nat j + 1)) with (Z_to_bv 64 (Z.of_nat (S j))) by (f_equal; lia).
  replace (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8))
    with (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat (S j))) by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8))
    with (Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat (S j))) by (f_equal; lia).
  exact (HK _ AS MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_after_next : forall (Q : machine_state -> Prop) pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    m (i j : nat) (fn len : Z) jj,
  (S i < n)%nat -> Z.of_nat (S j) = len -> len <= 6 ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
  rw_cells rsegs m (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [CB 8 jj] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 pv] ->
     munch [(bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
             bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] m m' -> wmono rsegs m m' ->
     st_head Q (S i) m') ->
  evt rsegs Q (st_after pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 i j m).
Proof using HN HSW HDW HDN.
  intros Q pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i j fn len jj Hi Hj Hl NC SL AS HK.
  unfold st_after.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  remember (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Z8 eqn:HZ8.
  remember (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Y eqn:HY.
  pose proof (munch_refl [(Z8, Z8 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  rewrite rec_calls_free.sx32_small by lia.
  do 5 step.
  rewrite rec_calls_free.lts_small by lia.
  replace (Z.of_nat j + 1 <? len) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  step.
  rewrite rec_calls_free.sx32_small by lia.
  eapply k_tail_next; [exact Hi|].
  subst X Z8 Y. exact (HK _ AS MU WM).
Qed.

Lemma k_after_last : forall (Q : machine_state -> Prop) pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    m (i j : nat) (fn len : Z) jj,
  (S i = n)%nat -> Z.of_nat (S j) = len -> len <= 6 ->
  rw_cells rsegs m (bv_unsigned sw + -80) FRC ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
  rw_cells rsegs m (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [CB 8 jj] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 pv] ->
     munch [(bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j,
             bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)] m m' -> wmono rsegs m m' ->
     st_ret Q m') ->
  evt rsegs Q (st_after pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 i j m).
Proof using HN HSW HDW HDN.
  intros Q pv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i j fn len jj Hi Hj Hl FR NC SL AS HK.
  unfold st_after. unfold FRC in FR.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  remember (bv_unsigned dw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Z8 eqn:HZ8.
  remember (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Y eqn:HY.
  pose proof (munch_refl [(Z8, Z8 + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  rewrite rec_calls_free.sx32_small by lia.
  do 5 step.
  rewrite rec_calls_free.lts_small by lia.
  replace (Z.of_nat j + 1 <? len) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  step.
  rewrite rec_calls_free.sx32_small by lia.
  eapply k_tail_last; [exact Hi | exact FR |].
  subst X Z8 Y. exact (HK _ AS MU WM).
Qed.

End KA.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecKindB RecChain RecModel
  RecInv RecInvP RecSeq RecStep RecGlue xstrdup_c rec_calls_copy_c.
From Stdlib Require Import Permutation.

Lemma rcc_b_app : forall b xs ys, rcc_b b (xs ++ ys) = rcc_b (rcc_b b xs) ys.
Proof. intros b xs ys. unfold rcc_b. apply fold_left_app. Qed.

Lemma rcc_b_snoc : forall b xs x, rcc_b b (xs ++ [x]) = sb_malloc (rcc_b b xs) (Z.of_nat (length x) + 1).
Proof. intros b xs x. rewrite rcc_b_app. reflexivity. Qed.

Lemma rcc_b_grow : forall ys b, sb_le b (rcc_b b ys).
Proof.
  induction ys as [|y ys IH]; intros b; unfold rcc_b in *; cbn [fold_left]; [apply sb_le_refl|].
  apply (sb_le_trans b (sb_malloc b (Z.of_nat (length y) + 1))); [apply sb_le_malloc; lia | apply IH].
Qed.

Lemma rcc_args_snoc : forall cs i c, nth_error cs i = Some c ->
  rcc_args (firstn (S i) cs) = rcc_args (firstn i cs) ++ snd c.
Proof.
  intros cs i c H. unfold rcc_args. rewrite (rec_calls_free.firstn_snoc cs i c H), map_app, concat_app.
  cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rcc_args_split : forall cs i c, nth_error cs i = Some c ->
  rcc_args cs = rcc_args (firstn i cs) ++ snd c ++ rcc_args (skipn (S i) cs).
Proof.
  intros cs i c H. rewrite app_assoc, <- (rcc_args_snoc cs i c H). unfold rcc_args.
  rewrite <- concat_app, <- map_app, firstn_skipn. reflexivity.
Qed.

Lemma rcc_xs_snoc : forall (cs : list rcall) (i : nat) (c : rcall) (j : nat) (x : list byte), nth_error (snd c) j = Some x ->
  rcc_args (firstn i cs) ++ firstn (S j) (snd c) = (rcc_args (firstn i cs) ++ firstn j (snd c)) ++ [x].
Proof. intros cs i c j x H. rewrite (rec_calls_free.firstn_snoc _ j x H), app_assoc. reflexivity. Qed.

Lemma rcc_room : forall b (cs : list rcall) (i : nat) (c : rcall) (j : nat) (x : list byte),
  nth_error cs i = Some c -> nth_error (snd c) j = Some x ->
  room_slots (rcc_b b (rcc_args cs)) (LMAX + 1) -> Z.of_nat (length x) <= LMAX ->
  room_slots (sb_malloc (rcc_b b (rcc_args (firstn i cs) ++ firstn j (snd c))) (Z.of_nat (length x) + 1))
    (Z.of_nat (length x) + 1).
Proof.
  intros b cs i c j x Hc Hx RM Hl.
  rewrite <- rcc_b_snoc, <- (rcc_xs_snoc cs i c j x Hx).
  apply (room_slots_mono _ (rcc_b b (rcc_args cs)) _ (LMAX + 1)); [| lia | exact RM].
  rewrite (rcc_args_split cs i c Hc). rewrite <- (firstn_skipn (S j) (snd c)) at 2.
  rewrite <- !app_assoc, app_assoc, (rcc_b_app b (rcc_args (firstn i cs) ++ firstn (S j) (snd c))).
  apply rcc_b_grow.
Qed.

Lemma not_out1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; cbn; split; [lia | exact I]].
Qed.

Lemma mkR_getr : forall R : bvmap 5 word, Regs6ss.mkR_of R =
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
      (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
      (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
      (getr R 29) (getr R 30) (getr R 31).
Proof. reflexivity. Qed.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis SLACK : block_slack_present B API.
Hypothesis XSD : xstrdup_contract B API.

Definition mchain (S K : Z) (E : Z -> Prop) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (b : sbound) (xs : list (list byte)) (N : list (Z * Z))
    (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
  aa_MR API Lc Ac memc mdc /\ WF Ac /\ bounded Ac /\
  layout_le A L Lc /\ (length (st_regions A) <= length (st_regions Ac))%nat /\
  (st_init_done A = true -> st_init_done Ac = true) /\
  (exists vm, mdc = with_vmmaps vm md) /\
  (forall y, In y (user_blocks A) -> In y (user_blocks Ac)) /\
  (forall p n, In (p, n) (user_blocks A) -> ptr_addr Lc p = ptr_addr L p) /\
  Permutation (blocks Lc Ac) (blocks L A ++ N) /\
  NoDup (map fst N) /\
  (forall pn q, In pn N -> In q (blocks L A) -> fst pn + snd pn <= fst q \/ fst q + snd q <= fst pn) /\
  (forall pn, In pn N -> 0 < snd pn) /\
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n ->
     mbyte (ms_segs B) memc (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) /\
  (forall a, hi_img B a -> ~ owned B L A a -> ~ (S - K <= a < S) -> ~ errw B a -> ~ E a ->
     mbyte (ms_segs B) memc a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) memc a)) /\
  (forall a, S - K <= a < S \/ errw B a -> writable_at (ms_segs B) memc a) /\
  ro_agree (ms_segs B) memc /\ guard_kept B mem memc /\
  res_ok_slots Ac (rcc_b b xs).

Lemma mchain_init : forall S K E L A regs mem md b,
  call_pre_k B (aa_MR API) K L A regs mem md -> ro_agree (ms_segs B) mem -> res_ok_slots A b -> spZ regs = S ->
  mchain S K E L A mem md b [] [] L A mem md.
Proof.
  intros S K E L A regs mem md b (HM & HW & HB & _ & _ & _ & _ & HWS & _ & HERR & _) HRO HRES <-.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [tauto|]. split; [exists (m_vmmaps md); apply YI04.with_vmmaps_self|].
  split; [intros y Hy; exact Hy|]. split; [intros; reflexivity|].
  split; [rewrite app_nil_r; apply Permutation_refl|].
  split; [constructor|]. split; [intros pn q []|]. split; [intros pn []|].
  split; [intros; reflexivity|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros a [Ha|Ha]; [apply HWS; exact Ha | apply HERR; exact Ha]|].
  split; [exact HRO|]. split; [intros i _; reflexivity|]. exact HRES.
Qed.

Lemma mchain_own : forall S K E L A mem md b xs N Lc Ac memc mdc m' W,
  mchain S K E L A mem md b xs N Lc Ac memc mdc ->
  munch W memc m' -> wmono (ms_segs B) memc m' ->
  alloc_ceiling + K <= S -> S <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (S - K <= a < S) \/ (E a /\ (alloc_ceiling <= a \/ in_globals frame_G a))) ->
  mchain S K E L A mem md b xs N Lc Ac m' mdc.
Proof using SEGS AX GOWN GFACT GOTG.
  intros S K E L A mem md b xs N Lc Ac memc mdc m' W
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME & HSCR
     & HRO & HGK & HRES) MU WM HK HS HW.
  pose proof alloc_ceiling_val as AC.
  assert (OUTL : forall a, 0 <= a < alloc_ceiling -> ~ in_globals frame_G a -> outside W a).
  { intros a Ha Hg. destruct (outside_dec W a) as [O|O]; [exact O|].
    destruct (HW a ltac:(lia) O) as [H|(_ & [H|H])]; [lia | lia | contradiction]. }
  assert (OUTB : forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> outside W (q + i)).
  { intros q k i Hin Hi. pose proof (block_facts B _ (aa_laws API) Lc Ac memc mdc q k i HMc Hin Hi) as (_ & H1 & H2 & _).
    apply OUTL; [lia|]. intros Hg. apply (block_not_img B API AX Lc Ac memc mdc q k i HMc Hin Hi).
    exact (proj1 (GFACT _ Hg)). }
  assert (OUTO : forall a, owned B Lc Ac a -> outside W a).
  { intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho). apply OUTL; [lia|].
    intros Hg. exact (GOWN _ _ _ _ a HMc Hg Ho). }
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & Hmat).
  split.
  { eapply (mr_frame B _ (aa_laws API) Lc Ac memc m' mdc mdc HMc).
    - intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_mbyte _ W memc m'); [exact MU | lia | exact (OUTO a Ho)].
    - intros a Ho Hp. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_present W memc m'); [exact MU | lia | exact (OUTO a Ho) | exact Hp].
    - intros p n i Hin Hi.
      assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (p, n); auto).
      pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (Hp & H1 & H2 & _).
      apply (munch_present W memc m'); [exact MU | lia | exact (OUTB _ _ i Hb Hi) | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|]. split; [exact HRG|]. split; [exact HINIT|].
  split; [exact HVM|]. split; [exact HSUB|]. split; [exact HPTR|]. split; [exact HPERM|].
  split; [exact HND|]. split; [exact HDJ|]. split; [exact HPOS|].
  split.
  { intros p n i Hin Hi.
    assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac))
      by (unfold blocks; apply in_map_iff; exists (p, n); split; [reflexivity | exact (HSUB _ Hin)]).
    pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (_ & H1 & H2 & _).
    rewrite <- (HPTR p n Hin).
    rewrite (munch_mbyte _ W memc m' (ptr_addr Lc p + i) MU ltac:(lia) (OUTB _ _ i Hb Hi)).
    rewrite (HPTR p n Hin). exact (HBYTES p n i Hin Hi). }
  split.
  { intros a Ha Hno Hs He HE. pose proof (hi_img_range B SEGS a Ha) as R.
    assert (O : outside W a).
    { destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso.
      destruct (HW a R O) as [H|(H & _)]; [exact (Hs H) | exact (HE H)]. }
    destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    split; [rewrite (munch_mbyte _ W memc m' a MU R O); exact E1|].
    rewrite E2. exact (munch_writable _ W memc m' a MU R O). }
  split; [intros a Ha; apply WM; exact (HSCR a Ha)|].
  split.
  { intros y Hro. unfold mrd.
    destruct (outside_dec W (bv_unsigned y)) as [O|O].
    - rewrite (MU y O). exact (HRO y Hro).
    - exfalso. pose proof (bv_unsigned_in_range 64 y) as R. unfold bv_modulus in R.
      rewrite SEGS in Hro.
      destruct (HW (bv_unsigned y) ltac:(cbn in R; lia) O) as [H|(_ & [H|H])].
      + rewrite <- (Z_to_bv_bv_unsigned y) in Hro. rewrite (hi_rw (bv_unsigned y)) in Hro by lia. discriminate.
      + rewrite <- (Z_to_bv_bv_unsigned y) in Hro. rewrite (hi_rw (bv_unsigned y)) in Hro by (cbn in R; lia).
        discriminate.
      + rewrite <- (Z_to_bv_bv_unsigned y) in Hro. rewrite (fg_rw (bv_unsigned y) H) in Hro. discriminate. }
  split.
  { intros i Hi. rewrite <- (HGK i Hi). rewrite GOTG.
    apply (munch_mbyte _ W memc m'); [exact MU | lia|]. apply OUTL; [lia|]. rewrite fg_iff. lia. }
  exact HRES.
Qed.

Lemma mchain_x : forall S K E L A mem md b xs N Lc Ac memc mdc regs_c x p L2 A2 regs2 mem2 md2,
  aa_MR API L A mem md -> alloc_ceiling + K <= S -> S <= 2 ^ 64 ->
  mchain S K E L A mem md b xs N Lc Ac memc mdc ->
  S - K <= spZ regs_c - XSTRDUP_K -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) XSTRDUP_K Lc Ac regs_c memc mdc (fun a => p <= a < p + Z.of_nat (length x) + 1)
    L2 A2 regs2 mem2 md2 ->
  fresh_block B p (Z.of_nat (length x) + 1) ->
  (exists b1 b2, blocks L2 A2 = b1 ++ (p, Z.of_nat (length x) + 1) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q k, In (q, k) (user_blocks Ac) -> In (q, k) (user_blocks A2)) ->
  ro_agree (ms_segs B) mem2 -> guard_kept B memc mem2 ->
  st_init_done A2 = true ->
  (length (st_regions Ac) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_malloc (rcc_b b xs) (Z.of_nat (length x) + 1)) ->
  mchain S K E L A mem md b (xs ++ [x]) (N ++ [(p, Z.of_nat (length x) + 1)]) L2 A2 mem2 md2.
Proof using CTX AX ERRNO.
  intros S K E L A mem md b xs N Lc Ac memc mdc regs_c x p L2 A2 regs2 mem2 md2 HM0 HK HS
    (HMc & HWc & HBc & HLE & HRG & HINIT & (vm & Hvm) & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME
     & HSCR & HRO & HGK & HRES)
    Hlo Hhi (HM2 & HW2 & HB2 & HLE2 & HSTAB & _ & (vm2 & Hvm2) & HFR2 & HKB2 & HSCR2)
    (FP1 & FP2 & FP3) (b1 & b2 & EB2 & EB1) HUB HRO2 HGK2 HI2 HRG2 HRES2.
  pose proof alloc_ceiling_val as AC.
  assert (INC : forall q, In q (blocks Lc Ac) ->
            fst q + snd q <= p \/ p + (Z.of_nat (length x) + 1) <= fst q).
  { intros [q kq] Hq. rewrite EB1 in Hq.
    exact (blocks_mid_disjoint B _ (aa_laws API) L2 A2 mem2 md2 b1 b2 p _ q kq HM2 EB2 Hq). }
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split; [exact (layout_le_trans A Ac L Lc L2 HLE HLE2 HRG)|].
  split; [lia|]. split; [intros _; exact HI2|].
  split; [exists vm2; rewrite Hvm2, Hvm; apply YI04.with_vmmaps_twice|].
  split; [intros [q kq] Hy; apply HUB; apply HSUB; exact Hy|].
  split; [intros q kq Hq; rewrite (HSTAB q kq (HSUB _ Hq) (HUB q kq (HSUB _ Hq))); exact (HPTR q kq Hq)|].
  split.
  { rewrite EB2. apply (Permutation_trans (l' := (p, Z.of_nat (length x) + 1) :: b1 ++ b2));
      [apply Permutation_sym, Permutation_middle|].
    apply (Permutation_trans (l' := (b1 ++ b2) ++ [(p, Z.of_nat (length x) + 1)])); [apply Permutation_cons_append|].
    rewrite <- EB1, app_assoc. apply Permutation_app_tail. exact HPERM. }
  split.
  { apply nodup_fst_snoc; [exact HND|]. intros Hin. apply in_map_iff in Hin as ([q kq] & Eq & Hq). cbn in Eq. subst q.
    assert (Hc : In (p, kq) (blocks Lc Ac))
      by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hq).
    pose proof (HPOS _ Hq) as Hp. cbn in Hp. destruct (INC _ Hc) as [D|D]; cbn in D; lia. }
  split.
  { intros pn q Hpn Hq. apply in_app_or in Hpn as [Hpn|Hpn]; [exact (HDJ pn q Hpn Hq)|].
    destruct Hpn as [<-|[]]. cbn [fst snd].
    assert (Hc : In q (blocks Lc Ac))
      by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hq).
    destruct (INC q Hc) as [D|D]; [right; exact D | left; exact D]. }
  split; [intros pn Hpn; apply in_app_or in Hpn as [Hpn|[<-|[]]]; [exact (HPOS _ Hpn) | cbn; lia]|].
  split.
  { intros q kq i Hq Hi. pose proof (HSUB _ Hq) as Hc.
    pose proof (HKB2 q kq i Hc (HUB q kq Hc) Hi) as Eb. rewrite (HPTR q kq Hq) in Eb. rewrite Eb.
    exact (HBYTES q kq i Hq Hi). }
  split.
  { intros a Ha Hno Hs He HE. destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    assert (Hnc : ~ owned B Lc Ac a) by exact (own_any B API AX CTX L A mem md Lc Ac memc mdc a HM0 HMc Ha Hno).
    assert (Hn2 : ~ owned B L2 A2 a) by exact (own_any B API AX CTX L A mem md L2 A2 mem2 md2 a HM0 HM2 Ha Hno).
    assert (Hns : ~ scratch_k B XSTRDUP_K regs_c a)
      by (unfold scratch_k; intros [H|H]; [apply Hs; lia | exact (He H)]).
    assert (Hnf : ~ (p <= a < p + Z.of_nat (length x) + 1)).
    { intros Hr. destruct Ha as [Ha|Ha]; [lia|]. apply (FP3 (a - p)); [lia|].
      replace (p + (a - p)) with a by ring. exact Ha. }
    destruct (HFR2 a Ha Hnc Hn2 Hns Hnf) as [F1 F2]. split; [congruence | tauto]. }
  split.
  { intros a Ha.
    destruct (Z_le_gt_dec (spZ regs_c - XSTRDUP_K) a) as [D1|D1];
      [destruct (Z_lt_ge_dec a (spZ regs_c)) as [D2|D2]|].
    - apply HSCR2. left. lia.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch_k B XSTRDUP_K regs_c a) by (unfold scratch_k; intros [H|H]; lia).
      assert (Hnf : ~ (p <= a < p + Z.of_nat (length x) + 1)) by lia.
      apply (proj2 (HFR2 a (or_introl Hh) Hn1 Hn2 Hns Hnf)). apply HSCR. left. exact Ha.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : alloc_ceiling <= a < 2 ^ 64) by (unfold XSTRDUP_K, ALLOC_STACK in *; lia).
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch_k B XSTRDUP_K regs_c a) by (unfold scratch_k; intros [H|H]; lia).
      assert (Hnf : ~ (p <= a < p + Z.of_nat (length x) + 1)) by lia.
      apply (proj2 (HFR2 a (or_introl Hh) Hn1 Hn2 Hns Hnf)). apply HSCR. left. exact Ha. }
  split; [exact HRO2|]. split; [intros i Hi; rewrite (HGK2 i Hi); exact (HGK i Hi)|].
  rewrite rcc_b_snoc. exact HRES2.
Qed.

Lemma mchain_post : forall S K E L A regs mem md b xs N L' A' regs' mem' md',
  spZ regs = S -> mchain S K E L A mem md b xs N L' A' mem' md' -> regs_preserved regs regs' ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md'.
Proof.
  intros S K E L A regs mem md b xs N L' A' regs' mem' md' HS
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES & HFRAME & HSCR
     & HRO & HGK & HRES) HREGS.
  split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|].
  split; [intros p n H1 _; exact (HPTR p n H1)|]. split; [exact HREGS|]. split; [exact HVM|].
  split.
  { intros a Ha Hno _ Hs HE. apply HFRAME; [exact Ha | exact Hno | | | exact HE].
    - intros H. apply Hs. unfold scratch_k. left. rewrite HS. exact H.
    - intros H. apply Hs. unfold scratch_k. right. exact H. }
  split; [intros p n i H1 _ Hi; exact (HBYTES p n i H1 Hi)|].
  intros a [Ha|Ha]; apply HSCR; [left; rewrite <- HS; exact Ha | right; exact Ha].
Qed.

Lemma rw2_bytes : forall segs m X u v, rw_cells segs m X [C4 u; C4 v] ->
  bytes_at segs m X (le4 u) /\ bytes_at segs m (X + 4) (le4 v) /\
  (forall t, 0 <= t < 8 -> writable_at segs m (X + t)).
Proof.
  intros segs m X u v [[_ HB] (_ & _ & HW)]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply bytes_at_app in HB as [H1 H2]. rewrite length_le4 in H2. change (Z.of_nat 4) with 4 in H2.
  split; [exact H1|]. split; [exact H2|]. intros t Ht. exact (HW t ltac:(cbn; lia)).
Qed.

Lemma rw2_intro : forall segs m X u v, bytes_at segs m X (le4 u) -> bytes_at segs m (X + 4) (le4 v) ->
  (forall t, 0 <= t < 8 -> writable_at segs m (X + t)) -> rw_cells segs m X [C4 u; C4 v].
Proof.
  intros segs m X u v H1 H2 HW. pose proof (bytes_at_bound _ _ _ _ H1) as B1.
  pose proof (bytes_at_bound _ _ _ _ H2) as B2. rewrite length_le4 in B1, B2.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact H1|]. rewrite length_le4. exact H2.
  - split; [lia|]. split; [cbn; lia|]. intros t Ht. exact (HW t ltac:(cbn in Ht; lia)).
Qed.

Lemma rw8_bytes : forall segs m X w, rw_cells segs m X [C8 w] -> bytes_at segs m X (le8 w).
Proof. intros segs m X w [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

Lemma rw8_wr : forall segs m X w t, rw_cells segs m X [C8 w] -> 0 <= t < 8 -> writable_at segs m (X + t).
Proof. intros segs m X w t [_ (_ & _ & HW)] Ht. exact (HW t ltac:(cbn; lia)). Qed.

Lemma slack_rebuild' : forall m s x, bytes_at rsegs m s (x ++ [Z_to_bv 8 0]) -> 0 <= s ->
  s + Z.of_nat (length x) + 1 + 8 <= 2 ^ 64 ->
  (forall a, s + (Z.of_nat (length x) + 1) <= a < 8 * ((s + (Z.of_nat (length x) + 1) + 7) / 8) -> present m a) ->
  exists slack, bytes_at rsegs m s (x ++ Z_to_bv 8 0 :: slack) /\
    (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    s + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) = 8 * ((s + (Z.of_nat (length x) + 1) + 7) / 8).
Proof.
  intros m s x H H0 H1 HP.
  destruct (slack_bytes rsegs m s (Z.of_nat (length x) + 1) (x ++ [Z_to_bv 8 0]) H
              ltac:(rewrite length_app; cbn [length]; lia) H0 ltac:(lia) HP) as (sl & HB & HL).
  exists sl. rewrite <- app_assoc in HB. cbn [app] in HB. split; [exact HB|].
  rewrite length_app. cbn [length]. split; Z.div_mod_to_equations; lia.
Qed.

Lemma ceil8_le : forall a b, a <= b -> b mod 8 = 0 -> 8 * ((a + 7) / 8) <= b.
Proof. intros a b H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma ceil8_mono : forall a b, a <= b -> 8 * ((a + 7) / 8) <= 8 * ((b + 7) / 8).
Proof. intros a b H. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.div_le_mono; lia. Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (R : rstate)
  (O : list (Z * Z)) (dst : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) RCC_K L A regs mem md.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis A0 : getr regs 10 = Z_to_bv 64 dst.
Hypothesis GR : g_rec_rep (ms_segs B) L A mem R O.
Hypothesis ARR : forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) ->
  spZ regs <= dst + j < 2 ^ 64 /\ writable_at (ms_segs B) mem (dst + j).
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : room_slots (rcc_b b (rcc_args (r_calls R))) (LMAX + 1).

Definition POST : config -> Prop := fun c' => exists L' A' regs' mem' md' (qs : list (list (Z * Z))),
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
  call_post_k B (aa_MR API) RCC_K L A regs mem md (rcc_writes dst (r_calls R)) L' A' regs' mem' md' /\
  getr regs' 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) /\
  length qs = length (r_calls R) /\
  (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
     call_at (ms_segs B) (blocks L' A') mem' (dst + 56 * Z.of_nat i) c P /\
     forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn ->
       snd pn = Z.of_nat (length s) + 1 /\ fresh_block B (fst pn) (snd pn)) /\
  Permutation (blocks L' A') (blocks L A ++ concat qs) /\
  NoDup (map fst (concat qs)) /\
  (forall pn q, In pn (concat qs) -> In q (blocks L A) -> fst pn + snd pn <= fst q \/ fst q + snd q <= fst pn) /\
  blocks_kept B L A mem mem' (fun _ => False) /\
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
  g_rec_rep (ms_segs B) L' A' mem' R O /\
  (forall a, in_globals frame_G a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
  (forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) -> writable_at (ms_segs B) mem' (dst + j)) /\
  ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  res_ok_slots A' (rcc_b b (rcc_args (r_calls R))).

Definition CHS (xs : list (list byte)) (N : list (Z * Z)) (Lc : layout) (Ac : astate) (mc : word -> option byte)
    (mdc : Model) : Prop :=
  mchain (spZ regs) RCC_K (rcc_writes dst (r_calls R)) L A mem md b xs N Lc Ac mc mdc.

Lemma pre_facts : aa_MR API L A mem md /\ alloc_ceiling + RCC_K <= spZ regs /\ spZ regs < 2 ^ 63 /\
  spZ regs mod 16 = 0 /\ YK0s.ret_ok (getr regs 1) /\ WF A /\ getr regs 4 = Z_to_bv 64 (ms_tp B).
Proof using PRE.
  destruct PRE as (HM & HW & _ & HRA & HAL & HCE & H63 & _ & HTP & _). auto 7.
Qed.

Lemma rep_facts : (length (r_calls R) <= 16)%nat /\
  bytes_at (ms_segs B) mem 0x33d50 (le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))) /\
  (forall i c, nth_error (r_calls R) i = Some c -> exists P,
     call_at (ms_segs B) (blocks L A) mem (0x33d58 + 56 * Z.of_nat i) c P /\
     Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)).
Proof using GR.
  destruct GR as (Q & (HS & (C1 & C2 & C3 & C4 & C5 & C6) & _) & _).
  split; [exact C1|]. split; [exact C3|].
  intros i c Hc. assert (Hi : (i < length (l_calls Q))%nat) by (rewrite C2; apply nth_error_Some; rewrite Hc; discriminate).
  destruct (nth_error (l_calls Q) i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
  exists P. destruct (C4 i c P Hc EP) as [H1 H2]. split; [|exact H2].
  replace (0x33d58 + 56 * Z.of_nat i) with (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i)
    by (unfold G_REC, OFF_CALLS, CALL_SIZE; lia).
  exact H1.
Qed.

Lemma call_len : forall i c, nth_error (r_calls R) i = Some c -> (length (snd c) <= 6)%nat.
Proof using GR.
  intros i c Hc. destruct rep_facts as (_ & _ & H). destruct (H i c Hc) as (P & (_ & Hl & _) & _). exact Hl.
Qed.

Lemma dst_facts : (0 < length (r_calls R))%nat ->
  bv_unsigned (getr regs 10) = dst /\ spZ regs <= dst /\ dst + 56 * Z.of_nat (length (r_calls R)) <= 2 ^ 64.
Proof using A0 ARR.
  intros Hn. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. unfold bv_modulus in RS. cbn in RS.
  destruct (ARR 0 ltac:(lia)) as [H1 _].
  destruct (ARR (56 * Z.of_nat (length (r_calls R)) - 1) ltac:(lia)) as [H2 _].
  unfold spZ in *. split; [rewrite A0; apply unsigned_lit; lia|]. lia.
Qed.

Lemma ka_hyps : (0 < length (r_calls R))%nat ->
  (length (r_calls R) <= 16)%nat /\ 2 ^ 20 <= bv_unsigned (getr regs 2) - 80 /\
  bv_unsigned (getr regs 2) <= bv_unsigned (getr regs 10) /\
  bv_unsigned (getr regs 10) + 56 * Z.of_nat (length (r_calls R)) <= 2 ^ 64 /\
  bv_unsigned (getr regs 10) = dst.
Proof using PRE GR A0 ARR.
  intros Hn. destruct pre_facts as (_ & HCE & _). destruct rep_facts as (H16 & _).
  destruct (dst_facts Hn) as (UC & D1 & D2). pose proof alloc_ceiling_val as AC.
  unfold spZ, RCC_K, XSTRDUP_K, ALLOC_STACK in *. rewrite UC. auto 6 with zarith.
Qed.

Lemma rw_hi : forall a, rcc_writes dst (r_calls R) a ->
  spZ regs <= a < 2 ^ 64 /\ dst <= a < dst + 56 * Z.of_nat (length (r_calls R)).
Proof using GR A0 ARR.
  intros a (i & c & Hc & Ha). pose proof (call_len i c Hc) as Hl.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  destruct (ARR (a - dst) ltac:(lia)) as [H _]. lia.
Qed.

Lemma mc_frame : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall a, hi_img B a -> ~ owned B L A a -> ~ (spZ regs - RCC_K <= a < spZ regs) -> ~ errw B a ->
    ~ rcc_writes dst (r_calls R) a ->
    mbyte (ms_segs B) mc a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mc a).
Proof. intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma mc_MR : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc -> aa_MR API Lc Ac mc mdc /\ WF Ac.
Proof. intros xs N Lc Ac mc mdc (H1 & H2 & _). auto. Qed.

Lemma mc_perm : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc -> Permutation (blocks Lc Ac) (blocks L A ++ N).
Proof. intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma mc_scr : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall a, spZ regs - RCC_K <= a < spZ regs \/ errw B a -> writable_at (ms_segs B) mc a.
Proof.
  intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma mc_misc : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  ro_agree (ms_segs B) mc /\ res_ok_slots Ac (rcc_b b xs) /\ bounded Ac /\
  (st_init_done A = true -> st_init_done Ac = true).
Proof.
  intros xs N Lc Ac mc mdc (_ & _ & HB & _ & _ & HI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _ & HRES).
  auto.
Qed.

Lemma old_kept : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall q k j, In (q, k) (blocks L A) -> 0 <= j < k ->
    mbyte (ms_segs B) mc (q + j) = mbyte (ms_segs B) mem (q + j).
Proof.
  intros xs N Lc Ac mc mdc (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HB & _) q k j Hq Hj.
  destruct (proj1 (YI04.blocks_In L A q k) Hq) as (p & Ep & Hp). subst q. exact (HB p k j Hp Hj).
Qed.

Lemma old_in : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall q, In q (blocks L A) -> In q (blocks Lc Ac).
Proof.
  intros xs N Lc Ac mc mdc CH q Hq. apply (Permutation_in _ (Permutation_sym (mc_perm _ _ _ _ _ _ CH))).
  apply in_or_app. left. exact Hq.
Qed.

Lemma glob_kept : forall xs N Lc Ac mc mdc, CHS xs N Lc Ac mc mdc ->
  forall a, in_globals frame_G a -> mbyte (ms_segs B) mc a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mc a).
Proof using PRE GR A0 ARR GFACT GOWN.
  intros xs N Lc Ac mc mdc CH a Ha. destruct pre_facts as (HM & HCE & _).
  destruct (GFACT a Ha) as (Hi & _ & _ & He). pose proof alloc_ceiling_val as AC.
  pose proof Ha as Ha'. apply fg_iff in Ha'.
  apply (mc_frame _ _ _ _ _ _ CH); [right; exact Hi | exact (GOWN _ _ _ _ a HM Ha) | | exact He |].
  - unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia.
  - intros HW. destruct (rw_hi a HW). unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia.
Qed.

Definition ARG (Lc : layout) (Ac : astate) (mc : word -> option byte) (i a : nat) (s : list byte) (pn : Z * Z)
    : Prop :=
  bytes_at (ms_segs B) mc (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a) (le8 (Z_to_bv 64 (fst pn))) /\
  fst pn <> 0 /\ In pn (blocks Lc Ac) /\ snd pn = Z.of_nat (length s) + 1 /\ fresh_block B (fst pn) (snd pn) /\
  bytes_at (ms_segs B) mc (fst pn) (s ++ [Z_to_bv 8 0]) /\ no0 s.

Definition ARGS (Lc : layout) (Ac : astate) (mc : word -> option byte) (i : nat) (c : rcall) (P : list (Z * Z))
    : Prop :=
  forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn -> ARG Lc Ac mc i a s pn.

Definition HDR (mc : word -> option byte) (i : nat) (c : rcall) : Prop :=
  bytes_at (ms_segs B) mc (dst + 56 * Z.of_nat i) (le4 (Z_to_bv 64 (fst c))) /\
  bytes_at (ms_segs B) mc (dst + 56 * Z.of_nat i + 4) (le4 (Z_to_bv 64 (Z.of_nat (length (snd c))))).

Definition DONE (Lc : layout) (Ac : astate) (mc : word -> option byte) (i : nat) (qs : list (list (Z * Z)))
    : Prop :=
  length qs = i /\ forall i' c P, nth_error (r_calls R) i' = Some c -> nth_error qs i' = Some P ->
    length P = length (snd c) /\ HDR mc i' c /\ ARGS Lc Ac mc i' c P.

Definition DSTW (mc : word -> option byte) : Prop :=
  forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) -> writable_at (ms_segs B) mc (dst + j).

Lemma args_transfer : forall Lc Ac mc Lc' Ac' mc' i c P,
  ARGS Lc Ac mc i c P ->
  (forall pn, In pn (blocks Lc Ac) -> In pn (blocks Lc' Ac')) ->
  (forall q k j, In (q, k) (blocks Lc Ac) -> 0 <= j < k ->
     mbyte (ms_segs B) mc' (q + j) = mbyte (ms_segs B) mc (q + j)) ->
  (forall j, 0 <= j < 8 + 8 * Z.of_nat (length (snd c)) ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + j)) ->
  ARGS Lc' Ac' mc' i c P.
Proof.
  intros Lc Ac mc Lc' Ac' mc' i c P H HB HK HD a s pn Es Ep.
  destruct (H a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (Ha : (a < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  split.
  { apply (bytes_at_transfer _ mc); [exact P1|]. intros t Ht. rewrite length_le8 in Ht. change (Z.of_nat 8) with 8 in Ht.
    replace (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) with (dst + 56 * Z.of_nat i + (8 + 8 * Z.of_nat a + t))
      by ring.
    apply HD. lia. }
  split; [exact P2|]. split; [exact (HB _ P3)|]. split; [exact P4|]. split; [exact P5|].
  split; [|exact P7].
  apply (bytes_at_transfer _ mc); [exact P6|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
  destruct pn as [q k]. cbn [fst snd] in *. apply (HK q k t P3). lia.
Qed.

Lemma args_transfer_lt : forall Lc Ac mc Lc' Ac' mc' i c P,
  ARGS Lc Ac mc i c P ->
  (forall pn, In pn (blocks Lc Ac) -> In pn (blocks Lc' Ac')) ->
  (forall q k j, In (q, k) (blocks Lc Ac) -> 0 <= j < k ->
     mbyte (ms_segs B) mc' (q + j) = mbyte (ms_segs B) mc (q + j)) ->
  (forall a t, (a < length P)%nat -> 0 <= t < 8 ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) =
     mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t)) ->
  ARGS Lc' Ac' mc' i c P.
Proof.
  intros Lc Ac mc Lc' Ac' mc' i c P H HB HK HD a s pn Es Ep.
  destruct (H a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (Ha : (a < length P)%nat) by (apply nth_error_Some; rewrite Ep; discriminate).
  split.
  { apply (bytes_at_transfer _ mc); [exact P1|]. intros t Ht. rewrite length_le8 in Ht. change (Z.of_nat 8) with 8 in Ht.
    apply HD; [exact Ha | lia]. }
  split; [exact P2|]. split; [exact (HB _ P3)|]. split; [exact P4|]. split; [exact P5|].
  split; [|exact P7].
  apply (bytes_at_transfer _ mc); [exact P6|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
  destruct pn as [q k]. cbn [fst snd] in *. apply (HK q k t P3). lia.
Qed.

Lemma hdr_transfer : forall mc mc' i c, HDR mc i c ->
  (forall j, 0 <= j < 8 ->
     mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i + j)) ->
  HDR mc' i c.
Proof.
  intros mc mc' i c (H1 & H2) HD. split.
  - apply (bytes_at_transfer _ mc); [exact H1|]. intros t Ht. rewrite length_le4 in Ht. change (Z.of_nat 4) with 4 in Ht.
    apply HD. lia.
  - apply (bytes_at_transfer _ mc); [exact H2|]. intros t Ht. rewrite length_le4 in Ht. change (Z.of_nat 4) with 4 in Ht.
    replace (dst + 56 * Z.of_nat i + 4 + t) with (dst + 56 * Z.of_nat i + (4 + t)) by ring. apply HD. lia.
Qed.

Lemma done_transfer : forall Lc Ac mc Lc' Ac' mc' i qs,
  DONE Lc Ac mc i qs ->
  (forall pn, In pn (blocks Lc Ac) -> In pn (blocks Lc' Ac')) ->
  (forall q k j, In (q, k) (blocks Lc Ac) -> 0 <= j < k ->
     mbyte (ms_segs B) mc' (q + j) = mbyte (ms_segs B) mc (q + j)) ->
  (forall j, 0 <= j < 56 * Z.of_nat i -> mbyte (ms_segs B) mc' (dst + j) = mbyte (ms_segs B) mc (dst + j)) ->
  DONE Lc' Ac' mc' i qs.
Proof using GR.
  intros Lc Ac mc Lc' Ac' mc' i qs (HL & HD) HB HK HM. split; [exact HL|].
  intros i' c P Hc HP. destruct (HD i' c P Hc HP) as (H1 & H2 & H3).
  assert (Hi : (i' < i)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite HP; discriminate).
  pose proof (call_len i' c Hc) as Hl.
  assert (HM' : forall j, 0 <= j < 56 ->
            mbyte (ms_segs B) mc' (dst + 56 * Z.of_nat i' + j) = mbyte (ms_segs B) mc (dst + 56 * Z.of_nat i' + j)).
  { intros j Hj. replace (dst + 56 * Z.of_nat i' + j) with (dst + (56 * Z.of_nat i' + j)) by ring. apply HM. lia. }
  split; [exact H1|]. split.
  - apply (hdr_transfer mc); [exact H2|]. intros j Hj. apply HM'. lia.
  - apply (args_transfer Lc Ac mc); [exact H3 | exact HB | exact HK |]. intros j Hj. apply HM'. lia.
Qed.

Definition RGB (Rc : bvmap 5 word) (i : nat) : Prop :=
  getr Rc 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -80) /\ getr Rc 3 = getr regs 3 /\ getr Rc 4 = getr regs 4 /\
  getr Rc 8 = getr regs 10 /\ getr Rc 9 = Z_to_bv 64 0x33d10 /\ getr Rc 18 = Z_to_bv 64 (Z.of_nat i) /\
  getr Rc 19 = Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i) /\
  getr Rc 20 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i) /\
  getr Rc 25 = getr regs 25 /\ getr Rc 26 = getr regs 26 /\ getr Rc 27 = getr regs 27.

Definition RG (Rc : bvmap 5 word) (i : nat) : Prop :=
  RGB Rc i /\ getr Rc 11 = Z_to_bv 64 (Z.of_nat (length (r_calls R))).

Definition RGI (Rc : bvmap 5 word) (i j : nat) : Prop :=
  RGB Rc i /\ getr Rc 21 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i) /\
  getr Rc 22 = Z_to_bv 64 (Z.of_nat j) /\ getr Rc 23 = Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j) /\
  getr Rc 24 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j).

Lemma mkR_of_RG : forall Rc i, RG Rc i -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -80)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (getr regs 10) (Z_to_bv 64 0x33d10) (getr Rc 10) (Z_to_bv 64 (Z.of_nat (length (r_calls R))))
      (getr Rc 12) (getr Rc 13) (getr Rc 14) (getr Rc 15) (getr Rc 16) (getr Rc 17) (Z_to_bv 64 (Z.of_nat i))
      (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i))
      (getr Rc 21) (getr Rc 22) (getr Rc 23) (getr Rc 24) (getr regs 25) (getr regs 26) (getr regs 27)
      (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i ((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G25 & G26 & G27) & G11).
  rewrite mkR_getr, G2, G3, G4, G8, G9, G11, G18, G19, G20, G25, G26, G27. reflexivity.
Qed.

Lemma mkR_of_RGI : forall Rc i j, RGI Rc i j -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -80)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (getr regs 10) (Z_to_bv 64 0x33d10) (getr Rc 10) (getr Rc 11)
      (getr Rc 12) (getr Rc 13) (getr Rc 14) (getr Rc 15) (getr Rc 16) (getr Rc 17) (Z_to_bv 64 (Z.of_nat i))
      (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i)) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i))
      (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j))
      (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j))
      (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j))
      (getr regs 25) (getr regs 26) (getr regs 27) (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i j ((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G25 & G26 & G27) & G21 & G22 & G23 & G24).
  rewrite mkR_getr, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27.
  reflexivity.
Qed.

Lemma rg_mkR : forall i y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y21 y22 y23 y24 y28 y29 y30 y31 Rc,
  Rc = mkR y1 (Z_to_bv 64 (bv_unsigned (getr regs 2) + -80)) (getr regs 3) (getr regs 4) y5 y6 y7 (getr regs 10)
         (Z_to_bv 64 0x33d10) y10 (Z_to_bv 64 (Z.of_nat (length (r_calls R)))) y12 y13 y14 y15 y16 y17
         (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i))
         (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i)) y21 y22 y23 y24
         (getr regs 25) (getr regs 26) (getr regs 27) y28 y29 y30 y31 ->
  RG Rc i.
Proof. intros. subst Rc. unfold RG, RGB. repeat split. Qed.

Lemma rgi_mkR : forall i j pw y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Rc,
  Rc = mkR (Z_to_bv 64 0x15720) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -80)) (getr regs 3) (getr regs 4)
         y5 y6 y7 (getr regs 10) (Z_to_bv 64 0x33d10) pw y11 y12 y13 y14 y15 y16 y17
         (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i))
         (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i))
         (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j))
         (Z_to_bv 64 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j))
         (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j))
         (getr regs 25) (getr regs 26) (getr regs 27) y28 y29 y30 y31 ->
  getr Rc 1 = Z_to_bv 64 0x15720 /\ getr Rc 10 = pw /\ RGI Rc i j.
Proof. intros. subst Rc. unfold RGI, RGB. repeat split. Qed.

Lemma pres_mkR : forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Rc,
  Rc = mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) y5 y6 y7 (getr regs 8) (getr regs 9)
         (Z_to_bv 64 (Z.of_nat (length (r_calls R)))) y11 y12 y13 y14 y15 y16 y17
         (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
         (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) y28 y29 y30 y31 ->
  regs_preserved regs Rc /\ getr Rc 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))).
Proof.
  intros. subst Rc. split; [|reflexivity]. intros r Hr. unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

Lemma rgb_pres : forall Rc Rc' i, regs_preserved Rc Rc' -> RGB Rc i -> RGB Rc' i.
Proof.
  intros Rc Rc' i HP (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G25 & G26 & G27).
  assert (E : forall r, callee_saved r -> getr Rc' (Z_to_bv 5 r) = getr Rc (Z_to_bv 5 r)) by exact HP.
  assert (CS : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27) -> callee_saved r)
    by (intros r Hr; exact Hr).
  split; [exact (eq_trans (E 2 (CS 2 ltac:(lia))) G2)|].
  split; [exact (eq_trans (E 3 (CS 3 ltac:(lia))) G3)|].
  split; [exact (eq_trans (E 4 (CS 4 ltac:(lia))) G4)|].
  split; [exact (eq_trans (E 8 (CS 8 ltac:(lia))) G8)|].
  split; [exact (eq_trans (E 9 (CS 9 ltac:(lia))) G9)|].
  split; [exact (eq_trans (E 18 (CS 18 ltac:(lia))) G18)|].
  split; [exact (eq_trans (E 19 (CS 19 ltac:(lia))) G19)|].
  split; [exact (eq_trans (E 20 (CS 20 ltac:(lia))) G20)|].
  split; [exact (eq_trans (E 25 (CS 25 ltac:(lia))) G25)|].
  split; [exact (eq_trans (E 26 (CS 26 ltac:(lia))) G26)|].
  exact (eq_trans (E 27 (CS 27 ltac:(lia))) G27).
Qed.

Lemma rgi_pres : forall Rc Rc' i j, regs_preserved Rc Rc' -> RGI Rc i j -> RGI Rc' i j.
Proof.
  intros Rc Rc' i j HP (GB & G21 & G22 & G23 & G24).
  assert (E : forall r, callee_saved r -> getr Rc' (Z_to_bv 5 r) = getr Rc (Z_to_bv 5 r)) by exact HP.
  assert (CS : forall r, 18 <= r <= 27 -> callee_saved r) by (intros r Hr; unfold callee_saved; lia).
  split; [exact (rgb_pres Rc Rc' i HP GB)|].
  split; [exact (eq_trans (E 21 (CS 21 ltac:(lia))) G21)|].
  split; [exact (eq_trans (E 22 (CS 22 ltac:(lia))) G22)|].
  split; [exact (eq_trans (E 23 (CS 23 ltac:(lia))) G23)|].
  exact (eq_trans (E 24 (CS 24 ltac:(lia))) G24).
Qed.

Lemma rg_eqv : forall Rc Rc' i, RG Rc i -> Regs6ss.xregs_eqv Rc Rc' -> RG Rc' i.
Proof. intros Rc Rc' i G X. unfold RG, RGB in *. repeat rewrite (rec_calls_free.getr_eqv Rc Rc' _ X). exact G. Qed.

Lemma rgi_eqv : forall Rc Rc' i j, RGI Rc i j -> Regs6ss.xregs_eqv Rc Rc' -> RGI Rc' i j.
Proof. intros Rc Rc' i j G X. unfold RGI, RGB in *. repeat rewrite (rec_calls_free.getr_eqv Rc Rc' _ X). exact G. Qed.

Lemma pres_eqv : forall Rc Rc', regs_preserved regs Rc -> Regs6ss.xregs_eqv Rc Rc' -> regs_preserved regs Rc'.
Proof. intros Rc Rc' P X r Hr. rewrite (rec_calls_free.getr_eqv Rc Rc' _ X). exact (P r Hr). Qed.

Lemma run_ka : forall Rc pc mc mdc (Q : machine_state -> Prop),
  m_halted mdc = None -> m_vm_lazy mdc = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of Rc) fp_regs pc fp_csr None mc (seg_rom rsegs)) ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR rsegs (mkCfg ms' mdc) POST) ->
  SR (ms_segs B) (mkCfg (mkst Rc pc mc (seg_rom (ms_segs B))) mdc) POST.
Proof using SEGS.
  intros Rc pc mc mdc Q Hh Hl HE K. rewrite SEGS.
  eapply evt_SR_canon; [rewrite canon_mkst; exact HE | exact Hh | exact Hl | exact K].
Qed.

Definition FRM (mc : word -> option byte) : Prop :=
  rw_cells rsegs mc (bv_unsigned (getr regs 2) + -80)
    (FRC (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
         (getr regs 22) (getr regs 23) (getr regs 24)).

Definition XS (i j : nat) (c : rcall) : list (list byte) := rcc_args (firstn i (r_calls R)) ++ firstn j (snd c).

Lemma frm_keep : forall mc m', FRM mc ->
  (forall a, spZ regs - 80 <= a < spZ regs ->
     mbyte (ms_segs B) m' a = mbyte (ms_segs B) mc a /\
     (writable_at (ms_segs B) mc a <-> writable_at (ms_segs B) m' a)) ->
  FRM m'.
Proof using SEGS.
  intros mc m' FR KH. unfold FRM in *. rewrite <- SEGS in FR |- *. apply (rw_cells_transfer _ mc); [exact FR|].
  intros t Ht. cbn [cells_size csize FRC Nat.add] in Ht.
  destruct (KH (bv_unsigned (getr regs 2) + -80 + t)) as [E1 E2]; [unfold spZ; lia|].
  split; [exact E1 | apply E2].
Qed.

Lemma xs_step : forall i c Po j s opn Rc mc mdc Lc Ac qs Pn,
  nth_error (r_calls R) i = Some c ->
  call_at (ms_segs B) (blocks L A) mem (0x33d58 + 56 * Z.of_nat i) c Po ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c) ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  getr Rc 1 = Z_to_bv 64 0x15720 -> getr Rc 10 = Z_to_bv 64 (fst opn) -> RGI Rc i j -> FRM mc ->
  CHS (XS i j c) (concat qs ++ Pn) Lc Ac mc mdc -> DONE Lc Ac mc i qs -> HDR mc i c -> ARGS Lc Ac mc i c Pn ->
  DSTW mc ->
  (forall L2 A2 R2 m2 md2 p, RGI R2 i j -> getr R2 10 = Z_to_bv 64 p -> FRM m2 ->
     CHS (XS i (S j) c) ((concat qs ++ Pn) ++ [(p, Z.of_nat (length s) + 1)]) L2 A2 m2 md2 ->
     DONE L2 A2 m2 i qs -> HDR m2 i c -> ARGS L2 A2 m2 i c Pn -> DSTW m2 ->
     p <> 0 -> In (p, Z.of_nat (length s) + 1) (blocks L2 A2) -> fresh_block B p (Z.of_nat (length s) + 1) ->
     bytes_at (ms_segs B) m2 p (s ++ [Z_to_bv 8 0]) ->
     SR (ms_segs B) (mkCfg (mkst R2 (Z_to_bv 64 0x15720) m2 (seg_rom (ms_segs B))) md2) POST) ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 XSTRDUP) mc (seg_rom (ms_segs B))) mdc) POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO SLACK XSD.
  intros i c Po j s opn Rc mc mdc Lc Ac qs Pn Hc CA FL Es Eo G1 G10 GI FR CH DN HD AG DW K.
  destruct pre_facts as (HM0 & HCE & H63 & HAL & HRA & HWA & HTP).
  pose proof alloc_ceiling_val as AC.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  destruct (ka_hyps ltac:(lia)) as (H16 & HSW & HDW & HDN & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (CK j s opn Es Eo) as (OB & ONZ & OIN & OSZ & OBY & ON0).
  assert (LX : Z.of_nat (length s) <= LMAX) by (rewrite Forall_forall in FL; apply FL; eapply nth_error_In; exact Es).
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & HWc).
  destruct (mc_misc _ _ _ _ _ _ CH) as (HROc & HRESc & HBc & HINc).
  destruct opn as [q k]. cbn [fst snd] in *.
  assert (QIN : In (q, k) (blocks Lc Ac)) by exact (old_in _ _ _ _ _ _ CH _ OIN).
  pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc q k 0 HMc QIN ltac:(lia)) as (_ & Q1 & Q2 & _).
  assert (SBY : bytes_at (ms_segs B) mc q (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer _ mem); [exact OBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    apply (old_kept _ _ _ _ _ _ CH q k t OIN). lia. }
  rewrite SEGS in SBY.
  destruct (slack_rebuild' mc q s SBY ltac:(lia) ltac:(lia)) as (slack & SBS & SAL & SEND).
  { intros a Ha. destruct (Z_lt_ge_dec a (q + k)) as [D|D].
    - replace a with (q + (a - q)) by ring.
      exact (proj1 (block_facts B _ (aa_laws API) Lc Ac mc mdc q k (a - q) HMc QIN ltac:(lia))).
    - apply (SLACK Lc Ac mc mdc q k a HMc QIN). split; [lia|].
      pose proof (ceil8_mono (q + (Z.of_nat (length s) + 1)) (q + k) ltac:(lia)). lia. }
  assert (AC8 : alloc_ceiling mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (SPC : spZ Rc = spZ regs - 80).
  { destruct GI as ((G2 & _) & _). unfold spZ at 1. rewrite G2. change (bv_unsigned (getr regs 2)) with (spZ regs).
    unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. rewrite unsigned_lit; lia. }
  assert (G4 : getr Rc 4 = getr regs 4) by (destruct GI as ((_ & _ & G4 & _) & _); exact G4).
  assert (INITA : st_init_done A = true).
  { destruct (proj1 (YI04.blocks_In L A q k) OIN) as (p0 & _ & Hp0). exact (YI04.init_done_of_block A (p0, k) HWA Hp0). }
  assert (PREc : call_pre_k B (aa_MR API) XSTRDUP_K Lc Ac Rc mc mdc).
  { split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|].
    split; [rewrite G1; apply bv_eq; vm_compute; reflexivity|].
    unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *.
    split; [rewrite SPC; replace (spZ regs - 80) with (spZ regs + (-5) * 16) by ring; rewrite Z.mod_add by lia;
            exact HAL|].
    split; [rewrite SPC; lia|]. split; [rewrite SPC; lia|].
    split; [intros a Ha; rewrite SPC in Ha; apply (mc_scr _ _ _ _ _ _ CH); left; unfold RCC_K, XSTRDUP_K, ALLOC_STACK;
            lia|].
    split; [rewrite G4; exact HTP|].
    split; [intros a Ha; apply (mc_scr _ _ _ _ _ _ CH); right; exact Ha|].
    intros Hni. rewrite (HINc INITA) in Hni. discriminate. }
  pose proof XSD as XSc. unfold xstrdup_contract in XSc. rewrite <- SEGS in SBS.
  eapply SR_bind.
  { apply (XSc Lc Ac Rc mc mdc q s slack (rcc_b b (XS i j c)) PREc G10 SBS ON0 LX SAL).
    - rewrite SPC. left. unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. rewrite SEND.
      pose proof (ceil8_le (q + (Z.of_nat (length s) + 1)) alloc_ceiling ltac:(lia) AC8). lia.
    - rewrite SPC. unfold str_home. right. left. exists q, k. split; [exact QIN | lia].
    - exact HRESc.
    - exact (rcc_room b (r_calls R) i c j s Hc Es ROOM LX).
    - exact HROc. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & A0' & PNZ & PAL & FRESH & BL & BKP & UB & BYP & BYS
    & RA2 & GK2 & INIT2 & RGN2 & RES2).
  pose proof POST2 as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  pose proof FRESH as (FP1 & FP2 & FP3).
  destruct BL as (b1 & b2 & EB2 & EB1).
  assert (KH : forall a, spZ regs - 80 <= a < 2 ^ 64 ->
            mbyte (ms_segs B) m2 a = mbyte (ms_segs B) mc a /\
            (writable_at (ms_segs B) mc a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha. unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. apply PF.
    - left. lia.
    - intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho). lia.
    - intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a PM Ho). lia.
    - unfold scratch_k. rewrite SPC. intros [H|H]; lia.
    - cbv beta. lia. }
  assert (BINC : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L2 A2)).
  { intros pn Hpn. rewrite EB1 in Hpn. rewrite EB2. apply in_app_or in Hpn as [H|H]; apply in_or_app; [left | right; right];
      exact H. }
  assert (BKEEP : forall q0 k0 t, In (q0, k0) (blocks Lc Ac) -> 0 <= t < k0 ->
            mbyte (ms_segs B) m2 (q0 + t) = mbyte (ms_segs B) mc (q0 + t)).
  { intros q0 k0 t Hq Ht. exact (BKP q0 k0 t Hq (fun F => F) Ht). }
  assert (DKEEP : forall t, 0 <= t < 56 * Z.of_nat (length (r_calls R)) ->
            mbyte (ms_segs B) m2 (dst + t) = mbyte (ms_segs B) mc (dst + t)).
  { intros t Ht. apply (KH (dst + t)). lia. }
  rewrite G1. apply (K L2 A2 R2 m2 md2 p).
  - exact (rgi_pres Rc R2 i j PR GI).
  - exact A0'.
  - apply (frm_keep mc); [exact FR|]. intros a Ha. apply KH. lia.
  - unfold CHS, XS. rewrite (rcc_xs_snoc (r_calls R) i c j s Es).
    eapply (mchain_x _ _ _ L A mem md b _ _ Lc Ac mc mdc Rc s p L2 A2 R2 m2 md2 HM0); [ | | exact CH | | | exact POST2
      | exact FRESH | exists b1, b2; split; [exact EB2 | exact EB1] | exact UB | exact RA2 | exact GK2 | exact INIT2
      | exact RGN2 | exact RES2].
    + exact HCE.
    + lia.
    + rewrite SPC. unfold RCC_K, XSTRDUP_K, ALLOC_STACK. lia.
    + rewrite SPC. lia.
  - apply (done_transfer Lc Ac mc); [exact DN | exact BINC | exact BKEEP |]. intros t Ht. apply DKEEP. lia.
  - apply (hdr_transfer mc); [exact HD|]. intros t Ht.
    replace (dst + 56 * Z.of_nat i + t) with (dst + (56 * Z.of_nat i + t)) by ring. apply DKEEP. lia.
  - pose proof (call_len i c Hc) as Hl6.
    apply (args_transfer Lc Ac mc); [exact AG | exact BINC | exact BKEEP |]. intros t Ht.
    replace (dst + 56 * Z.of_nat i + t) with (dst + (56 * Z.of_nat i + t)) by ring. apply DKEEP. lia.
  - intros t Ht. apply (proj1 (proj2 (KH (dst + t) ltac:(lia)))). exact (DW t Ht).
  - exact PNZ.
  - rewrite EB2. apply in_or_app. right. left. reflexivity.
  - exact FRESH.
  - exact BYP.
Qed.

Lemma glob_cells : forall m a cs, cells_wf cs -> bytes_at rsegs m a (cells_bytes cs) ->
  GLOB_LO <= a -> a + Z.of_nat (cells_size cs) <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs m a cs.
Proof.
  intros m a cs Hw Hb H1 H2. split; [split; assumption|].
  split; [unfold GLOB_LO in H1; lia|]. split; [unfold GLOB_LO in *; change (Z.of_nat GLOB_N) with 1020 in H2; lia|].
  intros t Ht. exact (glob_writable m (a + t) ltac:(lia)).
Qed.

Lemma rec_cells : forall xs N Lc Ac mc mdc a cs k, CHS xs N Lc Ac mc mdc -> cells_wf cs ->
  bytes_at (ms_segs B) mem a (cells_bytes cs) -> Z.of_nat (cells_size cs) = k ->
  GLOB_LO <= a -> a + k <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs mc a cs.
Proof using PRE GR A0 ARR GFACT GOWN SEGS.
  intros xs N Lc Ac mc mdc a cs k CH Hw Hb Hk H1 H2. apply glob_cells; [exact Hw | | exact H1 | lia].
  rewrite <- SEGS. apply (bytes_at_transfer _ mem); [exact Hb|]. intros t Ht.
  rewrite (cells_bytes_length cs Hw) in Ht.
  apply (glob_kept _ _ _ _ _ _ CH). apply glob_in. lia.
Qed.

Lemma dst_cells : forall mc (o : Z) (k : nat), DSTW mc -> (0 < length (r_calls R))%nat -> 0 <= o ->
  o + Z.of_nat k <= 56 * Z.of_nat (length (r_calls R)) ->
  exists junk, rw_cells rsegs mc (dst + o) [CB k junk].
Proof using PRE GR A0 ARR SEGS.
  intros mc o k DW Hn H1 H2. destruct (ka_hyps Hn) as (_ & HSW & HDW & _ & UC).
  destruct (dst_facts Hn) as (_ & D1 & D2).
  apply present_rw_cells; [lia | lia |]. intros t Ht. apply writable_hi_present; [lia|].
  rewrite <- SEGS. replace (dst + o + t) with (dst + (o + t)) by ring. apply DW. lia.
Qed.

Definition XW (X : Z) (cs : list cell) (mc m' : word -> option byte) : Prop :=
  rw_cells rsegs m' X cs /\ munch [(X, X + 8)] mc m' /\ wmono rsegs mc m'.

Lemma slot_store_common : forall xs N Lc Ac mc mdc m' X cs i c o,
  nth_error (r_calls R) i = Some c -> CHS xs N Lc Ac mc mdc -> FRM mc -> DSTW mc -> XW X cs mc m' ->
  X = dst + 56 * Z.of_nat i + o -> 0 <= o -> o + 8 <= 8 + 8 * Z.of_nat (length (snd c)) ->
  CHS xs N Lc Ac m' mdc /\ FRM m' /\ DSTW m' /\
  (forall q k t, In (q, k) (blocks Lc Ac) -> 0 <= t < k ->
     mbyte (ms_segs B) m' (q + t) = mbyte (ms_segs B) mc (q + t)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (X <= a < X + 8) -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) mc a).
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG.
  intros xs N Lc Ac mc mdc m' X cs i c o Hc CH FR DW (CW & MU & WM) HX Ho1 Ho2.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as (_ & HSW & HDW & HDN & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct pre_facts as (HM0 & HCE & H63 & _).
  assert (HCE' : alloc_ceiling + 8304 <= spZ regs) by (unfold RCC_K, XSTRDUP_K, ALLOC_STACK in HCE; exact HCE).
  pose proof alloc_ceiling_val as AC.
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & _).
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (X <= a < X + 8) -> outside [(X, X + 8)] a)
    by (intros a Ra Ha; apply outside_one; [exact Ra | exact Ha]).
  split.
  { apply (mchain_own _ _ _ L A mem md b xs N Lc Ac mc mdc m' [(X, X + 8)] CH MU); [rewrite SEGS; exact WM | | lia |].
    - unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia.
    - intros a Ra Hn. apply not_out1 in Hn. right. split.
      + exists i, c. split; [exact Hc | lia].
      + left. unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia. }
  split.
  { apply (frm_keep mc); [exact FR|]. intros a Ha.
    assert (Ow : outside [(X, X + 8)] a) by (apply OUT; unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *; lia).
    split; [exact (munch_mbyte _ _ _ _ a MU ltac:(lia) Ow) | exact (munch_writable _ _ _ _ a MU ltac:(lia) Ow)]. }
  split.
  { intros t Ht. rewrite <- SEGS in WM. apply WM. exact (DW t Ht). }
  split.
  { intros q k t Hq Ht. pose proof (block_facts B _ (aa_laws API) Lc Ac mc mdc q k t HMc Hq Ht) as (_ & B1 & B2 & _).
    apply (munch_mbyte _ _ _ _ _ MU); [lia|]. apply OUT; [lia|]. unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia. }
  intros a Ra Ha. exact (munch_mbyte _ _ _ _ a MU Ra (OUT a Ra Ha)).
Qed.

Lemma ar_store : forall xs N Lc Ac mc mdc m' i c j s pn qs Pn,
  nth_error (r_calls R) i = Some c -> nth_error (snd c) j = Some s -> length Pn = j ->
  CHS xs N Lc Ac mc mdc -> FRM mc -> DSTW mc -> DONE Lc Ac mc i qs -> HDR mc i c -> ARGS Lc Ac mc i c Pn ->
  fst pn <> 0 -> In pn (blocks Lc Ac) -> snd pn = Z.of_nat (length s) + 1 -> fresh_block B (fst pn) (snd pn) ->
  bytes_at (ms_segs B) mc (fst pn) (s ++ [Z_to_bv 8 0]) -> no0 s ->
  XW (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 (fst pn))] mc m' ->
  CHS xs N Lc Ac m' mdc /\ FRM m' /\ DSTW m' /\ DONE Lc Ac m' i qs /\ HDR m' i c /\ ARGS Lc Ac m' i c (Pn ++ [pn]).
Proof using PRE GR A0 ARR SEGS AX GOWN GFACT GOTG.
  intros xs N Lc Ac mc mdc m' i c j s pn qs Pn Hc Es HL CH FR DW DN HD AG PNZ PIN PSZ PFR PBY PN0 XWr.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  assert (Hj : (j < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as (_ & HSW & HDW & HDN & UC).
  rewrite UC in XWr.
  destruct (slot_store_common xs N Lc Ac mc mdc m' _ _ i c (8 + 8 * Z.of_nat j) Hc CH FR DW XWr ltac:(lia)
              ltac:(lia) ltac:(lia)) as (CH' & FR' & DW' & BK & KO).
  destruct XWr as (CW & _ & _).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  split; [exact CH'|]. split; [exact FR'|]. split; [exact DW'|].
  split.
  { apply (done_transfer Lc Ac mc); [exact DN | intros pn' H; exact H | exact BK |]. intros t Ht. apply KO; lia. }
  split.
  { apply (hdr_transfer mc); [exact HD|]. intros t Ht. apply KO; lia. }
  intros a s' pn' Es' Ep'.
  destruct (Nat.lt_ge_cases a j) as [Ha|Ha].
  - rewrite nth_error_app1 in Ep' by lia.
    apply (args_transfer_lt Lc Ac mc Lc Ac m' i c Pn AG (fun pn0 H => H) BK); [| exact Es' | exact Ep'].
    intros a' t Ha' Ht. apply KO; lia.
  - rewrite nth_error_app2 in Ep' by lia.
    destruct (a - length Pn)%nat as [|a0] eqn:E0; [|destruct a0; cbn in Ep'; discriminate].
    cbn in Ep'. injection Ep' as <-. assert (Ea : a = j) by lia. subst a.
    rewrite Es in Es'. injection Es' as <-.
    split.
    { apply rw8_bytes in CW. rewrite SEGS.
      replace (dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat j) with (dst + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) by lia.
      exact CW. }
    split; [exact PNZ|]. split; [exact PIN|]. split; [exact PSZ|]. split; [exact PFR|].
    split; [|exact PN0].
    apply (bytes_at_transfer _ mc); [exact PBY|]. intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    destruct pn as [q k]. cbn [fst snd] in *. apply (BK q k t PIN). lia.
Qed.

Lemma done_snoc : forall Lc Ac mc i qs c P, DONE Lc Ac mc i qs -> nth_error (r_calls R) i = Some c ->
  HDR mc i c -> ARGS Lc Ac mc i c P -> length P = length (snd c) -> DONE Lc Ac mc (S i) (qs ++ [P]).
Proof.
  intros Lc Ac mc i qs c P (HL & HD) Hc H1 H2 H3. split; [rewrite length_app; cbn [length]; lia|].
  intros i' c' P' Hc' HP'. destruct (Nat.lt_ge_cases i' i) as [Hlt|Hge].
  - rewrite nth_error_app1 in HP' by lia. exact (HD i' c' P' Hc' HP').
  - rewrite nth_error_app2 in HP' by lia.
    destruct (i' - length qs)%nat as [|a0] eqn:E0; [|destruct a0; cbn in HP'; discriminate].
    cbn in HP'. injection HP' as <-. assert (E : i' = i) by lia. subst i'.
    rewrite Hc in Hc'. injection Hc' as <-. split; [exact H3|]. split; [exact H1 | exact H2].
Qed.

Lemma concat_split : forall (qs : list (list (Z * Z))) i P, nth_error qs i = Some P ->
  concat qs = concat (firstn i qs) ++ P ++ concat (skipn (S i) qs).
Proof.
  intros qs i P H. rewrite <- (firstn_skipn (S i) qs) at 1. rewrite (rec_calls_free.firstn_snoc qs i P H).
  rewrite !concat_app. cbn [concat]. rewrite app_nil_r, app_assoc. reflexivity.
Qed.

Lemma nodup_mid : forall X P Y : list (Z * Z), NoDup (map fst (X ++ P ++ Y)) -> NoDup (map fst P).
Proof.
  intros X P Y H. rewrite !map_app in H. apply list_relations.list.NoDup_app in H as (_ & _ & H).
  apply list_relations.list.NoDup_app in H as (H & _ & _). exact H.
Qed.

Lemma O_old : forall pn, In pn O -> In pn (blocks L A).
Proof using GR.
  intros pn Hin. destruct GR as (Q & HR & HO).
  exact (rep_at_blocks (ms_segs B) _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)).
Qed.

Lemma ret_post : forall Rf mf mdf Lf Af qs, regs_preserved regs Rf ->
  getr Rf 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) ->
  CHS (rcc_args (r_calls R)) (concat qs) Lf Af mf mdf -> DONE Lf Af mf (length (r_calls R)) qs -> DSTW mf ->
  SR (ms_segs B) (mkCfg (mkst Rf (ret_pc (getr regs 1)) mf (seg_rom (ms_segs B))) mdf) POST.
Proof using PRE GR A0 ARR GFACT GOWN.
  intros Rf mf mdf Lf Af qs HR H10 CH (DL & DD) DW.
  destruct pre_facts as (HM0 & HCE & H63 & HAL & HRA & HWA & HTP).
  rewrite (ret_pc_of_ok _ HRA). apply SR_ret.
  pose proof CH as (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HPERM & HND & HDJ & HPOS & HBYTES
    & HFRAME & HSCR & HRO & HGK & HRES).
  exists Lf, Af, Rf, mf, mdf, qs. split; [reflexivity|].
  split; [exact (mchain_post _ _ _ L A regs mem md b _ _ Lf Af Rf mf mdf eq_refl CH HR)|].
  split; [exact H10|]. split; [exact DL|].
  split.
  { intros i c P Hc HP. destruct (DD i c P Hc HP) as (PL & (H1 & H2) & AG).
    destruct rep_facts as (_ & _ & RF). destruct (RF i c Hc) as (Po & (CF & CL & CP & _ & _ & _ & _) & FL).
    split.
    - split; [exact CF|]. split; [exact CL|]. split; [exact PL|].
      split; [unfold CALL_OFF_FN; rewrite Z.add_0_r; exact H1|]. split; [exact H2|].
      split.
      { apply (nodup_mid (concat (firstn i qs)) P (concat (skipn (S i) qs))).
        rewrite <- (concat_split qs i P HP). exact HND. }
      intros a s pn Es Ep. destruct (AG a s pn Es Ep) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      assert (LX : Z.of_nat (length s) <= LMAX)
        by (rewrite Forall_forall in FL; apply FL; eapply nth_error_In; exact Es).
      split; [unfold CALL_OFF_ARGS; exact P1|]. split; [exact P2|]. split; [exact P3|].
      split; [unfold LMAX in *; lia|]. split; [exact P6 | exact P7].
    - intros a s pn Es Ep. destruct (AG a s pn Es Ep) as (_ & _ & _ & P4 & P5 & _). split; [exact P4 | exact P5]. }
  split; [exact HPERM|]. split; [exact HND|]. split; [exact HDJ|].
  split; [intros a k t Hin _ Ht; exact (old_kept _ _ _ _ _ _ CH a k t Hin Ht)|].
  split; [intros q k Hq; exact (HSUB _ Hq)|].
  split.
  { unfold g_rec_rep in *. apply (rec_rep_frame (ms_segs B) G_REC REC_SC L A mem R O Lf Af mf GR).
    - intros a Ha.
      assert (Hg : in_globals frame_G a) by (apply fg_iff; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia).
      destruct (glob_kept _ _ _ _ _ _ CH a Hg) as [E1 E2]. split; [exact E1 | apply E2].
    - intros p n t Hp Ht. exact (old_kept _ _ _ _ _ _ CH p n t (O_old _ Hp) Ht).
    - intros pn Hpn. exact (old_in _ _ _ _ _ _ CH pn (O_old _ Hpn)). }
  split; [intros a Ha; exact (glob_kept _ _ _ _ _ _ CH a Ha)|].
  split; [exact DW|]. split; [exact HRO|]. split; [exact HGK|]. split; [exact HINIT|]. split; [exact HRG|].
  exact HRES.
Qed.

Definition QH (i : nat) (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (Z_to_bv 64 0x156e4) fp_csr None m' (seg_rom rsegs) /\ RG Rc i /\ X m'.

Definition QRET (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (ret_pc (getr regs 1)) fp_csr None m' (seg_rom rsegs) /\
    (regs_preserved regs Rc /\ getr Rc 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R)))) /\ X m'.

Definition QCALL (i j : nat) (pw : word) (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists Rc m', ms = MS Rc fp_regs (Z_to_bv 64 0x15780) fp_csr None m' (seg_rom rsegs) /\
    (getr Rc 1 = Z_to_bv 64 0x15720 /\ getr Rc 10 = pw /\ RGI Rc i j) /\ X m'.

Definition INV (i : nat) (cfg : config) : Prop :=
  exists Rc mc mdc Lc Ac qs, cfg = mkCfg (mkst Rc (Z_to_bv 64 0x156e4) mc (seg_rom (ms_segs B))) mdc /\
    RG Rc i /\ FRM mc /\ CHS (rcc_args (firstn i (r_calls R))) (concat qs) Lc Ac mc mdc /\ DONE Lc Ac mc i qs /\
    DSTW mc.

Definition NEXT (i : nat) : Prop :=
  (S i < length (r_calls R))%nat -> forall cfg, INV (S i) cfg -> SR (ms_segs B) cfg POST.

Lemma chs_end : forall i c qs Pn Lc Ac mc mdc, nth_error (r_calls R) i = Some c -> length Pn = length (snd c) ->
  CHS (XS i (length (snd c)) c) (concat qs ++ Pn) Lc Ac mc mdc ->
  CHS (rcc_args (firstn (S i) (r_calls R))) (concat (qs ++ [Pn])) Lc Ac mc mdc.
Proof.
  intros i c qs Pn Lc Ac mc mdc Hc HL CH. unfold XS in CH. rewrite firstn_all in CH.
  rewrite (rcc_args_snoc _ i c Hc), concat_app. cbn [concat]. rewrite app_nil_r. exact CH.
Qed.

Lemma inner : forall i c Po, nth_error (r_calls R) i = Some c ->
  call_at (ms_segs B) (blocks L A) mem (0x33d58 + 56 * Z.of_nat i) c Po ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c) -> NEXT i ->
  forall k j s opn Rc mc mdc Lc Ac qs Pn, (length (snd c) - S j = k)%nat ->
  nth_error (snd c) j = Some s -> nth_error Po j = Some opn ->
  getr Rc 1 = Z_to_bv 64 0x15720 -> getr Rc 10 = Z_to_bv 64 (fst opn) -> RGI Rc i j -> FRM mc ->
  CHS (XS i j c) (concat qs ++ Pn) Lc Ac mc mdc -> DONE Lc Ac mc i qs -> HDR mc i c -> ARGS Lc Ac mc i c Pn ->
  length Pn = j -> DSTW mc ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 XSTRDUP) mc (seg_rom (ms_segs B))) mdc) POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XSD.
  intros i c Po Hc CA FL NX k.
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  pose proof (call_len i c Hc) as Hl6.
  destruct (ka_hyps ltac:(lia)) as (HN0 & HSW0 & HDW0 & HDN0 & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct rep_facts as (H16 & NCB & _).
  pose proof CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  induction k as [|k IH]; intros j s opn Rc mc mdc Lc Ac qs Pn Hk Es Eo G1 G10 GI FR CH DN HD AG HL DW;
    (apply (xs_step i c Po j s opn Rc mc mdc Lc Ac qs Pn Hc CA FL Es Eo G1 G10 GI FR CH DN HD AG DW));
    intros L2 A2 R2 m2 md2 p GI2 A10 FR2 CH2 DN2 HD2 AG2 DW2 PNZ PIN PFR PBY;
    (assert (Hj : (j < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate));
    (destruct (CK j s opn Es Eo) as (_ & _ & _ & _ & _ & ON0));
    (destruct (mc_MR _ _ _ _ _ _ CH2) as (HM2 & _));
    (destruct (mr_model B _ (aa_laws API) _ _ _ _ HM2) as (Hh & Hl & _));
    (destruct HD2 as (HD2a & HD2b));
    (assert (SL2 : rw_cells rsegs m2 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)
                     [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))])
       by (rewrite UC, <- SEGS; apply rw2_intro; [exact HD2a | exact HD2b |]; intros t Ht;
           replace (dst + 56 * Z.of_nat i + t) with (dst + (56 * Z.of_nat i + t)) by ring; apply DW2; lia));
    (destruct (dst_cells m2 (8 + 56 * Z.of_nat i + 8 * Z.of_nat j) 8 DW2 ltac:(lia) ltac:(lia) ltac:(lia))
       as [jj AS2]);
    (replace (dst + (8 + 56 * Z.of_nat i + 8 * Z.of_nat j))
       with (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) in AS2 by lia);
    (assert (NC2 : rw_cells rsegs m2 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))])
       by (apply (rec_cells _ _ _ _ _ _ _ _ 4 CH2);
           [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact NCB | reflexivity | unfold GLOB_LO; lia
           | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia]));
    unfold FRM in FR2.
  - assert (HSj : S j = length (snd c)) by lia.
    assert (PIN' : In (p, Z.of_nat (length s) + 1) (blocks L2 A2)) by exact PIN.
    destruct (Nat.lt_ge_cases (S i) (length (r_calls R))) as [Hs|Hs].
    + apply (run_ka R2 _ m2 md2 (QH (S i) (XW (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j)
               [C8 (Z_to_bv 64 p)] m2)) Hh Hl).
      * rewrite (mkR_of_RGI R2 i j GI2), A10. eapply k_after_next.
        all: try exact FR2. all: try exact NC2. all: try exact SL2. all: try exact AS2. all: try assumption.
        all: try lia.
        intros m' AS' MU WM. intros. unfold QH. do 2 eexists. split; [reflexivity|].
        split; [eapply rg_mkR; reflexivity|]. exact (conj AS' (conj MU WM)).
      * intros ms' (can & (R0 & m' & -> & GR0 & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (ar_store _ _ L2 A2 m2 md2 m' i c j s (p, Z.of_nat (length s) + 1) qs Pn Hc Es HL CH2 FR2 DW2
                    DN2 (conj HD2a HD2b) AG2 PNZ PIN' eq_refl PFR PBY ON0 XX) as (CH3 & FR3 & DW3 & DN3 & HD3 & AG3).
        rewrite <- SEGS. apply NX; [exact Hs|].
        exists R', m', md2, L2, A2, (qs ++ [Pn ++ [(p, Z.of_nat (length s) + 1)]]). split; [reflexivity|].
        split; [exact (rg_eqv _ _ _ GR0 XR)|]. split; [exact FR3|].
        split.
        { apply (chs_end i c qs); [exact Hc | rewrite length_app; cbn [length]; lia |].
          rewrite <- HSj, app_assoc. exact CH3. }
        split; [|exact DW3].
        apply (done_snoc L2 A2 m' i qs c); [exact DN3 | exact Hc | exact HD3 | exact AG3 |].
        rewrite length_app. cbn [length]. lia.
    + apply (run_ka R2 _ m2 md2 (QRET (XW (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j)
               [C8 (Z_to_bv 64 p)] m2)) Hh Hl).
      * rewrite (mkR_of_RGI R2 i j GI2), A10. eapply k_after_last.
        all: try exact FR2. all: try exact NC2. all: try exact SL2. all: try exact AS2. all: try assumption.
        all: try lia.
        intros m' AS' MU WM. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
        split; [eapply pres_mkR; reflexivity|]. exact (conj AS' (conj MU WM)).
      * intros ms' (can & (R0 & m' & -> & (HP0 & H10) & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (ar_store _ _ L2 A2 m2 md2 m' i c j s (p, Z.of_nat (length s) + 1) qs Pn Hc Es HL CH2 FR2 DW2
                    DN2 (conj HD2a HD2b) AG2 PNZ PIN' eq_refl PFR PBY ON0 XX) as (CH3 & FR3 & DW3 & DN3 & HD3 & AG3).
        rewrite <- SEGS.
        assert (HSi : S i = length (r_calls R)) by lia.
        apply (ret_post R' m' md2 L2 A2 (qs ++ [Pn ++ [(p, Z.of_nat (length s) + 1)]])).
        -- exact (pres_eqv _ _ HP0 XR).
        -- rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact H10.
        -- rewrite <- (firstn_all (r_calls R)), <- HSi.
           apply (chs_end i c qs); [exact Hc | rewrite length_app; cbn [length]; lia |].
           rewrite <- HSj, app_assoc. exact CH3.
        -- rewrite <- HSi. apply (done_snoc L2 A2 m' i qs c); [exact DN3 | exact Hc | exact HD3 | exact AG3 |].
           rewrite length_app. cbn [length]. lia.
        -- exact DW3.
  - destruct (nth_error (snd c) (S j)) as [s'|] eqn:Es'; [|apply nth_error_None in Es'; lia].
    destruct (nth_error Po (S j)) as [opn'|] eqn:Eo'; [|apply nth_error_None in Eo'; lia].
    destruct (CK (S j) s' opn' Es' Eo') as (OB' & _).
    assert (RA2 : rw_cells rsegs m2 (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8) [C8 (Z_to_bv 64 (fst opn'))]).
    { apply (rec_cells _ _ _ _ _ _ _ _ 8 CH2); [cbn; tauto | | reflexivity | unfold GLOB_LO; lia
        | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      replace (0x33d60 + 56 * Z.of_nat i + 8 * Z.of_nat j + 8)
        with (0x33d58 + 56 * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat (S j)) by (unfold CALL_OFF_ARGS; lia).
      exact OB'. }
    assert (PIN' : In (p, Z.of_nat (length s) + 1) (blocks L2 A2)) by exact PIN.
    apply (run_ka R2 _ m2 md2 (QCALL i (S j) (Z_to_bv 64 (fst opn'))
             (XW (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 (Z_to_bv 64 p)] m2)) Hh Hl).
    + rewrite (mkR_of_RGI R2 i j GI2), A10. eapply k_after_call with (n := length (r_calls R)).
      all: try exact SL2. all: try exact AS2. all: try exact RA2. all: try assumption. all: try lia.
      intros m' AS' MU WM. intros. unfold QCALL. do 2 eexists. split; [reflexivity|].
      split; [eapply rgi_mkR; reflexivity|]. exact (conj AS' (conj MU WM)).
    + intros ms' (can & (R0 & m' & -> & (G1' & G10' & GI') & XX) & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (ar_store _ _ L2 A2 m2 md2 m' i c j s (p, Z.of_nat (length s) + 1) qs Pn Hc Es HL CH2 FR2 DW2
                  DN2 (conj HD2a HD2b) AG2 PNZ PIN' eq_refl PFR PBY ON0 XX) as (CH3 & FR3 & DW3 & DN3 & HD3 & AG3).
      rewrite <- SEGS.
      apply (IH (S j) s' opn' R' m' md2 L2 A2 qs (Pn ++ [(p, Z.of_nat (length s) + 1)])); [lia | exact Es' | exact Eo'
        | | | | exact FR3 | | exact DN3 | exact HD3 | exact AG3 | rewrite length_app; cbn [length]; lia | exact DW3].
      * rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact G1'.
      * rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact G10'.
      * exact (rgi_eqv _ _ _ _ GI' XR).
      * rewrite app_assoc. exact CH3.
Qed.

Lemma head : forall i Rc mc mdc Lc Ac qs, (i < length (r_calls R))%nat -> NEXT i -> RG Rc i -> FRM mc ->
  CHS (rcc_args (firstn i (r_calls R))) (concat qs) Lc Ac mc mdc -> DONE Lc Ac mc i qs -> DSTW mc ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 0x156e4) mc (seg_rom (ms_segs B))) mdc) POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XSD.
  intros i Rc mc mdc Lc Ac qs Hi NX GR0 FR CH DN DW.
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  destruct rep_facts as (H16 & NCB & RF). destruct (RF i c Hc) as (Po & CA & FL).
  pose proof CA as (CF & CL & CP & CB1 & CB2 & CND & CK).
  destruct (ka_hyps ltac:(lia)) as (HN0 & HSW0 & HDW0 & HDN0 & UC).
  destruct (dst_facts ltac:(lia)) as (_ & D1 & D2).
  destruct (mc_MR _ _ _ _ _ _ CH) as (HMc & HWc).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & _).
  assert (CF' : 0 <= fst c < 2 ^ 31) by (unfold REC_FN_COUNT in CF; lia).
  assert (RFc : rw_cells rsegs mc (0x33d10 + 56 * Z.of_nat i + 72)
                  [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))]).
  { apply (rec_cells _ _ _ _ _ _ _ _ 8 CH); [cbn; tauto | | reflexivity | unfold GLOB_LO; lia
      | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    - replace (0x33d10 + 56 * Z.of_nat i + 72) with (0x33d58 + 56 * Z.of_nat i + CALL_OFF_FN)
        by (unfold CALL_OFF_FN; lia). exact CB1.
    - rewrite length_le4. replace (0x33d10 + 56 * Z.of_nat i + 72 + Z.of_nat 4)
        with (0x33d58 + 56 * Z.of_nat i + CALL_OFF_NARGS) by (unfold CALL_OFF_NARGS; lia). exact CB2. }
  destruct (dst_cells mc (56 * Z.of_nat i) 8 DW ltac:(lia) ltac:(lia) ltac:(lia)) as [jk SL0].
  apply (rw_cells_split_CB rsegs _ _ [] 8%nat jk [] [4; 4]%nat) in SL0; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in SL0. rewrite <- UC in SL0.
  unfold FRM in FR.
  assert (XST : forall m' cs, XW (bv_unsigned (getr regs 10) + 56 * Z.of_nat i) cs mc m' ->
            XW (dst + 56 * Z.of_nat i) cs mc m') by (intros m' cs H; rewrite <- UC; exact H).
  destruct (snd c) as [|s0 rest] eqn:Esc.
  - assert (L0 : Z.of_nat (length (snd c)) = 0) by (rewrite Esc; reflexivity).
    cbn [length Z.of_nat] in RFc.
    assert (DONE1 : forall m', XW (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)
                                 [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)] mc m' ->
              FRM m' /\ CHS (rcc_args (firstn (S i) (r_calls R))) (concat (qs ++ [[]])) Lc Ac m' mdc /\
              DONE Lc Ac m' (S i) (qs ++ [[]]) /\ DSTW m').
    { intros m' XX. pose proof (XST _ _ XX) as XX'.
      destruct (slot_store_common _ _ Lc Ac mc mdc m' _ _ i c 0 Hc CH FR DW XX' ltac:(lia) ltac:(lia) ltac:(lia))
        as (CH' & FR' & DW' & BK & KO).
      destruct XX' as (CW & _ & _). apply rw2_bytes in CW as (CW1 & CW2 & _).
      split; [exact FR'|]. split.
      { rewrite (rcc_args_snoc _ i c Hc), Esc, app_nil_r, concat_app. cbn [concat]. rewrite !app_nil_r. exact CH'. }
      split; [|exact DW'].
      apply (done_snoc Lc Ac m' i qs c); [ | exact Hc | | | rewrite Esc; reflexivity].
      - apply (done_transfer Lc Ac mc); [exact DN | intros pn H; exact H | exact BK |]. intros t Ht. apply KO; lia.
      - rewrite <- SEGS in CW1, CW2. split; [exact CW1|]. rewrite L0. exact CW2.
      - intros a s pn _ Ep. destruct a; discriminate. }
    destruct (Nat.lt_ge_cases (S i) (length (r_calls R))) as [Hs|Hs].
    + apply (run_ka Rc _ mc mdc (QH (S i) (XW (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)
               [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)] mc)) Hh Hl).
      * rewrite (mkR_of_RG Rc i GR0). eapply k_head_skip_next.
        all: try exact FR. all: try exact RFc. all: try exact SL0. all: try assumption. all: try lia.
        intros m' SL' MU WM. intros. unfold QH. do 2 eexists. split; [reflexivity|].
        split; [eapply rg_mkR; reflexivity|]. exact (conj SL' (conj MU WM)).
      * intros ms' (can & (R0 & m' & -> & GR1 & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (DONE1 m' XX) as (FR' & CH' & DN' & DW').
        rewrite <- SEGS. apply NX; [exact Hs|].
        exists R', m', mdc, Lc, Ac, (qs ++ [[]]). split; [reflexivity|].
        split; [exact (rg_eqv _ _ _ GR1 XR)|]. split; [exact FR'|]. split; [exact CH'|]. split; [exact DN' | exact DW'].
    + apply (run_ka Rc _ mc mdc (QRET (XW (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)
               [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 0)] mc)) Hh Hl).
      * rewrite (mkR_of_RG Rc i GR0). eapply k_head_skip_last.
        all: try exact FR. all: try exact RFc. all: try exact SL0. all: try assumption. all: try lia.
        intros m' SL' MU WM. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
        split; [eapply pres_mkR; reflexivity|]. exact (conj SL' (conj MU WM)).
      * intros ms' (can & (R0 & m' & -> & (HP0 & H10) & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        destruct (DONE1 m' XX) as (FR' & CH' & DN' & DW').
        assert (HSi : S i = length (r_calls R)) by lia.
        rewrite <- SEGS. apply (ret_post R' m' mdc Lc Ac (qs ++ [[]])).
        -- exact (pres_eqv _ _ HP0 XR).
        -- rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact H10.
        -- rewrite <- (firstn_all (r_calls R)), <- HSi. exact CH'.
        -- rewrite <- HSi. exact DN'.
        -- exact DW'.
  - destruct Po as [|opn0 Po']; [cbn in CP; discriminate|].
    destruct (CK 0%nat s0 opn0 eq_refl eq_refl) as (OB0 & _).
    rewrite <- Esc in RFc, FL, CL.
    assert (RA0 : rw_cells rsegs mc (0x33d60 + 56 * Z.of_nat i) [C8 (Z_to_bv 64 (fst opn0))]).
    { apply (rec_cells _ _ _ _ _ _ _ _ 8 CH); [cbn; tauto | | reflexivity | unfold GLOB_LO; lia
        | unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      replace (0x33d60 + 56 * Z.of_nat i) with (0x33d58 + 56 * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat 0)
        by (unfold CALL_OFF_ARGS; lia).
      exact OB0. }
    assert (LP : (0 < length (s0 :: rest))%nat) by (cbn; lia).
    rewrite <- Esc in LP.
    apply (run_ka Rc _ mc mdc (QCALL i 0 (Z_to_bv 64 (fst opn0)) (XW (bv_unsigned (getr regs 10) + 56 * Z.of_nat i)
             [C4 (Z_to_bv 64 (fst c)); C4 (Z_to_bv 64 (Z.of_nat (length (snd c))))] mc)) Hh Hl).
    + rewrite (mkR_of_RG Rc i GR0). eapply k_head_call.
      all: try exact RFc. all: try exact RA0. all: try exact SL0. all: try assumption. all: try lia.
      intros m' SL' MU WM. intros. unfold QCALL. do 2 eexists. split; [reflexivity|].
      split; [eapply rgi_mkR; reflexivity|]. exact (conj SL' (conj MU WM)).
    + intros ms' (can & (R0 & m' & -> & (G1' & G10' & GI') & XX) & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      pose proof (XST _ _ XX) as XX'.
      destruct (slot_store_common _ _ Lc Ac mc mdc m' _ _ i c 0 Hc CH FR DW XX' ltac:(lia) ltac:(lia) ltac:(lia))
        as (CH' & FR' & DW' & BK & KO).
      destruct XX' as (CW & _ & _). apply rw2_bytes in CW as (CW1 & CW2 & _). rewrite <- SEGS in CW1, CW2.
      rewrite <- SEGS.
      apply (inner i c (opn0 :: Po') Hc CA FL NX (length (snd c) - 1) 0 s0 opn0 R' m' mdc Lc Ac qs []);
        [lia | rewrite Esc; reflexivity | reflexivity | | | | exact FR' | | | split; [exact CW1 | exact CW2] | | reflexivity
        | exact DW'].
      * rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact G1'.
      * rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact G10'.
      * exact (rgi_eqv _ _ _ _ GI' XR).
      * unfold XS. cbn [firstn]. rewrite !app_nil_r. exact CH'.
      * apply (done_transfer Lc Ac mc); [exact DN | intros pn H; exact H | exact BK |]. intros t Ht. apply KO; lia.
      * intros a s pn _ Ep. destruct a; discriminate.
Qed.

Lemma outer : forall k i cfg, (length (r_calls R) - i = S k)%nat -> INV i cfg -> SR (ms_segs B) cfg POST.
Proof using PRE GR A0 ARR ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XSD.
  induction k as [|k IH]; intros i cfg Hk (Rc & mc & mdc & Lc & Ac & qs & -> & GR0 & FR & CH & DN & DW);
    (apply (head i Rc mc mdc Lc Ac qs ltac:(lia)); [ | exact GR0 | exact FR | exact CH | exact DN | exact DW ]).
  - intros Hs. exfalso. lia.
  - intros Hs cfg' Hinv. apply (IH (S i) cfg'); [lia | exact Hinv].
Qed.

Lemma main_sr : SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 REC_CALLS_COPY) mem (seg_rom (ms_segs B))) md) POST.
Proof using PRE RO GR A0 ARR RES ROOM SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XSD.
  destruct pre_facts as (HM & HCE & H63 & HAL & HRA & HWA & HTP).
  pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & HWS & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  destruct rep_facts as (H16 & NCB & RF).
  pose proof alloc_ceiling_val as AC.
  pose proof (mchain_init (spZ regs) RCC_K (rcc_writes dst (r_calls R)) L A regs mem md b PRE RO RES eq_refl) as CH0.
  assert (NC0 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))]).
  { apply glob_cells; [cbn; tauto | | unfold GLOB_LO; lia | cbn; unfold GLOB_LO; change (Z.of_nat GLOB_N) with 1020; lia].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- SEGS. exact NCB. }
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct (present_rw_cells rsegs mem (bv_unsigned (getr regs 2) + -80) 80) as [junk FR0];
    [unfold spZ, RCC_K, XSTRDUP_K, ALLOC_STACK in *; lia | cbn; lia | |].
  { intros t Ht. cbn in Ht. apply writable_hi_present; [unfold spZ, RCC_K, XSTRDUP_K, ALLOC_STACK in *; lia|].
    rewrite <- SEGS. apply HWS. unfold spZ, RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia. }
  assert (FRAME : forall m', munch [(bv_unsigned (getr regs 2) + -80, bv_unsigned (getr regs 2))] mem m' ->
            wmono rsegs mem m' -> CHS [] [] L A m' md /\ DSTW m').
  { intros m' MU WM. split.
    - apply (mchain_own _ _ _ L A mem md b [] [] L A mem md m' _ CH0 MU); [rewrite SEGS; exact WM | | lia |].
      + unfold RCC_K, XSTRDUP_K, ALLOC_STACK in *. lia.
      + intros a Ra Hn. apply not_out1 in Hn. left. unfold spZ, RCC_K, XSTRDUP_K, ALLOC_STACK in *.
        lia.
    - intros t Ht. destruct (ARR t Ht) as [H1 H2]. unfold spZ in H1.
      assert (Ow : outside [(bv_unsigned (getr regs 2) + -80, bv_unsigned (getr regs 2))] (dst + t))
        by (apply outside_one; lia).
      exact (proj1 (munch_writable _ _ _ _ (dst + t) MU ltac:(lia) Ow) H2). }
  unfold REC_CALLS_COPY.
  destruct (Nat.eq_dec (length (r_calls R)) 0) as [E0|E0].
  - apply (run_ka regs _ mem md (QRET (fun m' => FRM m' /\
             munch [(bv_unsigned (getr regs 2) + -80, bv_unsigned (getr regs 2))] mem m' /\ wmono rsegs mem m')) Hh Hl).
    + assert (HSW0 : 2 ^ 20 <= bv_unsigned (getr regs 2) - 80) by (unfold spZ, RCC_K, XSTRDUP_K, ALLOC_STACK in *; lia).
      rewrite mkR_getr. eapply k_zero.
      all: try exact FR0. all: try exact NC0. all: try exact E0. all: try lia.
      intros m' FR' MU WM. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
      split; [eapply pres_mkR; reflexivity|]. exact (conj FR' (conj MU WM)).
    + intros ms' (can & (R0 & m' & -> & (HP0 & H10) & (FR' & MU & WM)) & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (FRAME m' MU WM) as (CH' & DW').
      apply length_zero_iff_nil in E0.
      rewrite <- SEGS. apply (ret_post R' m' md L A []).
      * exact (pres_eqv _ _ HP0 XR).
      * rewrite (rec_calls_free.getr_eqv R0 R' _ XR). exact H10.
      * rewrite E0. exact CH'.
      * split; [rewrite E0; reflexivity|]. intros i c P _ HP. destruct i; discriminate.
      * exact DW'.
  - apply (run_ka regs _ mem md (QH 0 (fun m' => FRM m' /\
             munch [(bv_unsigned (getr regs 2) + -80, bv_unsigned (getr regs 2))] mem m' /\ wmono rsegs mem m')) Hh Hl).
    + destruct (ka_hyps ltac:(lia)) as (HN0 & HSW0 & HDW0 & HDN0 & UC).
      rewrite mkR_getr. eapply k_pro.
      all: try exact FR0. all: try exact NC0. all: try assumption. all: try lia.
      intros m' FR' MU WM. intros. unfold QH. do 2 eexists. split; [reflexivity|].
      split; [eapply rg_mkR; reflexivity|]. exact (conj FR' (conj MU WM)).
    + intros ms' (can & (R0 & m' & -> & GR0 & (FR' & MU & WM)) & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      destruct (FRAME m' MU WM) as (CH' & DW').
      rewrite <- SEGS. apply (outer (length (r_calls R) - 1) 0); [lia|].
      exists R', m', md, L, A, []. split; [reflexivity|]. split; [exact (rg_eqv _ _ _ GR0 XR)|].
      split; [exact FR'|]. split; [exact CH'|]. split; [|exact DW'].
      split; [reflexivity|]. intros i c P _ HP. destruct i; discriminate.
Qed.

End Run.

Theorem rec_calls_copy_holds : rec_calls_copy_contract B API.
Proof using SEGS AX CTX GOWN GFACT ERRNO GOTG SLACK XSD.
  unfold rec_calls_copy_contract.
  intros L A regs mem md R O dst b PRE RO A0 GR ARR RES ROOM.
  exact (main_sr L A regs mem md R O dst b PRE RO A0 GR ARR RES ROOM).
Qed.

End SR.
