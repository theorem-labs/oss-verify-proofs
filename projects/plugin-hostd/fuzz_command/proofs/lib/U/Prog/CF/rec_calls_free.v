(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 779 of its 856 lines of code are new or changed and 471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/rec_clear.v, with its module paths, addresses and numbers changed; 1564 of its 1647 lines of code are new or changed and 773 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/rec_calls_copy.v, with its module paths, addresses and numbers changed; 921 of its 1112 lines of code are new or changed and 1456 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  destruct (Z.ltb_spec x (2 ^ 63)); [|lia]. destruct (Z.ltb_spec y (2 ^ 63)); [|lia]. reflexivity.
Qed.

Lemma eqb_small : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma addr56r : forall (x : word) (i : nat), (i <= 16)%nat ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3)) + bv_unsigned x)
  = Z_to_bv 64 (bv_unsigned x + 56 * Z.of_nat i).
Proof.
  intros x i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma snez1 : forall x : word, bv_unsigned x <> 0 -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof.
  intros x H. pose proof (zr_word x) as R. unfold inr64 in R.
  rewrite v_sltu_b2z, (unsigned_lit 0) by lia.
  replace (0 <? bv_unsigned x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma aligned1 : forall x : word, bv_unsigned x mod 8 = 0 ->
  v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned x) 7)) 1 = Z_to_bv 64 1.
Proof.
  intros x H. rewrite v_sltiu_b2z. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3) with 8. rewrite H. reflexivity.
Qed.

Lemma land11 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 1))) = Z_to_bv 64 1.
Proof. reflexivity. Qed.

Lemma seqz0 : forall X, 0 < X < 2^64 -> v_sltiu (Z_to_bv 64 X) 1 = Z_to_bv 64 0.
Proof.
  intros X HX. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (X <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma mask_pos : forall z, 0 < z < 2 ^ 63 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 z)))))
                     (bv_unsigned (Z_to_bv 64 z))) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_slt, c_lts. rewrite bv_lts_zero_l, (unsigned_lit z) by lia.
  replace (0 <? z) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  rewrite (unsigned_lit 1) by lia. rewrite unsigned_lit_wrap, Z.land_comm.
  replace ((0 - 1) mod 2 ^ 64) with (Z.ones 64) by reflexivity.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section KA.
Variables (sw cw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 : word) (F : bvmap 5 word)
  (fc : bv 32) (j0 : list byte).
Variable n : nat.
Hypothesis HN : (n <= 16)%nat.
Hypothesis HSW : 2 ^ 20 <= bv_unsigned sw - 112.
Hypothesis HCW : bv_unsigned cw + 56 * Z.of_nat n <= 2 ^ 64.
Hypothesis HAD : bv_unsigned cw + 56 * Z.of_nat n <= bv_unsigned sw - 112 \/ bv_unsigned sw <= bv_unsigned cw.
Hypothesis HNZ : bv_unsigned cw <> 0.
Hypothesis HA8 : bv_unsigned cw mod 8 = 0.

Definition FRC : list cell := [CB 8 j0; C8 s11_0; C8 s10_0; C8 s9_0; C8 s8_0; C8 s7_0; C8 s6_0; C8 s5_0; C8 s4_0;
  C8 s3_0; C8 s2_0; C8 s1_0; C8 s0_0; C8 ra0].

Definition nv (i : nat) : word := Z_to_bv 64 (18446744073709551615 - (bv_unsigned cw + 56 * Z.of_nat i + 8)).

Definition nfa (i : nat) : Z := bv_unsigned cw + 56 * Z.of_nat i + 4.

Definition st_oh (Q : machine_state -> Prop) (i : nat) (m : word -> option byte) : Prop :=
  forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y24 y25 y26 y27 y28 y29 y30 y31,
    Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp y5 y6 y7 cw (Z_to_bv 64 (Z.of_nat i)) y10 y11
               y12 y13 y14 y15 y16 y17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
               (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) y23 y24 y25 y26 y27 y28 y29 y30 y31)
          F (Z_to_bv 64 0x15b74) fc None m (seg_rom rsegs)).

Definition st_ret (Q : machine_state -> Prop) (m : word -> option byte) : Prop :=
  forall y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    Q (MS (mkR ra0 sw gp tp y5 y6 y7 s0_0 s1_0 y10 y11 y12 y13 y14 y15 y16 y17
               s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 y28 y29 y30 y31)
          F (ret_pc ra0) fc None m (seg_rom rsegs)).

Definition st_call (Q : machine_state -> Prop) (i a : nat) (pw : word) (m : word -> option byte) : Prop :=
  forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    Q (MS (mkR (Z_to_bv 64 0x15bbc) (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp y5 y6 y7 cw (Z_to_bv 64 (Z.of_nat i)) pw
               y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
               (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
               (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) (Z_to_bv 64 (8 * Z.of_nat a)) (Z_to_bv 64 (Z.of_nat a))
               (nv i) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) y28 y29 y30 y31)
          F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs)).

Lemma k_exit : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
    x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
  rw_cells rsegs m (bv_unsigned sw + -112) FRC -> st_ret Q m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15be4) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m FR HK.
  unfold FRC in FR.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  do 15 step.
  replace (Z_to_bv 64 (bv_unsigned sw + -112 + 112)) with sw by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  apply evt_done.
  exact (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_pro0 : forall (Q : machine_state -> Prop) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk,
  n = 0%nat ->
  rw_cells rsegs m (bv_unsigned sw + -112) [CB 8 j0; CB 104 junk] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC ->
     munch [(bv_unsigned sw + -112, bv_unsigned sw)] m m' -> wmono rsegs m m' -> st_ret Q m') ->
  evt rsegs Q (MS (mkR ra0 sw gp tp t0 t1 t2 s0_0 s1_0 cw (Z_to_bv 64 (Z.of_nat n)) a2 a3 a4 a5 a6 a7
                       s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15b08) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk Hn FR HK.
  pose proof (munch_refl [(bv_unsigned sw + -112, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  apply (rw_cells_split_CB rsegs _ _ [CB 8 j0] 104%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 15 step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb negb].
  eapply k_exit; [exact FR | exact (HK _ FR MU WM)].
Qed.

Lemma k_pro : forall (Q : machine_state -> Prop) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk,
  (0 < n)%nat ->
  rw_cells rsegs m (bv_unsigned sw + -112) [CB 8 j0; CB 104 junk] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC ->
     munch [(bv_unsigned sw + -112, bv_unsigned sw)] m m' -> wmono rsegs m m' -> st_oh Q 0 m') ->
  evt rsegs Q (MS (mkR ra0 sw gp tp t0 t1 t2 s0_0 s1_0 cw (Z_to_bv 64 (Z.of_nat n)) a2 a3 a4 a5 a6 a7
                       s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15b08) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk Hn FR HK.
  pose proof (munch_refl [(bv_unsigned sw + -112, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  apply (rw_cells_split_CB rsegs _ _ [CB 8 j0] 104%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 15 step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.of_nat n <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb].
  do 12 step.
  rewrite (snez1 cw HNZ), (aligned1 cw HA8), land11.
  rewrite (mask_pos (Z.of_nat n)) by lia.
  apply evt_done.
  replace (Z_to_bv 64 (bv_unsigned cw + 8)) with (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat 0)) by (f_equal; lia).
  exact (HK _ FR MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_oh : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27
    x28 x29 x30 x31 m (i : nat) (len : Z),
  (i < n)%nat -> 0 <= len <= 6 ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  (forall y11, evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i))
                (Z_to_bv 64 len) y11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1)
                (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1)
                (Z_to_bv 64 2147483647) (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) x24 x25 x26 x27
                x28 x29 x30 x31)
           F (Z_to_bv 64 0x15b98) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15b74) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 m i len Hi Hl NF HK.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  unfold nfa in NF.
  do 4 step.
  rewrite (addr56r cw i) by lia.
  step.
  rewrite seqz0 by lia.
  step. try if_false.
  step.
  replace (bv_ltu (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) cw) with false
    by (symmetry; unfold bv_ltu; rewrite unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  step. try if_false.
  step.
  rewrite sx32_small by lia.
  apply HK.
Qed.

Lemma k_tail_next : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27
    x28 x29 x30 x31 m (i : nat) (len : Z),
  (S i < n)%nat ->
  rw_cells rsegs m (bv_unsigned sw + -112) FRC ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC -> rw_cells rsegs m' (nfa i) [C4 (Z_to_bv 64 0)] ->
     munch [(nfa i, nfa i + 4)] m m' -> wmono rsegs m m' -> st_oh Q (S i) m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15bd0) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31 m i len Hi FR NF HK.
  unfold FRC, nfa in *.
  pose proof (munch_refl [(bv_unsigned cw + 56 * Z.of_nat i + 4, bv_unsigned cw + 56 * Z.of_nat i + 4 + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  do 2 step.
  rewrite eqb_small by lia.
  replace (Z.of_nat i =? 2147483647) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 3 step.
  rewrite eqb_small by lia.
  replace (Z.of_nat i + 1 =? Z.of_nat n) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  apply evt_done.
  replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (S i))) by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i + 56))
    with (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat (S i))) by (f_equal; lia).
  exact (HK _ FR NF MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_tail_last : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27
    x28 x29 x30 x31 m (i : nat) (len : Z),
  (S i = n)%nat ->
  rw_cells rsegs m (bv_unsigned sw + -112) FRC ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC -> rw_cells rsegs m' (nfa i) [C4 (Z_to_bv 64 0)] ->
     munch [(nfa i, nfa i + 4)] m m' -> wmono rsegs m m' -> st_ret Q m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15bd0) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31 m i len Hi FR NF HK.
  unfold FRC, nfa in *.
  pose proof (munch_refl [(bv_unsigned cw + 56 * Z.of_nat i + 4, bv_unsigned cw + 56 * Z.of_nat i + 4 + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  do 2 step.
  rewrite eqb_small by lia.
  replace (Z.of_nat i =? 2147483647) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 3 step.
  rewrite eqb_small by lia.
  replace (Z.of_nat i + 1 =? Z.of_nat n) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
  eapply k_exit; [exact FR | exact (HK _ FR NF MU WM)].
Qed.

Lemma k_oh_next : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27
    x28 x29 x30 x31 m (i : nat),
  (S i < n)%nat ->
  rw_cells rsegs m (bv_unsigned sw + -112) FRC ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 0)] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC -> rw_cells rsegs m' (nfa i) [C4 (Z_to_bv 64 0)] ->
     munch [(nfa i, nfa i + 4)] m m' -> wmono rsegs m m' -> st_oh Q (S i) m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15b74) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 m i Hi FR NF HK.
  eapply k_oh with (i := i) (len := 0); [lia | lia | exact NF |].
  intros y11. step.
  rewrite lts_small by lia. cbn [negb Z.ltb Z.compare].
  eapply k_tail_next; [exact Hi | exact FR | exact NF | exact HK].
Qed.

Lemma k_oh_last : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27
    x28 x29 x30 x31 m (i : nat),
  (S i = n)%nat ->
  rw_cells rsegs m (bv_unsigned sw + -112) FRC ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 0)] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC -> rw_cells rsegs m' (nfa i) [C4 (Z_to_bv 64 0)] ->
     munch [(nfa i, nfa i + 4)] m m' -> wmono rsegs m m' -> st_ret Q m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15b74) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 m i Hi FR NF HK.
  eapply k_oh with (i := i) (len := 0); [lia | lia | exact NF |].
  intros y11. step.
  rewrite lts_small by lia. cbn [negb Z.ltb Z.compare].
  eapply k_tail_last; [exact Hi | exact FR | exact NF | exact HK].
Qed.

Lemma k_in : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m
    (i a : nat) (len : Z) (pw w24 w25 w27 : word),
  (i < n)%nat -> Z.of_nat a < len <= 6 ->
  w24 = Z_to_bv 64 (8 * Z.of_nat a) -> w25 = Z_to_bv 64 (Z.of_nat a) ->
  w27 = Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) ->
  ov_read_bytes rsegs m (wa (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) 8 = Some (le8 pw) ->
  st_call Q i a pw m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) w24 w25 (nv i) w27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15bb0) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i a len pw w24 w25 w27 Hi Hl E24 E25 E27
    HS HK.
  subst w24 w25 w27.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  step.
  replace (bv_ltu (nv i) (Z_to_bv 64 (8 * Z.of_nat a))) with false
    by (symmetry; unfold bv_ltu, nv; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  do 2 step.
  apply evt_done.
  exact (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_oh_call : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27
    x28 x29 x30 x31 m (i : nat) (len : Z) (pw : word),
  (i < n)%nat -> 0 < len <= 6 ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  ov_read_bytes rsegs m (wa (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat 0)) 8 = Some (le8 pw) ->
  st_call Q i 0 pw m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647) x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x15b74) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 m i len pw Hi Hl NF HS HK.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  eapply k_oh with (i := i) (len := len); [lia | lia | exact NF |].
  intros y11. step.
  rewrite lts_small by lia.
  replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  do 5 step.
  match goal with |- context [Z_to_bv 64 (Z.lxor ?u 18446744073709551615)] =>
    replace (Z_to_bv 64 (Z.lxor u 18446744073709551615)) with (nv i)
      by (unfold nv; f_equal; rewrite ?unsigned_lit by lia; rewrite zb_lxor_ones by lia; lia)
  end.
  eapply k_in with (a := 0%nat) (len := len) (pw := pw);
    [exact Hi | lia | reflexivity | reflexivity | f_equal; lia | exact HS | exact HK].
Qed.

Lemma k_after_call : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
    x28 x29 x30 x31 m (i a : nat) (len : Z) (pw : word),
  (i < n)%nat -> Z.of_nat (S a) < len <= 6 ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  ov_read_bytes rsegs m (wa (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat (S a))) 8 = Some (le8 pw) ->
  st_call Q i (S a) pw m ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) (Z_to_bv 64 (8 * Z.of_nat a)) (Z_to_bv 64 (Z.of_nat a))
                (nv i) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) x28 x29 x30 x31)
           F (Z_to_bv 64 0x15bbc) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i a len pw Hi Hl NF HS HK.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  unfold nfa in NF.
  step.
  rewrite sx32_small by lia.
  do 4 step.
  rewrite lts_small by lia.
  replace (Z.of_nat a + 1 <? len) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  eapply k_in with (a := S a) (len := len) (pw := pw);
    [exact Hi | lia | f_equal; lia | f_equal; lia | f_equal; lia | exact HS | exact HK].
Qed.

Lemma k_after_next : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
    x28 x29 x30 x31 m (i a : nat) (len : Z),
  (S i < n)%nat -> Z.of_nat (S a) = len -> len <= 6 ->
  rw_cells rsegs m (bv_unsigned sw + -112) FRC ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC -> rw_cells rsegs m' (nfa i) [C4 (Z_to_bv 64 0)] ->
     munch [(nfa i, nfa i + 4)] m m' -> wmono rsegs m m' -> st_oh Q (S i) m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) (Z_to_bv 64 (8 * Z.of_nat a)) (Z_to_bv 64 (Z.of_nat a))
                (nv i) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) x28 x29 x30 x31)
           F (Z_to_bv 64 0x15bbc) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i a len Hi Hl Hl6 FR NF HK.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  pose proof NF as NF0. unfold nfa in NF.
  step.
  rewrite sx32_small by lia.
  do 4 step.
  rewrite lts_small by lia.
  replace (Z.of_nat a + 1 <? len) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  eapply k_tail_next; [exact Hi | exact FR | exact NF0 | exact HK].
Qed.

Lemma k_after_last : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
    x28 x29 x30 x31 m (i a : nat) (len : Z),
  (S i = n)%nat -> Z.of_nat (S a) = len -> len <= 6 ->
  rw_cells rsegs m (bv_unsigned sw + -112) FRC ->
  rw_cells rsegs m (nfa i) [C4 (Z_to_bv 64 len)] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -112) FRC -> rw_cells rsegs m' (nfa i) [C4 (Z_to_bv 64 0)] ->
     munch [(nfa i, nfa i + 4)] m m' -> wmono rsegs m m' -> st_ret Q m') ->
  evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sw + -112)) gp tp x5 x6 x7 cw (Z_to_bv 64 (Z.of_nat i)) x10 x11
                x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i))
                (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1) (Z_to_bv 64 2147483647)
                (Z_to_bv 64 (bv_unsigned cw + 56 * Z.of_nat i)) (Z_to_bv 64 (8 * Z.of_nat a)) (Z_to_bv 64 (Z.of_nat a))
                (nv i) (Z_to_bv 64 (bv_unsigned cw + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) x28 x29 x30 x31)
           F (Z_to_bv 64 0x15bbc) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m i a len Hi Hl Hl6 FR NF HK.
  pose proof (zr_word cw) as Rcw. unfold inr64 in Rcw.
  pose proof NF as NF0. unfold nfa in NF.
  step.
  rewrite sx32_small by lia.
  do 4 step.
  rewrite lts_small by lia.
  replace (Z.of_nat a + 1 <? len) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb].
  eapply k_tail_last; [exact Hi | exact FR | exact NF0 | exact HK].
Qed.

End KA.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB RecChain rec_calls_free_c.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.

Definition nzf (pn : Z * Z) : bool := negb (fst pn =? 0).
Definition nzl (pn : Z * Z) : list (Z * Z) := List.filter nzf [pn].

Lemma firstn_snoc : forall {X} (l : list X) a x, nth_error l a = Some x -> firstn (S a) l = firstn a l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|a] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - change (firstn (S (S a)) (y :: l)) with (y :: firstn (S a) l). rewrite (IH a x H). reflexivity.
Qed.

Lemma freed_S : forall ps i P, nth_error ps i = Some P -> freed (firstn (S i) ps) = freed (firstn i ps) ++ List.filter nzf P.
Proof.
  intros ps i P H. unfold freed. rewrite (firstn_snoc ps i P H), concat_app, List.filter_app. cbn [concat].
  rewrite app_nil_r. reflexivity.
Qed.

Lemma filter_S : forall (P : list (Z * Z)) a pn, nth_error P a = Some pn ->
  List.filter nzf (firstn (S a) P) = List.filter nzf (firstn a P) ++ nzl pn.
Proof. intros P a pn H. rewrite (firstn_snoc P a pn H), List.filter_app. reflexivity. Qed.

Lemma freed_split : forall ps i a P pn, nth_error ps i = Some P -> nth_error P a = Some pn ->
  exists rest, freed ps = (freed (firstn i ps) ++ List.filter nzf (firstn a P)) ++ nzl pn ++ rest.
Proof.
  intros ps i a P pn H1 H2.
  apply nth_error_split in H1 as (l1 & l2 & -> & <-).
  apply nth_error_split in H2 as (k1 & k2 & -> & <-).
  exists (List.filter nzf k2 ++ freed l2).
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  unfold freed, nzl. rewrite concat_app. cbn [concat].
  replace (k1 ++ pn :: k2) with (k1 ++ [pn] ++ k2) by reflexivity. rewrite !List.filter_app.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma nodup_split : forall (X Y : list (Z * Z)) pn, List.NoDup (map fst (X ++ nzl pn ++ Y)) -> fst pn <> 0 ->
  ~ In (fst pn) (map fst X).
Proof.
  intros X Y pn ND Hz Hin. unfold nzl, nzf in ND. cbn [List.filter] in ND.
  destruct (fst pn =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|]. cbn [negb] in ND.
  rewrite !map_app in ND. cbn [map app] in ND. apply List.NoDup_remove_2 in ND. apply ND. apply in_or_app. left. exact Hin.
Qed.

Lemma getr_eqv : forall R R' r, Regs6ss.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
  intros R R' r X. destruct (bv_eqb r 0) eqn:E.
  - unfold getr. rewrite E. reflexivity.
  - rewrite (getr_of_eqv R R' r X E). unfold getr. rewrite E. reflexivity.
Qed.

Lemma rw_cells_C4 : forall segs m a w, rw_cells segs m a [C4 w] -> Mem.bytes_at segs m a (le4 w).
Proof. intros segs m a w [[_ Hb] _]. cbn [cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rw_cells_wr : forall segs m a cs j, rw_cells segs m a cs -> 0 <= j < Z.of_nat (cells_size cs) ->
  writable_at segs m (a + j).
Proof. intros segs m a cs j [_ (_ & _ & H)] Hj. exact (H j Hj). Qed.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis FREE : free_contract B API.
Hypothesis FREE_NULL : free_null_contract B.

Lemma auxv_keep : forall sec lo m m',
  (forall x, lo <= x < 2 ^ 63 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  (forall x, ms_libc B + 8 <= x < ms_libc B + 16 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  auxv_pre B sec lo m -> auxv_pre B sec lo m'.
Proof.
  intros sec lo m m' Hhi Hlibc (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  exists av, ar. repeat split; try assumption.
  - intros k Hk. rewrite Hlibc by lia. apply H1. exact Hk.
  - intros k Hk j Hj. rewrite Hhi by lia. apply H2; assumption.
  - intros k Hk. rewrite Hhi by lia. apply H3. exact Hk.
  - intros k Hk. rewrite Hhi by lia. apply H4. exact Hk.
Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (c : Z)
  (ps : list (list (Z * Z))) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) RCF_K L A regs mem md.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis A0 : getr regs 10 = Z_to_bv 64 c.
Hypothesis A1 : getr regs 11 = Z_to_bv 64 (Z.of_nat (length ps)).
Hypothesis SLOTS : calls_slots B L A mem c ps.
Hypothesis NDF : List.NoDup (map fst (freed ps)).
Hypothesis C0 : 0 <= c.
Hypothesis CN : c + 56 * Z.of_nat (length ps) <= 2 ^ 64.
Hypothesis AL : (0 < length ps)%nat -> c <> 0 /\ c mod 8 = 0.
Hypothesis ARR : forall j, 0 <= j < 56 * Z.of_nat (length ps) -> spZ regs <= c + j \/ in_globals frame_G (c + j).
Hypothesis RES : res_ok_slots A b.

Definition NOF (Lc : layout) (Ac : astate) (mc : word -> option byte) : Prop :=
  st_init_done A = false -> Lc = L /\ Ac = A /\
    forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 112 <= x < spZ regs) -> ~ nargs_field c (length ps) x ->
      mbyte (ms_segs B) mc x = mbyte (ms_segs B) mem x.

Definition CH (F : list (Z * Z)) (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model) : Prop :=
  fchain B API (spZ regs) RCF_K (nargs_field c (length ps)) L A mem md b F Lc Ac mc mdc /\ NOF Lc Ac mc.

Definition FRM (mc : word -> option byte) : Prop :=
  exists j, rw_cells rsegs mc (bv_unsigned (getr regs 2) + -112)
    (FRC (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
         (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) j).

Definition NARGS (mc : word -> option byte) (i : nat) : Prop :=
  forall j P, nth_error ps j = Some P ->
    rw_cells rsegs mc (nfa (getr regs 10) j) [C4 (Z_to_bv 64 (if (j <? i)%nat then 0 else Z.of_nat (length P)))].

Definition RG (Rc : bvmap 5 word) (i : nat) : Prop :=
  getr Rc 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -112) /\ getr Rc 3 = getr regs 3 /\ getr Rc 4 = getr regs 4 /\
  getr Rc 8 = getr regs 10 /\ getr Rc 9 = Z_to_bv 64 (Z.of_nat i) /\ getr Rc 18 = Z_to_bv 64 1 /\
  getr Rc 19 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i) /\
  getr Rc 20 = Z_to_bv 64 (Z.of_nat (length ps)) /\ getr Rc 21 = Z_to_bv 64 1 /\
  getr Rc 22 = Z_to_bv 64 2147483647.

Definition RGI (Rc : bvmap 5 word) (i a : nat) : Prop :=
  RG Rc i /\ getr Rc 23 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i) /\
  getr Rc 24 = Z_to_bv 64 (8 * Z.of_nat a) /\ getr Rc 25 = Z_to_bv 64 (Z.of_nat a) /\
  getr Rc 26 = nv (getr regs 10) i /\
  getr Rc 27 = Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a).

Definition POST := rec_calls_free_ret B API L A regs mem md c ps b.

Lemma pre_facts : aa_MR API L A mem md /\ alloc_ceiling + RCF_K <= spZ regs /\ spZ regs < 2 ^ 63 /\
  spZ regs mod 16 = 0 /\ YK0s.ret_ok (getr regs 1).
Proof.
  destruct PRE as (HM & _ & _ & HRA & HAL & HCE & H63 & _). split; [exact HM|]. split; [exact HCE|].
  split; [exact H63|]. split; [exact HAL | exact HRA].
Qed.

Lemma arr_hi : forall j, 0 <= j < 56 * Z.of_nat (length ps) ->
  hi_img B (c + j) /\ ~ owned B L A (c + j) /\ ~ (spZ regs - RCF_K <= c + j < spZ regs) /\ ~ errw B (c + j).
Proof.
  intros j Hj. destruct pre_facts as (HM & HCE & H63 & _ & _). pose proof alloc_ceiling_val as AC.
  unfold RCF_K, ALLOC_STACK in *.
  destruct (ARR j Hj) as [H|H].
  - split; [unfold hi_img; left; lia|]. split; [intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ _ HM Ho); lia|].
    split; [lia|]. unfold errw. lia.
  - destruct (GFACT _ H) as (Hi & _ & _ & He). split; [unfold hi_img; right; exact Hi|]. split; [exact (GOWN _ _ _ _ _ HM H)|].
    apply fg_iff in H. split; [lia | exact He].
Qed.

Lemma c_lt : (0 < length ps)%nat -> 0 <= c < 2 ^ 64.
Proof. intros H. lia. Qed.

Lemma fin_post : forall Lf Af Rf mf mdf,
  CH (freed ps) Lf Af mf mdf ->
  regs_preserved regs Rf ->
  NARGS mf (length ps) ->
  POST (mkCfg (mkst Rf (getr regs 1) mf (seg_rom (ms_segs B))) mdf).
Proof.
  intros Lf Af Rf mf mdf (HC & NOFf) HR HN.
  destruct (fchain_post B API (spZ regs) RCF_K (nargs_field c (length ps)) L A regs mem md b (freed ps)
              Lf Af Rf mf mdf eq_refl HC HR) as (CP & PERM & BK & UK & US & ROf & GKf & INI & RGN & RESf).
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFR & _).
  destruct pre_facts as (HM & HCE & H63 & _ & _). pose proof alloc_ceiling_val as AC.
  exists Lf, Af, Rf, mf, mdf. split; [reflexivity|].
  split; [exact CP|]. split; [exact PERM|]. split; [exact BK|]. split; [exact UK|]. split; [exact US|].
  split.
  { intros i Hi. destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
    pose proof (c_lt ltac:(lia)) as HCL.
    pose proof (HN i P EP) as NF.
    replace (i <? length ps)%nat with true in NF by (symmetry; apply Nat.ltb_lt; exact Hi).
    unfold nfa in NF. rewrite A0, unsigned_lit in NF by lia. rewrite SEGS.
    split; [exact (rw_cells_C4 _ _ _ _ NF)|]. intros j Hj. exact (rw_cells_wr _ _ _ _ j NF ltac:(cbn; lia)). }
  split.
  { intros j Hj Hne. destruct (arr_hi j Hj) as (H1 & H2 & H3 & H4). exact (proj1 (HFR (c + j) H1 H2 H3 H4 Hne)). }
  split.
  { intros a Ha Hne. destruct (GFACT a Ha) as (Hi & _ & _ & He). apply HFR.
    - unfold hi_img. right. exact Hi.
    - exact (GOWN _ _ _ _ _ HM Ha).
    - apply fg_iff in Ha. unfold RCF_K, ALLOC_STACK in *. lia.
    - exact He.
    - exact Hne. }
  split; [exact ROf|]. split; [exact GKf|]. split; [exact INI|]. split; [exact RGN|].
  split; [|exact RESf].
  intros Hni. destruct (NOFf Hni) as (-> & -> & HMB). split; [reflexivity|]. split; [reflexivity|].
  intros lo Hlo1 Hlo2 HAX. apply (auxv_keep _ lo mem mf); [ | | exact HAX].
  - intros x Hx. apply HMB.
    + unfold spZ, RCF_K, ALLOC_STACK in *. lia.
    + unfold spZ in *. lia.
    + intros (i & Hi & Hr). lia.
  - intros x Hx.
    assert (Ho : owned B L A x) by (right; unfold static_owned; right; right; left; exact Hx).
    pose proof (owned_low B _ (aa_laws API) _ _ _ _ _ HM Ho) as Hlow.
    apply HMB.
    + lia.
    + unfold spZ, RCF_K, ALLOC_STACK in *. lia.
    + intros (i & Hi & Hr). destruct (arr_hi (x - c) ltac:(lia)) as (_ & Hno & _ & _). apply Hno.
      replace (c + (x - c)) with x by ring. exact Ho.
Qed.
Lemma fp_keep : forall Lc Ac Rc mc mdc q k L2 A2 R2 m2 md2 x,
  aa_MR API Lc Ac mc mdc ->
  call_post B (aa_MR API) Lc Ac Rc mc mdc (fun a => ptr_addr Lc q <= a < ptr_addr Lc q + k) L2 A2 R2 m2 md2 ->
  In (ptr_addr Lc q, k) (blocks Lc Ac) -> hi_img B x -> ~ owned B L A x -> ~ scratch B Rc x ->
  mbyte (ms_segs B) m2 x = mbyte (ms_segs B) mc x /\ (writable_at (ms_segs B) mc x <-> writable_at (ms_segs B) m2 x).
Proof.
  intros Lc Ac Rc mc mdc q k L2 A2 R2 m2 md2 x HMc (HM2 & _ & _ & _ & _ & _ & _ & HFR & _) INB Hx Hno Hns.
  destruct pre_facts as (HM & _).
  apply HFR; [exact Hx | exact (own_any B API AX CTX L A mem md Lc Ac mc mdc x HM HMc Hx Hno)
             | exact (own_any B API AX CTX L A mem md L2 A2 m2 md2 x HM HM2 Hx Hno) | exact Hns |].
  intros Hr. exact (block_not_hi_img B API AX Lc Ac mc mdc _ _ x HMc INB Hr Hx).
Qed.

Lemma rgi_pres : forall R R' i a, regs_preserved R R' -> RGI R i a -> RGI R' i a.
Proof.
  intros R R' i a HP ((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22) & G23 & G24 & G25 & G26 & G27).
  assert (E : forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) by exact HP.
  assert (CS : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27) -> callee_saved r)
    by (intros r Hr; exact Hr).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact (eq_trans (E 2 (CS 2 ltac:(lia))) G2)|].
    split; [exact (eq_trans (E 3 (CS 3 ltac:(lia))) G3)|].
    split; [exact (eq_trans (E 4 (CS 4 ltac:(lia))) G4)|].
    split; [exact (eq_trans (E 8 (CS 8 ltac:(lia))) G8)|].
    split; [exact (eq_trans (E 9 (CS 9 ltac:(lia))) G9)|].
    split; [exact (eq_trans (E 18 (CS 18 ltac:(lia))) G18)|].
    split; [exact (eq_trans (E 19 (CS 19 ltac:(lia))) G19)|].
    split; [exact (eq_trans (E 20 (CS 20 ltac:(lia))) G20)|].
    split; [exact (eq_trans (E 21 (CS 21 ltac:(lia))) G21)|].
    exact (eq_trans (E 22 (CS 22 ltac:(lia))) G22).
  - exact (eq_trans (E 23 (CS 23 ltac:(lia))) G23).
  - exact (eq_trans (E 24 (CS 24 ltac:(lia))) G24).
  - exact (eq_trans (E 25 (CS 25 ltac:(lia))) G25).
  - exact (eq_trans (E 26 (CS 26 ltac:(lia))) G26).
  - exact (eq_trans (E 27 (CS 27 ltac:(lia))) G27).
Qed.

Lemma free_step : forall i a P pn Lc Ac Rc mc mdc F,
  nth_error ps i = Some P -> nth_error P a = Some pn ->
  F = freed (firstn i ps) ++ List.filter nzf (firstn a P) ->
  getr Rc 1 = Z_to_bv 64 0x15bbc -> getr Rc 10 = Z_to_bv 64 (fst pn) -> RGI Rc i a -> FRM mc -> NARGS mc i ->
  CH F Lc Ac mc mdc ->
  (forall L2 A2 R2 m2 md2, RGI R2 i a -> FRM m2 -> NARGS m2 i -> CH (F ++ nzl pn) L2 A2 m2 md2 ->
     SR (ms_segs B) (mkCfg (mkst R2 (Z_to_bv 64 0x15bbc) m2 (seg_rom (ms_segs B))) md2) POST) ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 0x18ad0) mc (seg_rom (ms_segs B))) mdc) POST.
Proof.
  intros i a P pn Lc Ac Rc mc mdc F EP Epn EF G1 G10 GI FR NA HC K.
  pose proof (proj1 HC) as (HMc & HWc & HBc & _ & _ & _ & _ & _ & HPTR & HKEEP & _ & _ & _ & HSCR & HROc & _ & HRESc).
  destruct pre_facts as (HM0 & HCE & H63 & HAL & HRA).
  pose proof alloc_ceiling_val as AC.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & _).
  destruct SLOTS as (_ & SL). destruct (SL i P EP) as (LP & _ & _ & SLA). destruct (SLA a pn Epn) as (BYT & [Z0|INB]).
  - rewrite <- FREE_PC. eapply SR_bind.
    { apply FREE_NULL; [rewrite G1; apply bv_eq; vm_compute; reflexivity | rewrite G10, Z0; reflexivity | exact Hh | exact Hl]. }
    intros c' ->. rewrite G1. apply (K Lc Ac); [exact GI | exact FR | exact NA |].
    assert (NZ : nzl pn = []) by (unfold nzl, nzf; cbn [List.filter]; rewrite Z0; reflexivity).
    rewrite NZ, app_nil_r. exact HC.
  - pose proof INB as INB0. unfold blocks in INB. apply in_map_iff in INB as ([q k] & Eq & Hq). cbn [fst snd] in Eq.
    subst pn. cbn [fst snd] in *.
    pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q k HM0 Hq) as (Hq4 & Hqc).
    assert (HWA : WF A) by (destruct PRE as (_ & HWA & _); exact HWA).
    destruct (freed_split ps i a P (ptr_addr L q, k) EP Epn) as (rest & ER).
    assert (NIF : ~ In (ptr_addr L q) (map fst F)).
    { assert (NZq : ptr_addr L q <> 0) by lia.
      rewrite EF. rewrite ER in NDF. exact (nodup_split _ _ (ptr_addr L q, k) NDF NZq). }
    assert (KEEP : In (q, k) (user_blocks Ac)).
    { apply (HKEEP q k Hq). intros H. apply NIF. exact (in_map fst F _ H). }
    pose proof (HPTR q k KEEP) as PA.
    assert (SPC : spZ Rc = spZ regs - 112).
    { destruct GI as ((G2 & _) & _). unfold spZ at 1. rewrite G2. change (bv_unsigned (getr regs 2)) with (spZ regs).
      unfold RCF_K, ALLOC_STACK in *. rewrite unsigned_lit; lia. }
    assert (G4 : getr Rc 4 = getr regs 4) by (destruct GI as ((_ & _ & G4 & _) & _); exact G4).
    rewrite <- FREE_PC. eapply SR_bind.
    { eapply (FREE Lc Ac Rc mc mdc q k (rfree_b b F)); [ | exact HROc | exact KEEP | rewrite G10, PA; reflexivity | exact HRESc].
      split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|].
      split; [rewrite G1; apply bv_eq; vm_compute; reflexivity|].
      unfold RCF_K, ALLOC_STACK in *.
      split; [rewrite SPC; replace (spZ regs - 112) with (spZ regs + (-7) * 16) by ring; rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SPC; lia|]. split; [rewrite SPC; lia|].
      split; [intros x Hx; rewrite SPC in Hx; apply HSCR; left; lia|].
      split; [rewrite G4; destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & HTP & _); exact HTP|].
      split; [intros x Hx; apply HSCR; right; exact Hx|].
      intros Hni. rewrite (YI04.init_done_of_block Ac (q, k) HWc KEEP) in Hni. discriminate. }
    intros c' (L2 & A2 & R2 & m2 & md2 & -> & POSTF & BLK & BK2 & RO2 & GK2 & UBK & INI & RGN & RES2).
    rewrite G1.
    assert (INBc : In (ptr_addr Lc q, k) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (q, k); auto).
    pose proof POSTF as (_ & _ & _ & _ & _ & HPRES & _).
    apply (K L2 A2).
    + exact (rgi_pres Rc R2 i a HPRES GI).
    + unfold FRM in *. destruct FR as [jf FR]. exists jf.
      rewrite <- SEGS in FR |- *. apply (rw_cells_transfer _ mc); [exact FR|].
      intros t Ht. cbn [cells_size csize FRC Nat.add] in Ht.
      assert (Hx : hi_img B (bv_unsigned (getr regs 2) + -112 + t)).
      { unfold hi_img. left. change (bv_unsigned (getr regs 2)) with (spZ regs). unfold RCF_K, ALLOC_STACK in *. lia. }
      assert (Hno : ~ owned B L A (bv_unsigned (getr regs 2) + -112 + t)).
      { intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ _ HM0 Ho).
        change (bv_unsigned (getr regs 2)) with (spZ regs) in *. unfold RCF_K, ALLOC_STACK in *. lia. }
      assert (Hns : ~ scratch B Rc (bv_unsigned (getr regs 2) + -112 + t)).
      { unfold scratch. rewrite SPC. change (bv_unsigned (getr regs 2)) with (spZ regs).
        unfold RCF_K, ALLOC_STACK in *. intros [Hs|Hs]; lia. }
      destruct (fp_keep Lc Ac Rc mc mdc q k L2 A2 R2 m2 md2 _ HMc POSTF INBc Hx Hno Hns) as [E1 E2].
      split; [exact E1 | apply E2].
    + intros j P' EP'. pose proof (NA j P' EP') as NF. rewrite <- SEGS in NF |- *. apply (rw_cells_transfer _ mc); [exact NF|].
      intros t Ht. cbn [cells_size csize Nat.add] in Ht.
      assert (Hj : (j < length ps)%nat) by (apply nth_error_Some; rewrite EP'; discriminate).
      unfold nfa. rewrite A0. rewrite unsigned_lit by lia.
      replace (c + 56 * Z.of_nat j + 4 + t) with (c + (56 * Z.of_nat j + 4 + t)) by ring.
      destruct (arr_hi (56 * Z.of_nat j + 4 + t) ltac:(lia)) as (Hx & Hno & Hw & He).
      assert (Hns : ~ scratch B Rc (c + (56 * Z.of_nat j + 4 + t))).
      { unfold scratch. rewrite SPC. unfold RCF_K, ALLOC_STACK in *. intros [Hs|Hs]; [lia | exact (He Hs)]. }
      destruct (fp_keep Lc Ac Rc mc mdc q k L2 A2 R2 m2 md2 _ HMc POSTF INBc Hx Hno Hns) as [E1 E2].
      split; [exact E1 | apply E2].
    + assert (NZ : nzl (ptr_addr L q, k) = [(ptr_addr L q, k)]).
      { unfold nzl, nzf. cbn [List.filter fst]. replace (ptr_addr L q =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        reflexivity. }
      rewrite NZ. split.
      2: { intros Hni. exfalso. rewrite (YI04.init_done_of_block A (q, k) HWA Hq) in Hni. discriminate. }
      eapply (fchain_free B API AX CTX ERRNO); [exact HM0 | exact HCE | lia | exact (proj1 HC) | exact KEEP
        | rewrite SPC; unfold RCF_K, ALLOC_STACK; lia | rewrite SPC; lia | exact POSTF | exact BLK | exact RO2 | exact GK2
        | exact UBK | exact INI | exact RGN | exact RES2].
Qed.

Lemma mkR_of_getr : forall R : bvmap 5 word, Regs6ss.mkR_of R =
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
      (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
      (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
      (getr R 29) (getr R 30) (getr R 31).
Proof. reflexivity. Qed.

Lemma mkR_of_RG : forall Rc i, RG Rc i -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -112)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (getr regs 10) (Z_to_bv 64 (Z.of_nat i)) (getr Rc 10) (getr Rc 11) (getr Rc 12) (getr Rc 13)
      (getr Rc 14) (getr Rc 15) (getr Rc 16) (getr Rc 17) (Z_to_bv 64 1)
      (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ps)))
      (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (getr Rc 23) (getr Rc 24) (getr Rc 25) (getr Rc 26) (getr Rc 27)
      (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i (G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22).
  rewrite mkR_of_getr, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22. reflexivity.
Qed.

Lemma mkR_of_RGI : forall Rc i a, RGI Rc i a -> Regs6ss.mkR_of Rc =
  mkR (getr Rc 1) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -112)) (getr regs 3) (getr regs 4) (getr Rc 5) (getr Rc 6)
      (getr Rc 7) (getr regs 10) (Z_to_bv 64 (Z.of_nat i)) (getr Rc 10) (getr Rc 11) (getr Rc 12) (getr Rc 13)
      (getr Rc 14) (getr Rc 15) (getr Rc 16) (getr Rc 17) (Z_to_bv 64 1)
      (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ps)))
      (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i))
      (Z_to_bv 64 (8 * Z.of_nat a)) (Z_to_bv 64 (Z.of_nat a)) (nv (getr regs 10) i)
      (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a))
      (getr Rc 28) (getr Rc 29) (getr Rc 30) (getr Rc 31).
Proof.
  intros Rc i a ((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22) & G23 & G24 & G25 & G26 & G27).
  rewrite mkR_of_getr, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity.
Qed.

Lemma rg_mkR : forall i y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y24 y25 y26 y27 y28 y29 y30 y31 R,
  R = mkR y1 (Z_to_bv 64 (bv_unsigned (getr regs 2) + -112)) (getr regs 3) (getr regs 4) y5 y6 y7
        (getr regs 10) (Z_to_bv 64 (Z.of_nat i)) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 1)
        (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ps)))
        (Z_to_bv 64 1) (Z_to_bv 64 2147483647) y23 y24 y25 y26 y27 y28 y29 y30 y31 ->
  RG R i.
Proof. intros. subst R. unfold RG. repeat split. Qed.

Lemma rgi_mkR : forall i a pw y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 R,
  R = mkR (Z_to_bv 64 0x15bbc) (Z_to_bv 64 (bv_unsigned (getr regs 2) + -112)) (getr regs 3) (getr regs 4) y5 y6 y7
        (getr regs 10) (Z_to_bv 64 (Z.of_nat i)) pw y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 1)
        (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ps)))
        (Z_to_bv 64 1) (Z_to_bv 64 2147483647) (Z_to_bv 64 (bv_unsigned (getr regs 10) + 56 * Z.of_nat i))
        (Z_to_bv 64 (8 * Z.of_nat a)) (Z_to_bv 64 (Z.of_nat a)) (nv (getr regs 10) i)
        (Z_to_bv 64 (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) y28 y29 y30 y31 ->
  getr R 1 = Z_to_bv 64 0x15bbc /\ getr R 10 = pw /\ RGI R i a.
Proof. intros. subst R. unfold RGI, RG. repeat split. Qed.

Lemma pres_mkR : forall y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 R,
  R = mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) y5 y6 y7 (getr regs 8) (getr regs 9)
    y10 y11 y12 y13 y14 y15 y16 y17 (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
    (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) y28 y29 y30 y31 ->
  regs_preserved regs R.
Proof.
  intros. subst R. intros r Hr. unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

Lemma rg_eqv : forall R R' i, RG R i -> Regs6ss.xregs_eqv R R' -> RG R' i.
Proof. intros R R' i G X. unfold RG in *. repeat rewrite (getr_eqv R R' _ X). exact G. Qed.

Lemma rgi_eqv : forall R R' i a, RGI R i a -> Regs6ss.xregs_eqv R R' -> RGI R' i a.
Proof. intros R R' i a G X. unfold RGI, RG in *. repeat rewrite (getr_eqv R R' _ X). exact G. Qed.

Lemma pres_eqv : forall R R', regs_preserved regs R -> Regs6ss.xregs_eqv R R' -> regs_preserved regs R'.
Proof. intros R R' P X r Hr. rewrite (getr_eqv R R' _ X). exact (P r Hr). Qed.

Lemma run_ka : forall Rc pc mc mdc (Q : machine_state -> Prop),
  m_halted mdc = None -> m_vm_lazy mdc = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of Rc) fp_regs pc fp_csr None mc (seg_rom rsegs)) ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SR rsegs (mkCfg ms' mdc) POST) ->
  SR (ms_segs B) (mkCfg (mkst Rc pc mc (seg_rom (ms_segs B))) mdc) POST.
Proof.
  intros Rc pc mc mdc Q Hh Hl HE K. rewrite SEGS.
  eapply evt_SR_canon; [rewrite canon_mkst; exact HE | exact Hh | exact Hl | exact K].
Qed.

Lemma sw_low : 2 ^ 20 <= bv_unsigned (getr regs 2) - 112.
Proof.
  destruct pre_facts as (HM & HCE & H63 & _ & _). pose proof alloc_ceiling_val as AC.
  unfold spZ, RCF_K, ALLOC_STACK in *. lia.
Qed.

Lemma ka_hyps : (0 < length ps)%nat ->
  (length ps <= 16)%nat /\ 2 ^ 20 <= bv_unsigned (getr regs 2) - 112 /\
  bv_unsigned (getr regs 10) + 56 * Z.of_nat (length ps) <= 2 ^ 64 /\
  (bv_unsigned (getr regs 10) + 56 * Z.of_nat (length ps) <= bv_unsigned (getr regs 2) - 112 \/
   bv_unsigned (getr regs 2) <= bv_unsigned (getr regs 10)) /\
  bv_unsigned (getr regs 10) <> 0 /\ bv_unsigned (getr regs 10) mod 8 = 0 /\
  bv_unsigned (getr regs 10) = c.
Proof.
  intros HP. destruct pre_facts as (HM & HCE & H63 & _ & _). pose proof alloc_ceiling_val as AC.
  destruct SLOTS as (H16 & _). destruct (AL HP) as (NZ & A8).
  assert (UC : bv_unsigned (getr regs 10) = c) by (rewrite A0; apply unsigned_lit; lia).
  unfold spZ, RCF_K, ALLOC_STACK in *. rewrite UC.
  split; [exact H16|]. split; [lia|]. split; [lia|]. split; [|split; [exact NZ|split; [exact A8|reflexivity]]].
  destruct (ARR 0 ltac:(lia)) as [H|H]; [right; unfold spZ in H; lia|].
  left. apply fg_iff in H. lia.
Qed.
Lemma not_outside1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi);
    first [lia | exfalso; apply H; cbn; split; [lia | exact I]].
Qed.

Lemma rw_munch : forall segs m m' X cs W, rw_cells segs m X cs -> munch W m m' ->
  (forall t, 0 <= t < Z.of_nat (cells_size cs) -> 0 <= X + t < 2 ^ 64 /\ outside W (X + t)) -> rw_cells segs m' X cs.
Proof.
  intros segs m m' X cs W H MU HO. apply (rw_cells_transfer segs m); [exact H|]. intros t Ht.
  destruct (HO t Ht) as [R O]. split; [exact (munch_mbyte segs W m m' _ MU R O)|].
  exact (proj1 (munch_writable segs W m m' _ MU R O)).
Qed.

Lemma rw_C4_intro : forall segs m x w, Mem.bytes_at segs m x (le4 w) ->
  (forall t, 0 <= t < 4 -> writable_at segs m (x + t)) -> rw_cells segs m x [C4 w].
Proof.
  intros segs m x w HB HW. pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_le4 in BB.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - split; [lia|]. split; [cbn; lia|]. intros t Ht. exact (HW t ltac:(cbn in Ht; lia)).
Qed.

Lemma nargs_init : (0 < length ps)%nat -> NARGS mem 0.
Proof.
  intros HP j P EP. destruct (ka_hyps HP) as (_ & _ & _ & _ & _ & _ & UC). destruct SLOTS as (_ & SL).
  destruct (SL j P EP) as (_ & BY & WR & _).
  replace (j <? 0)%nat with false by reflexivity.
  unfold nfa. rewrite UC. rewrite SEGS in BY, WR. apply rw_C4_intro; [exact BY | exact WR].
Qed.

Lemma nargs_frame : forall m m' i, (0 < length ps)%nat -> NARGS m i ->
  munch [(bv_unsigned (getr regs 2) + -112, bv_unsigned (getr regs 2))] m m' -> NARGS m' i.
Proof.
  intros m m' i HP NA MU j P EP. destruct (ka_hyps HP) as (H16 & HSW & HCW & HAD & _ & _ & UC).
  pose proof (zr_word (getr regs 10)) as R10. unfold inr64 in R10.
  assert (Hj : (j < length ps)%nat) by (apply nth_error_Some; rewrite EP; discriminate).
  apply (rw_munch rsegs m m' _ _ _ (NA j P EP) MU). intros t Ht. cbn in Ht. unfold nfa.
  split; [lia|]. apply outside_one; lia.
Qed.

Lemma nargs_step : forall m m' i, (i < length ps)%nat -> NARGS m i ->
  rw_cells rsegs m' (nfa (getr regs 10) i) [C4 (Z_to_bv 64 0)] ->
  munch [(nfa (getr regs 10) i, nfa (getr regs 10) i + 4)] m m' -> NARGS m' (S i).
Proof.
  intros m m' i Hi NA NF MU j P EP.
  destruct (ka_hyps ltac:(lia)) as (H16 & HSW & HCW & HAD & _ & _ & UC).
  pose proof (zr_word (getr regs 10)) as R10. unfold inr64 in R10.
  assert (Hj : (j < length ps)%nat) by (apply nth_error_Some; rewrite EP; discriminate).
  destruct (Nat.eq_dec j i) as [->|Hne].
  - replace (i <? S i)%nat with true by (symmetry; apply Nat.ltb_lt; lia). exact NF.
  - replace (j <? S i)%nat with (j <? i)%nat
      by (destruct (Nat.ltb_spec j i); destruct (Nat.ltb_spec j (S i)); first [reflexivity | lia]).
    apply (rw_munch rsegs m m' _ _ _ (NA j P EP) MU). intros t Ht. cbn in Ht. unfold nfa.
    split; [lia|]. apply outside_one; lia.
Qed.

Lemma ch_model : forall F Lc Ac mc mdc, CH F Lc Ac mc mdc -> m_halted mdc = None /\ m_vm_lazy mdc = [].
Proof.
  intros F Lc Ac mc mdc HC. destruct (mr_model B _ (aa_laws API) _ _ _ _ (proj1 (proj1 HC))) as (Hh & Hl & _).
  split; assumption.
Qed.

Lemma ch_frame : forall F Lc Ac mc mdc m', CH F Lc Ac mc mdc ->
  munch [(bv_unsigned (getr regs 2) + -112, bv_unsigned (getr regs 2))] mc m' -> wmono rsegs mc m' ->
  CH F Lc Ac m' mdc.
Proof.
  intros F Lc Ac mc mdc m' (HC & NO) MU WM. destruct pre_facts as (HM & HCE & H63 & _). pose proof alloc_ceiling_val as AC.
  split.
  2: { intros Hni. destruct (NO Hni) as (E1 & E2 & HMB). split; [exact E1|]. split; [exact E2|].
       intros x Hx Hf Hn. rewrite <- (HMB x Hx Hf Hn). apply (munch_mbyte (ms_segs B) _ mc m' x MU Hx).
       apply outside_one; [exact Hx|]. unfold spZ in Hf. lia. }
  eapply (fchain_own B API SEGS AX GOWN GFACT GOTG); [exact HC | exact MU | rewrite SEGS; exact WM | | |].
  - unfold RCF_K, ALLOC_STACK in *. lia.
  - lia.
  - intros a Ha O. left. apply not_outside1 in O. unfold spZ, RCF_K, ALLOC_STACK in *. lia.
Qed.

Lemma ch_nf : forall F Lc Ac mc mdc m' i, (i < length ps)%nat -> CH F Lc Ac mc mdc ->
  munch [(nfa (getr regs 10) i, nfa (getr regs 10) i + 4)] mc m' -> wmono rsegs mc m' -> CH F Lc Ac m' mdc.
Proof.
  intros F Lc Ac mc mdc m' i Hi (HC & NO) MU WM. destruct pre_facts as (HM & HCE & H63 & _).
  pose proof alloc_ceiling_val as AC.
  destruct (ka_hyps ltac:(lia)) as (H16 & HSW & HCW & HAD & _ & _ & UC).
  split.
  2: { intros Hni. destruct (NO Hni) as (E1 & E2 & HMB). split; [exact E1|]. split; [exact E2|].
       intros x Hx Hf Hn. rewrite <- (HMB x Hx Hf Hn). apply (munch_mbyte (ms_segs B) _ mc m' x MU Hx).
       apply outside_one; [exact Hx|]. intros Hr. apply Hn. unfold nfa in Hr. rewrite UC in Hr.
       exists i. split; [exact Hi | lia]. }
  eapply (fchain_own B API SEGS AX GOWN GFACT GOTG); [exact HC | exact MU | rewrite SEGS; exact WM | | |].
  - unfold RCF_K, ALLOC_STACK in *. lia.
  - lia.
  - intros a Ha O. apply not_outside1 in O. unfold nfa in O. rewrite UC in O. right. split.
    + exists i. split; [exact Hi | lia].
    + destruct (ARR (a - c) ltac:(lia)) as [H|H].
      * left. unfold spZ, RCF_K, ALLOC_STACK in *. lia.
      * right. replace a with (c + (a - c)) by ring. exact H.
Qed.

Lemma slot_read : forall i P a pn F Lc Ac mc mdc, nth_error ps i = Some P -> nth_error P a = Some pn ->
  CH F Lc Ac mc mdc ->
  ov_read_bytes rsegs mc (wa (bv_unsigned (getr regs 10) + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a)) 8 =
    Some (le8 (Z_to_bv 64 (fst pn))).
Proof.
  intros i P a pn F Lc Ac mc mdc EP Ea HC.
  assert (Hi : (i < length ps)%nat) by (apply nth_error_Some; rewrite EP; discriminate).
  assert (Ha : (a < length P)%nat) by (apply nth_error_Some; rewrite Ea; discriminate).
  destruct (ka_hyps ltac:(lia)) as (H16 & HSW & HCW & HAD & _ & _ & UC).
  pose proof SLOTS as (_ & SL). destruct (SL i P EP) as (LP & _ & _ & SA). destruct (SA a pn Ea) as (BY & _).
  pose proof (proj1 HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFR & _).
  assert (BY' : Mem.bytes_at rsegs mc (c + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a) (le8 (Z_to_bv 64 (fst pn)))).
  { rewrite SEGS in BY. apply (bytes_at_transfer rsegs mem); [exact BY|]. intros t Ht. rewrite length_le8 in Ht.
    replace (c + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) with (c + (56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t)) by ring.
    destruct (arr_hi (56 * Z.of_nat i + 8 + 8 * Z.of_nat a + t) ltac:(lia)) as (H1 & H2 & H3 & H4).
    rewrite <- SEGS. apply (HFR _ H1 H2 H3 H4). intros (i' & Hi' & Hr). lia. }
  rewrite UC.
  replace (c + 8 + 56 * Z.of_nat i + 8 * Z.of_nat a) with (c + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a + Z.of_nat 0) by lia.
  rewrite (bytes_at_ov_read rsegs mc _ _ 0 8 BY') by (rewrite length_le8; lia).
  rewrite skipn_O. rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
Qed.

Definition XN (i : nat) (mc m' : word -> option byte) : Prop :=
  FRM m' /\ rw_cells rsegs m' (nfa (getr regs 10) i) [C4 (Z_to_bv 64 0)] /\
  munch [(nfa (getr regs 10) i, nfa (getr regs 10) i + 4)] mc m' /\ wmono rsegs mc m'.

Definition QOH (i : nat) (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists R m', ms = MS R fp_regs (Z_to_bv 64 0x15b74) fp_csr None m' (seg_rom rsegs) /\ RG R i /\ X m'.

Definition QRET (X : (word -> option byte) -> Prop) (ms : machine_state) : Prop :=
  exists R m', ms = MS R fp_regs (ret_pc (getr regs 1)) fp_csr None m' (seg_rom rsegs) /\ regs_preserved regs R /\ X m'.

Definition QCALL (i a : nat) (pw : word) (mc : word -> option byte) (ms : machine_state) : Prop :=
  exists R, ms = MS R fp_regs (Z_to_bv 64 0x18ad0) fp_csr None mc (seg_rom rsegs) /\
    getr R 1 = Z_to_bv 64 0x15bbc /\ getr R 10 = pw /\ RGI R i a.

Definition INV (i : nat) (cfg : config) : Prop :=
  exists Rc mc mdc Lc Ac, cfg = mkCfg (mkst Rc (Z_to_bv 64 0x15b74) mc (seg_rom (ms_segs B))) mdc /\
    RG Rc i /\ FRM mc /\ NARGS mc i /\ CH (freed (firstn i ps)) Lc Ac mc mdc.

Definition NEXT (i : nat) : Prop :=
  (S i < length ps)%nat -> forall cfg, INV (S i) cfg -> SR (ms_segs B) cfg POST.

Lemma inv_next : forall i R' mc m' mdc Lc Ac, (i < length ps)%nat -> RG R' (S i) -> XN i mc m' -> NARGS mc i ->
  CH (freed (firstn (S i) ps)) Lc Ac mc mdc ->
  INV (S i) (mkCfg (mkst R' (Z_to_bv 64 0x15b74) m' (seg_rom (ms_segs B))) mdc).
Proof.
  intros i R' mc m' mdc Lc Ac Hi GR (FR & NF & MU & WM) NA HC.
  exists R', m', mdc, Lc, Ac. split; [reflexivity|]. split; [exact GR|]. split; [exact FR|].
  split; [exact (nargs_step mc m' i Hi NA NF MU)|]. exact (ch_nf _ _ _ _ _ _ _ Hi HC MU WM).
Qed.

Lemma ret_post : forall i R' mc m' mdc Lc Ac, (S i = length ps)%nat -> regs_preserved regs R' -> XN i mc m' ->
  NARGS mc i -> CH (freed (firstn (S i) ps)) Lc Ac mc mdc ->
  SR (ms_segs B) (mkCfg (mkst R' (ret_pc (getr regs 1)) m' (seg_rom (ms_segs B))) mdc) POST.
Proof.
  intros i R' mc m' mdc Lc Ac HS HR (FR & NF & MU & WM) NA HC. destruct pre_facts as (_ & _ & _ & _ & HRA).
  rewrite (ret_pc_of_ok _ HRA). apply SR_ret. apply (fin_post Lc Ac); [ | exact HR | ].
  - rewrite HS, firstn_all in HC. exact (ch_nf _ _ _ _ _ _ i ltac:(lia) HC MU WM).
  - rewrite <- HS. exact (nargs_step mc m' i ltac:(lia) NA NF MU).
Qed.

Lemma inner : forall i P, nth_error ps i = Some P -> NEXT i ->
  forall k a pn Rc mc mdc Lc Ac, (length P - S a)%nat = k -> nth_error P a = Some pn ->
  getr Rc 1 = Z_to_bv 64 0x15bbc -> getr Rc 10 = Z_to_bv 64 (fst pn) -> RGI Rc i a -> FRM mc -> NARGS mc i ->
  CH (freed (firstn i ps) ++ List.filter nzf (firstn a P)) Lc Ac mc mdc ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 0x18ad0) mc (seg_rom (ms_segs B))) mdc) POST.
Proof.
  intros i P EP NX k. induction k as [|k IH]; intros a pn Rc mc mdc Lc Ac Hk Ea G1 G10 GI FR NA HC;
    (apply (free_step i a P pn Lc Ac Rc mc mdc _ EP Ea eq_refl G1 G10 GI FR NA HC));
    intros L2 A2 R2 m2 md2 GI2 FR2 NA2 HC2;
    (assert (Hi : (i < length ps)%nat) by (apply nth_error_Some; rewrite EP; discriminate));
    (assert (Ha : (a < length P)%nat) by (apply nth_error_Some; rewrite Ea; discriminate));
    destruct (ka_hyps ltac:(lia)) as (HN0 & HSW0 & HCW0 & HAD0 & NZ0 & A80 & UC);
    (pose proof SLOTS as (_ & SL)); (destruct (SL i P EP) as (LP & _ & _ & _));
    (rewrite <- app_assoc, <- (filter_S P a pn Ea) in HC2);
    (destruct (ch_model _ _ _ _ _ HC2) as (Hh & Hl));
    (pose proof (NA2 i P EP) as NF); (replace (i <? i)%nat with false in NF by (symmetry; apply Nat.ltb_irrefl));
    cbv beta iota in NF.
  - assert (HSa : S a = length P) by lia.
    assert (HC3 : CH (freed (firstn (S i) ps)) L2 A2 m2 md2).
    { rewrite (freed_S ps i P EP). rewrite HSa, firstn_all in HC2. exact HC2. }
    destruct FR2 as [j2 FR2].
    destruct (Nat.lt_ge_cases (S i) (length ps)) as [Hs|Hs].
    + apply (run_ka R2 _ m2 md2 (QOH (S i) (XN i m2)) Hh Hl).
      * rewrite (mkR_of_RGI R2 i a GI2). eapply k_after_next.
        all: try exact FR2. all: try exact NF. all: try assumption. all: try lia.
        intros m' FR' NF' MU WM. intros. unfold QOH. do 2 eexists. split; [reflexivity|].
        split; [eapply rg_mkR; reflexivity|]. split; [unfold FRM; eexists; exact FR' | exact (conj NF' (conj MU WM))].
      * intros ms' (can & (R0 & m' & -> & GR0 & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        rewrite <- SEGS. apply NX; [exact Hs|].
        exact (inv_next i R' m2 m' md2 L2 A2 Hi (rg_eqv _ _ _ GR0 XR) XX NA2 HC3).
    + apply (run_ka R2 _ m2 md2 (QRET (XN i m2)) Hh Hl).
      * rewrite (mkR_of_RGI R2 i a GI2). eapply k_after_last.
        all: try exact FR2. all: try exact NF. all: try assumption. all: try lia.
        intros m' FR' NF' MU WM. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
        split; [eapply pres_mkR; reflexivity|]. split; [unfold FRM; eexists; exact FR' | exact (conj NF' (conj MU WM))].
      * intros ms' (can & (R0 & m' & -> & HP0 & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        rewrite <- SEGS. exact (ret_post i R' m2 m' md2 L2 A2 ltac:(lia) (pres_eqv _ _ HP0 XR) XX NA2 HC3).
  - destruct (nth_error P (S a)) as [pn'|] eqn:Ea'; [|apply nth_error_None in Ea'; lia].
    pose proof (slot_read i P (S a) pn' _ L2 A2 m2 md2 EP Ea' HC2) as HS.
    apply (run_ka R2 _ m2 md2 (QCALL i (S a) (Z_to_bv 64 (fst pn')) m2) Hh Hl).
    + rewrite (mkR_of_RGI R2 i a GI2). eapply k_after_call.
      all: try exact NF. all: try exact HS. all: try assumption. all: try lia.
      intros. unfold QCALL. eexists. split; [reflexivity|]. eapply rgi_mkR. reflexivity.
    + intros ms' (can & (R0 & -> & G1' & G10' & GI') & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      rewrite <- SEGS. apply (IH (S a) pn' R' m2 md2 L2 A2); [lia | exact Ea' | | | | exact FR2 | exact NA2 | exact HC2].
      * rewrite (getr_eqv R0 R' _ XR). exact G1'.
      * rewrite (getr_eqv R0 R' _ XR). exact G10'.
      * exact (rgi_eqv _ _ _ _ GI' XR).
Qed.

Lemma head : forall i Rc mc mdc Lc Ac, (i < length ps)%nat -> NEXT i -> RG Rc i -> FRM mc -> NARGS mc i ->
  CH (freed (firstn i ps)) Lc Ac mc mdc ->
  SR (ms_segs B) (mkCfg (mkst Rc (Z_to_bv 64 0x15b74) mc (seg_rom (ms_segs B))) mdc) POST.
Proof.
  intros i Rc mc mdc Lc Ac Hi NX GR FR NA HC.
  destruct (nth_error ps i) as [P|] eqn:EP; [|apply nth_error_None in EP; lia].
  destruct (ka_hyps ltac:(lia)) as (HN0 & HSW0 & HCW0 & HAD0 & NZ0 & A80 & UC).
  pose proof SLOTS as (_ & SL). destruct (SL i P EP) as (LP & _ & _ & _).
  destruct (ch_model _ _ _ _ _ HC) as (Hh & Hl).
  pose proof (NA i P EP) as NF. replace (i <? i)%nat with false in NF by (symmetry; apply Nat.ltb_irrefl).
  cbv beta iota in NF.
  destruct P as [|pn P'].
  - assert (HCS : CH (freed (firstn (S i) ps)) Lc Ac mc mdc)
      by (rewrite (freed_S ps i [] EP); cbn [List.filter]; rewrite app_nil_r; exact HC).
    destruct FR as [j0 FR].
    destruct (Nat.lt_ge_cases (S i) (length ps)) as [Hs|Hs].
    + apply (run_ka Rc _ mc mdc (QOH (S i) (XN i mc)) Hh Hl).
      * rewrite (mkR_of_RG Rc i GR). eapply k_oh_next.
        all: try exact FR. all: try exact NF. all: try assumption.
        intros m' FR' NF' MU WM. intros. unfold QOH. do 2 eexists. split; [reflexivity|].
        split; [eapply rg_mkR; reflexivity|]. split; [unfold FRM; eexists; exact FR' | exact (conj NF' (conj MU WM))].
      * intros ms' (can & (R0 & m' & -> & GR0 & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        rewrite <- SEGS. apply NX; [exact Hs|].
        exact (inv_next i R' mc m' mdc Lc Ac Hi (rg_eqv _ _ _ GR0 XR) XX NA HCS).
    + apply (run_ka Rc _ mc mdc (QRET (XN i mc)) Hh Hl).
      * rewrite (mkR_of_RG Rc i GR). eapply k_oh_last.
        all: try exact FR. all: try exact NF. all: try assumption. all: try lia.
        intros m' FR' NF' MU WM. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
        split; [eapply pres_mkR; reflexivity|]. split; [unfold FRM; eexists; exact FR' | exact (conj NF' (conj MU WM))].
      * intros ms' (can & (R0 & m' & -> & HP0 & XX) & EQ).
        destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
        rewrite <- SEGS. exact (ret_post i R' mc m' mdc Lc Ac ltac:(lia) (pres_eqv _ _ HP0 XR) XX NA HCS).
  - pose proof (slot_read i (pn :: P') 0 pn _ Lc Ac mc mdc EP eq_refl HC) as HS.
    apply (run_ka Rc _ mc mdc (QCALL i 0 (Z_to_bv 64 (fst pn)) mc) Hh Hl).
    + rewrite (mkR_of_RG Rc i GR). eapply k_oh_call.
      all: try exact NF. all: try exact HS. all: try assumption. all: try (cbn [length] in *; lia).
      intros. unfold QCALL. eexists. split; [reflexivity|]. eapply rgi_mkR. reflexivity.
    + intros ms' (can & (R0 & -> & G1' & G10' & GI') & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      rewrite <- SEGS. apply (inner i (pn :: P') EP NX (length P') 0 pn R' mc mdc Lc Ac); [cbn; lia | reflexivity | | | | exact FR | exact NA |].
      * rewrite (getr_eqv R0 R' _ XR). exact G1'.
      * rewrite (getr_eqv R0 R' _ XR). exact G10'.
      * exact (rgi_eqv _ _ _ _ GI' XR).
      * cbn [firstn List.filter]. rewrite app_nil_r. exact HC.
Qed.

Lemma outer : forall k i cfg, (length ps - i = S k)%nat -> INV i cfg -> SR (ms_segs B) cfg POST.
Proof.
  induction k as [|k IH]; intros i cfg Hk (Rc & mc & mdc & Lc & Ac & -> & GR & FR & NA & HC);
    (apply (head i Rc mc mdc Lc Ac ltac:(lia)); [ | exact GR | exact FR | exact NA | exact HC ]).
  - intros Hs. exfalso. lia.
  - intros Hs cfg' Hinv. apply (IH (S i) cfg'); [lia | exact Hinv].
Qed.

Lemma main_sr : SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 REC_CALLS_FREE) mem (seg_rom (ms_segs B))) md) POST.
Proof.
  destruct pre_facts as (HM & HCE & H63 & HAL & HRA).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (fchain_init B API (spZ regs) RCF_K (nargs_field c (length ps)) L A regs mem md b PRE RO RES eq_refl) as HF0.
  assert (HC0 : CH [] L A mem md).
  { split; [exact HF0|]. intros _. split; [reflexivity|]. split; [reflexivity|]. intros x _ _ _. reflexivity. }
  pose proof sw_low as HSW0.
  pose proof SLOTS as (HN0 & _).
  pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & HWS & _).
  destruct (present_rw_cells rsegs mem (bv_unsigned (getr regs 2) + -112) 112) as [junk FR0];
    [lia | unfold spZ in H63; cbn; lia | |].
  { intros t Ht. cbn in Ht. unfold spZ in H63. apply writable_hi_present; [lia|]. rewrite <- SEGS. apply HWS.
    unfold spZ, RCF_K, ALLOC_STACK. lia. }
  apply (rw_cells_split_CB rsegs _ _ [] 112%nat junk [] [8; 104]%nat) in FR0; [|reflexivity].
  cbn [mk_CB_cells app] in FR0.
  unfold REC_CALLS_FREE.
  destruct (Nat.eq_dec (length ps) 0) as [E0|E0].
  - apply (run_ka regs _ mem md
             (QRET (fun m' => FRM m' /\ munch [(bv_unsigned (getr regs 2) + -112, bv_unsigned (getr regs 2))] mem m' /\
                               wmono rsegs mem m')) Hh Hl).
    + rewrite mkR_of_getr, A1. eapply k_pro0.
      all: try exact FR0. all: try assumption. all: try lia.
      intros m' FR' MU WM. intros. unfold QRET. do 2 eexists. split; [reflexivity|].
      split; [eapply pres_mkR; reflexivity|]. split; [unfold FRM; eexists; exact FR' | exact (conj MU WM)].
    + intros ms' (can & (R0 & m' & -> & HP0 & (FR' & MU & WM)) & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      rewrite <- SEGS. rewrite (ret_pc_of_ok _ HRA). apply SR_ret.
      apply length_zero_iff_nil in E0.
      apply (fin_post L A); [ | exact (pres_eqv _ _ HP0 XR) | ].
      * rewrite E0. exact (ch_frame [] L A mem md m' HC0 MU WM).
      * intros j P EP. rewrite E0 in EP. destruct j; discriminate.
  - destruct (ka_hyps ltac:(lia)) as (HN1 & HSW1 & HCW0 & HAD0 & NZ0 & A80 & UC).
    apply (run_ka regs _ mem md
             (QOH 0 (fun m' => FRM m' /\ munch [(bv_unsigned (getr regs 2) + -112, bv_unsigned (getr regs 2))] mem m' /\
                               wmono rsegs mem m')) Hh Hl).
    + rewrite mkR_of_getr, A1. eapply k_pro.
      all: try exact FR0. all: try assumption. all: try lia.
      intros m' FR' MU WM. intros. unfold QOH. do 2 eexists. split; [reflexivity|].
      split; [eapply rg_mkR; reflexivity|]. split; [unfold FRM; eexists; exact FR' | exact (conj MU WM)].
    + intros ms' (can & (R0 & m' & -> & GR0 & (FR' & MU & WM)) & EQ).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & XR).
      rewrite <- SEGS. apply (outer (length ps - 1) 0); [lia|].
      exists R', m', md, L, A. split; [reflexivity|]. split; [exact (rg_eqv _ _ _ GR0 XR)|]. split; [exact FR'|].
      split; [exact (nargs_frame mem m' 0 ltac:(lia) (nargs_init ltac:(lia)) MU)|].
      exact (ch_frame [] L A mem md m' HC0 MU WM).
Qed.

End Run.

Theorem rec_calls_free_holds : rec_calls_free_contract B API.
Proof.
  unfold rec_calls_free_contract.
  intros L A regs mem md c ps b PRE RO A0 A1 SLOTS NDF C0 CN AL ARR RES.
  apply (main_sr L A regs mem md c ps b PRE RO A0 A1 SLOTS); try assumption.
  apply NoDup_ListNoDup. exact NDF.
Qed.

End SR.
