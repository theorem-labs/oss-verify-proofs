(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 779 of its 856 lines of code are new or changed and 471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/rec_clear.v, with its module paths, addresses and numbers changed; 1564 of its 1647 lines of code are new or changed and 773 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/rec_calls_copy.v, with its module paths, addresses and numbers changed; 243 of its 346 lines of code are new or changed and 1544 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c memcpy_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rk_addr56 : forall c (i : nat), (i <= 16)%nat ->
  Z_to_bv 64 (c + (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
                   bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3))))
  = Z_to_bv 64 (c + 56 * Z.of_nat i).
Proof.
  intros c i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma rk_mul56 : forall (i : nat), (i <= 16)%nat ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 6)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 3)))
  = Z_to_bv 64 (56 * Z.of_nat i).
Proof.
  intros i Hi. rewrite (unsigned_lit (Z.of_nat i)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6) with 64. change (2^3) with 8.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma rk_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rk_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rk_snez : forall x : word, bv_unsigned x <> 0 -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof.
  intros x H. pose proof (zr_word x) as R. unfold inr64 in R.
  rewrite v_sltu_b2z, (unsigned_lit 0) by lia.
  replace (0 <? bv_unsigned x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rk_aligned : forall x : word, bv_unsigned x mod 8 = 0 ->
  v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned x) 7)) 1 = Z_to_bv 64 1.
Proof.
  intros x H. rewrite v_sltiu_b2z. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3) with 8. rewrite H. reflexivity.
Qed.

Lemma rk_land11 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 1))) = Z_to_bv 64 1.
Proof. reflexivity. Qed.

Lemma rk_seqz0 : forall X, 0 < X < 2^64 -> v_sltiu (Z_to_bv 64 X) 1 = Z_to_bv 64 0.
Proof.
  intros X HX. rewrite v_sltiu_b2z, unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (X <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rk_app_split : forall segs m A k cs1 cs2, Z.of_nat (cells_size cs1) = k -> rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + k) cs2.
Proof.
  intros segs m A k cs1 cs2 Hk [[Hwf Hb] (W1 & W2 & W3)]. subst k.
  apply cells_wf_app in Hwf as [Hw1 Hw2]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 Hb2].
  rewrite cells_size_app in W2, W3. rewrite (cells_bytes_length cs1 Hw1) in Hb2.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by ring.
    apply W3. lia.
Qed.

Section KA.
Variables (sw dw ra0 gp tp s0_0 s1_0 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 : word)
  (F : bvmap 5 word) (fc : bv 32).
Variable n : nat.

Definition KOK : Prop :=
  (n <= 16)%nat /\ 2 ^ 20 <= bv_unsigned sw - 128 /\ bv_unsigned sw <= bv_unsigned dw /\
  bv_unsigned dw + 56 * Z.of_nat n <= 2 ^ 64.

Definition FRL : list cell := [C8 dw; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1)].

Definition FRS : list cell :=
  [C8 s11_0; C8 s10_0; C8 s9_0; C8 s8_0; C8 s7_0; C8 s6_0; C8 s5_0; C8 s4_0; C8 s3_0; C8 s2_0; C8 s1_0; C8 s0_0;
   C8 ra0].

Definition SPW : word := Z_to_bv 64 (bv_unsigned sw + -128).
Definition S7 (i : nat) : word := Z_to_bv 64 (0x34040 + 56 * Z.of_nat i).
Definition S8 (i : nat) : word := Z_to_bv 64 (bv_unsigned dw + 8 + 56 * Z.of_nat i).
Definition N4 (i : nat) : word := Z_to_bv 64 (18446744073709551615 - (bv_unsigned dw + 8 + 56 * Z.of_nat i)).
Definition N9 (i : nat) : word := Z_to_bv 64 (18446744073709551615 - (0x34040 + 56 * Z.of_nat i)).

Definition entry_ms (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) : machine_state :=
  MS (mkR ra0 sw gp tp t0 t1 t2 s0_0 s1_0 dw a1 a2 a3 a4 a5 a6 a7 s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0
          t3 t4 t5 t6)
     F (Z_to_bv 64 0x15c24) fc None m (seg_rom rsegs).

Definition head_ms (i : nat) (y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 : word)
    (m : word -> option byte) : machine_state :=
  MS (mkR y1 SPW gp tp y5 y6 y7 y8 y9 dw (Z_to_bv 64 (Z.of_nat n)) y12 y13 (Z_to_bv 64 0x33ff0) y15 y16 y17
          y18 y19 y20 (Z_to_bv 64 (Z.of_nat i)) y22 (S7 i) (S8 i) y25 y26 y27 y28 y29 y30 y31)
     F (Z_to_bv 64 0x15c94) fc None m (seg_rom rsegs).

Definition st_head (Q : machine_state -> Prop) (i : nat) (m : word -> option byte) : Prop :=
  forall y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31,
    Q (head_ms i y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m).

Definition st_tl (Q : machine_state -> Prop) (i : nat) (m : word -> option byte) : Prop :=
  forall y1 y5 y6 y7 y8 y9 y10 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31,
    evt rsegs Q (MS (mkR y1 SPW gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 (Z.of_nat n)) y12 y13 (Z_to_bv 64 0x33ff0)
                         y15 y16 y17 y18 y19 y20 (Z_to_bv 64 (Z.of_nat i)) y22 (S7 i) (S8 i) y25 y26 y27
                         y28 y29 y30 y31)
                    F (Z_to_bv 64 0x15d54) fc None m (seg_rom rsegs)).

Definition lp_ms (i j : nat) (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word)
    (m : word -> option byte) : machine_state :=
  MS (mkR y1 SPW gp tp y5 y6 y7 (Z_to_bv 64 0x33ff0) y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 (N4 i)
          (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j)) (S7 i) (S8 i) (N9 i) (Z_to_bv 64 (8 * Z.of_nat j))
          (Z_to_bv 64 (bv_unsigned dw + 56 * Z.of_nat i)) y28 y29 y30 y31)
     F (Z_to_bv 64 0x15d00) fc None m (seg_rom rsegs).

Definition st_lp (Q : machine_state -> Prop) (i j : nat) (m : word -> option byte) : Prop :=
  forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31,
    evt rsegs Q (lp_ms i j y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 m).

Definition st_xm (Q : machine_state -> Prop) (i j : nat) (len : Z) (pw : word) (m : word -> option byte) : Prop :=
  forall y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    Q (MS (mkR (Z_to_bv 64 0x15d20) SPW gp tp y5 y6 y7 (Z_to_bv 64 0x33ff0) y9 (Z_to_bv 64 (len + 1))
               y11 y12 y13 y14 y15 y16 y17 pw (Z_to_bv 64 (len + 1)) (N4 i) (Z_to_bv 64 (Z.of_nat i))
               (Z_to_bv 64 (Z.of_nat j)) (S7 i) (S8 i) (N9 i) (Z_to_bv 64 (8 * Z.of_nat j))
               (Z_to_bv 64 (bv_unsigned dw + 56 * Z.of_nat i)) y28 y29 y30 y31)
          F (Z_to_bv 64 0x15a88) fc None m (seg_rom rsegs)).

Definition af_ms (i j : nat) (len : Z) (pw : word) (p : Z)
    (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : word -> option byte) : machine_state :=
  MS (mkR y1 SPW gp tp y5 y6 y7 (Z_to_bv 64 0x33ff0) y9 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
          pw (Z_to_bv 64 (len + 1)) (N4 i) (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (Z.of_nat j)) (S7 i) (S8 i) (N9 i)
          (Z_to_bv 64 (8 * Z.of_nat j)) (Z_to_bv 64 (bv_unsigned dw + 56 * Z.of_nat i)) y28 y29 y30 y31)
     F (Z_to_bv 64 0x15d20) fc None m (seg_rom rsegs).

Definition st_ret (Q : machine_state -> Prop) (m : word -> option byte) : Prop :=
  forall y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    Q (MS (mkR ra0 sw gp tp y5 y6 y7 s0_0 s1_0 (Z_to_bv 64 (Z.of_nat n)) y11 y12 y13 y14 y15 y16 y17
               s2_0 s3_0 s4_0 s5_0 s6_0 s7_0 s8_0 s9_0 s10_0 s11_0 y28 y29 y30 y31)
          F (ret_pc ra0) fc None m (seg_rom rsegs)).

Lemma k_epi : forall (Q : machine_state -> Prop) x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17
    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
  KOK -> rw_cells rsegs m (bv_unsigned sw + -104) FRS -> st_ret Q m ->
  evt rsegs Q (MS (mkR x1 SPW gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (Z.of_nat n)) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15d68) fc None m (seg_rom rsegs)).
Proof.
  intros Q x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m OK FR HK.
  pose proof OK as (HN & HSW & HDW & HDN).
  unfold SPW, FRS in *.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  do 16 step.
  replace (Z_to_bv 64 (bv_unsigned sw + -128 + 128)) with sw by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  apply evt_done.
  exact (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_zero : forall (Q : machine_state -> Prop) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk,
  KOK -> n = 0%nat ->
  rw_cells rsegs m (bv_unsigned sw + -128) [CB 128 junk] ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -104) FRS ->
     munch [(bv_unsigned sw + -128, bv_unsigned sw)] m m' -> wmono rsegs m m' -> st_ret Q m') ->
  evt rsegs Q (entry_ms t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m).
Proof.
  intros Q t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk OK Hn FR NC HK.
  pose proof OK as (HN & HSW & HDW & HDN). unfold entry_ms.
  pose proof (munch_refl [(bv_unsigned sw + -128, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  apply (rw_cells_split_CB rsegs _ _ [] 128%nat junk [] [24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 17 step.
  rewrite rk_sx32 by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with false by (rewrite Hn; reflexivity). cbn [andb negb].
  destruct (rk_app_split rsegs _ _ 24 [CB 24 (firstn 24 junk)] FRS eq_refl FR) as [_ F2].
  replace (bv_unsigned sw + -128 + 24) with (bv_unsigned sw + -104) in F2 by lia.
  eapply k_epi; [exact OK | exact F2 | exact (HK _ F2 MU WM)].
Qed.

Lemma k_pro : forall (Q : machine_state -> Prop) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk,
  KOK -> (0 < n)%nat -> bv_unsigned dw mod 8 = 0 ->
  rw_cells rsegs m (bv_unsigned sw + -128) [CB 128 junk] ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n))] ->
  (forall m', rw_cells rsegs m' (bv_unsigned sw + -128) FRL -> rw_cells rsegs m' (bv_unsigned sw + -104) FRS ->
     munch [(bv_unsigned sw + -128, bv_unsigned sw)] m m' -> wmono rsegs m m' -> st_head Q 0 m') ->
  evt rsegs Q (entry_ms t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m).
Proof.
  intros Q t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m junk OK Hn HA8 FR NC HK.
  pose proof OK as (HN & HSW & HDW & HDN). unfold entry_ms.
  pose proof (munch_refl [(bv_unsigned sw + -128, bv_unsigned sw)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  apply (rw_cells_split_CB rsegs _ _ [] 128%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 17 step.
  rewrite rk_sx32 by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (0 <? Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (Z.of_nat n <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb].
  do 2 step.
  rewrite (rk_snez dw) by lia.
  do 4 step.
  rewrite (rk_aligned dw HA8).
  do 2 step.
  try rewrite rk_land11.
  do 2 step.
  destruct (rk_app_split rsegs _ _ 24 FRL FRS eq_refl FR) as [F1 F2].
  replace (bv_unsigned sw + -128 + 24) with (bv_unsigned sw + -104) in F2 by lia.
  apply evt_done.
  replace (Z_to_bv 64 (bv_unsigned dw + 8)) with (S8 0) by (unfold S8; f_equal; lia).
  exact (HK _ F1 F2 MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_head_call : forall (Q : machine_state -> Prop) (i : nat) (fn len : Z) j1 j2
    y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m,
  KOK -> (i < n)%nat -> 0 <= fn < 2 ^ 31 -> 0 < len < 2 ^ 31 ->
  rw_cells rsegs m (bv_unsigned sw + -128) FRL ->
  rw_cells rsegs m (0x33ff0 + 56 * Z.of_nat i + 72) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [CB 4 j1; CB 4 j2] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 len)] ->
     munch [(bv_unsigned dw + 56 * Z.of_nat i, bv_unsigned dw + 56 * Z.of_nat i + 8)] m m' -> wmono rsegs m m' ->
     st_lp Q i 0 m') ->
  evt rsegs Q (head_ms i y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m).
Proof.
  intros Q i fn len j1 j2 y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m
    OK Hi Hfn Hl FL RF SL HK.
  pose proof OK as (HN & HSW & HDW & HDN).
  unfold head_ms, SPW, FRL in *.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  do 2 step.
  rewrite rk_eqb by lia. replace (Z.of_nat i =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 4 step.
  rewrite rk_addr56 by lia.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  pose proof (munch_refl [(X, X + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  replace (bv_ltu (Z_to_bv 64 X) dw) with false
    by (symmetry; unfold bv_ltu; rewrite unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  step.
  rewrite rk_seqz0 by lia.
  do 3 step. if_false.
  do 2 step. if_false.
  do 2 step.
  rewrite rk_addr56 by lia.
  do 2 step.
  rewrite rk_sx32 by lia.
  step.
  rewrite rk_sx32 by lia.
  do 3 step.
  rewrite bv_lts_zero_l, (unsigned_lit len) by lia.
  replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (len <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb negb].
  do 6 step.
  subst X.
  rewrite (unsigned_lit (212976 + 56 * Z.of_nat i + 80)) by lia.
  rewrite (unsigned_lit (bv_unsigned dw + 56 * Z.of_nat i + 8)) by lia.
  rewrite !zb_lxor_ones by lia.
  replace (Z_to_bv 64 (18446744073709551615 - (212976 + 56 * Z.of_nat i + 80))) with (N9 i)
    by (unfold N9; f_equal; lia).
  replace (Z_to_bv 64 (18446744073709551615 - (bv_unsigned dw + 56 * Z.of_nat i + 8))) with (N4 i)
    by (unfold N4; f_equal; lia).
  exact (HK _ SL MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_head_skip : forall (Q : machine_state -> Prop) (i : nat) (fn : Z) j1 j2
    y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m,
  KOK -> (i < n)%nat -> 0 <= fn < 2 ^ 31 ->
  rw_cells rsegs m (bv_unsigned sw + -128) FRL ->
  rw_cells rsegs m (0x33ff0 + 56 * Z.of_nat i + 72) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (bv_unsigned dw + 56 * Z.of_nat i) [CB 4 j1; CB 4 j2] ->
  (forall m', rw_cells rsegs m' (bv_unsigned dw + 56 * Z.of_nat i) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] ->
     munch [(bv_unsigned dw + 56 * Z.of_nat i, bv_unsigned dw + 56 * Z.of_nat i + 8)] m m' -> wmono rsegs m m' ->
     st_tl Q i m') ->
  evt rsegs Q (head_ms i y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m).
Proof.
  intros Q i fn j1 j2 y1 y5 y6 y7 y8 y9 y12 y13 y15 y16 y17 y18 y19 y20 y22 y25 y26 y27 y28 y29 y30 y31 m
    OK Hi Hfn FL RF SL HK.
  pose proof OK as (HN & HSW & HDW & HDN).
  unfold head_ms, SPW, FRL in *.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  do 2 step.
  rewrite rk_eqb by lia. replace (Z.of_nat i =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 4 step.
  rewrite rk_addr56 by lia.
  remember (bv_unsigned dw + 56 * Z.of_nat i) as X eqn:HX.
  pose proof (munch_refl [(X, X + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  replace (bv_ltu (Z_to_bv 64 X) dw) with false
    by (symmetry; unfold bv_ltu; rewrite unsigned_lit by lia; apply Z.ltb_ge; lia).
  cbv iota.
  step.
  rewrite rk_seqz0 by lia.
  do 3 step. if_false.
  do 2 step. if_false.
  do 2 step.
  rewrite rk_addr56 by lia.
  do 2 step.
  rewrite rk_sx32 by lia.
  step.
  try rewrite rk_sx32 by lia.
  do 3 step.
  rewrite bv_lts_zero_l, (unsigned_lit 0) by lia.
  replace (0 <? 0) with false by reflexivity. cbn [andb negb].
  subst X.
  exact (HK _ SL MU WM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.

Lemma k_loop : strlen_contract -> forall (Q : machine_state -> Prop) (i j : nat) (pw : word) (str slack : list byte)
    y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 m,
  KOK -> (i < n)%nat -> (j < 6)%nat ->
  rw_cells rsegs m (0x34040 + 56 * Z.of_nat i + 8 * Z.of_nat j) [C8 pw] ->
  bytes_at rsegs m (bv_unsigned pw) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  (- (bv_unsigned pw + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  mem_inv rsegs m ->
  (forall m', munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bytes_at rsegs m' (bv_unsigned pw) (str ++ Z_to_bv 8 0 :: slack) ->
     st_xm Q i j (Z.of_nat (length str)) pw m') ->
  evt rsegs Q (lp_ms i j y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 m).
Proof.
  intros SLEN Q i j pw str slack y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 m
    OK Hi Hj RA BS NONUL PAD MI HK.
  pose proof OK as (HN & HSW & HDW & HDN).
  unfold lp_ms, SPW, S7, S8, N4, N9 in *. unfold st_xm in HK.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (zr_word sw) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word dw) as Rdw. unfold inr64 in Rdw.
  pose proof (zr_word pw) as Rpw. unfold inr64 in Rpw.
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  remember (0x34040 + 56 * Z.of_nat i + 8 * Z.of_nat j) as Y eqn:HY.
  step.
  match goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia)
  end.
  cbv iota.
  step.
  rewrite <- HY.
  do 3 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  1-4: first [eassumption | lia].
  cbv delta [mkR].
  assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length str))) = Z.of_nat (length str)) by (apply unsigned_lit; lia).
  do 3 step.
  rewrite ?UL.
  apply evt_done.
  subst Y.
  eapply HK; eassumption.
Qed.

End KA.
