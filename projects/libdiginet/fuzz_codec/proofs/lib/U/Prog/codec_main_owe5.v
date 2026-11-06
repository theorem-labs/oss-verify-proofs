(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 509 of its 532 lines of code are new or changed and 121 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img
  codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE5 of the walk of LLVMFuzzerTestOneInput in the UBSan image: the RING case of owe()
    (fuzz_codec.c:177-189), 0x14790-0x1488c and the tail 0x1491c-0x14924 it shares with METER. The
    two range tests go to SPEC_E_RANGE at 0x14a2c; otherwise pl[3] at sp + 0x12e is filled by the
    LED loop (lemmas [ring_pass], one pass, and [ring_loop], the 14 passes) and owe_sysex, inlined,
    writes want[0..8), want_len, want_key and want_display before the checks at 0x14a34. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** lw of an unsigned field: the register is the field sign-extended from bit 31. *)
Lemma sx32_u : forall a, 0 <= a < 2 ^ 32 ->
  bv_unsigned (sx32 (Z_to_bv 64 a)) = if a <? 2 ^ 31 then a else a + (2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold sx32. rewrite (unsigned_lit a) by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec a (2 ^ 31)).
  - rewrite (Z.mod_small (a + 2 ^ 31) (2 ^ 32)) by lia.
    replace (a + 2 ^ 31 - 2 ^ 31) with a by lia. apply Z.mod_small. lia.
  - replace ((a + 2 ^ 31) mod 2 ^ 32) with (a + 2 ^ 31 - 2 ^ 32)
      by (apply Z.mod_unique with 1; lia).
    symmetry. apply Z.mod_unique with (-1); lia.
Qed.

(** lwu of an unsigned field. *)
Lemma zx32_u : forall b, 0 <= b < 2 ^ 32 -> zx32 (Z_to_bv 64 b) = Z_to_bv 64 b.
Proof. intros b Hb. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma u8_unsigned : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_small. exact Hx.
Qed.

(** k.desk of a kind that needs a desk is &SPEC_C24 or &SPEC_PC. *)
Lemma desk5 : forall k, desk_at k -> k_desk k <> 0 ->
  exists d, od_of k = Some d /\ ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)).
Proof.
  intros k [[_ E]|[[_ E]|[_ E]]] H; [contradiction | exists c24 | exists pc];
    (split; [unfold od_of; rewrite E; reflexivity | auto]).
Qed.

(** d->strips (lbu 9(s7)) and d->device (lbu 8(s7)) read from the RELRO desks. *)
Lemma desk_rd5 : forall m2 k d, relro_img m2 ->
  ((k_desk k = SDESK_C24 /\ d = c24) \/ (k_desk k = SDESK_PC /\ d = pc)) ->
  ov_read_bytes rsegs m2 (Z_to_bv 64 (k_desk k + 9)) 1 = Some [Z_to_bv 8 (d_strips d)] /\
  ov_read_bytes rsegs m2 (Z_to_bv 64 (k_desk k + 8)) 1 = Some [Z_to_bv 8 (d_dev d)].
Proof.
  intros m2 k d HR [[E ->] | [E ->]]; rewrite E; unfold SDESK_C24, SDESK_PC.
  - pose proof (codec_SPEC_C24_at m2 HR) as DK. unfold codec_SPEC_C24_cells in DK. split.
    + exact (ro_cells_read_at rsegs m2 0x1f690 _ 9 (C1 (Z_to_bv 8 24)) 1 _ DK eq_refl eq_refl eq_refl).
    + exact (ro_cells_read_at rsegs m2 0x1f690 _ 8 (C1 (Z_to_bv 8 1)) 1 _ DK eq_refl eq_refl eq_refl).
  - pose proof (codec_SPEC_PC_at m2 HR) as DK. unfold codec_SPEC_PC_cells in DK. split.
    + exact (ro_cells_read_at rsegs m2 0x1f6a0 _ 9 (C1 (Z_to_bv 8 8)) 1 _ DK eq_refl eq_refl eq_refl).
    + exact (ro_cells_read_at rsegs m2 0x1f6a0 _ 8 (C1 (Z_to_bv 8 0)) 1 _ DK eq_refl eq_refl eq_refl).
Qed.

(** ---- the LED loop (0x147d8-0x14834) ---- *)

(** srlw then andi 1 (0x147dc-0x147e0): bit j of b. *)
Lemma ring_bit : forall b j, 0 <= b < 2 ^ 32 -> 1 <= j <= 14 ->
  Z.land (bv_swrap 32 (bv_wrap 32 b ≫ (j mod 32)) mod 18446744073709551616) 1 = if Z.testbit b j then 1 else 0.
Proof.
  intros b j Hb Hj.
  rewrite (Z.mod_small j 32) by lia.
  unfold bv_wrap at 1. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small b (2 ^ 32)) by lia.
  assert (Hs : 0 <= b ≫ j < 2 ^ 31).
  { rewrite Z.shiftr_div_pow2 by lia.
    assert (2 <= 2 ^ j) by (change 2 with (2 ^ 1); apply Z.pow_le_mono_r; lia).
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. nia. }
  unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small (b ≫ j + 2 ^ 31) (2 ^ 32)) by lia.
  replace (b ≫ j + 2 ^ 31 - 2 ^ 31) with (b ≫ j) by lia.
  rewrite (Z.mod_small (b ≫ j)) by lia.
  replace (Z.testbit b j) with (Z.testbit (b ≫ j) 0) by (rewrite Z.shiftr_spec by lia; f_equal; lia).
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. rewrite Z.pow_1_r.
  rewrite Zmod_odd, Z.bit0_odd. reflexivity.
Qed.

Lemma swrap_sub : forall c led, 0 <= c <= 15 -> 0 <= led <= 16 ->
  bv_swrap 32 (c + - led mod 18446744073709551616) = c - led.
Proof.
  intros c led Hc Hl. unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma pow_sllw : forall x, 0 <= x <= 6 -> bv_swrap 32 (1 ≪ (x mod 32)) mod 18446744073709551616 = 2 ^ x.
Proof.
  intros x Hx. assert (E : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; reflexivity |]). subst x. vm_compute. reflexivity.
Qed.

Lemma swrap_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap_neg : forall led, 2 <= led <= 15 -> bv_swrap 32 (- led mod 18446744073709551616 + -1) = - (led + 1).
Proof.
  intros led Hl. unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

(** The latch of the LED loop, 0x14828-0x14834: led and -led one on, back to 0x147d8 or out. *)
Ltac pass_tail K led :=
  zstep; zstep; zstep;
  rewrite (swrap_small (led + 1)) by lia;
  rewrite (swrap_neg led) by lia;
  zstep;
  let E5 := fresh "E5" in
  if_cases E5;
  [ zify_cond E5;
    let L15 := fresh "L15" in
    assert (L15 : led <> 15) by (intro; subst led; apply E5; reflexivity);
    rewrite (proj2 (Z.eqb_neq led 15) L15) in K; eapply K; eassumption
  | zify_cond E5;
    let L15 := fresh "L15" in
    assert (L15 : led = 15) by (Z.div_mod_to_equations; lia);
    subst led; eapply K; eassumption ].

(** One pass of the LED loop at 0x147d8 (fuzz_codec.c:180-182): led = a2, a3 = -led, pl[] at P; bit
    led - 1 of b ORs 1 << (8 - led) into pl[1] (led <= 8) or 1 << (15 - led) into pl[2]. The shift
    exponent test (0x14804) and the pointer test on &pl[...] (0x14810) never trap. *)
Lemma ring_pass : forall (Q : machine_state -> Prop) F fc m (P : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 a4 a5 a6
    (b led x1 x2 : Z) (p0 : byte) (rest : list byte),
  0 <= b < 2 ^ 32 -> 2 <= led <= 15 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  rw_cells rsegs m P [C1 p0; C1 (Z_to_bv 8 x1); C1 (Z_to_bv 8 x2); CB 7 rest] ->
  mem_inv rsegs m ->
  (forall m' a4' a5' a6',
     rw_cells rsegs m' P [C1 p0; C1 (Z_to_bv 8 (fst (owe_ring_step b (x1, x2) led)));
                          C1 (Z_to_bv 8 (snd (owe_ring_step b (x1, x2) led))); CB 7 rest] ->
     mem_inv rsegs m' -> munch [(P, P + 10)] m m' -> wmono rsegs m m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 b) (Z_to_bv 64 (led + 1))
                       (Z_to_bv 64 (- (led + 1))) a4' a5' a6' (Z_to_bv 64 P)
                       s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if led =? 15 then 0x14838 else 0x147d8)) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 b) (Z_to_bv 64 led)
                   (Z_to_bv 64 (- led)) a4 a5 a6 (Z_to_bv 64 P)
                   s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x147d8) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m P ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 a4 a5 a6
         b led x1 x2 p0 rest Hb Hl Hx1 Hx2 PL HMI K.
  pose proof (rw_cells_bound rsegs m P _ PL) as HPB. cbn [cells_size csize Nat.add] in HPB.
  pose proof (munch_refl [(P, P + 10)] m) as MU0.
  pose proof (wmono_refl rsegs m) as WM0.
  zstep. zstep. zstep. zstep.
  if_cases E1.
  - (* bit led - 1 clear: pl[] unchanged *)
    zify_cond E1. rewrite (ring_bit b (led + -1)) in E1 by lia.
    assert (Tb : Z.testbit b (led - 1) = false)
      by (replace (led - 1) with (led + -1) by lia; destruct (Z.testbit b (led + -1));
          [discriminate E1 | reflexivity]).
    assert (Es : owe_ring_step b (x1, x2) led = (x1, x2))
      by (unfold owe_ring_step; cbn [fst snd]; rewrite Tb; cbn [bit_or_0]; rewrite !Z.lor_0_r;
          destruct (led <=? 8); reflexivity).
    rewrite Es in K. cbn [fst snd] in K.
    pass_tail K led.
  - zify_cond E1. rewrite (ring_bit b (led + -1)) in E1 by lia.
    assert (Tb : Z.testbit b (led - 1) = true)
      by (replace (led - 1) with (led + -1) by lia; destruct (Z.testbit b (led + -1));
          [reflexivity | exfalso; apply E1; reflexivity]).
    zstep. zstep. if_cases E2.
    + (* led <= 8: pl[1] *)
      assert (L9 : (led <? 9) = true) by (zify_cond E2; apply Z.ltb_lt; lia).
      zstep. zstep. rewrite (swrap_sub 8 led) by lia. zstep. zstep. if_cases E3.
      { exfalso. zify_cond E3. lia. }
      zstep. rewrite L9. cbn [Z.b2z]. zstep. zstep. if_cases E4.
      { exfalso. zify_cond E4. lia. }
      pose proof (rw_cells_app_split m P [C1 p0] [C1 (Z_to_bv 8 x1); C1 (Z_to_bv 8 x2); CB 7 rest] PL)
        as [PA PB].
      cbn [cells_size csize Nat.add] in PB.
      replace (P + Z.of_nat 1) with (P - 1 + 2) in PB by lia. clear PL.
      zstep. zstep. zstep. zstep.
      rewrite (pow_sllw (8 - led)) by lia. rewrite (u8_unsigned x1) by lia.
      assert (RV : 0 <= Z.lor x1 (2 ^ (8 - led)) < 256).
      { change 256 with (2 ^ 8). apply lor_lt_pow2; [lia|].
        split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
      zstep.
      rewrite (unsigned_lit (Z.lor x1 (2 ^ (8 - led)))) in PB by lia.
      assert (Es : owe_ring_step b (x1, x2) led = (Z.lor x1 (2 ^ (8 - led)), x2))
        by (unfold owe_ring_step; cbn [fst snd]; rewrite Tb; cbn [bit_or_0];
            replace (led <=? 8) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
      rewrite Es in K. cbn [fst snd] in K.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PL' : rw_cells rsegs mm P
                        [C1 p0; C1 (Z_to_bv 8 (Z.lor x1 (2 ^ (8 - led)))); C1 (Z_to_bv 8 x2); CB 7 rest])
          by (apply (rw_cells_app_join mm P [C1 p0]); [exact PA |];
              cbn [cells_size csize Nat.add]; replace (P + Z.of_nat 1) with (P - 1 + 2) by lia; exact PB)
      end.
      clear PA PB.
      pass_tail K led.
    + (* led >= 9: pl[2] *)
      assert (L9 : (led <? 9) = false) by (zify_cond E2; apply Z.ltb_ge; lia).
      zstep. zstep. zstep. rewrite (swrap_sub 15 led) by lia. zstep. zstep. if_cases E3.
      { exfalso. zify_cond E3. lia. }
      zstep. rewrite L9. cbn [Z.b2z]. zstep. zstep. if_cases E4.
      { exfalso. zify_cond E4. lia. }
      pose proof (rw_cells_app_split m P [C1 p0; C1 (Z_to_bv 8 x1)] [C1 (Z_to_bv 8 x2); CB 7 rest] PL)
        as [PA PB].
      cbn [cells_size csize Nat.add] in PB.
      replace (P + Z.of_nat 2) with (P - 0 + 2) in PB by lia. clear PL.
      zstep. zstep. zstep. zstep.
      rewrite (pow_sllw (15 - led)) by lia. rewrite (u8_unsigned x2) by lia.
      assert (RV : 0 <= Z.lor x2 (2 ^ (15 - led)) < 256).
      { change 256 with (2 ^ 8). apply lor_lt_pow2; [lia|].
        split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
      zstep.
      rewrite (unsigned_lit (Z.lor x2 (2 ^ (15 - led)))) in PB by lia.
      assert (Es : owe_ring_step b (x1, x2) led = (x1, Z.lor x2 (2 ^ (15 - led))))
        by (unfold owe_ring_step; cbn [fst snd]; rewrite Tb; cbn [bit_or_0];
            replace (led <=? 8) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      rewrite Es in K. cbn [fst snd] in K.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (PL' : rw_cells rsegs mm P
                        [C1 p0; C1 (Z_to_bv 8 x1); C1 (Z_to_bv 8 (Z.lor x2 (2 ^ (15 - led)))); CB 7 rest])
          by (apply (rw_cells_app_join mm P [C1 p0; C1 (Z_to_bv 8 x1)]
                       [C1 (Z_to_bv 8 (Z.lor x2 (2 ^ (15 - led)))); CB 7 rest]); [exact PA |];
              cbn [cells_size csize Nat.add]; replace (P + Z.of_nat 2) with (P - 0 + 2) by lia; exact PB)
      end.
      clear PA PB.
      pass_tail K led.
Qed.

Lemma ring_acc_range : forall b l p, Forall (fun x => 2 <= x <= 15) l ->
  0 <= fst p < 128 -> 0 <= snd p < 128 ->
  0 <= fst (fold_left (owe_ring_step b) l p) < 128 /\ 0 <= snd (fold_left (owe_ring_step b) l p) < 128.
Proof.
  intros b l p Hl H1 H2.
  apply (fold_left_inv (fun pr => 0 <= fst pr < 128 /\ 0 <= snd pr < 128)); [split; assumption|].
  intros [x1 x2] y Hy [Hx1 Hx2]. rewrite Forall_forall in Hl. specialize (Hl y Hy).
  cbn [fst snd] in *. unfold owe_ring_step. cbn [fst snd].
  assert (B : forall t k, 0 <= k <= 6 -> 0 <= bit_or_0 t (2 ^ k) < 128).
  { intros [|] k Hk; cbn [bit_or_0]; [|lia].
    split; [apply Z.pow_nonneg; lia|]. change 128 with (2 ^ 7). apply Z.pow_lt_mono_r; lia. }
  destruct (Z.leb_spec y 8).
  - split; [|exact Hx2]. change 128 with (2 ^ 7). apply lor_lt_pow2; [exact Hx1 | apply B; lia].
  - split; [exact Hx1|]. change 128 with (2 ^ 7). apply lor_lt_pow2; [exact Hx2 | apply B; lia].
Qed.

Lemma seq_leds : forall n, (n <= 14)%nat -> Forall (fun x => 2 <= x <= 15) (map Z.of_nat (seq 2 n)).
Proof.
  intros n Hn. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
  apply in_seq in Hy. lia.
Qed.

(** The loop invariant: after the passes for led = 2 .. 1 + j, pl[1..2] hold the fold of
    owe_ring_step over those leds. *)
Definition rfold (b : Z) (j : nat) : Z * Z := fold_left (owe_ring_step b) (map Z.of_nat (seq 2 j)) (0, 0).

Lemma rfold_step : forall b j, rfold b (S j) = owe_ring_step b (rfold b j) (2 + Z.of_nat j).
Proof.
  intros b j. unfold rfold. rewrite seq_S, map_app, fold_left_app. cbn [map fold_left]. f_equal. lia.
Qed.

Lemma rfold_range : forall b j, (j <= 14)%nat -> 0 <= fst (rfold b j) < 256 /\ 0 <= snd (rfold b j) < 256.
Proof.
  intros b j Hj. unfold rfold.
  pose proof (ring_acc_range b (map Z.of_nat (seq 2 j)) (0, 0) (seq_leds j Hj) ltac:(cbn; lia) ltac:(cbn; lia)).
  lia.
Qed.

Lemma rfold_end : forall b, rfold b 14 = owe_ring b.
Proof. intros b. unfold rfold. symmetry. apply owe_ring_step_eq. Qed.

(** The LED loop 0x147d8-0x14834, 14 passes, from pl[1] = pl[2] = 0 to owe_ring b. *)
Lemma ring_loop : forall (Q : machine_state -> Prop) F fc m (P : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6
    (b : Z) (p0 : byte) (rest : list byte),
  0 <= b < 2 ^ 32 ->
  rw_cells rsegs m P [C1 p0; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 7 rest] ->
  mem_inv rsegs m ->
  (forall m' a2' a3' a4' a5' a6',
     rw_cells rsegs m' P [C1 p0; C1 (Z_to_bv 8 (fst (owe_ring b))); C1 (Z_to_bv 8 (snd (owe_ring b)));
                          CB 7 rest] ->
     mem_inv rsegs m' -> munch [(P, P + 10)] m m' -> wmono rsegs m m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 b) a2' a3' a4' a5' a6' (Z_to_bv 64 P)
                       s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14838) fc None m' (seg_rom rsegs))) ->
  forall a4 a5 a6,
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 b) (Z_to_bv 64 2) (Z_to_bv 64 (-2))
                   a4 a5 a6 (Z_to_bv 64 P) s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x147d8) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m P ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 b p0 rest
         Hb PL HMI K.
  assert (G : forall r, (r <= 13)%nat -> forall m1 a4 a5 a6,
    rw_cells rsegs m1 P [C1 p0; C1 (Z_to_bv 8 (fst (rfold b (13 - r))));
                         C1 (Z_to_bv 8 (snd (rfold b (13 - r)))); CB 7 rest] ->
    mem_inv rsegs m1 -> munch [(P, P + 10)] m m1 -> wmono rsegs m m1 ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 b) (Z_to_bv 64 (2 + Z.of_nat (13 - r)))
                     (Z_to_bv 64 (- (2 + Z.of_nat (13 - r)))) a4 a5 a6 (Z_to_bv 64 P)
                     s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 1) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x147d8) fc None m1 (seg_rom rsegs))).
  { induction r as [|r IH]; intros Hr m1 a4 a5 a6 PL1 HMI1 MU1 WM1.
    - pose proof (rfold_range b (13 - 0) ltac:(lia)) as RA.
      eapply ring_pass; [exact Hb | cbn; lia | exact (proj1 RA) | exact (proj2 RA) | exact PL1 | exact HMI1 |].
      intros m' a4' a5' a6' PL' HMI' MU' WM'.
      rewrite <- surjective_pairing in PL'.
      replace (owe_ring_step b (rfold b (13 - 0)) (2 + Z.of_nat (13 - 0))) with (owe_ring b) in PL'
        by (rewrite <- rfold_end, rfold_step; reflexivity).
      eapply K; [exact PL' | exact HMI' | exact (munch_trans _ _ _ _ MU1 MU') | exact (wmono_trans rsegs _ _ _ WM1 WM')].
    - pose proof (rfold_range b (13 - S r) ltac:(lia)) as RA.
      eapply ring_pass; [exact Hb | lia | exact (proj1 RA) | exact (proj2 RA) | exact PL1 | exact HMI1 |].
      intros m' a4' a5' a6' PL' HMI' MU' WM'.
      rewrite <- surjective_pairing in PL'.
      replace (owe_ring_step b (rfold b (13 - S r)) (2 + Z.of_nat (13 - S r))) with (rfold b (13 - r)) in PL'
        by (replace (13 - r)%nat with (S (13 - S r)) by lia; apply rfold_step).
      replace (2 + Z.of_nat (13 - S r) =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 + Z.of_nat (13 - S r) + 1) with (2 + Z.of_nat (13 - r)) by lia.
      apply IH; [lia | exact PL' | exact HMI' | exact (munch_trans _ _ _ _ MU1 MU') | exact (wmono_trans rsegs _ _ _ WM1 WM')]. }
  intros a4 a5 a6.
  exact (G 13%nat ltac:(lia) m a4 a5 a6 PL HMI (munch_refl _ _) (wmono_refl rsegs _)).
Qed.

(** ---- the record owe() hands the checks ---- *)

Lemma owe_k5 : forall k d, k_kind k = 5 -> od_of k = Some d ->
  owe_k k = if (d_strips d <=? k_a k) || negb (Z.shiftr (k_b k) 15 =? 0) then (E_RANGE, noc)
            else (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x00] ++
                      [u8 (Z.lor (k_a k) (bit_or_0 (Z.testbit (k_b k) 0) 0x40));
                       fst (owe_ring (k_b k)); snd (owe_ring (k_b k))] ++ [0xf7],
                      KEY 3 (k_a k), 0)).
Proof.
  intros k d HK HO. unfold owe_k, owe_spec. rewrite HK, HO.
  destruct (owe_ring (k_b k)) as [p1 p2]. reflexivity.
Qed.

Lemma enc_rc5 : forall k d, rec_wf k -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  fst (enc_k k) = fst (owe_k k).
Proof.
  intros k d (HK & _ & _ & _ & _ & _ & _ & _ & _ & HRD) HO Hd.
  assert (OD : od_ok (od_of k)) by (unfold od_ok; rewrite HO; destruct Hd as [-> | ->]; auto).
  pose proof (agree_all (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                HK OD HRD) as A.
  unfold agrees in A. revert A. unfold enc_k, owe_k.
  destruct (enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
    as [rc o].
  intros [A _]. cbn [fst]. symmetry. exact A.
Qed.

Lemma desk_range : forall k, desk_at k -> 0 <= k_p k < 2 ^ 64 /\ 0 <= k_desk k < 2 ^ 64.
Proof.
  intros k [[E1 E2]|[[E1 E2]|[E1 E2]]]; rewrite E1, E2; unfold PERS, SDESK_C24, SDESK_PC; lia.
Qed.

Ltac kproj := cbn [with_want_rc with_want_key set_want k_run with_rc with_out
                   k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
                   k_want_len k_want_key k_want_display].

(** A range test failed: want_rc = SPEC_E_RANGE (0x14a2c-0x14a30). *)
Lemma chk_wf_err5 : forall k d, rec_wf k -> k_kind k = 5 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  (d_strips d <= k_a k \/ Z.shiftr (k_b k) 15 <> 0) ->
  chk_wf (with_want_rc (k_run k) E_RANGE).
Proof.
  intros k d WF HK HO Hd Hbad.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  assert (OW : owe_k k = (E_RANGE, noc)).
  { rewrite (owe_k5 k d HK HO). destruct Hbad as [Hs | Hb].
    - replace (d_strips d <=? k_a k) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - replace (Z.shiftr (k_b k) 15 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
      rewrite orb_true_r. reflexivity. }
  pose proof (enc_rc5 k d WF HO Hd) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (with_want_rc (k_run k) E_RANGE) = enc_k k) by reflexivity.
  assert (E2 : owe_k (with_want_rc (k_run k) E_RANGE) = owe_k k) by reflexivity.
  unfold chk_wf. rewrite E1, E2, OW. kproj.
  pose proof (desk_range k HDA) as [Rp Rd].
  pose proof HRD as (Ra & Rb & Rc & Rdl & _ & _ & Rn & _).
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj. rewrite HK, EC, HWL0, HWK0, HWD0. unfold E_RANGE. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. cbn [fst]. unfold E_RANGE. intros H. discriminate H.
Qed.

(** Both range tests passed: the want bytes, want_len 8, the key, display 0, want_rc still 0. *)
Lemma chk_wf_ok5 : forall k d W, rec_wf k -> k_kind k = 5 -> od_of k = Some d -> (d = c24 \/ d = pc) ->
  k_a k < d_strips d -> Z.shiftr (k_b k) 15 = 0 ->
  firstn 8 W = bz ([0xf0; 0x13; u8 (d_dev d); u8 0x00] ++
                   [u8 (Z.lor (k_a k) (bit_or_0 (Z.testbit (k_b k) 0) 0x40));
                    fst (owe_ring (k_b k)); snd (owe_ring (k_b k))] ++ [0xf7]) ->
  chk_wf (with_want_key (set_want (k_run k) W 8 0) (KEY 3 (k_a k))).
Proof.
  intros k d W WF HK HO Hd Ha Hb HW.
  pose proof WF as (HK' & HDA & HBF & HOUT & HRC0 & HWRC0 & HWL0 & HWK0 & HWD0 & HRD).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & _ & Rn & _).
  assert (OW : owe_k k = (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x00] ++
                      [u8 (Z.lor (k_a k) (bit_or_0 (Z.testbit (k_b k) 0) 0x40));
                       fst (owe_ring (k_b k)); snd (owe_ring (k_b k))] ++ [0xf7], KEY 3 (k_a k), 0))).
  { rewrite (owe_k5 k d HK HO).
    replace (d_strips d <=? k_a k) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.shiftr (k_b k) 15 =? 0) with true by (symmetry; apply Z.eqb_eq; exact Hb). reflexivity. }
  pose proof (enc_rc5 k d WF HO Hd) as EC. rewrite OW in EC. cbn [fst] in EC.
  assert (E1 : enc_k (with_want_key (set_want (k_run k) W 8 0) (KEY 3 (k_a k))) = enc_k k) by reflexivity.
  assert (E2 : owe_k (with_want_key (set_want (k_run k) W 8 0) (KEY 3 (k_a k))) = owe_k k) by reflexivity.
  assert (KR : 0 <= KEY 3 (k_a k) < 2 ^ 32) by (apply KEY_range; lia).
  unfold chk_wf. rewrite E1, E2, OW. kproj.
  pose proof (desk_range k HDA) as [Rp Rd].
  split; [lia|]. split; [exact HDA|]. split.
  { unfold kcall_wf. kproj. rewrite HK, EC, HWRC0. lia. }
  split; [exact HBF|]. split; [exact HRD|]. split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [fst]; exact HWRC0|]. intros _. cbn [snd length app].
  split; [exact HW|]. split; [reflexivity|]. split; [lia|]. split; reflexivity.
Qed.

(** ---- bytes and the record cells ---- *)

Lemma rw_cells_merge_at : forall m A cs i j,
  rw_cells rsegs m A cs ->
  rw_cells rsegs m A (firstn i cs ++ CB (cells_size (firstn j (skipn i cs))) (cells_bytes (firstn j (skipn i cs)))
                       :: skipn j (skipn i cs)).
Proof.
  intros m A cs i j H.
  apply rw_cells_merge.
  rewrite firstn_skipn. rewrite firstn_skipn. exact H.
Qed.

Lemma b8_lit : forall x, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 x)) = b8 x.
Proof.
  intros x. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite (Z.mod_eq x (bv_modulus 64)) by (cbv; discriminate).
  replace (bv_modulus 64) with (2 ^ 8 * 2 ^ 56) by reflexivity.
  replace (bv_modulus 8) with (2 ^ 8) by reflexivity.
  replace (x - 2 ^ 8 * 2 ^ 56 * (x / (2 ^ 8 * 2 ^ 56))) with (x + (- (2 ^ 56 * (x / (2 ^ 8 * 2 ^ 56)))) * 2 ^ 8) by ring.
  apply Z.mod_add. lia.
Qed.

Lemma b8_u8 : forall x, b8 (u8 x) = b8 x.
Proof.
  intros x. unfold b8, u8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_mod. lia.
Qed.

Lemma byte_norm : forall x, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 x)))) = b8 x.
Proof.
  intros x. rewrite b8_lit. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 8) with 256 by reflexivity. apply Z.mod_mod. lia.
Qed.

Lemma bytes_eq_of_unsigned : forall l1 l2 : list byte,
  map (fun b => bv_unsigned b) l1 = map (fun b => bv_unsigned b) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx | apply IH; exact Hl].
Qed.

(** slli 63 then srli 57 (0x147b8-0x147c0): bit 0 of b in bit 6. *)
Lemma shl63_shr57 : forall b, 0 <= b ->
  (Z.shiftl b 63 mod 18446744073709551616) ≫ 57 = bit_or_0 (Z.testbit b 0) 64.
Proof.
  intros b Hb. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.bit0_odd. pose proof (Z.div_mod b 2 ltac:(lia)) as Hd. rewrite Zmod_odd in Hd.
  set (q := b / 2) in Hd. clearbody q.
  destruct (Z.odd b); cbn [bit_or_0]; rewrite Hd.
  - replace ((2 * q + 1) * 2 ^ 63) with (2 ^ 63 + q * 18446744073709551616) by ring.
    rewrite Z.mod_add by lia. reflexivity.
  - replace ((2 * q + 0) * 2 ^ 63) with (0 + q * 18446744073709551616) by ring.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma codec_main_owe5 : seg_owe5_stmt.
Proof.
  unfold seg_owe5_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CHK k WF K5.
  pose proof (fun m1 => relro_at _ m1 ENV) as RELRO.
  unfold owe_ok, chk_ok, fr in *. cenv_cbn.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' s5' t3' t4' t5' t6' cur rem u0 pj tj plj c ops m1
         _ ND HOPS HOPS2 HCUR HC0 HCN FR ST MU WM HMI.
  pose proof WF as (HK & HDK & HBF & HOUT & HRC & HWRC & HWL & HWK & HWD & HRD).
  destruct (ND ltac:(rewrite K5; reflexivity)) as [-> HDNZ]. clear ND.
  destruct (desk5 k HDK HDNZ) as (d & HOD & HDC).
  assert (Hd : d = c24 \/ d = pc) by (destruct HDC as [[_ ->]|[_ ->]]; auto).
  destruct (desk_rd5 m1 k d (RELRO m1 MU) HDC) as [RDS _].
  assert (HDR : 0x1f690 <= k_desk k <= 0x1f6a0)
    by (destruct HDC as [[E _]|[E _]]; rewrite E; unfold SDESK_C24, SDESK_PC; lia).
  assert (HD7 : Z.land (k_desk k) 7 = 0)
    by (destruct HDC as [[E _]|[E _]]; rewrite E; reflexivity).
  assert (HDS : d_strips d = 24 \/ d_strips d = 8) by (destruct HDC as [[_ ->]|[_ ->]]; cbn; lia).
  assert (HDD : 0 <= d_dev d <= 1) by (destruct HDC as [[_ ->]|[_ ->]]; cbn; lia).
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & Rb16 & _ & _). specialize (Rb16 K5).
  destruct ENV as (BY & HMI0 & ST0 & LO & SPA & DJ & HPB & HPNZ & RI & DJR).
  destruct FR as (HS & F0 & F8 & FK & FIN & FPD & FTX & FPL & FSV).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST0 as (Hlo0 & Hhi0 & _).
  unfold kcall_cells, k_run, with_rc, with_out in FK.
  cbn [k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FK.
  rewrite K5. replace (pc_owe 5) with 0x14790 by reflexivity.
  (* 0x14790-0x1479c: d != NULL and aligned (the trap edge is dead) *)
  do 4 zstep.
  if_cases T1.
  { exfalso. rewrite HD7 in T1. vm_compute in T1. discriminate T1. }
  (* 0x147a0-0x147a8: a >= d->strips *)
  zstep. zstep. cbv beta. rewrite (u8_unsigned (d_strips d)) by lia.
  zstep.
  if_cases T2.
  { zify_cond T2. rewrite sx32_u in T2 by lia.
    assert (Has : d_strips d <= k_a k) by (destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
    zstep. zstep.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE)); try eassumption.
    - apply (chk_wf_err5 k d); auto.
    - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T2. rewrite sx32_u in T2 by lia.
  assert (Has : k_a k < d_strips d) by (destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
  rewrite (sx32_small (k_a k)) by lia.
  (* 0x147ac-0x147b4: b >> 15 != 0 *)
  zstep. rewrite (zx32_u (k_b k)) by lia. zstep. zstep. if_cases T3.
  { zify_cond T3.
    assert (Hb15 : Z.shiftr (k_b k) 15 <> 0) by lia.
    zstep. zstep.
    eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_rc (k_run k) E_RANGE)); try eassumption.
    - apply (chk_wf_err5 k d); auto.
    - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj FPL FSV)))))))). }
  zify_cond T3.
  assert (Hb15 : Z.shiftr (k_b k) 15 = 0) by lia.
  (* 0x147b8-0x147d4: pl[0] = a | (b & 1) << 6, pl[1] = pl[2] = 0, led = 2 *)
  do 8 zstep.
  (* the LED loop 0x147d8-0x14834 *)
  eapply ring_loop; [ lia | exact FPL | exact HMI | ].
  intros m2 a2x a3x a4x a5x a6x PL2 HMI2 MU2 WM2.
  clear FPL HMI.
  assert (TR : forall A cs, rw_cells rsegs m0 A cs ->
                 A + Z.of_nat (cells_size cs) <= bv_unsigned sp + -114 \/ bv_unsigned sp + -104 <= A ->
                 rw_cells rsegs m2 A cs).
  { intros A cs H Hdj. eapply rw_cells_transport; [exact H | exact MU2 | exact WM2 |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  apply TR in F0; [| cbn [cells_size csize Nat.add]; lia].
  apply TR in F8; [| cbn [cells_size csize Nat.add]; lia].
  apply TR in FK; [| cbn [cells_size csize Nat.add]; lia].
  apply TR in FIN; [| cbn [cells_size csize Nat.add]; lia].
  apply TR in FPD; [| cbn [cells_size csize Nat.add]; lia].
  apply TR in FTX; [| cbn [cells_size csize Nat.add]; lia].
  apply TR in FSV; [| right; lia].
  clear TR.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; split; [lia | exact I]))
    as ST2.
  assert (MU3 : munch [(bv_unsigned sp - 640, bv_unsigned sp)] m m2).
  { apply (munch_trans _ m m0 m2 MU).
    apply (munch_weaken [(bv_unsigned sp + -114, bv_unsigned sp + -114 + 10)]); [| exact MU2].
    intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
  clear ST MU WM MU2 WM2.
  destruct (desk_rd5 m2 k d (RELRO m2 MU3) HDC) as [_ RDD].
  pose proof (owe_ring_range (k_b k)) as RR.
  (* 0x14838-0x1488c: owe_sysex inlined; 0x1491c-0x14924 the shared tail *)
  zstep. zstep. zstep. zstep. cbv beta. rewrite (u8_unsigned (d_dev d)) by lia.
  do 21 zstep.
  (* 0x14a34: the record with owe()'s want, want_len 8, the key and display 0 *)
  replace (Z.lor (Z.land (k_a k) 65535) 196608) with (KEY 3 (k_a k)) in FK
    by (unfold KEY; rewrite Z.lor_comm; reflexivity).
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (rw_cells_merge_at mm _ _ 14 8) in FK;
    apply (rw_cells_merge_at mm _ _ 0 4) in PL2
  end.
  cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in FK.
  cbn [firstn skipn cells_size csize Nat.add app] in PL2.
  match type of FK with context [CB 24 ?W :: C8 (Z_to_bv 64 8) :: _] => set (Wv := W) in FK end.
  eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (with_want_key (set_want (k_run k) Wv 8 0) (KEY 3 (k_a k))));
    try eassumption.
  - apply (chk_wf_ok5 k d Wv WF K5 HOD Hd Has Hb15).
    unfold Wv.
    replace (le2 (Z_to_bv 64 5104)) with [b8 0xf0; b8 0x13]
      by (apply bytes_eq_of_unsigned; vm_compute; reflexivity).
    cbn [firstn app bz map].
    rewrite !byte_norm, !b8_lit, !b8_u8.
    rewrite (shl63_shr57 (k_b k)) by lia. rewrite (Z.lor_comm (bit_or_0 _ _) (k_a k)).
    replace (b8 (-9)) with (b8 0xf7) by (apply bv_eq; reflexivity).
    reflexivity.
  - exact (conj (kcall_cells_size _) (conj F0 (conj F8 (conj FK (conj FIN (conj FPD (conj FTX (conj PL2 FSV)))))))).
Qed.
