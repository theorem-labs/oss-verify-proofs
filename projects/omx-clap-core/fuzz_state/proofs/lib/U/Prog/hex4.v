From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import hex4_c.
Import ListNotations.
Open Scope Z_scope.

Lemma hex4_lor_low4 : forall x y, 0 <= x < 16 -> 0 <= y -> Z.lor x (y * 2^4) = 16 * y + x.
Proof.
  intros x y Hx Hy. rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (H0 : Z.land x (Z.shiftl y 4) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 4).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite <- (Z.mod_small x (2^4)) by (change (2^4) with 16; lia).
      rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- (Z.lxor_lor _ _ H0), <- (Z.add_nocarry_lxor _ _ H0), Z.shiftl_mul_pow2 by lia.
  change (2^4) with 16. lia.
Qed.

Lemma hex4_acc : forall v z K, 0 <= v < 2^12 -> 0 <= K + z < 16 -> 0 <= z < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (K + bv_unsigned (Z_to_bv 64 z))))
                    (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 v)) 4)))) =
  Z_to_bv 64 (16 * v + (K + z)).
Proof.
  intros v z K Hv Hk Hz.
  rewrite (unsigned_lit z) by lia. rewrite (unsigned_lit v) by lia. rewrite (unsigned_lit (K + z)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (v * 2^4)) by (change (2^4) with 16; lia).
  rewrite hex4_lor_low4 by lia. reflexivity.
Qed.

Lemma hex4_sltiu_pos : forall P, 0 < P < 2^64 -> v_sltiu (Z_to_bv 64 P) 1 = Z_to_bv 64 0.
Proof.
  intros P HP. unfold v_sltiu. rewrite (unsigned_lit P) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec P 1); [ lia | reflexivity ].
Qed.

Lemma hex4_sltu_pos : forall p, 0 < p < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 p) = Z_to_bv 64 1.
Proof.
  intros p Hp. rewrite v_sltu_b2z, (unsigned_lit p) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec 0 p); [ reflexivity | lia ].
Qed.

Lemma hexval_range : forall c d, hexval c = Some d -> 0 <= d < 16.
Proof.
  intros c d. unfold hexval.
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
  intro Hsome; try discriminate Hsome; injection Hsome as E; subst d; lia.
Qed.

Local Ltac hexval_solve :=
  unfold hexval;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
  first [ reflexivity | f_equal; lia | exfalso; lia ].

Local Ltac cond_fact H := zify_cond H; rewrite ?unsigned_lit_wrap in H.

Local Ltac nobr H := if_cases H; [ cond_fact H; exfalso; Z.div_mod_to_equations; lia | clear H ].

Lemma hex4_turn : forall (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w4 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (p P v n : Z) (c : byte),
  0 < p -> p <= P < 2^64 -> 0 <= v < 2^12 -> 1 <= n <= 4 -> w4 = Z_to_bv 64 1 ->
  ov_read_bytes rsegs m (wa P) 1 = Some [c] ->
  (forall d, hexval c = Some d -> forall x2 x3 y5 y6 y7 y28 : word,
     x2 = Z_to_bv 64 (16 * v + d) -> x3 = Z_to_bv 64 (n - 1) -> y5 = Z_to_bv 64 (P + 1) -> y6 = Z_to_bv 64 (P + 1) ->
     evt rsegs Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 p) a1 x2 x3 w4 (Z_to_bv 64 10) (Z_to_bv 64 6) (Z_to_bv 64 5)
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6) F (Z_to_bv 64 0x15d74) fc None m (seg_rom rsegs))) ->
  (hexval c = None -> forall x0 y5 y6 y7 y28 : word, x0 = Z_to_bv 64 (-1) ->
     evt rsegs Q (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 x0 a1 (Z_to_bv 64 v) (Z_to_bv 64 n) w4 (Z_to_bv 64 10) (Z_to_bv 64 6) (Z_to_bv 64 5)
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 P) (Z_to_bv 64 P) t2 s0 s1 (Z_to_bv 64 p) a1 (Z_to_bv 64 v) (Z_to_bv 64 n)
                        w4 (Z_to_bv 64 10) (Z_to_bv 64 6) (Z_to_bv 64 5)
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15d18) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w4 F fc m Q p P v n c Hp HP HV HN E4 RD KS KF.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  step. nobr HB1.
  step. rewrite (hex4_sltiu_pos P) by lia.
  subst w4. step. step. nobr HB2.
  step. nobr HB3.
  step. step. step.
  if_cases HC1.
  - cond_fact HC1.
    assert (N1 : ~ (48 <= bv_unsigned c <= 57)) by (Z.div_mod_to_equations; lia). clear HC1.
    step. step.
    if_cases HC2.
    + cond_fact HC2.
      assert (N2 : ~ (97 <= bv_unsigned c <= 102)) by (Z.div_mod_to_equations; lia). clear HC2.
      step. step.
      if_cases HC3.
      * cond_fact HC3.
        assert (N3 : ~ (65 <= bv_unsigned c <= 70)) by (Z.div_mod_to_equations; lia). clear HC3.
        step. step.
        eapply KF; [ hexval_solve | first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].
      * cond_fact HC3.
        assert (D : 65 <= bv_unsigned c <= 70) by (Z.div_mod_to_equations; lia). clear HC3.
        step. step. step. step. step. step. step.
        unfold zxb.
        eapply (KS (-55 + bv_unsigned c));
          [ hexval_solve | apply hex4_acc; lia | f_equal; lia | reflexivity | reflexivity ].
    + cond_fact HC2.
      assert (D : 97 <= bv_unsigned c <= 102) by (Z.div_mod_to_equations; lia). clear HC2.
      step. step. step. step. step. step. step. step.
      unfold zxb.
      eapply (KS (-87 + bv_unsigned c));
        [ hexval_solve | apply hex4_acc; lia | f_equal; lia | reflexivity | reflexivity ].
  - cond_fact HC1.
    assert (D : 48 <= bv_unsigned c <= 57) by (Z.div_mod_to_equations; lia). clear HC1.
    step. step. step. step. step. step. step. step.
    unfold zxb.
    eapply (KS (-48 + bv_unsigned c));
      [ hexval_solve | apply hex4_acc; lia | f_equal; lia | reflexivity | reflexivity ].
Qed.

Lemma hex4_bytes_at_le4 : forall m o x y, x = y -> 0 <= o -> o + 4 <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) (le4 (Z_to_bv 64 x))) o (le4 (Z_to_bv 64 y)).
Proof. intros m o x y E Ho Ho4. subst y. apply bytes_at_write_same; rewrite ?length_le4; cbn; lia. Qed.

Local Ltac rd R :=
  lazymatch type of R with
  | ov_read_bytes _ _ (wa ?A) _ = _ =>
      lazymatch goal with |- ov_read_bytes _ _ (wa ?a) _ = _ => replace a with A by lia; exact R end
  end.

Local Ltac close_fail :=
  apply evt_done; cbv beta; do 16 eexists; split; [ reflexivity | ];
  split; [ apply munch_refl | ]; split; [ apply wmono_refl | ];
  cbv beta iota delta [hex4];
  repeat match goal with H : hexval _ = _ |- _ => rewrite H; clear H end;
  cbv beta iota; split; [ first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] | reflexivity ].

Theorem hex4_holds : hex4_contract.
Proof.
  unfold hex4_contract, HEX4.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p o b0 b1 b2 b3
    E0 E1 HP0 HB HO0 HOM HW HD.
  subst a0 a1.
  pose proof HB as (HPl & HPh & _). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HPh.
  pose proof HW as (HOl & HOh & _).
  assert (HL : Z.land o 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact HOM).
  assert (R0 : ov_read_bytes rsegs m (wa p) 1 = Some [b0]).
  { rewrite <- (Z.add_0_r p) at 1. rewrite (bytes_at_read rsegs m p _ 0 1 HB) by (cbn; lia). reflexivity. }
  assert (R1 : ov_read_bytes rsegs m (wa (p + 1)) 1 = Some [b1]).
  { rewrite (bytes_at_read rsegs m p _ 1 1 HB) by (cbn; lia). reflexivity. }
  assert (R2 : ov_read_bytes rsegs m (wa (p + 2)) 1 = Some [b2]).
  { rewrite (bytes_at_read rsegs m p _ 2 1 HB) by (cbn; lia). reflexivity. }
  assert (R3 : ov_read_bytes rsegs m (wa (p + 3)) 1 = Some [b3]).
  { rewrite (bytes_at_read rsegs m p _ 3 1 HB) by (cbn; lia). reflexivity. }
  assert (ST : store_ok rsegs m (wa o) 4 = true).
  { rewrite <- (Z.add_0_r o) at 1. apply (wr_at_store_ok rsegs m o 4 0 4%nat HW); cbn; lia. }
  step. step. step. step. step. step. step. step.
  eapply hex4_turn; [ lia | lia | lia | lia | apply hex4_sltu_pos; lia | rd R0
                    | intros d0 H0 ? ? ? ? ? ? -> -> -> -> | intros H0 ? ? ? ? ? -> ].
  2: close_fail.
  pose proof (hexval_range _ _ H0) as G0.
  step. if_true.
  eapply hex4_turn; [ lia | lia | lia | lia | apply hex4_sltu_pos; lia | rd R1
                    | intros d1 H1 ? ? ? ? ? ? -> -> -> -> | intros H1 ? ? ? ? ? -> ].
  2: close_fail.
  pose proof (hexval_range _ _ H1) as G1.
  step. if_true.
  eapply hex4_turn; [ lia | lia | lia | lia | apply hex4_sltu_pos; lia | rd R2
                    | intros d2 H2 ? ? ? ? ? ? -> -> -> -> | intros H2 ? ? ? ? ? -> ].
  2: close_fail.
  pose proof (hexval_range _ _ H2) as G2.
  step. if_true.
  eapply hex4_turn; [ lia | lia | lia | lia | apply hex4_sltu_pos; lia | rd R3
                    | intros d3 H3 ? ? ? ? ? ? -> -> -> -> | intros H3 ? ? ? ? ? -> ].
  2: close_fail.
  pose proof (hexval_range _ _ H3) as G3.
  step. if_false.
  step. step.
  if_cases HA; [ cond_fact HA; exfalso; rewrite ?(Z.mod_small o) in HA by lia; lia | clear HA ].
  step. step.
  apply evt_done; cbv beta; do 16 eexists; split; [ reflexivity | ].
  split; [ apply munch_write; [ apply munch_refl | lia | rewrite length_le4; cbn; lia | cbn [inside]; rewrite length_le4; cbn; lia ] | ].
  split; [ apply wmono_write, wmono_refl | ].
  cbv beta iota delta [hex4]. rewrite H0, H1, H2, H3. cbv beta iota.
  split; [ rewrite (unsigned_lit o) by lia; rewrite HL; reflexivity | ].
  apply hex4_bytes_at_le4; lia.
Qed.
