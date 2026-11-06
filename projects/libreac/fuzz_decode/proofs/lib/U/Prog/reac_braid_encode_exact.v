(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 317 of its 350 lines of code are new or changed and 668 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/Prog/RcBraidLib.v, with its numbers changed; 388 of its 413 lines of code are new or changed and 325 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import reac_braid_encode_exact_c.
Import ListNotations.
Open Scope Z_scope.

Definition rbeu_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns : Z) (K : Z -> Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get F k) /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (a, a + 3 * N * ns)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp - 112) (bv_unsigned sp) /\
    (forall x : word, outside [(bv_unsigned sp - 112, bv_unsigned sp)] (bv_unsigned x) ->
       m' x = rb_enc m (rb_rows a N K (Z.to_nat ns)) x).

Lemma rbeu_swrap32 : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma rbeu_land_m2 : forall x, 0 <= x < 2^63 -> Z.land x 18446744073709551614 = x - x mod 2.
Proof.
  intros x Hx.
  replace (x - x mod 2) with (Z.shiftl (Z.shiftr x 1) 1)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_eq by lia; change (2^1) with 2; lia).
  change 18446744073709551614 with (Z.shiftl (Z.ones 63) 1).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (i - 1 + 1) with i by lia.
    destruct (Z.lt_ge_cases (i - 1) 63).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 63; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma rbeu_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rbeu_sltiu1 : forall x, 0 < x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  replace (x <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rbeu_snez1 : forall x, 0 < x < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltu, c_ltu. rewrite (rbe_ltu 0 x) by lia.
  replace (0 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rbeu_snez0 : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. unfold v_sltu, c_ltu. rewrite (rbe_ltu 0 0) by lia. reflexivity. Qed.

Ltac uzfix := repeat match goal with
  | |- context [Z.land ?x 18446744073709551614] => rewrite (rbeu_land_m2 x) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia
  | |- context [Z.land ?x 3] => rewrite (rbe_land3 x) by lia
  | |- context [Z.land ?x 1] => rewrite (rbe_land1 x) by lia
  | |- context [bv_swrap 32 ?z] => rewrite (rbeu_swrap32 z) by lia
  | |- context [v_sltiu (Z_to_bv 64 ?x) 1] => rewrite (rbeu_sltiu1 x) by lia
  | |- context [Z.lxor 1 0] => change (Z.lxor 1 0) with 1
  end.
(* The register equations at a loop entry. Run in a context cleared down to the bounds it needs:
   s * N is a monomial lia takes from the hypothesis bounding it. *)
Ltac uzn := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia
  | |- context [bv_swrap 32 ?z] => rewrite (rbeu_swrap32 z) by lia
  | |- context [Z.land ?x 7] => rewrite (rbeu_land7 x) by lia
  | |- context [Z.lxor ?x ?x] => rewrite (Z.lxor_nilpotent x)
  | |- context [v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)] => rewrite rbeu_snez0
  | |- context [v_sltu (Z_to_bv 64 0) (Z_to_bv 64 ?x)] => rewrite (rbeu_snez1 x) by lia
  end.
Ltac uweq := uzn; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.pow_1_r;
  first [ reflexivity | f_equal; lia | f_equal; nia ].
Ltac ufp v w HM HL1 HL2 HC := rbe_fpc; rewrite ?(rbe_ld4 v) by lia; rewrite ?(rbe_u32 v) by lia;
  rewrite ?(rbe_u32 w) by lia; rewrite ?HM, ?HL1, ?HL2, ?HC; cbn [fst snd]; rewrite ?rbe_fc_same.
Ltac ucond := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  first [ replace c with false by (symmetry; rewrite ?rbe_lts by lia; unfold bv_eqb, bv_ltu; uzfix; solve_cond_rec); cbv iota
        | replace c with true by (symmetry; rewrite ?rbe_lts by lia; unfold bv_eqb, bv_ltu; uzfix; solve_cond_rec); cbv iota ]
  end.
Ltac ugo := repeat first [ ucond | rbe_st ].
Ltac ujeq := uzfix; f_equal; unfold rb_lo, rb_mid, rb_hi, rb_G; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.pow_1_r; lia.

Section Run.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns : Z) (Q : Z -> Z) (V K : Z -> Z -> Z).
  Hypothesis HN : 2 <= N <= 127.
  Hypothesis HNe : N mod 2 = 0.
  Hypothesis Hns : 1 <= ns <= 12.
  Hypothesis FRM : frm0 fc.
  Hypothesis Ha : 0 < a.
  Hypothesis HaE : a + 3 * N * ns <= 2^64.
  Hypothesis HP0 : 0 < P.
  Hypothesis HP8m : P mod 8 = 0.
  Hypothesis HP8 : P + 8 * N <= 2^64.
  Hypothesis HQ : forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64.
  Hypothesis HV : forall s ch, 0 <= s < ns -> 0 <= ch < N ->
    bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch).
  Hypothesis HD1 : a + 3 * N * ns <= P \/ P + 8 * N <= a.
  Hypothesis HD2 : forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a.
  Hypothesis HD3 : a + 3 * N * ns <= bv_unsigned sp + -112 \/ bv_unsigned sp <= a.
  Hypothesis HD4 : P + 8 * N <= bv_unsigned sp + -112 \/ bv_unsigned sp <= P.
  Hypothesis HD5 : forall ch, 0 <= ch < N -> Q ch + 4 * ns <= bv_unsigned sp + -112 \/ bv_unsigned sp <= Q ch.
  Hypothesis Hsp : 112 <= bv_unsigned sp.
  Hypothesis Hsp2 : bv_unsigned sp < 2^64.

  Definition INVU (mm : word -> option byte) (L : list (Z * byte)) : Prop :=
    (forall ch, 0 <= ch < N -> bytes_at rsegs mm (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) /\
    (forall s ch, 0 <= s < ns -> 0 <= ch < N -> bytes_at rsegs mm (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch)))) /\
    wr_at rsegs mm a (3 * N * ns) /\ mem_inv rsegs mm /\
    (forall x, outside [(bv_unsigned sp + -112, bv_unsigned sp)] (bv_unsigned x) -> mm x = rb_enc m L x) /\
    munch [(bv_unsigned sp + -112, bv_unsigned sp); (a, a + 3 * N * ns)] m mm /\ wmono rsegs m mm.

  Lemma INVU_store : forall mm L X b, INVU mm L -> a <= X < a + 3 * N * ns ->
    INVU (write_to_mem mm (wa X) [b]) (L ++ [(X, b)]).
  Proof.
    intros mm L X b (I1 & I2 & I3 & I4 & I5 & I6 & I7) HX.
    assert (HL : X + Z.of_nat (length [b]) <= 2^64) by (cbn [length Z.of_nat]; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros ch Hch. apply bytes_at_write_other; [apply I1; exact Hch | lia | exact HL |].
      rewrite length_le8. cbn [length Z.of_nat]. destruct HD1; lia.
    - intros s ch Hs Hch. apply bytes_at_write_other; [apply I2; assumption | lia | exact HL |].
      rewrite length_le4. cbn [length Z.of_nat]. destruct (HD2 ch Hch); lia.
    - apply wr_at_write. exact I3.
    - apply mem_inv_store; [exact I4|]. cbn [length].
      replace (wa X) with (wa (a + (X - a))) by (f_equal; lia).
      apply (wr_at_store_ok rsegs mm a (3 * N * ns) (X - a) 1 I3); lia.
    - intros x Hx. rewrite rb_enc_app.
      change (rb_enc (rb_enc m L) [(X, b)]) with (write_to_mem (rb_enc m L) (wa X) [b]).
      apply (rbe_wr_agree [(bv_unsigned sp + -112, bv_unsigned sp)]); [lia | exact I5 | exact Hx].
    - apply munch_write; [exact I6 | lia | exact HL | cbn [inside length Z.of_nat]; lia].
    - apply wmono_write. exact I7.
  Qed.

  Lemma INVU_spill : forall mm L X v, INVU mm L -> bv_unsigned sp + -112 <= X -> X + 8 <= bv_unsigned sp + -80 ->
    stk rsegs mm (bv_unsigned sp + -112) (bv_unsigned sp + -80) ->
    INVU (write_to_mem mm (wa X) (le8 v)) L.
  Proof.
    intros mm L X v (I1 & I2 & I3 & I4 & I5 & I6 & I7) HX1 HX2 SP.
    assert (HL : X + Z.of_nat (length (le8 v)) <= 2^64) by (rewrite length_le8; cbn [Z.of_nat]; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros ch Hch. apply bytes_at_write_other; [apply I1; exact Hch | lia | exact HL |].
      rewrite !length_le8. cbn [Z.of_nat]. destruct HD4; lia.
    - intros s ch Hs Hch. apply bytes_at_write_other; [apply I2; assumption | lia | exact HL |].
      rewrite length_le4, length_le8. cbn [Z.of_nat]. destruct (HD5 ch Hch); lia.
    - apply wr_at_write. exact I3.
    - apply mem_inv_store; [exact I4|]. rewrite length_le8.
      pose proof (rbe_stk_wr rsegs mm _ _ SP ltac:(lia)) as W.
      replace (wa X) with (wa (bv_unsigned sp + -112 + (X - (bv_unsigned sp + -112)))) by (f_equal; lia).
      apply (wr_at_store_ok rsegs mm _ _ (X - (bv_unsigned sp + -112)) 8 W); lia.
    - intros x Hx. rewrite (rbe_wr_out [(bv_unsigned sp + -112, bv_unsigned sp)]); [apply I5; exact Hx | lia | exact HL | | exact Hx].
      rewrite length_le8. cbn [inside Z.of_nat]. lia.
    - apply munch_write; [exact I6 | lia | exact HL | rewrite length_le8; cbn [inside Z.of_nat]; lia].
    - apply wmono_write. exact I7.
  Qed.

  Lemma FRs_store : forall mm cs X bs, rw_cells rsegs mm (bv_unsigned sp + -80) cs -> cells_size cs = 80%nat ->
    0 <= X -> X + Z.of_nat (length bs) <= 2^64 ->
    (X + Z.of_nat (length bs) <= bv_unsigned sp + -80 \/ bv_unsigned sp <= X) ->
    rw_cells rsegs (write_to_mem mm (wa X) bs) (bv_unsigned sp + -80) cs.
  Proof.
    intros mm cs X bs H Hs H0 H1 HX. apply rw_cells_frame; [exact H | lia | exact H1 |].
    rewrite Hs. lia.
  Qed.

  Lemma INVU_list : forall mm L L', INVU mm L -> L = L' -> INVU mm L'.
  Proof. intros mm L L' H ->. exact H. Qed.

  Lemma SP_ok : forall mm k, stk rsegs mm (bv_unsigned sp + -112) (bv_unsigned sp + -80) -> 0 <= k -> k + 8 <= 32 ->
    store_ok rsegs mm (wa (bv_unsigned sp + -112 + k)) 8 = true.
  Proof.
    intros mm k H Hk1 Hk2. pose proof (rbe_stk_wr rsegs mm _ _ H ltac:(lia)) as W.
    replace (bv_unsigned sp + -80 - (bv_unsigned sp + -112)) with 32 in W by lia.
    apply (wr_at_store_ok rsegs mm _ 32 k 8 W); cbn [Z.of_nat]; lia.
  Qed.

  Ltac uspill :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?A (le8 ?v)) _) =>
      let X := lazymatch A with wa ?X => X | Z_to_bv 64 ?X => X end in
      match goal with
      | HI : INVU m0 _, FRs : rw_cells _ m0 _ _, SP : stk _ m0 _ _ |- _ =>
          let HI' := fresh "HI" in let FR' := fresh "FRs" in let SP' := fresh "SP" in
          pose proof (INVU_spill m0 _ X v HI ltac:(lia) ltac:(lia) SP) as HI';
          pose proof (FRs_store m0 _ X (le8 v) FRs eq_refl ltac:(lia) ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)
                        ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)) as FR';
          pose proof (stk_write rsegs m0 _ _ X (le8 v) SP ltac:(lia) ltac:(rewrite length_le8; cbn [Z.of_nat]; lia)) as SP';
          change (write_to_mem m0 A (le8 v)) with (write_to_mem m0 (wa X) (le8 v)) in *;
          let mn := fresh "mm" in
          set (mn := write_to_mem m0 (wa X) (le8 v)) in *; clearbody mn; clear HI FRs SP
      end
  end.

  Lemma U_store : forall mm L X b, INVU mm L ->
    rw_cells rsegs mm (bv_unsigned sp + -80) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
    stk rsegs mm (bv_unsigned sp + -112) (bv_unsigned sp + -80) -> a <= X < a + 3 * N * ns ->
    INVU (write_to_mem mm (wa X) [b]) (L ++ [(X, b)]) /\
    rw_cells rsegs (write_to_mem mm (wa X) [b]) (bv_unsigned sp + -80)
      [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] /\
    stk rsegs (write_to_mem mm (wa X) [b]) (bv_unsigned sp + -112) (bv_unsigned sp + -80).
  Proof.
    intros mm L X b HI FR SP HX. split; [apply INVU_store; assumption|]. split.
    - apply FRs_store; [exact FR | reflexivity | lia | cbn [length Z.of_nat]; lia |].
      cbn [length Z.of_nat]. destruct HD3; lia.
    - apply stk_write; [exact SP | lia | cbn [length Z.of_nat]; lia].
  Qed.

  (* One byte store to the audio at a + k: the store, then INVU, the saved-register cells and the spill area. *)
  Ltac ubyte k :=
  match goal with
  | HI : INVU ?m0 ?L0, FRs : rw_cells _ ?m0 _ _, SP : stk _ ?m0 _ _ |- _ =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs m0 (wa (a + k)) 1 = true)
        by (apply (wr_at_store_ok rsegs m0 a (3 * N * ns) k 1 (proj1 (proj2 (proj2 HI)))); cbn [Z.of_nat]; lia);
      uzfix; step; clear HS;
      uzfix; rewrite ?rbe_le1; rewrite ?rbe_b0, ?rbe_b1, ?rbe_b2;
      change (Z_to_bv 64 (a + k)) with (wa (a + k));
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m0 (wa (a + k)) [?bb]) _) =>
        let HI' := fresh "HI" in let FR' := fresh "FRs" in let SP' := fresh "SP" in
        destruct (U_store m0 L0 (a + k) bb HI FRs SP ltac:(lia)) as (HI' & FR' & SP');
        let mn := fresh "mm" in
        set (mn := write_to_mem m0 (wa (a + k)) [bb]) in *; clearbody mn; clear HI FRs SP
      end
  end.


  Lemma rbeu_loop : forall (n : nat) (s ch : Z) (mm : word -> option byte) (G : bvmap 5 word)
      (x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word),
    n = Z.to_nat ((ns - s) * N - ch) -> 0 <= s < ns -> 0 <= ch < N ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -112) -> x5 = Z_to_bv 64 (18446744073709551615 - P) ->
    x6 = Z_to_bv 64 18446744073709551608 -> x7 = Z_to_bv 64 (bv_unsigned sp + -104) ->
    x8 = Z_to_bv 64 (8 * ch) -> x9 = Z_to_bv 64 ch -> x14 = Z_to_bv 64 ns -> x15 = Z_to_bv 64 s ->
    x16 = Z_to_bv 64 (18446744073709551615 - a) -> x17 = Z_to_bv 64 0 -> x18 = Z_to_bv 64 (4 * s) ->
    x19 = Z_to_bv 64 0 -> x20 = Z_to_bv 64 (s * N) -> x21 = Z_to_bv 64 (P + 8 * ch) ->
    x28 = Z_to_bv 64 18446744073709551599 -> x29 = Z_to_bv 64 1 -> x30 = Z_to_bv 64 18446744073709551607 ->
    x31 = Z_to_bv 64 ch ->
    INVU mm (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) ->
    rw_cells rsegs mm (bv_unsigned sp + -80) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
    stk rsegs mm (bv_unsigned sp + -112) (bv_unsigned sp + -80) ->
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get G k = reg_get F k) ->
    evt rsegs (rbeu_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
               x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
          (bvmap_set 12 (Z_to_bv 64 18446744072820359168) (bvmap_set 13 (Z_to_bv 64 18446744070672875518)
            (bvmap_set 14 (Z_to_bv 64 18446744070672875520) (bvmap_set 15 (Z_to_bv 64 18446744069414584320) G))))
          (Z_to_bv 64 0x13d74) fc None mm (seg_rom rsegs)).
  Proof.
    induction n as [|n IH];
      intros s ch mm G x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31
        Hn Hs Hch E2 E5 E6 E7 E8 E9 E14 E15 E16 E17 E18 E19 E20 E21 E28 E29 E30 E31 HI FRs SP HG.
    { exfalso. clear - Hn Hs Hch HN. assert (s * N <= ns * N - N) by nia. lia. }
    subst x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31.
    destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE).
    destruct (HV s ch Hs Hch) as [_ HVs].
    destruct (rbe_pipe (V s ch) (K s ch) HVs) as (Hv & w & Hw & HM & HL1 & HL2 & HC).
    destruct HVs as [HK _].
    unfold F2P23, FCLAMP_HI, FCLAMP_LO in HM, HL1, HL2.
    pose proof (rbe_pos_bound N s ch ns Hs Hch HNe) as HB.
    assert (HsN : 0 <= s * N <= 1524) by (clear - Hs Hns HN; nia).
    pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hc2.
    assert (RP : ov_read_bytes rsegs mm (wa (P + 8 * ch)) 8 = Some (le8 (Z_to_bv 64 (Q ch))))
      by (apply rbe_rd8; apply (proj1 HI); exact Hch).
    assert (RV : ov_read_bytes rsegs mm (wa (Q ch + 4 * s)) 4 = Some (le4 (Z_to_bv 64 (V s ch))))
      by (apply rbe_rd4; apply (proj1 (proj2 HI)); assumption).
    pose proof (Z.mod_pos_bound (K s ch) (2^64) ltac:(lia)) as HKm.
    ugo. ufp (V s ch) w HM HL1 HL2 HC.
    ugo. ufp (V s ch) w HM HL1 HL2 HC.
    ugo. ufp (V s ch) w HM HL1 HL2 HC.
    ugo.
    uzfix.
    destruct HB as [HB0 HB1].
    assert (HX1 : a <= a + rb_lo N s ch < a + 3 * N * ns) by (unfold rb_lo; lia).
    assert (HX2 : a <= a + rb_mid N s ch < a + 3 * N * ns) by (unfold rb_mid; lia).
    assert (HX3 : a <= a + rb_hi N s ch < a + 3 * N * ns) by (unfold rb_hi; lia).
    set (L := rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) in *.
    (* Both parity arms meet at 0x13e40 (sd s7,24(sp)) with s6 = mid, s7 = hi, s8 = a + lo, s9 = 1 + ch mod 2. *)
    assert (JOIN : forall (mmj : word -> option byte) (x22 x23 x24 x25 : word),
      x22 = Z_to_bv 64 (rb_mid N s ch) -> x23 = Z_to_bv 64 (rb_hi N s ch) ->
      x24 = Z_to_bv 64 (a + rb_lo N s ch) -> x25 = Z_to_bv 64 (1 + ch mod 2) ->
      INVU mmj L ->
      rw_cells rsegs mmj (bv_unsigned sp + -80) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
      stk rsegs mmj (bv_unsigned sp + -112) (bv_unsigned sp + -80) ->
      evt rsegs (rbeu_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 (18446744073709551615 - P))
                 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 (bv_unsigned sp + -104)) (Z_to_bv 64 (8 * ch))
                 (Z_to_bv 64 ch) (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N) (Z_to_bv 64 ns)
                 (Z_to_bv 64 s) (Z_to_bv 64 (18446744073709551615 - a)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * s))
                 (Z_to_bv 64 0) (Z_to_bv 64 (s * N)) (Z_to_bv 64 (P + 8 * ch)) x22 x23 x24 x25 s10 s11
                 (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 ch))
            (bvmap_set 10 (nan_box (Z_to_bv 32 w)) (bvmap_set 11 (nan_box (Z_to_bv 32 w))
              (bvmap_set 12 (Z_to_bv 64 18446744072820359168) (bvmap_set 13 (Z_to_bv 64 18446744070672875518)
                (bvmap_set 14 (Z_to_bv 64 18446744070672875520) (bvmap_set 15 (Z_to_bv 64 18446744069414584320) G))))))
            (Z_to_bv 64 0x13e40) fc None mmj (seg_rom rsegs))).
    { intros mmj y22 y23 y24 y25 -> -> -> -> HIj FRj SPj.
      clear HI FRs SP RP RV.
      pose proof (SP_ok mmj 24 SPj ltac:(lia) ltac:(lia)) as HSc.
      step. uspill. clear HSc.
      ugo. ufp (V s ch) w HM HL1 HL2 HC.
      ubyte (rb_lo N s ch). ugo.
      ubyte (rb_mid N s ch). ugo.
      ubyte (rb_hi N s ch).
      match goal with HI3 : INVU ?m3 _ |- _ =>
        assert (HI4 : INVU m3 (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat (ch + 1))))
          by (apply (INVU_list m3 _ _ HI3); subst L; rewrite rb_row_succ by lia; unfold rb_turn;
              rewrite <- !app_assoc; reflexivity);
        clear HI3
      end.
      rbe_st. step.
      rewrite (rbe_eqb N (ch + 1)) by lia.
      destruct (Z.eq_dec (ch + 1) N) as [Hlast|Hmore].
      - replace (N =? ch + 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. rbe_rif.
        rbe_st. step.
        rewrite (rbe_eqb (s + 1) ns) by lia.
        destruct (Z.eq_dec (s + 1) ns) as [Hend|Hnext].
        + replace (s + 1 =? ns) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. rbe_rif.
          do 11 rbe_st.
          match goal with FR3 : rw_cells _ ?m3 _ _, ST3 : stk _ ?m3 _ _ |- _ =>
            release_frame FR3 ST3 (bv_unsigned sp) end.
          step.
          destruct HI4 as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
          apply evt_done. unfold rbeu_post. do 13 eexists. split; [reflexivity|].
          split; [intros k Hk; rewrite rbe_fget6 by (first [exact Hk | reflexivity]); apply HG; exact Hk|].
          split; [exact I6|]. split; [exact I7|]. split; [exact I4|]. split; [eassumption|].
          intros x Hx. rewrite (I5 x Hx). rewrite <- Hend, rb_rows_succ by lia. rewrite <- Hlast. reflexivity.
        + replace (s + 1 =? ns) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rbe_rif.
          step. rewrite (rbe_lts 0 N) by lia. if_false.
          do 11 rbe_st.
          rewrite rbe_frot by reflexivity.
          match goal with HI5 : INVU ?m3 _ |- _ => eapply (IH (s + 1) 0 m3) end.
          all: lazymatch goal with
               | |- INVU _ _ => apply (INVU_list _ _ _ HI4); rewrite rb_rows_succ by lia; rewrite <- Hlast;
                               cbn [Z.to_nat rb_row]; rewrite app_nil_r; reflexivity
               | |- rw_cells _ _ _ _ => eassumption
               | |- stk _ _ _ _ => eassumption
               | |- forall k, _ -> _ => intros k Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
               | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hsp Hsp2 Ha HaE HP0 HP8; uweq
               | |- _ => clear - Hn Hs Hch HN Hlast Hnext; nia
               end.
      - replace (N =? ch + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rbe_rif.
        rewrite rbe_frot by reflexivity.
        match goal with HI5 : INVU ?m3 _ |- _ => eapply (IH s (ch + 1) m3) end.
        all: lazymatch goal with
             | |- INVU _ _ => exact HI4
             | |- rw_cells _ _ _ _ => eassumption
             | |- stk _ _ _ _ => eassumption
             | |- forall k, _ -> _ => intros k Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
             | |- _ = Z_to_bv 64 _ => clear - HN Hns Hs Hch HsN Hsp Hsp2 Ha HaE HP0 HP8; uweq
             | |- _ => clear - Hn Hs Hch HN Hmore; nia
             end. }
    destruct (Z.eq_dec (ch mod 2) 0) as [Ev|Od].
    - ucond. rbe_st.
      pose proof (SP_ok mm 8 SP ltac:(lia) ltac:(lia)) as HSa.
      step. uspill. clear HSa.
      ugo.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SP_ok mc 16 ltac:(eassumption) ltac:(lia) ltac:(lia)) as HSb end.
      step. uspill. clear HSb.
      ugo.
      eapply JOIN; [ ujeq | ujeq | ujeq | ujeq | eassumption | eassumption | eassumption ].
    - ucond. rbe_st.
      pose proof (SP_ok mm 8 SP ltac:(lia) ltac:(lia)) as HSa.
      step. uspill. clear HSa.
      ugo.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SP_ok mc 16 ltac:(eassumption) ltac:(lia) ltac:(lia)) as HSb end.
      step. uspill. clear HSb.
      ugo.
      eapply JOIN; [ ujeq | ujeq | ujeq | ujeq | eassumption | eassumption | eassumption ].
  Qed.

End Run.

Theorem reac_braid_encode_exact_holds : reac_braid_encode_exact_contract.
Proof.
  unfold reac_braid_encode_exact_contract, REAC_BRAID_ENCODE, REAC_BRAID_ENCODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    a N P ns Q V K -> -> -> -> -> HN HNe Hns FRM HI ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5.
  change (evt rsegs ?Qx ?ms) with
    (evt rsegs (rbeu_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K) ms).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  (* addi sp and the ten callee-saved stores *)
  do 11 step.
  step. rewrite (rbe_lts 0 ns) by lia. if_false.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
  assert (PRO : forall x14 x15 : word, x14 = Z_to_bv 64 ns ->
    evt rsegs (rbeu_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N)
               (Z_to_bv 64 P) (Z_to_bv 64 N) x14 x15 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13d04) fc None m3 (seg_rom rsegs)))
  end.
  { intros x14 x15 ->.
    do 16 rbe_st.
    step. rewrite (rbe_lts 0 N) by lia. if_false.
    do 11 rbe_st.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      assert (HI0 : INVU sp m a N P ns Q V m4 (rb_rows a N K (Z.to_nat 0) ++ rb_row a N K 0 (Z.to_nat 0)))
    end.
    { unfold INVU. cbn [rb_rows rb_row Z.to_nat app].
      split.
      { intros ch Hch. eapply bytes_at_transport; [apply HPb; exact Hch | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le8. destruct HD4; lia. }
      split.
      { intros s' ch Hs' Hch. eapply bytes_at_transport; [apply (proj1 (HV s' ch Hs' Hch)) | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le4. destruct (HD5 ch Hch); lia. }
      split; [exact HW|].
      split; [exact HI|].
      split; [intros x Hx; exact (MU x Hx)|].
      split; [eapply munch_weaken; [|exact MU]; intros x [H1 [H2 _]]; split; [exact H1|exact I]|].
      exact WM. }
    assert (HNns : 0 <= N * ns) by (clear - HN Hns; nia).
    eapply rbeu_loop with (n := Z.to_nat ((ns - 0) * N - 0)) (s := 0) (ch := 0).
    all: first
      [ exact HI0
      | match goal with |- forall k, _ -> _ => intros k Hk; reflexivity end
      | eassumption
      | reflexivity
      | lazymatch goal with |- _ = Z_to_bv 64 _ => clear - HN Hns HNns Ha HaE HP0 HP8 HP8m Rsp ST0; uweq end
      | apply bv_eq; rewrite !unsigned_lit_wrap; reflexivity
      | lia ]. }
  if_cases HC12.
  - apply (PRO (Z_to_bv 64 ns) (Z_to_bv 64 12)). reflexivity.
  - rbe_rif. step. apply (PRO (Z_to_bv 64 12) (Z_to_bv 64 12)).
    unfold bv_ltu in HC12. rewrite !unsigned_lit in HC12 by lia. apply Z.ltb_ge in HC12.
    f_equal. lia.
Qed.
