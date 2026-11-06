(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Step.v; 317 of its 350 lines of code are new or changed and 668 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import FloatExact RcBraid.
Import ListNotations.
Open Scope Z_scope.

Definition fcvt_l_s (md : rmode) (a : word) : word :=
  Z_to_bv 64 (fst (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s a)))).

Lemma exec_fcvt_l_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_L FC_S rd rs1 rm) c =
  EDone (rset rd (fcvt_l_s md (fget c rs1))
          (accrue (snd (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. unfold fcvt_l_s. fcvt_tac H. Qed.

Ltac exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | _ => idtac
    end
  end;
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

Ltac post_step i ::= idtac.

Lemma rbe_u32 : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 32) with (2^32). lia. Qed.

Lemma rbe_fc_same : forall fc : bv 32, Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits no_flags)) = fc.
Proof.
  intros fc. change (fflags_bits no_flags) with 0. rewrite Z.lor_0_r.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma rbe_testbit_hi32 : forall (y : bv 32) i, 32 <= i -> Z.testbit (bv_unsigned y) i = false.
Proof.
  intros y i Hi. pose proof (bv_unsigned_in_range 32 y) as Hy. change (bv_modulus 32) with (2^32) in Hy.
  destruct (Z.eq_dec (bv_unsigned y) 0) as [E|E]; [rewrite E; apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 32; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma rbe_unbox_box : forall y : bv 32, unbox_s (nan_box y) = y.
Proof.
  intros y. unfold unbox_s, nan_box, low32.
  pose proof (bv_unsigned_in_range 32 y) as Hy. change (bv_modulus 32) with (2^32) in Hy.
  assert (E : bv_unsigned (bv_concat 64 (Z_to_bv 32 (-1)) y) = Z.lor (Z.shiftl (2^32 - 1) 32) (bv_unsigned y)).
  { rewrite bv_concat_unsigned by reflexivity. reflexivity. }
  assert (Hhi : bv_unsigned (bv_extract 32 32 (bv_concat 64 (Z_to_bv 32 (-1)) y)) = Z.ones 32).
  { rewrite bv_extract_unsigned, E. apply Z.bits_inj'. intros i Hi.
    change (bv_wrap 32 ?x) with (x mod 2^32). change (Z.of_N 32) with 32.
    destruct (Z.lt_ge_cases i 32).
    - rewrite testbit_mod_pow2_low, Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
      replace (i + 32 - 32) with i by lia. change (2^32 - 1) with (Z.ones 32).
      rewrite (rbe_testbit_hi32 y (i + 32)) by lia. rewrite orb_false_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia.
      apply andb_false_r. }
  rewrite Hhi, Z.eqb_refl.
  apply bv_eq. rewrite bv_extract_unsigned, E, Z.shiftr_0_r. change (bv_wrap 32 ?x) with (x mod 2^32).
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite testbit_mod_pow2_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high, andb_false_r by lia.
    symmetry. apply rbe_testbit_hi32. lia.
Qed.

Lemma rbe_sgnj32 : forall y : bv 32, sgnj_val F_SGNJ y y = y.
Proof.
  intros y. pose proof (bv_unsigned_in_range 32 y) as Hy. change (bv_modulus 32) with (2^32) in Hy.
  apply bv_eq. unfold sgnj_val, bit.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
  change (Z.of_N (32 - 1)) with 31.
  change (bv_wrap (32 - 1) ?x) with (x mod 2^31).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.testbit (bv_unsigned y) 31) eqn:Eb.
  - change (bv_wrap 1 1) with 1.
    destruct (Z.lt_trichotomy i 31) as [Hlt|[->|Hgt]].
    + rewrite Z.shiftl_spec_low by lia. rewrite testbit_mod_pow2_low by lia. reflexivity.
    + rewrite Eb. rewrite Z.shiftl_spec_high by lia. reflexivity.
    + rewrite Z.shiftl_spec_high by lia. rewrite (Z.bits_above_log2 1 (i - 31)) by (cbn; lia).
      rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia. rewrite andb_false_r.
      symmetry. apply rbe_testbit_hi32. lia.
  - change (bv_wrap 1 0) with 0. rewrite Z.shiftl_0_l, Z.testbit_0_l. cbn [orb].
    destruct (Z.lt_ge_cases i 31) as [Hlt|Hge].
    + rewrite testbit_mod_pow2_low by lia. reflexivity.
    + rewrite <- Z.land_ones, Z.land_spec, Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec i 31) as [->|]; [rewrite Eb; reflexivity|]. symmetry. apply rbe_testbit_hi32. lia.
Qed.

Lemma rbe_fmv_box : forall y : bv 32, nan_box (sgnj_val F_SGNJ (unbox_s (nan_box y)) (unbox_s (nan_box y))) = nan_box y.
Proof. intros y. rewrite rbe_unbox_box, rbe_sgnj32. reflexivity. Qed.

Lemma rbe_ld4 : forall v, 0 <= v < 2^32 -> bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 v))) = Z_to_bv 32 v.
Proof.
  intros v Hv. apply bv_eq. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  rewrite unsigned_lit by lia. change (Z.of_N 32) with 32. rewrite Z.mod_mod by lia.
  rewrite rbe_u32 by lia. apply Z.mod_small. lia.
Qed.

Ltac rbe_fl_lit := repeat match goal with
  | |- context [nan_box (sgnj_val ?op (unbox_s (Z_to_bv 64 ?z)) (unbox_s (Z_to_bv 64 ?z)))] =>
      let t := constr:(nan_box (sgnj_val op (unbox_s (Z_to_bv 64 z)) (unbox_s (Z_to_bv 64 z)))) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [nan_box (sgnj_val F_SGNJ (unbox_s (nan_box ?y)) (unbox_s (nan_box ?y)))] =>
      rewrite (rbe_fmv_box y)
  end.

Ltac rbe_closed t :=
  lazymatch t with
  | true => idtac
  | false => idtac
  | Z_to_bv _ ?z => is_Zlit z
  | negb ?x => rbe_closed x
  | bv_eqb ?x ?y => rbe_closed x; rbe_closed y
  | bv_ltu ?x ?y => rbe_closed x; rbe_closed y
  | bv_lts ?x ?y => rbe_closed x; rbe_closed y
  | bv_leu ?x ?y => rbe_closed x; rbe_closed y
  end.

Ltac rbe_rif := try (lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  rbe_closed c;
  let v := eval vm_compute in c in
  lazymatch v with
  | true => replace c with true by (vm_compute; reflexivity); cbv iota
  | false => replace c with false by (vm_compute; reflexivity); cbv iota
  end end).

Ltac rbe_st := rbe_rif; step; rbe_fl_lit; rbe_rif.

Ltac rbe_fpc := unfold fmul_s, fari_fl, fari_sem, fcmp_fl, fcmp_sem, flt_s, fcvt_l_s, bword;
  rewrite ?rbe_unbox_box;
  repeat match goal with |- context [bv_unsigned (unbox_s (Z_to_bv 64 ?z))] =>
    let z' := eval vm_compute in (bv_unsigned (unbox_s (Z_to_bv 64 z))) in
    change (bv_unsigned (unbox_s (Z_to_bv 64 z))) with z' end.

Lemma rbe_pipe : forall v k, rb_sample v k ->
  0 <= v < 2^32 /\ exists w, 0 <= w < 2^32 /\
    fp_mul fmt_single RNE v F2P23 = (w, no_flags) /\
    fp_lt fmt_single FCLAMP_HI w = (false, no_flags) /\
    fp_lt fmt_single w FCLAMP_LO = (false, no_flags) /\
    fp_to_int fmt_single RNE true 64 w = (k mod 2^64, no_flags).
Proof.
  intros v k [Hk [-> | [-> ->]]].
  - split; [apply f32_range; lia|]. exists (f32 k 0). split; [apply f32_range; lia|].
    split; [apply f32_mul_p23; lia|]. split; [apply f32_lt_hi; lia|]. split; [apply f32_lt_lo; lia|].
    apply f32_to_int; lia.
  - split; [lia|]. exists (2^31). split; [lia|]. vm_compute. repeat split.
Qed.

Lemma rbe_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rbe_lts : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rbe_land_even : forall x, 0 <= x < 2^31 -> Z.land x 2147483646 = x - x mod 2.
Proof.
  intros x Hx.
  replace (x - x mod 2) with (Z.shiftl (Z.shiftr x 1) 1)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_eq by lia; change (2^1) with 2; lia).
  change 2147483646 with (Z.shiftl (Z.ones 30) 1).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hi0].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. replace (i - 1 + 1) with i by lia.
    destruct (Z.lt_ge_cases (i - 1) 30).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma rbe_land1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x Hx. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rbe_neg5 : forall c, 0 <= c <= 1 -> Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - c)))) 5 = 5 * c.
Proof. intros c Hc. assert (c = 0 \/ c = 1) as [-> | ->] by lia; vm_compute; reflexivity. Qed.

Lemma rbe_le1 : forall e, le1 (Z_to_bv 64 e) = [Z_to_bv 8 e].
Proof.
  intros e. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. apply mod_mod8_of_modw. lia.
Qed.

Lemma rbe_b0 : forall k, Z_to_bv 8 (k mod 2^64) = Z_to_bv 8 ((k mod 2^24) mod 256).
Proof.
  intros k. apply Z_to_bv8_mod. change 256 with (2^8). rewrite Z.mod_mod by lia.
  rewrite !mod_mod8_of_modw by lia. reflexivity.
Qed.

Lemma rbe_b1 : forall k, Z_to_bv 8 (Z.shiftr (k mod 2^64) 8) = Z_to_bv 8 ((k mod 2^24) / 256 mod 256).
Proof.
  intros k. apply Z_to_bv8_mod. change 256 with (2^8). rewrite Z.mod_mod by lia.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite !shiftr_mod_mod8 by lia. reflexivity.
Qed.

Lemma rbe_b2 : forall k, Z_to_bv 8 (Z.shiftr (k mod 2^64) 16) = Z_to_bv 8 ((k mod 2^24) / 65536).
Proof.
  intros k. apply Z_to_bv8_mod. change 65536 with (2^16).
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite !shiftr_mod_mod8 by lia. reflexivity.
Qed.

Lemma rbe_rd8 : forall segs m A w, bytes_at segs m A (le8 w) -> ov_read_bytes segs m (wa A) 8 = Some (le8 w).
Proof.
  intros segs m A w H. rewrite <- (Z.add_0_r A) at 1.
  rewrite (bytes_at_read segs m A _ 0 8 H) by (rewrite ?length_le8; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le8; lia ].
Qed.

Lemma rbe_rd4 : forall segs m A w, bytes_at segs m A (le4 w) -> ov_read_bytes segs m (wa A) 4 = Some (le4 w).
Proof.
  intros segs m A w H. rewrite <- (Z.add_0_r A) at 1.
  rewrite (bytes_at_read segs m A _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma rbe_wr_agree : forall (W : list ivl) (m1 m2 : word -> option byte) X b,
  0 <= X < 2^64 -> (forall x, outside W (bv_unsigned x) -> m1 x = m2 x) ->
  forall x, outside W (bv_unsigned x) -> write_to_mem m1 (wa X) [b] x = write_to_mem m2 (wa X) [b] x.
Proof.
  intros W m1 m2 X b HX H x Hx. rewrite !write_to_mem_spec by (cbn [length Z.of_nat]; lia).
  destruct (_ && _)%bool; [reflexivity| apply H; exact Hx].
Qed.

Lemma rb_enc_app : forall m L1 L2, rb_enc m (L1 ++ L2) = rb_enc (rb_enc m L1) L2.
Proof. intros. unfold rb_enc. apply fold_left_app. Qed.

Lemma rbe_outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [Ho|Ho].
  - destruct (Z_lt_dec x lo) as [H1|H1]; [left; split; [lia|exact Ho]|].
    destruct (Z_lt_dec x hi) as [H2|H2]; [right; intros [H3 _]; lia | left; split; [lia|exact Ho]].
  - right. intros [_ H]. exact (Ho H).
Qed.

Lemma rbe_mem_inv_munch : forall segs W m m', munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview segs m x <> None) ->
  mem_inv segs m -> mem_inv segs m'.
Proof.
  intros segs W m m' MU WV HI x b Hx. destruct (rbe_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (HI x b Hx).
  - destruct (m x) eqn:E.
    + exact (HI x _ E).
    + apply (wview_not_ro segs m x); [apply WV; exact Ho | exact E].
Qed.

Lemma rbe_stk_wv : forall segs m lo hi, stk segs m lo hi ->
  forall x : word, ~ outside [(lo, hi)] (bv_unsigned x) -> wview segs m x <> None.
Proof.
  intros segs m lo hi (H1 & H2 & H) x Hx. cbn [outside] in Hx.
  assert (lo <= bv_unsigned x < hi) by (destruct (Z_lt_dec (bv_unsigned x) lo); destruct (Z_lt_dec (bv_unsigned x) hi); tauto).
  destruct (H (bv_unsigned x) H0) as [W _]. unfold wa in W. rewrite Z_to_bv_lit_self in W. exact W.
Qed.

Lemma rbe_frot : forall (k10 k11 k12 k13 k14 k15 : bv 5) x10 x11 c12 c13 c14 c15 (G : bvmap 5 word),
  bv_unsigned k10 = 10 -> bv_unsigned k11 = 11 -> bv_unsigned k12 = 12 -> bv_unsigned k13 = 13 ->
  bv_unsigned k14 = 14 -> bv_unsigned k15 = 15 ->
  bvmap_set k10 x10 (bvmap_set k11 x11 (bvmap_set k12 c12 (bvmap_set k13 c13 (bvmap_set k14 c14 (bvmap_set k15 c15 G)))))
  = bvmap_set k12 c12 (bvmap_set k13 c13 (bvmap_set k14 c14 (bvmap_set k15 c15 (bvmap_set k10 x10 (bvmap_set k11 x11 G))))).
Proof.
  intros k10 k11 k12 k13 k14 k15 x10 x11 c12 c13 c14 c15 G H10 H11 H12 H13 H14 H15.
  assert (NE : forall p q : bv 5, bv_unsigned p <> bv_unsigned q -> bv_eqb p q = false)
    by (intros p q Hpq; unfold bv_eqb; apply Z.eqb_neq; exact Hpq).
  rewrite (bvmap_set_set_comm k11 k12) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k11 k13) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k11 k14) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k11 k15) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k10 k12) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k10 k13) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k10 k14) by (apply NE; lia).
  rewrite (bvmap_set_set_comm k10 k15) by (apply NE; lia).
  reflexivity.
Qed.

Lemma rbe_key_ne : forall (c : bv 5) (k : bv 5), 10 <= bv_unsigned c <= 15 -> ~ (10 <= bv_unsigned k <= 15) ->
  bv_eqb c k = false.
Proof. intros c k Hc Hk. unfold bv_eqb. apply Z.eqb_neq. intros E. apply Hk. rewrite <- E. exact Hc. Qed.

Lemma rbe_fget2 : forall (k10 k11 : bv 5) x10 x11 (G : bvmap 5 word) (k : bv 5),
  bv_unsigned k10 = 10 -> bv_unsigned k11 = 11 -> ~ (10 <= bv_unsigned k <= 15) ->
  reg_get (bvmap_set k10 x10 (bvmap_set k11 x11 G)) k = reg_get G k.
Proof.
  intros k10 k11 x10 x11 G k H10 H11 Hk.
  rewrite (freg_get_other _ k10) by (apply rbe_key_ne; [lia | exact Hk]).
  rewrite (freg_get_other _ k11) by (apply rbe_key_ne; [lia | exact Hk]). reflexivity.
Qed.

Lemma rbe_fget6 : forall (k10 k11 k12 k13 k14 k15 : bv 5) x10 x11 c12 c13 c14 c15 (G : bvmap 5 word) (k : bv 5),
  bv_unsigned k10 = 10 -> bv_unsigned k11 = 11 -> bv_unsigned k12 = 12 -> bv_unsigned k13 = 13 ->
  bv_unsigned k14 = 14 -> bv_unsigned k15 = 15 -> ~ (10 <= bv_unsigned k <= 15) ->
  reg_get (bvmap_set k10 x10 (bvmap_set k11 x11 (bvmap_set k12 c12 (bvmap_set k13 c13 (bvmap_set k14 c14
    (bvmap_set k15 c15 G)))))) k = reg_get G k.
Proof.
  intros k10 k11 k12 k13 k14 k15 x10 x11 c12 c13 c14 c15 G k H10 H11 H12 H13 H14 H15 Hk.
  rewrite (freg_get_other _ k10) by (apply rbe_key_ne; [lia | exact Hk]).
  rewrite (freg_get_other _ k11) by (apply rbe_key_ne; [lia | exact Hk]).
  rewrite (freg_get_other _ k12) by (apply rbe_key_ne; [lia | exact Hk]).
  rewrite (freg_get_other _ k13) by (apply rbe_key_ne; [lia | exact Hk]).
  rewrite (freg_get_other _ k14) by (apply rbe_key_ne; [lia | exact Hk]).
  rewrite (freg_get_other _ k15) by (apply rbe_key_ne; [lia | exact Hk]). reflexivity.
Qed.

Lemma rb_row_succ : forall a N K s ch, 0 <= ch ->
  rb_row a N K s (Z.to_nat (ch + 1)) = rb_row a N K s (Z.to_nat ch) ++ rb_turn a N s ch (K s ch mod 2^24).
Proof.
  intros a N K s ch Hch. replace (Z.to_nat (ch + 1)) with (S (Z.to_nat ch)) by lia.
  cbn [rb_row]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma rb_rows_succ : forall a N K s, 0 <= s ->
  rb_rows a N K (Z.to_nat (s + 1)) = rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat N).
Proof.
  intros a N K s Hs. replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia.
  cbn [rb_rows]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma rbe_pos_bound : forall N s ch ns, 0 <= s < ns -> 0 <= ch < N -> N mod 2 = 0 ->
  0 <= rb_G N s ch /\ 3 * rb_G N s ch + 6 <= 3 * N * ns.
Proof.
  intros N s ch ns Hs Hch HN. unfold rb_G.
  assert (s * N <= ns * N - N) by nia. assert (0 <= s * N) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)). pose proof (Z.div_mod ch 2 ltac:(lia)).
  pose proof (Z.div_mod N 2 ltac:(lia)). split; [lia|]. nia.
Qed.

Ltac rbe_weq :=
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by nia end;
  rewrite ?Z.div_mul by lia;
  first [ reflexivity | f_equal; nia ].

Lemma rbe_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma rbe_stk_wr : forall segs m lo hi, stk segs m lo hi -> lo <= hi -> wr_at segs m lo (hi - lo).
Proof.
  intros segs m lo hi (H1 & H2 & H) Hle. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as [W _]. exact W.
Qed.

Lemma rbe_wr_out : forall W (m : word -> option byte) X bs x, 0 <= X -> X + Z.of_nat (length bs) <= 2^64 ->
  inside W X (Z.of_nat (length bs)) -> outside W (bv_unsigned x) -> write_to_mem m (wa X) bs x = m x.
Proof.
  intros W m X bs x H0 H1 Hin Hx. rewrite write_to_mem_spec by lia.
  pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 X (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (X + Z.of_nat (length bs)));
    cbn [andb]; try reflexivity.
  exfalso. eapply (inside_not_outside W X _ (bv_unsigned x) Hin); [lia | exact Hx].
Qed.

Lemma rbe_rw_cells_tail : forall segs m A c cs, rw_cells segs m A (c :: cs) ->
  rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros segs m A c cs [[[Hc Hcs] (Ha & Hl & Hb)] (Wa & Wl & Ww)].
  cbn [cells_bytes cells_size] in *. rewrite length_app, (cbytes_length c Hc) in Hl.
  split; [split; [exact Hcs|]|].
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + Z.of_nat i) with (A + Z.of_nat (csize c + i)) by lia.
    rewrite Hb by (rewrite length_app, (cbytes_length c Hc); lia).
    rewrite nth_error_app2 by (rewrite (cbytes_length c Hc); lia).
    rewrite (cbytes_length c Hc). f_equal. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply Ww. lia.
Qed.

Lemma rbe_land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
