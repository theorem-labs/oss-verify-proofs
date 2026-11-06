(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec StepTac StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg RelocSpan CanonSpans.      (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition wr_readable_chk (segs : list Segment) : bool :=
  forallb (fun seg => implb (seg_writable seg) (seg_readable seg)) segs.

Lemma wr_readable_chk_sound : forall segs, wr_readable_chk segs = true -> wr_readable segs.
Proof.
  intros segs H seg Hin Hw. unfold wr_readable_chk in H. rewrite forallb_forall in H.
  specialize (H seg Hin). rewrite Hw in H. exact H.
Qed.

Definition pages_chk {RL : Reloc} : bool :=
  (2^16 <=? rl_img_lo) && (rl_img_lo <=? rl_rw_lo) && (rl_rw_lo + 4096 <=? rl_img_hi) && (rl_img_hi <=? 2^32).

Class RelocLept (RL : Reloc) := {
  rl_wr_readable_ok : wr_readable_chk rl_segs = true;
  rl_pages_ok : pages_chk = true;
  (* [comment removed for export] *)
  rl_clr_extra : list (Z * Z)
}.

Lemma rl_wr_readable : forall {RL : Reloc} {RLP : RelocLept RL}, wr_readable rl_segs.
Proof. intros RL RLP. exact (wr_readable_chk_sound _ rl_wr_readable_ok). Qed.

Lemma rl_pages : forall {RL : Reloc} {RLP : RelocLept RL},
  2^16 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo + 4096 <= rl_img_hi /\ rl_img_hi <= 2^32.
Proof.
  intros RL RLP. pose proof rl_pages_ok as H. unfold pages_chk in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. auto.
Qed.

(* [comment removed for export] *)
Section Strs.
Context {RL : Reloc}.

Definition str_okP (a k : Z) : Prop :=
  rostr_chk rl_segs a k = true /\ 0 <= k <= 200 /\ rl_img_lo <= a /\ a + SSP.rostr_win a k <= rl_rw_lo.

Definition str_okb (e : positive * Z * Z) : bool :=
  let '(b, c, k) := e in
  let a := c + rl_delta b in
  rostr_chk rl_segs a k && (0 <=? k) && (k <=? 200) && (rl_img_lo <=? a) && (a + SSP.rostr_win a k <=? rl_rw_lo)
  && (a + 216 <=? rl_rw_lo).        (* [comment removed for export] *)

Definition strs_check (tbl : list (positive * Z * Z)) : bool := forallb str_okb tbl.

Definition str_eqb (e1 e2 : positive * Z * Z) : bool :=
  let '(b1, c1, k1) := e1 in let '(b2, c2, k2) := e2 in Pos.eqb b1 b2 && Z.eqb c1 c2 && Z.eqb k1 k2.

Lemma str_fact : forall tbl, strs_check tbl = true -> forall b c k,
  existsb (str_eqb (b, c, k)) tbl = true -> str_okP (c + rl_delta b) k.
Proof.
  intros tbl Hok b c k Hex. apply existsb_exists in Hex as ([[b' c'] k'] & Hin & He).
  unfold str_eqb in He. apply andb_prop in He as [He Hk]. apply andb_prop in He as [Hb Hc].
  apply Pos.eqb_eq in Hb. apply Z.eqb_eq in Hc. apply Z.eqb_eq in Hk. subst b' c' k'.
  unfold strs_check in Hok. rewrite forallb_forall in Hok. specialize (Hok _ Hin). unfold str_okb in Hok.
  apply andb_prop in Hok as [Hok H6]. apply andb_prop in Hok as [Hok H5]. apply andb_prop in Hok as [Hok H4]. apply andb_prop in Hok as [Hok H3].
  apply andb_prop in Hok as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  unfold str_okP. auto.
Qed.

Definition str_at (b : positive) (c : Z) (e : positive * Z * Z) : bool := let '(b', c', _) := e in Pos.eqb b b' && Z.eqb c c'.

Lemma str_far_fact : forall tbl, strs_check tbl = true -> forall b c,
  existsb (str_at b c) tbl = true -> c + rl_delta b + 216 <= rl_rw_lo.
Proof.
  intros tbl Hok b c Hex. apply existsb_exists in Hex as ([[b' c'] k'] & Hin & He).
  unfold str_at in He. apply andb_prop in He as [Hb Hc]. apply Pos.eqb_eq in Hb. apply Z.eqb_eq in Hc. subst b' c'.
  unfold strs_check in Hok. rewrite forallb_forall in Hok. specialize (Hok _ Hin). unfold str_okb in Hok.
  apply andb_prop in Hok as [_ H6]. apply Z.leb_le in H6. exact H6.
Qed.

(* [comment removed for export] *)
Lemma str_span : forall a k, str_okP a k -> 0 <= k <= 200 /\ rl_img_lo <= a /\ a + k + 1 <= rl_rw_lo.
Proof.
  intros a k (_ & Hk & Ha & Hw). unfold SSP.rostr_win in Hw.
  pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + k) 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma rostr_win_bd : forall a k, k + 1 <= SSP.rostr_win a k <= k + 8.
Proof.
  intros a k. unfold SSP.rostr_win.
  pose proof (Z.div_mod (a + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + k) 8 ltac:(lia)). lia.
Qed.
End Strs.

(* [comment removed for export] *)
Ltac rl_str_tac tbl ok :=
  lazymatch goal with
  | |- _ (?c + @rl_delta ?RL ?b) ?k => exact (@str_fact RL tbl ok b c k (@eq_refl bool true))
  end.

(* [comment removed for export] *)
Ltac rl_dbounds_rec l :=
  lazymatch l with
  | nil => idtac
  | cons (@rl_delta ?RL ?b) ?t => let h := fresh "Hdbd" in pose proof (@rl_delta_bd RL b) as h; rl_dbounds_rec t
  end.
(* [comment removed for export] *)
Ltac rl_dbounds l := rl_dbounds_rec l; rl_chains l.

(* [comment removed for export] *)
Lemma rl_cell_val : forall {RL : Reloc} n b c, 2^16 <= c < 2^63 ->
  word_to_le_bytes n (rl (rl_delta b) c) = Z_to_le_bytes n (c + rl_delta b).
Proof. intros RL n b c Hc. unfold word_to_le_bytes. rewrite rl_delta_u by exact Hc. reflexivity. Qed.

(* [comment removed for export] *)
Ltac rl_zval := gres; pin; imm_norm; rewrite ?rl_unfold; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
Ltac rl_bare_in H :=
  repeat match type of H with
         | context [(?c + @rl_delta ?RL ?b)%Z] =>
             let z := eval vm_compute in (c + @rl_delta RL b)%Z in
             change (c + @rl_delta RL b)%Z with z in H
         end.
Ltac rl_bare :=
  repeat match goal with
         | |- context [(?c + @rl_delta ?RL ?b)%Z] =>
             let z := eval vm_compute in (c + @rl_delta RL b)%Z in
             change (c + @rl_delta RL b)%Z with z
         end.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall p, 0 <= p < 2^64 -> Z.lxor p (2^64 - 1) = 2^64 - 1 - p.
Proof.
  intros p Hp. change (2^64 - 1) with (Z.ones 64).
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) p).
  - apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec.
    destruct (Z_lt_ge_dec n 64) as [Hlt|Hge].
    + rewrite Z.ones_spec_low by lia. destruct (Z.testbit p n); reflexivity.
    + rewrite Z.ones_spec_high by lia.
      assert (Hb : Z.testbit p n = false).
      { destruct (Z.eq_dec p 0) as [->|Hne]; [apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|]. assert (Z.log2 p < 64) by (apply Z.log2_lt_pow2; lia). lia. }
      rewrite Hb. reflexivity.
  - destruct (Z.eq_dec p 0) as [->|Hne]; [apply Z.ldiff_0_l|].
    apply Z.ldiff_ones_r_low; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma rl_not : forall d c, 0 <= c + d < 2^64 -> v_xori (rl d c) (-1) = Z_to_bv 64 (2^64 - 1 - (c + d)).
Proof.
  intros d c H. unfold v_xori. rewrite rl_u by exact H. change (bv_wrap 64 (-1)) with (2^64 - 1).
  rewrite lxor_ones64 by exact H. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac rl_condZ :=
  pin; rewrite ?rl_not by lia; rewrite ?rl_unfold;
  rewrite ?c_ltu_Z by lia; rewrite ?c_lts_Z by lia; rewrite ?c_eq_Zm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq | reflexivity ];
  rewrite ?Z.mod_small by lia; lia.

(* [comment removed for export] *)
Ltac rl_pgbounds := let h := fresh "Hpgbd" in pose proof rl_pages as h.

(* [comment removed for export] *)
Ltac rl_lay := rl_pgbounds; rl_dbounds (dA_1e348 :: dA_1e3a0 :: dA_1e3b8 :: dA_1f3f8 :: dA_1f430 :: dA_2f6b0 :: dA_2f848 :: dF_1365c :: dF_13660 :: dF_13694 :: dF_13730 :: dF_15a00 :: dF_15b38 :: dF_15b3c :: dF_1c9b4 :: dF_1cdb8 :: nil).

(* [comment removed for export] *)
Ltac rl_exact t :=
  first [ exact t
        | rewrite ?Z.add_0_r; exact t
        | let H := fresh "RLX" in
          pose proof t as H; rewrite ?rl_unfold in H; rewrite ?rl_unfold; rewrite ?Z.add_0_r in H; rewrite ?Z.add_0_r; exact H ].

(* [comment removed for export] *)
Section Spans.
Context {RL : Reloc}.
Definition span_P (e : bool * positive * Z * Z) : Prop :=
  let '(rw, b, c, n) := e in
  if rw then rl_rw_lo <= c + rl_delta b /\ c + rl_delta b + n <= rl_img_hi
  else rl_img_lo <= c + rl_delta b /\ c + rl_delta b + n <= rl_rw_lo.
Definition span_okb (e : bool * positive * Z * Z) : bool :=
  let '(rw, b, c, n) := e in
  if rw then (rl_rw_lo <=? c + rl_delta b) && (c + rl_delta b + n <=? rl_img_hi)
  else (rl_img_lo <=? c + rl_delta b) && (c + rl_delta b + n <=? rl_rw_lo).
Definition spans_check (tbl : list (bool * positive * Z * Z)) : bool := forallb span_okb tbl.
Lemma span_fact : forall tbl, spans_check tbl = true -> forall i e, nth_error tbl i = Some e -> span_P e.
Proof.
  intros tbl Hok i e Hi. unfold spans_check in Hok. rewrite forallb_forall in Hok.
  specialize (Hok e (nth_error_In _ _ Hi)). destruct e as [[[rw b] c] n]. unfold span_okb in Hok. unfold span_P.
  destruct rw; apply andb_prop in Hok as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; auto.
Qed.
End Spans.

(* [comment removed for export] *)
Ltac rl_jr_fix :=
  repeat match goal with
         | H : ret_ok (rl ?d ?c) |- context [v_jalr (rl ?d ?c) ?e] =>
             replace (v_jalr (rl d c) e) with (rl d c) by (symmetry; exact H)
         end.
