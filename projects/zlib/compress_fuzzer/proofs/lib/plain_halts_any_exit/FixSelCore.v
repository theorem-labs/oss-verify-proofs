(** * FixSelCore — the concrete-table core for the FIXED-leg selection
    mirrors (q7-decode fixsel fork, 2026-08-21, OFF-TREE SCRATCH —
    PROVISIONAL: statement owner an earlier development run, Gap7FixSel.v md5
    ; prover q7 per the fastsel
    protocol ownership ruling).

    Three layers:
    1. [zr_own_agree] — two ent functions owning the SAME root table at
       the SAME lengths agree on every root-fitting coded symbol
       (prefix-freeness + [hdecode_complete] on the index spelling; the
       index witness is Q6R's [zr_cwval], the [write_bits] inverse).
    2. The DESIGN-PREMISE vm pins: at the concrete fixed tables the
       invalid-op class is EXACTLY {286,287} (len, after excluding the
       op&32 EOB) / {30,31} (dist) — the symbols whose declarative
       base-table lookups ([length_base]/[dist_base]) are None.  If any
       of these vm equations failed, g1's strengthened-BAD spelling
       would be falsified (statement-owner STOP protocol).
    3. [zr_invl_own]/[zr_invd_own] — the quantified-ent dischargers the
       sel mirrors consume: ownership at the concrete table turns the
       machine's invalid-op branch facts into the declarative failure
       ([257 <= sym] + [nth_error length_base (sym-257) = None]; dist
       analog), via 1 + 2.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec InflateFast Inflate
  ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6R.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Ownership agreement.
   ========================================================================== *)

Lemma zr_cwval_range : forall cw, 0 <= zr_cwval cw < 2 ^ Z.of_nat (length cw).
Proof.
  induction cw as [|b tl IH]; cbn [zr_cwval length].
  - cbn. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct b; lia.
Qed.

Lemma zr_own_agree :
  forall (T : ztbl) (root : Z) (lens : list nat) (maxBits : nat)
         (ent1 ent2 : nat -> Code),
    0 < root <= 15 ->
    ValidLengths lens maxBits ->
    ZReproQ6M.zr_root_own T root lens maxBits ent1 ->
    ZReproQ6M.zr_root_own T root lens maxBits ent2 ->
    forall sym cw, code_for lens maxBits sym = Some cw ->
    Z.of_nat (length cw) <= root ->
    ent1 sym = ent2 sym.
Proof.
  intros T root lens maxBits ent1 ent2 Hroot HV Hown1 Hown2 sym cw Hcf Hfit.
  set (i := zr_cwval cw).
  pose proof (zr_cwval_range cw) as Hcr. fold i in Hcr.
  assert (Hir : 0 <= i < 2 ^ root).
  { split; [lia|].
    apply (Z.lt_le_trans _ (2 ^ Z.of_nat (length cw))); [lia|].
    apply Z.pow_le_mono_r; lia. }
  set (w := write_bits (Z.to_nat root) i).
  assert (Hkn : (length cw <= Z.to_nat root)%nat).
  { assert (HZ : Z.of_nat (length cw) <= Z.of_nat (Z.to_nat root))
      by (rewrite Z2Nat.id; lia).
    lia. }
  assert (Hwpref : firstn (length cw) w = cw).
  { unfold w. rewrite firstn_write_bits by exact Hkn.
    apply zr_write_cwval. }
  assert (KEY : forall (ent : nat -> Code) (s1 : nat) (c1 : list bool),
      code_for lens maxBits s1 = Some c1 ->
      T i = ent s1 ->
      firstn (length c1) w = c1 ->
      T i = ent sym).
  { intros ent s1 c1 Hcf1 HTi Hp1.
    pose proof (firstn_skipn (length c1) w) as FS1.
    rewrite Hp1 in FS1.
    pose proof (hdecode_complete nat Nat.eq_dec (code_table lens maxBits)
                  c1 s1 (skipn (length c1) w)
                  (code_table_prefix_free lens maxBits HV)
                  (proj2 (code_table_In_iff lens maxBits s1 c1) Hcf1)) as Hd1.
    rewrite FS1 in Hd1.
    pose proof (firstn_skipn (length cw) w) as FS0.
    rewrite Hwpref in FS0.
    pose proof (hdecode_complete nat Nat.eq_dec (code_table lens maxBits)
                  cw sym (skipn (length cw) w)
                  (code_table_prefix_free lens maxBits HV)
                  (proj2 (code_table_In_iff lens maxBits sym cw) Hcf)) as Hd0.
    rewrite FS0 in Hd0.
    rewrite Hd0 in Hd1.
    injection Hd1 as Hs _.
    rewrite Hs. exact HTi. }
  destruct (Hown1 i Hir) as (s1 & c1 & Hcf1 & _ & HT1 & _ & Hp1).
  destruct (Hown2 i Hir) as (s2 & c2 & Hcf2 & _ & HT2 & _ & Hp2).
  rewrite <- (KEY ent1 s1 c1 Hcf1 HT1 Hp1).
  exact (KEY ent2 s2 c2 Hcf2 HT2 Hp2).
Qed.

(* ==========================================================================
   2.  The vm pins at the concrete fixed tables.
   ========================================================================== *)

Definition zr_fitl_ok_at (sym : nat) : bool :=
  match code_for fixed_lit_lengths 15%nat sym with
  | Some cw => (length cw <=? 9)%nat
  | None => true
  end.

Lemma zr_fitl_all : forallb zr_fitl_ok_at (seq 0 288) = true.
Proof. vm_compute. reflexivity. Qed.

Definition zr_fitd_ok_at (sym : nat) : bool :=
  match code_for fixed_dist_lengths 15%nat sym with
  | Some cw => (length cw <=? 5)%nat
  | None => true
  end.

Lemma zr_fitd_all : forallb zr_fitd_ok_at (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_cw_fits_l : forall sym cw,
  code_for fixed_lit_lengths 15%nat sym = Some cw ->
  Z.of_nat (length cw) <= 9.
Proof.
  intros sym cw HC.
  pose proof (code_for_range _ _ _ _ HC) as Hr.
  rewrite zr_lit_len_288 in Hr.
  pose proof (proj1 (forallb_forall zr_fitl_ok_at (seq 0 288))
                zr_fitl_all sym ltac:(apply in_seq; lia)) as HB.
  unfold zr_fitl_ok_at in HB. rewrite HC in HB.
  apply Nat.leb_le in HB. lia.
Qed.

Lemma zr_cw_fits_d : forall sym cw,
  code_for fixed_dist_lengths 15%nat sym = Some cw ->
  Z.of_nat (length cw) <= 5.
Proof.
  intros sym cw HC.
  pose proof (code_for_range _ _ _ _ HC) as Hr.
  rewrite zr_dist_len_32 in Hr.
  pose proof (proj1 (forallb_forall zr_fitd_ok_at (seq 0 32))
                zr_fitd_all sym ltac:(apply in_seq; lia)) as HB.
  unfold zr_fitd_ok_at in HB. rewrite HC in HB.
  apply Nat.leb_le in HB. lia.
Qed.

(** The DESIGN-PREMISE checks (both-fail-together at the corners). *)
Definition zr_invl_ok_at (sym : nat) : bool :=
  match code_for fixed_lit_lengths 15%nat sym with
  | None => true
  | Some _ =>
      if negb (Z.land (c_op (zr_entl_fix sym)) 64 =? 0)
         && (Z.land (c_op (zr_entl_fix sym)) 32 =? 0)
      then (257 <=? sym)%nat
           && match nth_error length_base (sym - 257)%nat with
              | None => true
              | Some _ => false
              end
      else true
  end.

Lemma zr_invl_all : forallb zr_invl_ok_at (seq 0 288) = true.
Proof. vm_compute. reflexivity. Qed.

Definition zr_invd_ok_at (sym : nat) : bool :=
  match code_for fixed_dist_lengths 15%nat sym with
  | None => true
  | Some _ =>
      if negb (Z.land (c_op (zr_entd_fix sym)) 64 =? 0)
      then match nth_error dist_base sym with
           | None => true
           | Some _ => false
           end
      else true
  end.

Lemma zr_invd_all : forallb zr_invd_ok_at (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

(** The corner sets, pinned exactly (receipt tier: the invalid class at
    the concrete tables and the None-ness of its base lookups). *)
Lemma zr_invl_corners_64 :
  filter (fun sym => negb (Z.land (c_op (zr_entl_fix sym)) 64 =? 0))
         (seq 0 288) = [256; 286; 287]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_invl_corners_strict :
  filter (fun sym => negb (Z.land (c_op (zr_entl_fix sym)) 64 =? 0)
                     && (Z.land (c_op (zr_entl_fix sym)) 32 =? 0))
         (seq 0 288) = [286; 287]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_invd_corners :
  filter (fun sym => negb (Z.land (c_op (zr_entd_fix sym)) 64 =? 0))
         (seq 0 32) = [30; 31]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_lenbase_none_29 : nth_error length_base 29%nat = None.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_lenbase_none_30 : nth_error length_base 30%nat = None.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_distbase_none_30 : nth_error dist_base 30%nat = None.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_distbase_none_31 : nth_error dist_base 31%nat = None.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   3.  The quantified-ent dischargers.
   ========================================================================== *)

Lemma zr_agree_l : forall entl,
  ZReproQ6M.zr_root_own lenfix 9 fixed_lit_lengths 15%nat entl ->
  forall sym cw, code_for fixed_lit_lengths 15%nat sym = Some cw ->
  entl sym = zr_entl_fix sym.
Proof.
  intros entl Hown sym cw Hcf.
  exact (zr_own_agree lenfix 9 fixed_lit_lengths 15%nat entl zr_entl_fix
           ltac:(lia) fixed_lit_valid Hown zr_ownl_fix sym cw Hcf
           (zr_cw_fits_l sym cw Hcf)).
Qed.

Lemma zr_agree_d : forall entd,
  ZReproQ6M.zr_root_own distfix 5 fixed_dist_lengths 15%nat entd ->
  forall sym cw, code_for fixed_dist_lengths 15%nat sym = Some cw ->
  entd sym = zr_entd_fix sym.
Proof.
  intros entd Hown sym cw Hcf.
  exact (zr_own_agree distfix 5 fixed_dist_lengths 15%nat entd zr_entd_fix
           ltac:(lia) fixed_dist_valid Hown zr_ownd_fix sym cw Hcf
           (zr_cw_fits_d sym cw Hcf)).
Qed.

(** The invalid-corner packs the sel mirrors thread (generic spelling;
    at the fixed lists they are discharged from ownership alone). *)
Definition zr_inv_len (ll : list nat) (entl : nat -> Code) : Prop :=
  forall sym cw, code_for ll 15%nat sym = Some cw ->
    Z.land (c_op (entl sym)) 64 <> 0 ->
    Z.land (c_op (entl sym)) 32 = 0 ->
    (257 <= sym)%nat /\ nth_error length_base (sym - 257)%nat = None.

Definition zr_inv_dist (dl : list nat) (entd : nat -> Code) : Prop :=
  forall sym cw, code_for dl 15%nat sym = Some cw ->
    Z.land (c_op (entd sym)) 64 <> 0 ->
    nth_error dist_base sym = None.

Lemma zr_invl_own : forall entl,
  ZReproQ6M.zr_root_own lenfix 9 fixed_lit_lengths 15%nat entl ->
  zr_inv_len fixed_lit_lengths entl.
Proof.
  intros entl Hown sym cw Hcf H64 H32.
  rewrite (zr_agree_l entl Hown sym cw Hcf) in H64, H32.
  pose proof (code_for_range _ _ _ _ Hcf) as Hr.
  rewrite zr_lit_len_288 in Hr.
  pose proof (proj1 (forallb_forall zr_invl_ok_at (seq 0 288))
                zr_invl_all sym ltac:(apply in_seq; lia)) as HB.
  unfold zr_invl_ok_at in HB. rewrite Hcf in HB.
  rewrite (proj2 (Z.eqb_neq (Z.land (c_op (zr_entl_fix sym)) 64) 0) H64)
    in HB.
  rewrite (proj2 (Z.eqb_eq (Z.land (c_op (zr_entl_fix sym)) 32) 0) H32)
    in HB.
  cbn [negb andb] in HB. cbv beta iota in HB.
  apply andb_prop in HB as (Hs & Hn).
  split.
  - apply Nat.leb_le in Hs. exact Hs.
  - destruct (nth_error length_base (sym - 257)%nat);
      [discriminate | reflexivity].
Qed.

Lemma zr_invd_own : forall entd,
  ZReproQ6M.zr_root_own distfix 5 fixed_dist_lengths 15%nat entd ->
  zr_inv_dist fixed_dist_lengths entd.
Proof.
  intros entd Hown sym cw Hcf H64.
  rewrite (zr_agree_d entd Hown sym cw Hcf) in H64.
  pose proof (code_for_range _ _ _ _ Hcf) as Hr.
  rewrite zr_dist_len_32 in Hr.
  pose proof (proj1 (forallb_forall zr_invd_ok_at (seq 0 32))
                zr_invd_all sym ltac:(apply in_seq; lia)) as HB.
  unfold zr_invd_ok_at in HB. rewrite Hcf in HB.
  rewrite (proj2 (Z.eqb_neq (Z.land (c_op (zr_entd_fix sym)) 64) 0) H64)
    in HB.
  cbn [negb] in HB. cbv beta iota in HB.
  destruct (nth_error dist_base sym); [discriminate | reflexivity].
Qed.

Set Printing Width 2000.
Print Assumptions zr_own_agree.
Print Assumptions zr_invl_own.
Print Assumptions zr_invd_own.
Print Assumptions zr_invl_corners_strict.
Print Assumptions zr_invd_corners.
