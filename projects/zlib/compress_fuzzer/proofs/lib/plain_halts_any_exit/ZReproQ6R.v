(** * ZReproQ6R — the FIXED-table pack instantiation (LEN-chain layer 4a).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).

    The chain's table hypotheses ([zr_root_own], [zr_len_ents],
    [zr_dist_ents], the sub guards) instantiated at the two inffixed.h
    tables, each decided by one [vm_compute] over the finite index/symbol
    range and extracted to the quantified Prop.  The ent functions are
    defined THROUGH the codeword value ([zr_cwval], the [write_bits]
    inverse), which quotients the root replication by construction.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6F ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.
(* amendment window 2 (q7-decode per TL grant 2026-08-20; owner review
   trails): the vm checkers gain the pack pins 1/2/3/4/6 booleans. *)

(* ==========================================================================
   1.  The codeword value: the inverse of [write_bits].
   ========================================================================== *)

Fixpoint zr_cwval (cw : list bool) : Z :=
  match cw with
  | [] => 0
  | b :: tl => (if b then 1 else 0) + 2 * zr_cwval tl
  end.

Lemma zr_write_cwval : forall cw,
  write_bits (length cw) (zr_cwval cw) = cw.
Proof.
  induction cw as [|b tl IH]; [reflexivity|].
  cbn [length write_bits zr_cwval].
  f_equal.
  - destruct b; rewrite Z.odd_add_mul_2; reflexivity.
  - replace ((if b then 1 else 0) + 2 * zr_cwval tl)
      with (zr_cwval tl * 2 + (if b then 1 else 0)) by ring.
    rewrite Z.div_add_l by lia.
    destruct b; cbn [Z.div]; rewrite Z.add_0_r; exact IH.
Qed.

(* ==========================================================================
   2.  The fixed ent functions.
   ========================================================================== *)

Definition zr_entl_fix (sym : nat) : Code :=
  match code_for fixed_lit_lengths 15%nat sym with
  | Some cw => lenfix (zr_cwval cw)
  | None => mkCode 0 0 0
  end.

Definition zr_entd_fix (sym : nat) : Code :=
  match code_for fixed_dist_lengths 15%nat sym with
  | Some cw => distfix (zr_cwval cw)
  | None => mkCode 0 0 0
  end.

Definition zr_code_eqb (a b : Code) : bool :=
  (c_op a =? c_op b) && (c_bits a =? c_bits b) && (c_val a =? c_val b).

Lemma zr_code_eqb_eq : forall a b, zr_code_eqb a b = true -> a = b.
Proof.
  intros [oa ba va] [ob bb vb] H. unfold zr_code_eqb in H. cbn in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1, H2, H3. congruence.
Qed.

(* ==========================================================================
   3.  Root ownership, decided per index.  The canonical code tables are
       PRECOMPUTED once — the finder is only a witness device, so no
       bridge lemma is needed; every Prop-bearing fact re-checks against
       [code_for] itself.
   ========================================================================== *)

Definition zr_flltab : list (list bool * nat) :=
  Eval vm_compute in code_table fixed_lit_lengths 15%nat.

Definition zr_fdltab : list (list bool * nat) :=
  Eval vm_compute in code_table fixed_dist_lengths 15%nat.

Definition zr_ownl_ok_at (i : nat) : bool :=
  let idx := Z.of_nat i in
  let E := lenfix idx in
  match zr_tbl_find (zr_cw E idx) zr_flltab with
  | Some sym =>
      match code_for fixed_lit_lengths 15%nat sym with
      | Some cw =>
          (Z.of_nat (length cw) <=? 9)
          && zr_code_eqb (lenfix idx) (zr_entl_fix sym)
          && (c_bits (zr_entl_fix sym) =? Z.of_nat (length cw))
          && zr_blist_eqb
               (firstn (length cw) (write_bits (Z.to_nat 9) idx)) cw
      | None => false
      end
  | None => false
  end.

Definition zr_ownd_ok_at (i : nat) : bool :=
  let idx := Z.of_nat i in
  let E := distfix idx in
  match zr_tbl_find (zr_cw E idx) zr_fdltab with
  | Some sym =>
      match code_for fixed_dist_lengths 15%nat sym with
      | Some cw =>
          (Z.of_nat (length cw) <=? 5)
          && zr_code_eqb (distfix idx) (zr_entd_fix sym)
          && (c_bits (zr_entd_fix sym) =? Z.of_nat (length cw))
          && zr_blist_eqb
               (firstn (length cw) (write_bits (Z.to_nat 5) idx)) cw
      | None => false
      end
  | None => false
  end.

Lemma zr_ownl_all : forallb zr_ownl_ok_at (seq 0 512) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_ownd_all : forallb zr_ownd_ok_at (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_ownl_fix :
  ZReproQ6M.zr_root_own lenfix 9 fixed_lit_lengths 15%nat zr_entl_fix.
Proof.
  intros i Hi.
  pose proof (proj1 (forallb_forall zr_ownl_ok_at (seq 0 512))
                zr_ownl_all (Z.to_nat i)
                ltac:(apply in_seq; lia)) as HB.
  unfold zr_ownl_ok_at in HB.
  rewrite Z2Nat.id in HB by lia.
  destruct (zr_tbl_find (zr_cw (lenfix i) i) zr_flltab) as [sym|] eqn:HF;
    [|discriminate].
  destruct (code_for fixed_lit_lengths 15%nat sym) as [cw|] eqn:HC;
    [|discriminate].
  apply andb_prop in HB as [HB B4]. apply andb_prop in HB as [HB B3].
  apply andb_prop in HB as [B1 B2].
  exists sym, cw.
  split; [exact HC|].
  split; [apply Z.leb_le in B1; lia|].
  split; [exact (zr_code_eqb_eq _ _ B2)|].
  split; [apply Z.eqb_eq in B3; exact B3|].
  exact (zr_blist_eqb_eq _ _ B4).
Qed.

Lemma zr_ownd_fix :
  ZReproQ6M.zr_root_own distfix 5 fixed_dist_lengths 15%nat zr_entd_fix.
Proof.
  intros i Hi.
  pose proof (proj1 (forallb_forall zr_ownd_ok_at (seq 0 32))
                zr_ownd_all (Z.to_nat i)
                ltac:(apply in_seq; lia)) as HB.
  unfold zr_ownd_ok_at in HB.
  rewrite Z2Nat.id in HB by lia.
  destruct (zr_tbl_find (zr_cw (distfix i) i) zr_fdltab) as [sym|] eqn:HF;
    [|discriminate].
  destruct (code_for fixed_dist_lengths 15%nat sym) as [cw|] eqn:HC;
    [|discriminate].
  apply andb_prop in HB as [HB B4]. apply andb_prop in HB as [HB B3].
  apply andb_prop in HB as [B1 B2].
  exists sym, cw.
  split; [exact HC|].
  split; [apply Z.leb_le in B1; lia|].
  split; [exact (zr_code_eqb_eq _ _ B2)|].
  split; [apply Z.eqb_eq in B3; exact B3|].
  exact (zr_blist_eqb_eq _ _ B4).
Qed.

(* ==========================================================================
   4.  The entry-interpretation packs and sub guards, decided per symbol.
   ========================================================================== *)

Definition zr_entsl_ok_at (sym : nat) : bool :=
  match code_for fixed_lit_lengths 15%nat sym with
  | None => true
  | Some _ =>
      let E := zr_entl_fix sym in
      negb (sub_len E)
      && (if (sym <? 256)%nat then
            (c_op E =? 0) && (c_val E =? Z.of_nat sym)
          else if (sym =? 256)%nat then
            negb (c_op E =? 0) && negb (Z.land (c_op E) 32 =? 0)
            && (Z.land (c_op E) 16 =? 0) && negb (Z.land (c_op E) 64 =? 0)
          else
            match nth_error length_base (sym - 257)%nat,
                  nth_error length_extra (sym - 257)%nat with
            | Some b0, Some e0 =>
                (c_op E =? 16 + Z.of_nat e0)
                && (Z.land (c_op E) 32 =? 0)
                && (Z.land (c_op E) 64 =? 0)
                && (Z.land (c_op E) 15 =? Z.of_nat e0)
                && (c_val E =? Z.of_nat b0)
                && (3 <=? b0)%nat && (b0 <=? 258)%nat && (e0 <=? 5)%nat
                && (b0 + 2 ^ e0 - 1 <=? 258)%nat
            | _, _ =>
                negb (c_op E =? 0) && (Z.land (c_op E) 32 =? 0)
                && (Z.land (c_op E) 16 =? 0)
                && negb (Z.land (c_op E) 64 =? 0)
            end)
  end.

Definition zr_entsd_ok_at (sym : nat) : bool :=
  match code_for fixed_dist_lengths 15%nat sym with
  | None => true
  | Some _ =>
      let E := zr_entd_fix sym in
      negb (sub_dist E)
      && match nth_error dist_base sym, nth_error dist_extra sym with
         | Some b0, Some e0 =>
             (c_op E =? 16 + Z.of_nat e0)
             && (Z.land (c_op E) 64 =? 0)
             && (Z.land (c_op E) 15 =? Z.of_nat e0)
             && (c_val E =? Z.of_nat b0)
             && (1 <=? Z.of_nat b0) && (Z.of_nat b0 <=? 32768)
             && (e0 <=? 13)%nat
         | _, _ => negb (Z.land (c_op E) 64 =? 0)
                   && (Z.land (c_op E) 16 =? 0)
         end
  end.

Lemma zr_entsl_all : forallb zr_entsl_ok_at (seq 0 288) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_entsd_all : forallb zr_entsd_ok_at (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_lit_len_288 : length fixed_lit_lengths = 288%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma zr_dist_len_32 : length fixed_dist_lengths = 32%nat.
Proof. vm_compute. reflexivity. Qed.

(** Symbols beyond the length table have no codeword, making the pack
    vacuous there; inside, the vm decision rules. *)
Lemma zr_entsl_at : forall sym, zr_entsl_ok_at sym = true.
Proof.
  intro sym.
  destruct (Nat.ltb_spec sym 288) as [Hlt|Hge].
  - exact (proj1 (forallb_forall zr_entsl_ok_at (seq 0 288))
             zr_entsl_all sym ltac:(apply in_seq; lia)).
  - unfold zr_entsl_ok_at.
    destruct (code_for fixed_lit_lengths 15%nat sym) eqn:HC;
      [|reflexivity].
    exfalso. unfold code_for in HC.
    rewrite (proj2 (nth_error_None fixed_lit_lengths sym)) in HC;
      [discriminate | rewrite zr_lit_len_288; lia].
Qed.

Lemma zr_entsd_at : forall sym, zr_entsd_ok_at sym = true.
Proof.
  intro sym.
  destruct (Nat.ltb_spec sym 32) as [Hlt|Hge].
  - exact (proj1 (forallb_forall zr_entsd_ok_at (seq 0 32))
             zr_entsd_all sym ltac:(apply in_seq; lia)).
  - unfold zr_entsd_ok_at.
    destruct (code_for fixed_dist_lengths 15%nat sym) eqn:HC;
      [|reflexivity].
    exfalso. unfold code_for in HC.
    rewrite (proj2 (nth_error_None fixed_dist_lengths sym)) in HC;
      [discriminate | rewrite zr_dist_len_32; lia].
Qed.

Lemma zr_subl_fix : forall sym cw,
  code_for fixed_lit_lengths 15%nat sym = Some cw ->
  sub_len (zr_entl_fix sym) = false.
Proof.
  intros sym cw HC.
  pose proof (zr_entsl_at sym) as HB.
  unfold zr_entsl_ok_at in HB. rewrite HC in HB.
  apply andb_prop in HB as [Hs _].
  apply negb_true_iff in Hs. exact Hs.
Qed.

Lemma zr_subd_fix : forall sym cw,
  code_for fixed_dist_lengths 15%nat sym = Some cw ->
  sub_dist (zr_entd_fix sym) = false.
Proof.
  intros sym cw HC.
  pose proof (zr_entsd_at sym) as HB.
  unfold zr_entsd_ok_at in HB. rewrite HC in HB.
  apply andb_prop in HB as [Hs _].
  apply negb_true_iff in Hs. exact Hs.
Qed.

Lemma zr_entsl_fix : zr_len_ents fixed_lit_lengths zr_entl_fix.
Proof.
  intros sym cw HC.
  pose proof (zr_entsl_at sym) as HB.
  unfold zr_entsl_ok_at in HB. rewrite HC in HB.
  apply andb_prop in HB as [_ HB].
  destruct (Nat.ltb_spec sym 256) as [Hlt|Hge].
  - left.
    apply andb_prop in HB as [H1 H2].
    apply Z.eqb_eq in H1, H2. auto.
  - destruct (Nat.eqb_spec sym 256) as [Heq|Hne].
    + right; left.
      apply andb_prop in HB as [HB H64].
      apply andb_prop in HB as [HB H16].
      apply andb_prop in HB as [H1 H2].
      apply negb_true_iff in H1, H2, H64.
      apply Z.eqb_neq in H1, H2, H64.
      apply Z.eqb_eq in H16.
      repeat split; assumption.
    + destruct (nth_error length_base (sym - 257)%nat) as [b0|] eqn:HBb;
        destruct (nth_error length_extra (sym - 257)%nat) as [e0|] eqn:HEe.
      * right; right; left.
        split; [lia|].
        exists b0, e0.
        apply andb_prop in HB as [HB B9]. apply andb_prop in HB as [HB B8].
        apply andb_prop in HB as [HB B7]. apply andb_prop in HB as [HB B6].
        apply andb_prop in HB as [HB B5]. apply andb_prop in HB as [HB B4].
        apply andb_prop in HB as [HB B3]. apply andb_prop in HB as [B1 B2].
        apply Z.eqb_eq in B1, B2, B3, B4, B5.
        apply Nat.leb_le in B6, B7, B8, B9.
        repeat split; assumption.
      * right; right; right.
        apply andb_prop in HB as [HB H4]. apply andb_prop in HB as [HB H3].
        apply andb_prop in HB as [H1 H2].
        apply negb_true_iff in H1, H4.
        apply Z.eqb_neq in H1, H4. apply Z.eqb_eq in H2, H3.
        repeat split; assumption.
      * right; right; right.
        apply andb_prop in HB as [HB H4]. apply andb_prop in HB as [HB H3].
        apply andb_prop in HB as [H1 H2].
        apply negb_true_iff in H1, H4.
        apply Z.eqb_neq in H1, H4. apply Z.eqb_eq in H2, H3.
        repeat split; assumption.
      * right; right; right.
        apply andb_prop in HB as [HB H4]. apply andb_prop in HB as [HB H3].
        apply andb_prop in HB as [H1 H2].
        apply negb_true_iff in H1, H4.
        apply Z.eqb_neq in H1, H4. apply Z.eqb_eq in H2, H3.
        repeat split; assumption.
Qed.

Lemma zr_entsd_fix : zr_dist_ents fixed_dist_lengths zr_entd_fix.
Proof.
  intros sym cw HC.
  pose proof (zr_entsd_at sym) as HB.
  unfold zr_entsd_ok_at in HB. rewrite HC in HB.
  apply andb_prop in HB as [_ HB].
  destruct (nth_error dist_base sym) as [b0|] eqn:HBb;
    destruct (nth_error dist_extra sym) as [e0|] eqn:HEe.
  - left. exists b0, e0.
    apply andb_prop in HB as [HB B7]. apply andb_prop in HB as [HB B6].
    apply andb_prop in HB as [HB B5]. apply andb_prop in HB as [HB B4].
    apply andb_prop in HB as [HB B3]. apply andb_prop in HB as [B1 B2].
    apply Z.eqb_eq in B1, B2, B3, B4.
    apply Z.leb_le in B5, B6. apply Nat.leb_le in B7.
    repeat split; assumption.
  - right.
    apply andb_prop in HB as [HB H16].
    apply negb_true_iff in HB. apply Z.eqb_neq in HB.
    apply Z.eqb_eq in H16.
    split; [exact HB | exact H16].
  - right.
    apply andb_prop in HB as [HB H16].
    apply negb_true_iff in HB. apply Z.eqb_neq in HB.
    apply Z.eqb_eq in H16.
    split; [exact HB | exact H16].
  - right.
    apply andb_prop in HB as [HB H16].
    apply negb_true_iff in HB. apply Z.eqb_neq in HB.
    apply Z.eqb_eq in H16.
    split; [exact HB | exact H16].
Qed.

Print Assumptions zr_ownl_fix.
Print Assumptions zr_ownd_fix.
Print Assumptions zr_entsl_fix.
Print Assumptions zr_entsd_fix.
Print Assumptions zr_subl_fix.
Print Assumptions zr_subd_fix.
