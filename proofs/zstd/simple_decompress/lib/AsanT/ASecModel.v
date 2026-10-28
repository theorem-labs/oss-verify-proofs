(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import ABase AModelFacts APrimFacts ASecFacts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition st_sec (st : astate) (nres' a ms n : Z) : astate :=
  let st1 := set_nres nres' (set_nsec (a_nsec st + 1) st) in
  set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CSec a ms n ]> (a_live st1)) st1).

Lemma st_sec_fields : forall st nres' a ms n,
  a_space_beg (st_sec st nres' a ms n) = a_space_beg st /\ a_ptr_array (st_sec st nres' a ms n) = a_ptr_array st
  /\ a_nres (st_sec st nres' a ms n) = nres' /\ a_nsec (st_sec st nres' a ms n) = a_nsec st + 1
  /\ a_cinit (st_sec st nres' a ms n) = a_cinit st /\ a_cls (st_sec st nres' a ms n) = a_cls st
  /\ a_live (st_sec st nres' a ms n) = <[ a_next st := CSec a ms n ]> (a_live st) /\ a_next (st_sec st nres' a ms n) = N.succ (a_next st)
  /\ a_qloc (st_sec st nres' a ms n) = a_qloc st /\ a_qloc_bytes (st_sec st nres' a ms n) = a_qloc_bytes st
  /\ a_qglob (st_sec st nres' a ms n) = a_qglob st /\ a_qglob_bytes (st_sec st nres' a ms n) = a_qglob_bytes st.
Proof. intros. repeat split; reflexivity. Qed.

Lemma get_cls_st_sec : forall st nres' a ms n c, get_cls (st_sec st nres' a ms n) c = get_cls st c.
Proof. reflexivity. Qed.
Lemma max_count_st_sec : forall st nres' a ms n c, max_count (st_sec st nres' a ms n) c = max_count st c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition fin_sec (st1 : astate) (a ms n : Z) : AM (astate * option aptr) :=
  poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7))
    (aret (set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CSec a ms n ]> (a_live st1)) st1), Some (a_next st1))).

(* [comment removed for export] *)
Definition KS2 (st : astate) (n a r : Z) : itree node (exc (astate * option aptr)) :=
  let ms := sec_map_size n in
  aembed ATOP (if negb (fixed_answer_ok (a_ptr_array st + 8 * a_nres st) r) then aundef_ UBadAnswer (aret (st, @None aptr))
          else if is_err r then aundef_ USpin (aret (st, @None aptr))
          else fin_sec (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) a ms n).

(* [comment removed for export] *)
Definition sfresh (RESV : list (Z * Z)) (st : astate) (n a : Z) : bool :=
  mmap_answer_ok ATOP (sec_map_size n) a && negb (is_err a) && avoids_all a (sec_map_size n) (RESV ++ asec_ranges st).

(* [comment removed for export] *)
Definition KS (RESV : list (Z * Z)) (st : astate) (n a : Z) : itree node (exc (astate * option aptr)) :=
  let ms := sec_map_size n in
  aembed ATOP (if negb (mmap_answer_ok ATOP ms a) then aundef_ UBadAnswer (aret (st, @None aptr))
          else if is_err a then aret (st, @None aptr)
          else if negb (avoids_all a ms (RESV ++ asec_ranges st)) then aundef_ UBadAnswer (aret (st, @None aptr))
          else if a_nsec st =? a_nres st then
                 if K_PTRARR_RESERVE <? 8 * (a_nres st + K_CHUNKS_BLOCK) then aundef_ (UCheck 42) (aret (st, @None aptr))
                 else ev (AMmap (a_ptr_array st + 8 * a_nres st) K_PTRARR_COMMIT PROT_RW F_FIXED)
                         (fun r => if negb (fixed_answer_ok (a_ptr_array st + 8 * a_nres st) r) then aundef_ UBadAnswer (aret (st, @None aptr))
                                   else if is_err r then aundef_ USpin (aret (st, @None aptr))
                                   else fin_sec (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) a ms n)
               else fin_sec (set_nsec (a_nsec st + 1) st) a ms n).

Lemma amalloc_sec_eq : forall RESV st n,
  1 <= n <= AREQMAX -> is_primary n = false ->
  aembed ATOP (amalloc ATOP RESV st n)
  = ebind (enode (NMmap 0 (sec_map_size n) 3 34) (adec_mmap ATOP (sec_map_size n) 3)) (KS RESV st n).
Proof.
  intros RESV st n N PRIM.
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; unfold AREQMAX in N; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM. unfold large_alloc, ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_ANON. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma KS_unr_bad : forall RESV st n a, mmap_answer_ok ATOP (sec_map_size n) a = false -> KS RESV st n a = Ret Unr.
Proof. intros RESV st n a H. unfold KS. rewrite H. cbn [negb]. apply aembed_aundef_. Qed.

Lemma is_err_pos_false : forall r, 0 < r -> r + 1 <= TWO64 - 4096 + 1 -> is_err r = false.
Proof. intros r H1 H2. unfold is_err. apply Z.ltb_ge. lia. Qed.

Lemma KS_unr_phantom : forall RESV st n a,
  mmap_answer_ok ATOP (sec_map_size n) a = true -> is_err a = false ->
  avoids_all a (sec_map_size n) (RESV ++ asec_ranges st) = false ->
  KS RESV st n a = Ret Unr.
Proof. intros RESV st n a H1 H2 H3. unfold KS. rewrite H1, H2, H3. cbn [negb]. apply aembed_aundef_. Qed.

Lemma sfresh_false_cases : forall RESV st n a,
  sfresh RESV st n a = false ->
  mmap_answer_ok ATOP (sec_map_size n) a = false \/ is_err a = true
  \/ (mmap_answer_ok ATOP (sec_map_size n) a = true /\ is_err a = false /\ avoids_all a (sec_map_size n) (RESV ++ asec_ranges st) = false).
Proof.
  intros RESV st n a H. unfold sfresh in H.
  destruct (mmap_answer_ok ATOP (sec_map_size n) a); [| left; reflexivity].
  destruct (is_err a); [right; left; reflexivity|].
  right; right. cbn [negb andb] in H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

Lemma sfresh_true_facts : forall RESV st n a,
  sfresh RESV st n a = true ->
  mmap_answer_ok ATOP (sec_map_size n) a = true /\ is_err a = false
  /\ avoids_all a (sec_map_size n) RESV = true /\ avoids_all a (sec_map_size n) (asec_ranges st) = true
  /\ 0 < a /\ a mod 4096 = 0 /\ a + sec_map_size n <= ATOP /\ a < TWO64.
Proof.
  intros RESV st n a H. unfold sfresh in H.
  apply andb_prop in H. destruct H as [H12 H4]. apply andb_prop in H12. destruct H12 as [H1 H2].
  unfold avoids_all in H4. rewrite forallb_app in H4. apply andb_prop in H4. destruct H4 as [H4 H5].
  assert (E2 : is_err a = false) by (destruct (is_err a); [discriminate| reflexivity]).
  split; [exact H1|]. split; [exact E2|]. split; [exact H4|]. split; [exact H5|].
  unfold mmap_answer_ok in H1. rewrite E2 in H1. cbn [orb] in H1.
  apply andb_prop in H1. destruct H1 as [H1 H9]. apply andb_prop in H1. destruct H1 as [H1 H8]. apply andb_prop in H1. destruct H1 as [H6 H7].
  apply Z.ltb_lt in H6. apply Z.eqb_eq in H7. apply Z.leb_le in H8. apply Z.ltb_lt in H9.
  unfold rup, PG in H8. change PG with 4096 in H7.
  split; [exact H6|]. split; [exact H7|]. split; [| exact H9]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma KS_fresh_nocommit : forall RESV st n a,
  sfresh RESV st n a = true -> a_nsec st <> a_nres st ->
  KS RESV st n a = aembed ATOP (fin_sec (set_nsec (a_nsec st + 1) st) a (sec_map_size n) n).
Proof.
  intros RESV st n a H NE. destruct (sfresh_true_facts RESV st n a H) as (H1 & H2 & H4 & H5 & _).
  unfold KS. rewrite H1, H2. unfold avoids_all. rewrite forallb_app. unfold avoids_all in H4, H5. rewrite H4, H5.
  cbn [negb andb].
  replace (a_nsec st =? a_nres st) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
Qed.

Lemma KS_fresh_commit : forall RESV st n a,
  sfresh RESV st n a = true -> a_nsec st = a_nres st -> a_nres st + 16384 <= 1048576 ->
  KS RESV st n a = ebind (enode (NMmap (a_ptr_array st + 8 * a_nres st) 131072 3 50) (adec_mmap ATOP 131072 3)) (KS2 st n a).
Proof.
  intros RESV st n a H EQ NRB. destruct (sfresh_true_facts RESV st n a H) as (H1 & H2 & H4 & H5 & _).
  unfold KS. rewrite H1, H2. unfold avoids_all. rewrite forallb_app. unfold avoids_all in H4, H5. rewrite H4, H5.
  cbn [negb andb].
  replace (a_nsec st =? a_nres st) with true by (symmetry; apply Z.eqb_eq; exact EQ).
  replace (K_PTRARR_RESERVE <? 8 * (a_nres st + K_CHUNKS_BLOCK)) with false
    by (symmetry; apply Z.ltb_ge; unfold K_PTRARR_RESERVE, K_CHUNKS_BLOCK; lia).
  unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED, K_PTRARR_COMMIT. reflexivity.
Qed.

Lemma KS_fresh_overflow : forall RESV st n a,
  sfresh RESV st n a = true -> a_nsec st = a_nres st -> 1048576 < a_nres st + 16384 -> KS RESV st n a = Ret Unr.
Proof.
  intros RESV st n a H EQ OV. destruct (sfresh_true_facts RESV st n a H) as (H1 & H2 & H4 & H5 & _).
  unfold KS. rewrite H1, H2. unfold avoids_all. rewrite forallb_app. unfold avoids_all in H4, H5. rewrite H4, H5.
  cbn [negb andb].
  replace (a_nsec st =? a_nres st) with true by (symmetry; apply Z.eqb_eq; exact EQ).
  replace (K_PTRARR_RESERVE <? 8 * (a_nres st + K_CHUNKS_BLOCK)) with true
    by (symmetry; apply Z.ltb_lt; unfold K_PTRARR_RESERVE, K_CHUNKS_BLOCK; lia).
  apply aembed_aundef_.
Qed.

(* [comment removed for export] *)
Lemma KS2_other : forall st n a r, r <> a_ptr_array st + 8 * a_nres st -> 0 < r -> r + 131072 <= ATOP -> KS2 st n a r = Ret Unr.
Proof.
  intros st n a r NE POS CE. unfold KS2, fixed_answer_ok.
  rewrite (is_err_pos_false r POS) by (atop_facts; unfold TWO64; lia).
  replace (r =? a_ptr_array st + 8 * a_nres st) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [orb negb]. apply aembed_aundef_.
Qed.

Lemma KS2_granted : forall st n a, 0 < a_ptr_array st + 8 * a_nres st -> a_ptr_array st + 8 * a_nres st + 131072 <= ATOP ->
  KS2 st n a (a_ptr_array st + 8 * a_nres st)
  = aembed ATOP (fin_sec (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) a (sec_map_size n) n).
Proof.
  intros st n a POS CE. unfold KS2, fixed_answer_ok.
  rewrite (is_err_pos_false _ POS) by (atop_facts; unfold TWO64; lia).
  rewrite Z.eqb_refl. cbn [orb negb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fin_sec_nocommit : forall st a ms n,
  fin_sec (set_nsec (a_nsec st + 1) st) a ms n
  = poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st (a_nres st) a ms n, Some (a_next st))).
Proof. reflexivity. Qed.
Lemma fin_sec_commit : forall st a ms n,
  fin_sec (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) a ms n
  = poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st (a_nres st + 16384) a ms n, Some (a_next st))).
Proof. reflexivity. Qed.
End CANSEC1.
