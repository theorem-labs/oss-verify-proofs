(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LibAcc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma af_lib_acc : forall Σ (m : mem) g a n, ART RT Σ m -> In g GDESC -> gd_beg g <= a -> a + n <= gd_beg g + gd_size g -> acc bsegs m a n.
Proof using AF.
  intros Σ m g a n HA Hg H1 H2. pose proof (af_lib_sh RT AF Σ m g HA Hg) as X.
  pose proof (GDESC_bounds g Hg) as (A & (S1 & S2) & _ & LO & HI).
  assert (A8 : gd_beg g mod 8 = 0).
  { pose proof (Z.div_mod (gd_beg g) 32 ltac:(lia)) as E. rewrite A in E.
    replace (gd_beg g) with (4 * (gd_beg g / 32) * 8) by lia. apply Z.mod_mul. lia. }
  apply (acc_sub bsegs m (gd_beg g) (gd_size g)); [|exact H1 | exact H2].
  apply (acc_ushadow bsegs m _ _ A8); [lia | lia | exact X].
Qed.

(* [comment removed for export] *)
Lemma af_lib_acc_lit : forall Σ (m : mem) g a n, ART RT Σ m -> gd_memb g = true -> gd_beg g <= a -> a + n <= gd_beg g + gd_size g -> acc bsegs m a n.
Proof using AF. intros Σ m g a n HA Hg. exact (af_lib_acc Σ m g a n HA (gd_memb_In g Hg)). Qed.

(* [comment removed for export] *)
Lemma af_relro : forall Σ (m : mem), ART RT Σ m -> relro_pristine m.
Proof using AF. intros Σ m HA. destruct (af_client_consts RT AF Σ m HA) as (_ & _ & _ & _ & R). exact R. Qed.

End LibAcc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint img_bytesb (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom bsegs (wa a) with Some x => bv_unsigned x =? bv_unsigned b | None => false end && img_bytesb (a + 1) bs'
  end.

Lemma img_bytesb_nth : forall bs a i b, img_bytesb a bs = true -> nth_error bs i = Some b -> seg_rom bsegs (wa (a + Z.of_nat i)) = Some b.
Proof.
  induction bs as [|x bs IH]; intros a i b H Hn; [destruct i; discriminate|].
  cbn [img_bytesb] in H. apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth_error] in Hn.
  - injection Hn as <-. rewrite Z.add_0_r. destruct (seg_rom bsegs (wa a)) as [y|]; [|discriminate].
    apply Z.eqb_eq in H1. f_equal. apply bv_eq. exact H1.
  - replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. exact (IH _ _ _ H2 Hn).
Qed.

Lemma relro_bytes_at : forall (m : mem) a bs, relro_pristine m -> RELRO_LO <= a -> a + Z.of_nat (length bs) <= RELRO_HI ->
  img_bytesb a bs = true -> bytes_at bsegs m a bs.
Proof.
  intros m a bs R H1 H2 HB. unfold RELRO_LO, RELRO_HI in *. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  rewrite (R (wa (a + Z.of_nat i))) by (unfold RELRO_LO, RELRO_HI; rewrite wa_unsigned by lia; lia).
  exact (img_bytesb_nth bs a i b HB E).
Qed.

Lemma relro_ro_cells : forall (m : mem) a cs, relro_pristine m -> cells_wf cs -> RELRO_LO <= a -> a + Z.of_nat (cells_size cs) <= RELRO_HI ->
  img_bytesb a (cells_bytes cs) = true -> ro_cells bsegs m a cs.
Proof.
  intros m a cs R W H1 H2 HB. split; [exact W|]. apply (relro_bytes_at m a _ R H1); [|exact HB].
  rewrite (cells_bytes_length cs W). exact H2.
Qed.

(* [comment removed for export] *)
Goal img_bytesb 0x5e22d8 (cells_bytes [C8 (Z_to_bv 64 0x1f261c)]) = true. Proof. vm_compute. reflexivity. Qed.
Goal img_bytesb 0x5e22f0 (cells_bytes [C8 (Z_to_bv 64 0x1f2b40)]) = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_remove_perm : forall p (l l' : list (Z * Z)), Permutation l l' -> Permutation (live_remove p l) (live_remove p l').
Proof.   (* [comment removed for export] *)
  intros p l l' H. unfold live_remove. exact (stdpp.list_relations.list.filter_Permutation _ l l' H).
Qed.

Lemma in_live_perm : forall (l l' : list (Z * Z)) a, Permutation l l' -> in_live l a -> in_live l' a.
Proof. intros l l' a H (p & n & Hin & Hp). exists p, n. split; [exact (Permutation_in _ H Hin) | exact Hp]. Qed.

Lemma aclient_perm : forall (l l' : list (Z * Z)) fr sp a, Permutation l l' -> aclient l fr sp a -> aclient l' fr sp a.
Proof.
  intros l l' fr sp a H [X|[X|[X|[X|X]]]]; [left; exact X | right; left; exact X | right; right; left; exact (in_live_perm l l' a H X)
                                            | right; right; right; left; exact X | right; right; right; right; exact X].
Qed.

Lemma rt_pres_perm : forall (l l' : list (Z * Z)) fr sp (m m' : mem), Permutation l l' -> rt_pres l fr sp m m' -> rt_pres l' fr sp m m'.
Proof. intros l l' fr sp m m' H P a Ha. apply P. exact (aclient_perm l' l fr sp _ (Permutation_sym H) Ha). Qed.

Lemma rt_pres_ex_perm : forall (l l' : list (Z * Z)) fr sp d n (m m' : mem), Permutation l l' -> rt_pres_ex l fr sp d n m m' -> rt_pres_ex l' fr sp d n m m'.
Proof. intros l l' fr sp d n m m' H P a Ha Hn. apply P; [exact (aclient_perm l' l fr sp _ (Permutation_sym H) Ha) | exact Hn]. Qed.

Lemma rt_pres_fp_perm : forall (l l' : list (Z * Z)) fr sp W (m m' : mem), Permutation l l' -> rt_pres_fp l fr sp W m m' -> rt_pres_fp l' fr sp W m m'.
Proof. intros l l' fr sp W m m' H P a Ha Ho. apply P; [exact (aclient_perm l' l fr sp _ (Permutation_sym H) Ha) | exact Ho]. Qed.

(* [comment removed for export] *)
Lemma af_live_disj_perm : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) p1 n1 p2 n2 (L : list (Z * Z)),
  ART RT Σ m -> Permutation (rt_live RT Σ) ((p1, n1) :: L) -> In (p2, n2) L -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros RT AF Σ m p1 n1 p2 n2 L HA HP Hin.
  assert (H1 : In (p1, n1) (rt_live RT Σ)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA E).
  rewrite E in HP. apply Permutation_sym, Permutation_cons_app_inv in HP.
  exact (Permutation_in _ HP Hin).
Qed.

(* [comment removed for export] *)
Lemma live_remove_other : forall p (L : list (Z * Z)), (forall q k, In (q, k) L -> q <> p) -> live_remove p L = L.
Proof.
  intros p L. unfold live_remove. induction L as [|[q k] L IH]; intros H; [reflexivity|].
  rewrite stdpp.list_basics.list.filter_cons. cbn [fst].
  assert (Hq : q <> p) by (apply (H q k); left; reflexivity).
  destruct (stdpp.base.decide _) as [_|N].
  - f_equal. apply IH. intros q' k' Hin. apply (H q' k'). right. exact Hin.
  - exfalso. apply N. apply Is_true_eq_left. apply negb_true_iff. apply Z.eqb_neq. exact Hq.
Qed.

Lemma live_remove_hd : forall p n (L : list (Z * Z)), live_remove p ((p, n) :: L) = live_remove p L.
Proof.
  intros p n L. unfold live_remove. rewrite stdpp.list_basics.list.filter_cons. cbn [fst].
  destruct (stdpp.base.decide _) as [Y|_]; [|reflexivity].
  exfalso. rewrite Z.eqb_refl in Y. exact Y.
Qed.

Lemma live_remove_head_perm : forall p n (l L : list (Z * Z)), Permutation l ((p, n) :: L) -> (forall q k, In (q, k) L -> q <> p) ->
  Permutation (live_remove p l) L.
Proof.
  intros p n l L HP HL. pose proof (live_remove_perm p _ _ HP) as X. rewrite live_remove_hd, (live_remove_other p L HL) in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma live_starts_differ : forall (RT : rt_sig) (AF : art_facts RT) Σ (m : mem) p n (L : list (Z * Z)),
  ART RT Σ m -> Permutation (rt_live RT Σ) ((p, n) :: L) -> 0 < n -> (forall q k, In (q, k) L -> 0 < k) -> forall q k, In (q, k) L -> q <> p.
Proof.
  intros RT AF Σ m p n L HA HP Hn HL q k Hin E. subst q.
  pose proof (af_live_disj_perm RT AF Σ m p n p k L HA HP Hin). pose proof (HL p k Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma live_remove_in : forall p (e : Z * Z) (l : list (Z * Z)), In e l -> fst e <> p -> In e (live_remove p l).
Proof.
  intros p e l. unfold live_remove. induction l as [|x l IH]; intros Hin Hne; [destruct Hin|].
  rewrite stdpp.list_basics.list.filter_cons. destruct (stdpp.base.decide _) as [Y|N].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; exact (IH Hin Hne)].
  - destruct Hin as [->|Hin]; [| exact (IH Hin Hne)].
    exfalso. apply N. apply Is_true_eq_left. apply negb_true_iff. apply Z.eqb_neq. exact Hne.
Qed.
