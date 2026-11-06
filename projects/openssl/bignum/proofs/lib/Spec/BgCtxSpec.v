(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnInv BgState BgLib BgArith BgMont BgInv BgSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CtxSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).

Lemma hoareG_free_frame : forall p n F s,
  hoareG ((p, n) :: F) (fun _ => F) s (bfree ops p) (fun _ s' => s' = s).
Proof.
  intros p n F s X Hs Hfl (HP & HF & HFs). cbn.
  exists n, (blocks_of s ++ F). split.
  - eapply Permutation_trans; [exact HP|]. apply Permutation_sym. apply Permutation_middle.
  - split; [exact Hs|]. split; [exact Hfl|]. split; [|reflexivity]. split; [apply Permutation_refl|].
    cbn [length] in HF. inversion HFs; subst. split; [lia|assumption].
Qed.

Lemma hoareG_bind_free_frame : forall {B} p n F (f : unit -> BMu B) s Q,
  hoare F s (f tt) Q -> hoareG ((p, n) :: F) (fun _ => F) s (bbind ops (bfree ops p) f) Q.
Proof.
  intros B p n F f s Q H. eapply hoareG_bind; [apply hoareG_free_frame|]. intros [] s' _ ->. exact H.
Qed.

Lemma hoareG_malloc_frame : forall {B} n F (F' : B -> blocks) (f : ptr -> BMu B) s Q,
  0 <= n <= BG_BSZ -> (length F < BG_NF)%nat ->
  (forall p, hoareG ((p, n) :: F) F' s (f p) Q) ->
  hoareG F F' s (bbind ops (bmalloc ops n) f) Q.
Proof.
  intros B n F F' f s Q Hn HF H X Hs Hfl Ho. pose proof Ho as (HP & HL & HFs).
  cbn [bbind bmalloc bind lib_malloc tree_ops tbind gwp ret unreachable].
  split; [eapply own_ok_bg; [exact Hs|exact Ho|exact Hn]|]. split; [reflexivity|].
  intros p Hp. cbn [fst snd]. apply (H p ((p, n) :: X) Hs Hfl).
  split; [|split; [cbn [length]; lia|constructor; [cbn [snd]; exact Hn|exact HFs]]].
  eapply Permutation_trans; [apply perm_skip; exact HP|]. apply Permutation_middle.
Qed.

Lemma free_member_spec : forall (clear : bool) r F s,
  (5 <= r)%nat -> (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s ((if clear then BN_clear_free ops r None else BN_free ops r None)) (fun _ s' => s' = setbn r (bn_nil 0) s).
Proof.
  intros clear r F s H5 Hr Hn X Hs Hfl (HP & HF & HFs).
  pose proof (fl_ok_flags0 r s Hfl H5 Hr Hn) as Ef.
  assert (E1 : has_flag (getbn r s) BN_FLG_STATIC_DATA = false) by (unfold has_flag; rewrite Ef; reflexivity).
  assert (E2 : has_flag (getbn r s) BN_FLG_MALLOCED = false) by (unfold has_flag; rewrite Ef; reflexivity).
  destruct (blocks_setbn r s Hr) as (R & HR1 & HR2).
  assert (Hfin : st_wf (setbn r (bn_nil 0) s) /\ fl_ok (setbn r (bn_nil 0) s) /\ own (setbn r (bn_nil 0) s) F (R ++ F) /\
                 setbn r (bn_nil 0) s = setbn r (bn_nil 0) s).
  { split; [apply st_wf_setbn; [exact Hs|exact Hn|apply bg_ok_nil; left; reflexivity]|].
    split; [apply fl_ok_setbn; [exact Hfl|rewrite Ef; reflexivity]|]. split; [|reflexivity].
    split; [|split; assumption]. specialize (HR2 (bn_nil 0)). cbn [bn_blocks bn_nil bn_d app] in HR2.
    apply Permutation_app_tail. apply Permutation_sym. exact HR2. }
  assert (HPX : Permutation X (bn_blocks (getbn r s) ++ R ++ F)).
  { eapply Permutation_trans; [exact HP|]. rewrite app_assoc. apply Permutation_app_tail. exact HR1. }
  destruct clear; unfold BN_clear_free, BN_free; cbn [bbind bget bind tree_ops tbind ret fst snd]; rewrite E1, E2;
    unfold bn_blocks in HPX; destruct (bn_d (getbn r s)) as [q|];
    cbn [bfree_opt bfree bret bset bind lib_free tree_ops tbind gwp ret fst snd] in *.
  - exists (8 * Z.of_nat (bn_dmax (getbn r s))), (R ++ F). split; [exact HPX|exact Hfin].
  - destruct Hfin as (W1 & W2 & (W3 & W4) & W5). split; [exact W1|]. split; [exact W2|]. split; [|reflexivity].
    split; [|exact W4]. eapply Permutation_trans; [exact HPX|exact W3].
  - exists (8 * Z.of_nat (bn_dmax (getbn r s))), (R ++ F). split; [exact HPX|exact Hfin].
  - destruct Hfin as (W1 & W2 & (W3 & W4) & W5). split; [exact W1|]. split; [exact W2|]. split; [|reflexivity].
    split; [|exact W4]. eapply Permutation_trans; [exact HPX|exact W3].
Qed.

Lemma BN_clear_free_member_spec : forall r F s,
  (5 <= r)%nat -> (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s (BN_clear_free ops r None) (fun _ s' => s' = setbn r (bn_nil 0) s).
Proof. intros r F s. apply (free_member_spec true r F s). Qed.

Lemma BN_free_member_spec : forall r F s,
  (5 <= r)%nat -> (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s (BN_free ops r None) (fun _ s' => s' = setbn r (bn_nil 0) s).
Proof. intros r F s. apply (free_member_spec false r F s). Qed.

Lemma set_mont_same : forall (s : ST) ri n0, st_ri s = ri -> st_n0 s = n0 -> set_mont ri n0 s = s.
Proof. intros [l c a b x y] ri n0 E1 E2. cbn in *. subst. reflexivity. Qed.

Lemma setbn_same : forall r (b : BN) (s : ST), getbn r s = b -> setbn r b s = s.
Proof. intros r b s <-. apply setbn_getbn_id. Qed.

Definition mont_pristine (s : ST) : Prop :=
  getbn RMontRR s = bn_nil 0 /\ getbn RMontN s = bn_nil 0 /\ getbn RMontNi s = bn_nil 0 /\ st_ri s = 0 /\ st_n0 s = 0.

Lemma BN_MONT_CTX_new_spec : forall F s,
  (length F < BG_NF)%nat -> mont_pristine s ->
  hoareG F (fun p => (p, MONT_CTX_BYTES) :: F) s (BN_MONT_CTX_new ops) (fun _ s' => s' = s).
Proof.
  intros F s HF (E1 & E2 & E3 & E4 & E5). unfold BN_MONT_CTX_new.
  apply hoareG_malloc_frame; [unfold MONT_CTX_BYTES, BG_BSZ; lia|exact HF|]. intros p.
  assert (Es : setbn RMontNi (bn_nil 0) (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) (set_mont 0 0 s))) = s).
  { rewrite (set_mont_same s 0 0 E4 E5). rewrite (setbn_same RMontRR) by exact E1. rewrite (setbn_same RMontN) by exact E2.
    apply setbn_same. exact E3. }
  intros X Hs Hfl Ho. cbn. rewrite Es. split; [exact Hs|]. split; [exact Hfl|]. split; [exact Ho|reflexivity].
Qed.

Lemma BN_MONT_CTX_free_spec : forall p F s,
  getbn RMontNi s = bn_nil 0 ->
  hoareG ((p, MONT_CTX_BYTES) :: F) (fun _ => F) s (BN_MONT_CTX_free ops p)
         (fun _ s' => s' = set_mont 0 0 (setbn RMontN (bn_nil 0) (setbn RMontRR (bn_nil 0) s))).
Proof.
  intros p F s ENi. apply hoareG_wf. intros Hs. apply hoareG_fl. intros Hfl. unfold BN_MONT_CTX_free.
  assert (HL : (NFIX <= length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; lia).
  assert (DD : RMontRR <> ROne /\ RMontN <> ROne /\ RMontNi <> ROne) by (unfold RMontRR, RMontN, RMontNi, ROne; repeat split; lia).
  destruct DD as (D1 & D2 & D3).

  assert (G1 : has_flag (getbn RMontRR s) BN_FLG_MALLOCED = false)
    by (unfold has_flag; rewrite (fl_ok_flags0 RMontRR s Hfl); [reflexivity| unfold RMontRR; lia| unfold RMontRR, NFIX in *; lia| exact D1]).
  assert (G2 : has_flag (getbn RMontN s) BN_FLG_MALLOCED = false)
    by (unfold has_flag; rewrite (fl_ok_flags0 RMontN s Hfl); [reflexivity| unfold RMontN; lia| unfold RMontN, NFIX in *; lia| exact D2]).
  assert (G3 : has_flag (getbn RMontNi s) BN_FLG_MALLOCED = false)
    by (unfold has_flag; rewrite (fl_ok_flags0 RMontNi s Hfl); [reflexivity| unfold RMontNi; lia| unfold RMontNi, NFIX in *; lia| exact D3]).
  eapply hoareG_bind; [apply (hoare_get RMontRR _ s (fun b s' => b = getbn RMontRR s /\ s' = s)); split; reflexivity|]. intros b1 s1' _ [-> ->].
  eapply hoareG_bind; [apply (hoare_get RMontN _ s (fun b s' => b = getbn RMontN s /\ s' = s)); split; reflexivity|]. intros b2 s2' _ [-> ->].
  eapply hoareG_bind; [apply (hoare_get RMontNi _ s (fun b s' => b = getbn RMontNi s /\ s' = s)); split; reflexivity|]. intros b3 s3' _ [-> ->].
  rewrite G1, G2, G3. cbn [orb].
  eapply hoareG_bind; [apply BN_clear_free_member_spec; [unfold RMontRR; lia|unfold RMontRR, NFIX in *; lia|exact D1]|].
  intros [] s1 Hs1 ->.
  eapply hoareG_bind; [apply BN_clear_free_member_spec; [unfold RMontN; lia|rewrite length_setbn; unfold RMontN, NFIX in *; lia|exact D2]|].
  intros [] s2 Hs2 ->.
  eapply hoareG_bind; [apply BN_clear_free_member_spec; [unfold RMontNi; lia|rewrite !length_setbn; unfold RMontNi, NFIX in *; lia|exact D3]|].
  intros [] s3 Hs3 ->.
  apply hoareG_bind_free_frame. apply hoare_setmont.
  rewrite (setbn_same RMontNi); [reflexivity|].
  rewrite !getbn_setbn_other by (unfold RMontN, RMontRR, RMontNi; lia). exact ENi.
Qed.

Definition recp_pristine (s : ST) : Prop :=
  getbn RRecpN s = bn_nil 0 /\ getbn RRecpNr s = bn_nil 0 /\ st_rbits s = 0 /\ st_rshift s = 0.

Lemma set_recp_same : forall (s : ST) a b, st_rbits s = a -> st_rshift s = b -> set_recp a b s = s.
Proof. intros [l c u v x y] a b E1 E2. cbn in *. subst. reflexivity. Qed.

Lemma BN_RECP_CTX_init_spec : forall F s,
  recp_pristine s -> hoare F s (BN_RECP_CTX_init ops) (fun _ s' => s' = s).
Proof.
  intros F s (E1 & E2 & E3 & E4). unfold BN_RECP_CTX_init.
  assert (Es : setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) (set_recp 0 0 s)) = s).
  { rewrite (set_recp_same s 0 0 E3 E4). rewrite (setbn_same RRecpN) by exact E1. apply setbn_same. exact E2. }
  intros X Hs Hfl Ho. cbn. rewrite Es. split; [exact Hs|]. split; [exact Hfl|]. split; [exact Ho|reflexivity].
Qed.

Lemma BN_RECP_CTX_free_spec : forall F s,
  hoare F s (BN_RECP_CTX_free ops) (fun _ s' => s' = set_recp 0 0 (setbn RRecpNr (bn_nil 0) (setbn RRecpN (bn_nil 0) s))).
Proof.
  intros F s. apply hoare_wf. intros Hs. apply hoare_fl. intros Hfl. unfold BN_RECP_CTX_free.
  assert (HL : (NFIX <= length (st_bns s))%nat) by (destruct Hs as (E & _); rewrite E; lia).
  assert (DD : RRecpN <> ROne /\ RRecpNr <> ROne) by (unfold RRecpN, RRecpNr, ROne; split; lia). destruct DD as (D1 & D2).

  assert (G1 : has_flag (getbn RRecpN s) BN_FLG_MALLOCED = false)
    by (unfold has_flag; rewrite (fl_ok_flags0 RRecpN s Hfl); [reflexivity| unfold RRecpN; lia| unfold RRecpN, NFIX in *; lia| exact D1]).
  assert (G2 : has_flag (getbn RRecpNr s) BN_FLG_MALLOCED = false)
    by (unfold has_flag; rewrite (fl_ok_flags0 RRecpNr s Hfl); [reflexivity| unfold RRecpNr; lia| unfold RRecpNr, NFIX in *; lia| exact D2]).
  eapply hoare_bind; [apply (hoare_get RRecpN _ s (fun b s' => b = getbn RRecpN s /\ s' = s)); split; reflexivity|]. intros b1 s1' _ [-> ->].
  eapply hoare_bind; [apply (hoare_get RRecpNr _ s (fun b s' => b = getbn RRecpNr s /\ s' = s)); split; reflexivity|]. intros b2 s2' _ [-> ->].
  rewrite G1, G2. cbn [orb].
  eapply hoare_bind; [apply BN_free_member_spec; [unfold RRecpN; lia|unfold RRecpN, NFIX in *; lia|exact D1]|].
  intros [] s1 Hs1 ->.
  eapply hoare_bind; [apply BN_free_member_spec; [unfold RRecpNr; lia|rewrite length_setbn; unfold RRecpNr, NFIX in *; lia|exact D2]|].
  intros [] s2 Hs2 ->. apply hoare_setrecp. reflexivity.
Qed.

End CtxSpec.
