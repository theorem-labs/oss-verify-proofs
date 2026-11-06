(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnWords BnModel BnTree BgState BgInv BgLib BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun ImplA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).
Local Notation BN := (bignum bptr).
Local Notation BMu := (BM (M := btree bptr) (ptr := bptr)).

Definition ms_exit : BMu unit :=
  bbind ops (BN_CTX_end ops) (fun _ =>
  bbind ops (bget ops RTmod) (fun tm =>
  if (match bn_d tm with Some _ => true | None => false end) then bunr ops else
  bset ops RTmod (bn_nil 0))).

Definition ms_fix : BMu unit :=
  bbind ops (bget ops RMontRR) (fun rr =>
  bbind ops (bget ops RMontN) (fun n =>
  if (bn_dmax rr <? bn_top n)%nat then bunr ops else
  bbind ops (bset ops RMontRR (mkBN (bn_d rr) (splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr))) (bn_top n)
                                 (bn_neg rr) (bn_flags rr))) (fun _ =>
  ms_exit))).

Definition ms_rr (ri : Z) : BMu unit :=
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (bgetst ops) (fun st =>
  if negb (st_ri st =? ri) then bunr ops else
  bbind ops (BN_set_bit ops RMontRR (ri * 2)) (fun _ =>
  bbind ops (BN_mod ops RMontRR RMontRR RMontN) (fun _ =>
  ms_fix)))).

Definition ms_n0 (rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (BN_div ops (Some rRi) None rRi RTmod) (fun _ =>
  bbind ops (bget ops rRi) (fun x =>
  let n0 := if (0 <? bn_top x)%nat then nth 0 (bn_buf x) 0 else 0 in
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops (st_ri st) n0)) (fun _ =>
  ms_rr ri))).

Definition ms_sub (rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (BN_lshift ops rRi rRi 64) (fun _ =>
  bbind ops (bget ops rRi) (fun x =>
  bbind ops (if negb (is_zero_pure x) then (if lval (firstn (bn_top x) (bn_buf x)) <? 1 then bunr ops else BN_sub_word ops rRi 1)
             else BN_set_word ops rRi BN_MASK2) (fun _ =>
  ms_n0 rRi ri))).

Definition ms_inv (rRi : bnref) (ri : Z) : BMu unit :=
  bbind ops (bget ops RTmod) (fun tm =>
  bbind ops (if is_one_pure tm then BN_zero ops rRi else BN_mod_inverse ops rRi RMontRR RTmod) (fun _ =>
  ms_sub rRi ri)).

Definition ms_mid (rmod rRi : bnref) : BMu unit :=
  bbind ops (BN_copy ops RMontN rmod) (fun _ =>
  bbind ops (bbind ops (bget ops RMontN) (fun n => bset ops RMontN (bn_with_neg n false))) (fun _ =>
  bbind ops (BN_num_bits ops rmod) (fun nb =>
  let ri := (nb + 63) / 64 * 64 in
  bbind ops (bbind ops (bgetst ops) (fun st => bsetmont ops ri (st_n0 st))) (fun _ =>
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (BN_set_bit ops RMontRR 64) (fun _ =>
  bbind ops (bget ops rmod) (fun m =>
  if (bn_top m =? 0)%nat then bunr ops else
  let b0 := nth 0 (bn_buf m) 0 in
  bbind ops (bset ops RTmod (mkBN None [b0; 0] (if b0 =? 0 then 0%nat else 1%nat) false 0)) (fun _ =>
  ms_inv rRi ri)))))))).

Definition ms_all (rmod : bnref) : BMu unit :=
  bbind ops (bget ops rmod) (fun m =>
  if is_zero_pure m then bunr ops else
  bbind ops (BN_CTX_start ops) (fun _ =>
  bbind ops (BN_CTX_get ops) (fun rRi =>
  ms_mid rmod rRi))).

Lemma BN_MONT_CTX_set_eq : forall rmod, BN_MONT_CTX_set ops rmod = ms_all rmod.
Proof. reflexivity. Qed.

Definition ms_exit0 : BMu unit := bbind ops (BN_CTX_end ops) (fun _ => bret ops tt).

Definition ms_fix0 : BMu unit :=
  bbind ops (bget ops RMontRR) (fun rr =>
  bbind ops (bget ops RMontN) (fun n =>
  if (bn_dmax rr <? bn_top n)%nat then bunr ops else
  bbind ops (bset ops RMontRR (mkBN (bn_d rr) (splice (bn_buf rr) (bn_top rr) (repeat 0 (bn_top n - bn_top rr))) (bn_top n)
                                 (bn_neg rr) (bn_flags rr))) (fun _ =>
  ms_exit0))).

Definition ms_rr0 (ri : Z) : BMu unit :=
  bbind ops (BN_zero ops RMontRR) (fun _ =>
  bbind ops (bgetst ops) (fun st =>
  if negb (st_ri st =? ri) then bunr ops else
  bbind ops (BN_set_bit ops RMontRR (ri * 2)) (fun _ =>
  bbind ops (BN_mod ops RMontRR RMontRR RMontN) (fun _ =>
  ms_fix0)))).

Inductive tsim {A B : Type} (R : A -> B -> Prop) : btree bptr A -> btree bptr B -> Prop :=
| ts_ret : forall a b, R a b -> tsim R (TRet a) (TRet b)
| ts_unr : forall t, tsim R TUnr t
| ts_malloc : forall n k k', (forall o, tsim R (k o) (k' o)) -> tsim R (TMalloc n k) (TMalloc n k')
| ts_free : forall p k k', tsim R k k' -> tsim R (TFree p k) (TFree p k').

Lemma tsim_bind : forall {A B A' B' : Type} (R : A -> A' -> Prop) (R2 : B -> B' -> Prop) (m : btree bptr A) (m' : btree bptr A')
    (f : A -> btree bptr B) (f' : A' -> btree bptr B'),
  tsim R m m' -> (forall a a', R a a' -> tsim R2 (f a) (f' a')) -> tsim R2 (tbind m f) (tbind m' f').
Proof.
  intros A B A' B' R R2 m m' f f' H HF. induction H as [a b HR | t | n k k' HK IH | p k k' HK IH]; cbn [tbind].
  - apply HF. exact HR.
  - apply ts_unr.
  - apply ts_malloc. intros o. apply IH.
  - apply ts_free. exact IH.
Qed.

Lemma tsim_mono : forall {A B : Type} (R R' : A -> B -> Prop) (t : btree bptr A) (t' : btree bptr B),
  tsim R t t' -> (forall a b, R a b -> R' a b) -> tsim R' t t'.
Proof.
  intros A B R R' t t' H HR. induction H as [a b HR0 | t | n k k' HK IH | p k k' HK IH].
  - apply ts_ret. apply HR. exact HR0.
  - apply ts_unr.
  - apply ts_malloc. intros o. apply IH.
  - apply ts_free. exact IH.
Qed.

Lemma safe_tsim : forall {A B : Type} (R : A -> B -> Prop) (t : btree bptr A) (t' : btree bptr B),
  tsim R t t' -> forall X (Φ : A -> @blocks bptr -> Prop), safe t X Φ -> safe t' X (fun b X' => exists a, R a b /\ Φ a X').
Proof.
  intros A B R t t' H. induction H as [a b HR | t | n k k' HK IH | p k k' HK IH]; intros X Φ S; cbn [safe] in *.
  - exists a. split; [exact HR | exact S].
  - destruct S.
  - destruct S as (Hn & S). split; [exact Hn|]. intros q Hq. apply IH. apply S. exact Hq.
  - destruct S as (m & X' & E & S). exists m, X'. split; [exact E|]. apply IH. exact S.
Qed.

Lemma safe_inhab : forall {A : Type} (t : btree bptr A) X (Ψ : A -> @blocks bptr -> Prop), safe t X Ψ -> exists a X', Ψ a X'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Ψ S; cbn [safe] in S.
  - exists a, X. exact S.
  - destruct S.
  - destruct S as (_ & S). destruct (bptr_fresh (map fst X)) as [q Hq]. exact (IH (Some q) _ _ (S q Hq)).
  - destruct S as (m & X' & _ & S). exact (IH _ _ S).
Qed.

Section WithAR.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).

Lemma implA_tsim : forall {A B : Type} (C : Prop) (R : A -> B -> Prop) (t : btree bptr A) (t' : btree bptr B) (Σ : rts RT)
    (Q : A -> rts RT -> machine_state -> Prop) (Q' : B -> rts RT -> machine_state -> Prop) ms,
  tsim (fun a b => R a b /\ C) t t' ->
  (C -> implA t' Σ Q' ms) ->
  (forall a b Σ' ms', R a b -> Q' b Σ' ms' -> Q a Σ' ms') ->
  implA t Σ Q ms.
Proof.
  intros A B C R t t' Σ Q Q' ms SIM H HQ X Φ S.
  pose proof (safe_tsim _ _ _ SIM X Φ S) as S'.
  destruct (safe_inhab _ _ _ S') as (b0 & X0 & (a0 & (_ & HC) & _)).
  intros T c Hc Hk.
  apply (H HC X _ S' T c Hc).
  intros c' (b & X' & Σ' & (a & (HR & _) & HΦ) & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0. apply (HQ a b). exact HR.
Qed.
End WithAR.

Lemma list_set_comm : forall {A} (l : list A) i j a b, i <> j -> list_set (list_set l i a) j b = list_set (list_set l j b) i a.
Proof.
  intros A l. induction l as [|x l IH]; intros i j a b NE; [reflexivity|].
  destruct i as [|i], j as [|j]; cbn [list_set]; try reflexivity; [exfalso; apply NE; reflexivity|].
  f_equal. apply IH. intros E. apply NE. f_equal. exact E.
Qed.

Lemma setbn_comm : forall r r' b b' (s : ST), r <> r' -> setbn r b (setbn r' b' s) = setbn r' b' (setbn r b s).
Proof.
  intros r r' b b' s NE. unfold setbn, set_bns. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift]. f_equal.
  apply list_set_comm. intros E. apply NE. symmetry. exact E.
Qed.

Section Indep.
Variables (v w : BN).

Definition U (s : ST) : ST := setbn RTmod v s.
Definition okst (s : ST) : Prop := (RTmod < length (st_bns s))%nat /\ getbn RTmod s = w.
Definition Rst {A : Type} (P : A -> Prop) (x y : A * ST) : Prop := fst y = fst x /\ snd y = U (snd x) /\ okst (snd x) /\ P (fst x).
Definition bsim {A B : Type} (R : A * ST -> B * ST -> Prop) (m : BMu A) (m' : BMu B) : Prop := forall s, okst s -> tsim R (m s) (m' (U s)).
Notation indep P m := (bsim (Rst P) m m).
Notation TT := (fun _ => True).

Lemma bsim_bind : forall {A B B' : Type} (P : A -> Prop) (R : B * ST -> B' * ST -> Prop) (m : BMu A) (f : A -> BMu B) (f' : A -> BMu B'),
  indep P m -> (forall a, P a -> bsim R (f a) (f' a)) -> bsim R (bbind ops m f) (bbind ops m f').
Proof.
  intros A B B' P R m f f' HM HF s OK. unfold bbind. cbn [bind tree_ops].
  eapply tsim_bind; [exact (HM s OK)|]. intros [a s1] [a' s1'] (E1 & E2 & OK1 & PA). cbn [fst snd] in *. subst a' s1'. exact (HF a PA s1 OK1).
Qed.

Lemma indep_weaken : forall {A : Type} (P P' : A -> Prop) (m : BMu A), indep P m -> (forall a, P a -> P' a) -> indep P' m.
Proof.
  intros A P P' m H HP s OK. eapply tsim_mono; [exact (H s OK)|]. intros x y (E1 & E2 & OK1 & PA). split; [exact E1|]. split; [exact E2|]. split; [exact OK1 | exact (HP _ PA)].
Qed.

Lemma okst_setbn : forall r b s, r <> RTmod -> okst s -> okst (setbn r b s).
Proof. intros r b s NE (L & G). split; [rewrite length_setbn; exact L | rewrite getbn_setbn_other by exact NE; exact G]. Qed.

Lemma indep_ret : forall {A : Type} (P : A -> Prop) (a : A), P a -> indep P (bret ops a).
Proof. intros A P a PA s OK. apply ts_ret. split; [reflexivity|]. split; [reflexivity|]. split; [exact OK | exact PA]. Qed.

Lemma bsim_unr : forall {A B : Type} (R : A * ST -> B * ST -> Prop) (m' : BMu B), bsim R (bunr ops) m'.
Proof. intros A B R m' s OK. apply ts_unr. Qed.

Lemma indep_get : forall r, r <> RTmod -> indep TT (bget ops r).
Proof.
  intros r NE s OK. apply ts_ret. cbn [fst snd]. split; [unfold U; apply getbn_setbn_other; intros E; apply NE; symmetry; exact E|].
  split; [reflexivity|]. split; [exact OK | exact I].
Qed.

Lemma indep_set : forall r b, r <> RTmod -> indep TT (bset ops r b).
Proof.
  intros r b NE s OK. apply ts_ret. cbn [fst snd]. split; [reflexivity|]. split; [unfold U; apply setbn_comm; exact NE|].
  split; [exact (okst_setbn r b s NE OK) | exact I].
Qed.

Lemma indep_getctx : indep TT (bgetctx ops).
Proof. intros s OK. apply ts_ret. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact OK | exact I]. Qed.

Lemma indep_setctx : forall c, indep TT (bsetctx ops c).
Proof. intros c s OK. apply ts_ret. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact OK | exact I]. Qed.

Lemma indep_malloc : forall n, indep TT (bmalloc ops n).
Proof.
  intros n s OK. unfold bmalloc. cbn [bind lib_malloc tree_ops tbind]. apply ts_malloc. intros [p|]; cbn [tbind].
  - apply ts_ret. split; [reflexivity|]. split; [reflexivity|]. split; [exact OK | exact I].
  - apply ts_unr.
Qed.

Lemma indep_free_opt : forall o, indep TT (bfree_opt ops o).
Proof.
  intros [p|] s OK; unfold bfree_opt, bfree, bret; cbn [bind lib_free ret tree_ops tbind].
  - apply ts_free. apply ts_ret. split; [reflexivity|]. split; [reflexivity|]. split; [exact OK | exact I].
  - apply ts_ret. split; [reflexivity|]. split; [reflexivity|]. split; [exact OK | exact I].
Qed.

Lemma bsim_getst : forall {B B' : Type} (R : B * ST -> B' * ST -> Prop) (f : ST -> BMu B) (f' : ST -> BMu B'),
  (forall s, okst s -> tsim R (f s s) (f' (U s) (U s))) -> bsim R (bbind ops (bgetst ops) f) (bbind ops (bgetst ops) f').
Proof. intros B B' R f f' H s OK. exact (H s OK). Qed.

Lemma bsim_append : forall {B B' : Type} (R : B * ST -> B' * ST -> Prop) (X : list BN) (K : BMu B) (K' : BMu B'),
  bsim R K K' ->
  bsim R (bbind ops (bgetst ops) (fun s => bbind ops (bsetbns ops (st_bns s ++ X)) (fun _ => K)))
         (bbind ops (bgetst ops) (fun s => bbind ops (bsetbns ops (st_bns s ++ X)) (fun _ => K'))).
Proof.
  intros B B' R X K K' HK. apply bsim_getst. intros s OK. unfold bbind, bsetbns. cbn [bind ret tree_ops tbind fst snd].
  assert (E : set_bns (st_bns (U s) ++ X) (U s) = U (set_bns (st_bns s ++ X) s)).
  { unfold U, setbn, set_bns. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift]. f_equal. symmetry. apply list_set_app_l. exact (proj1 OK). }
  rewrite E. apply HK. destruct OK as (L & G). split.
  - unfold set_bns. cbn [st_bns]. rewrite length_app. clear - L. lia.
  - unfold getbn, set_bns in *. cbn [st_bns]. rewrite app_nth1 by exact L. exact G.
Qed.

Ltac ind_side := first [ exact I | assumption | discriminate | (unfold RPool, RTmod, RMontRR, RMontN, NFIX in *; intros E__; injection E__; intros; lia) | (unfold RPool, RTmod, RMontRR, RMontN, NFIX in *; lia) ].
Ltac ind1 :=
  lazymatch goal with
  | |- bsim _ (bunr ops) _ => apply bsim_unr
  | |- bsim _ (bbind ops (bgetst ops) (fun s => bbind ops (bsetbns ops (st_bns s ++ _)) _)) _ => apply bsim_append
  | |- bsim _ (bbind ops _ _) (bbind ops _ _) => eapply bsim_bind; [| intros ? ?]
  | |- bsim _ (if ?c then _ else _) _ => destruct c
  | |- bsim _ (match ?x with Some _ => _ | None => _ end) _ => destruct x
  | |- bsim _ (match ?x with [] => _ | _ :: _ => _ end) _ => destruct x
  | |- bsim _ (let '(_, _) := ?x in _) _ => destruct x
  | |- bsim (Rst _) (bret ops _) _ => apply indep_ret
  | |- bsim (Rst _) (bget ops _) _ => eapply indep_weaken; [apply indep_get | intros ? _]
  | |- bsim (Rst _) (bset ops _ _) _ => eapply indep_weaken; [apply indep_set | intros ? _]
  | |- bsim (Rst _) (bgetctx ops) _ => eapply indep_weaken; [apply indep_getctx | intros ? _]
  | |- bsim (Rst _) (bsetctx ops _) _ => eapply indep_weaken; [apply indep_setctx | intros ? _]
  | |- bsim (Rst _) (bmalloc ops _) _ => eapply indep_weaken; [apply indep_malloc | intros ? _]
  | |- bsim (Rst _) (bfree_opt ops _) _ => eapply indep_weaken; [apply indep_free_opt | intros ? _]
  end.
Ltac ind := repeat first [ind1 | progress ind_side].

Lemma indep_wexpand : forall r n, r <> RTmod -> indep TT (bn_wexpand ops r n).
Proof. intros r n NE. unfold bn_wexpand. ind. Qed.

Lemma indep_zero : forall r, r <> RTmod -> indep TT (BN_zero ops r).
Proof. intros r NE. unfold BN_zero. ind. Qed.

Lemma indep_set_bit : forall r n, r <> RTmod -> indep TT (BN_set_bit ops r n).
Proof.
  intros r n NE. unfold BN_set_bit. destruct (n <? 0); [apply bsim_unr|].
  eapply bsim_bind; [apply indep_get; exact NE | intros a _].
  eapply bsim_bind with (P := TT); [| intros ? _; ind].
  destruct (bn_top a <=? Z.to_nat (n / 64))%nat; [| ind].
  eapply bsim_bind; [apply indep_wexpand; exact NE | intros ? _]. ind.
Qed.

Lemma indep_copy : forall ra rb, ra <> RTmod -> rb <> RTmod -> indep TT (BN_copy ops ra rb).
Proof.
  intros ra rb NA NB. unfold BN_copy.
  eapply bsim_bind; [apply indep_get; exact NB | intros b _].
  destruct (has_flag b BN_FLG_CONSTTIME); [apply bsim_unr|]. destruct (ra =? rb)%nat; [ind|].
  eapply bsim_bind; [apply indep_wexpand; exact NA | intros ? _]. ind.
Qed.

Lemma indep_ctx_start : indep TT (BN_CTX_start ops).
Proof. unfold BN_CTX_start. ind. Qed.

Lemma indep_ctx_end : indep TT (BN_CTX_end ops).
Proof. unfold BN_CTX_end. ind. Qed.

Lemma indep_ctx_get : indep (fun r => r <> RTmod) (BN_CTX_get ops).
Proof.
  unfold BN_CTX_get.
  eapply bsim_bind; [apply indep_getctx | intros c _].
  destruct (negb (gx_err_stack c =? 0)%nat || gx_too_many c); [apply bsim_unr|].
  eapply bsim_bind with (P := TT).
  - destruct (gx_pused c =? BN_CTX_POOL_SIZE * length (gx_items c))%nat; [| ind].
    destruct (3 <=? length (gx_items c))%nat; [apply bsim_unr|].
    eapply bsim_bind; [apply indep_malloc | intros p _]. ind.
  - intros i _. ind.
Qed.

Lemma indep_left_align : forall r, r <> RTmod -> indep TT (bn_left_align ops r).
Proof. intros r NE. unfold bn_left_align. ind. Qed.

Lemma indep_lshift_ft : forall rr ra n, rr <> RTmod -> ra <> RTmod -> indep TT (bn_lshift_fixed_top ops rr ra n).
Proof.
  intros rr ra n NR NA. unfold bn_lshift_fixed_top. destruct (n <? 0); [apply bsim_unr|].
  eapply bsim_bind; [apply indep_get; exact NA | intros a0 _].
  eapply bsim_bind; [apply indep_wexpand; exact NR | intros ? _]. ind.
Qed.

Lemma indep_rshift_ft : forall rr ra n, rr <> RTmod -> ra <> RTmod -> indep TT (bn_rshift_fixed_top ops rr ra n).
Proof.
  intros rr ra n NR NA. unfold bn_rshift_fixed_top. destruct (n <? 0); [apply bsim_unr|].
  eapply bsim_bind; [apply indep_get; exact NA | intros a _].
  destruct (bn_top a <=? Z.to_nat (n / 64))%nat; [apply indep_zero; exact NR|].
  eapply bsim_bind with (P := TT); [| intros ? _; ind].
  destruct (rr =? ra)%nat; [ind | apply indep_wexpand; exact NR].
Qed.

Lemma indep_div_ft_mod : forall rm num divisor, rm <> RTmod -> num <> RTmod -> divisor <> RTmod ->
  indep TT (bn_div_fixed_top ops None (Some rm) num divisor).
Proof.
  intros rm num divisor NM NN ND. unfold bn_div_fixed_top, bn_live.
  eapply bsim_bind; [apply indep_getctx | intros c _].
  destruct (live_refs c (num :: divisor :: opt_refs None ++ opt_refs (Some rm))); [| apply bsim_unr].
  eapply bsim_bind; [apply indep_ctx_start | intros ? _].
  eapply bsim_bind; [apply indep_ctx_get | intros res NRES].
  eapply bsim_bind; [apply indep_ctx_get | intros tmp NTMP].
  eapply bsim_bind; [apply indep_ctx_get | intros snum NSNUM].
  eapply bsim_bind; [apply indep_ctx_get | intros sdiv NSDIV].
  eapply bsim_bind; [apply indep_copy; assumption | intros ? _].
  eapply bsim_bind; [apply indep_left_align; assumption | intros norm_shift _].
  eapply bsim_bind with (P := TT); [ind | intros ? _].
  eapply bsim_bind; [apply indep_lshift_ft; assumption | intros ? _].
  eapply bsim_bind; [apply indep_get; assumption | intros sd _].
  eapply bsim_bind; [apply indep_get; assumption | intros sn _].
  eapply bsim_bind with (P := TT).
  { destruct (bn_top sn <=? bn_top sd)%nat; [| ind].
    eapply bsim_bind; [apply indep_wexpand; assumption | intros ? _]. ind. }
  intros ? _.
  eapply bsim_bind; [apply indep_get; assumption | intros sn2 _].
  eapply bsim_bind; [apply indep_wexpand; assumption | intros ? _].
  eapply bsim_bind; [apply indep_get; assumption | intros nm _].
  eapply bsim_bind; [apply indep_get; assumption | intros dvs _].
  eapply bsim_bind with (P := TT); [ind | intros ? _].
  eapply bsim_bind; [apply indep_wexpand; assumption | intros ? _].
  eapply bsim_bind; [apply indep_get; assumption | intros sn3 _].
  eapply bsim_bind; [apply indep_get; assumption | intros tm _].
  eapply bsim_bind; [apply indep_get; assumption | intros r _].
  destruct (div_loop (bn_buf sd) (bn_top sd) (bn_top sn2 - bn_top sd) (bn_top sn2) (nth (bn_top sd - 1) (bn_buf sd) 0)
              (if (bn_top sd =? 1)%nat then 0 else nth (bn_top sd - 2) (bn_buf sd) 0) (bn_top sn2 - bn_top sd) 0 (bn_buf sn3, bn_buf tm, bn_buf r)) as [[snb tmb] rb].
  eapply bsim_bind; [apply indep_set; assumption | intros ? _].
  eapply bsim_bind; [apply indep_set; assumption | intros ? _].
  eapply bsim_bind; [apply indep_set; assumption | intros ? _].
  eapply bsim_bind; [apply indep_rshift_ft; assumption | intros ? _].
  apply indep_ctx_end.
Qed.

Lemma indep_mod : forall rm num divisor, rm <> RTmod -> num <> RTmod -> divisor <> RTmod -> indep TT (BN_mod ops rm num divisor).
Proof.
  intros rm num divisor NM NN ND. unfold BN_mod, BN_div.
  eapply bsim_bind; [apply indep_get; exact ND | intros d _].
  destruct (bn_top d =? 0)%nat; [apply bsim_unr|]. destruct (nth (bn_top d - 1) (bn_buf d) 0 =? 0); [apply bsim_unr|].
  eapply bsim_bind; [apply indep_div_ft_mod; assumption | intros ? _]. cbv beta iota.
  eapply bsim_bind with (P := TT); [apply indep_ret; exact I | intros ? _].
  eapply bsim_bind; [apply indep_get; exact NM | intros b _]. apply indep_set. exact NM.
Qed.

Definition Rfin (x y : unit * ST) : Prop := y = x /\ bn_d w = None.

Lemma ms_exit_sim : v = bn_nil 0 -> bsim Rfin ms_exit ms_exit0.
Proof.
  intros EV. unfold ms_exit, ms_exit0.
  eapply bsim_bind; [apply indep_ctx_end | intros ? _].
  intros s (L & G). unfold bbind, bget, bret, bset, bunr. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite G.
  destruct (bn_d w) as [q|] eqn:ED; [apply ts_unr|].
  apply ts_ret. split; [| exact ED]. unfold U. rewrite EV. reflexivity.
Qed.

Lemma ms_fix_sim : v = bn_nil 0 -> bsim Rfin ms_fix ms_fix0.
Proof.
  intros EV. unfold ms_fix, ms_fix0.
  eapply bsim_bind; [apply indep_get; discriminate | intros rr _].
  eapply bsim_bind; [apply indep_get; discriminate | intros n _].
  destruct (bn_dmax rr <? bn_top n)%nat; [apply bsim_unr|].
  eapply bsim_bind; [apply indep_set; discriminate | intros ? _].
  exact (ms_exit_sim EV).
Qed.

Lemma ms_rr_sim : forall ri, v = bn_nil 0 -> bsim Rfin (ms_rr ri) (ms_rr0 ri).
Proof.
  intros ri EV. unfold ms_rr, ms_rr0.
  eapply bsim_bind; [apply indep_zero; discriminate | intros ? _].
  apply bsim_getst. intros s OK. cbn [U setbn set_bns st_ri].
  destruct (negb (st_ri s =? ri)); [apply ts_unr|].
  revert s OK. change (bsim Rfin (bbind ops (BN_set_bit ops RMontRR (ri * 2)) (fun _ => bbind ops (BN_mod ops RMontRR RMontRR RMontN) (fun _ => ms_fix)))
                                 (bbind ops (BN_set_bit ops RMontRR (ri * 2)) (fun _ => bbind ops (BN_mod ops RMontRR RMontRR RMontN) (fun _ => ms_fix0)))).
  eapply bsim_bind; [apply indep_set_bit; discriminate | intros ? _].
  eapply bsim_bind; [apply indep_mod; discriminate | intros ? _].
  exact (ms_fix_sim EV).
Qed.

End Indep.

Section Switch.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).

Theorem ms_rr_switch : forall (ri : Z) (s : ST) (Σ : rts RT) (Q : unit * ST -> rts RT -> machine_state -> Prop) ms,
  (RTmod < length (st_bns s))%nat ->
  (bn_d (getbn RTmod s) = None -> implA (ms_rr0 ri (setbn RTmod (bn_nil 0) s)) Σ Q ms) ->
  implA (ms_rr ri s) Σ Q ms.
Proof.
  intros ri s Σ Q ms L H.
  eapply (implA_tsim (bn_d (getbn RTmod s) = None) (fun x y => y = x)); [| exact H | intros a b Σ' ms' -> HQ; exact HQ].
  exact (ms_rr_sim (bn_nil 0) (getbn RTmod s) ri eq_refl s (conj L eq_refl)).
Qed.
End Switch.
