(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tmap {A B} (f : A -> B) (t : tree A) : tree B :=
  match t with TEmpty => TEmpty | TNode l v r => TNode (tmap f l) (option_map f v) (tmap f r) end.
Lemma tget_tmap : forall {A B} (f : A -> B) p t, tget p (tmap f t) = option_map f (tget p t).
Proof. intros A B f p. induction p as [p IH|p IH|]; intros [|l v r]; cbn; try reflexivity; apply IH. Qed.

(* [comment removed for export] *)
Fixpoint tforall_acc {A} (f : positive -> A -> bool) (t : tree A) (k : positive -> positive) : bool :=
  match t with
  | TEmpty => true
  | TNode l v r =>
      (match v with Some x => f (k xH) x | None => true end
       && tforall_acc f l (fun p => k (xO p)) && tforall_acc f r (fun p => k (xI p)))%bool
  end.
Definition tforall {A} (f : positive -> A -> bool) (t : tree A) : bool := tforall_acc f t (fun p => p).

Lemma tforall_acc_spec : forall {A} (f : positive -> A -> bool) t k, tforall_acc f t k = true ->
  forall p x, tget p t = Some x -> f (k p) x = true.
Proof.
  intros A f t. induction t as [|l IHl v r IHr]; intros k H p x Hp; [rewrite tget_empty in Hp; discriminate|].
  cbn [tforall_acc] in H. apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hv Hl].
  destruct p as [p|p|]; cbn [tget] in Hp.
  - exact (IHr _ Hr p x Hp).
  - exact (IHl _ Hl p x Hp).
  - subst v. exact Hv.
Qed.
Lemma tforall_spec : forall {A} (f : positive -> A -> bool) t, tforall f t = true -> forall p x, tget p t = Some x -> f p x = true.
Proof. intros A f t H p x Hp. exact (tforall_acc_spec f t (fun p => p) H p x Hp). Qed.

(* [comment removed for export] *)
Definition tsplit {B} (u : tree B) : tree B * option B * tree B :=
  match u with TEmpty => (TEmpty, None, TEmpty) | TNode l v r => (l, v, r) end.
Fixpoint tforall2 {A B} (f : A -> option B -> bool) (t : tree A) (u : tree B) : bool :=
  match t with
  | TEmpty => true
  | TNode l v r =>
      let '(ul, uv, ur) := tsplit u in
      (match v with Some x => f x uv | None => true end && tforall2 f l ul && tforall2 f r ur)%bool
  end.
Lemma tforall2_spec : forall {A B} (f : A -> option B -> bool) t u, tforall2 f t u = true ->
  forall p x, tget p t = Some x -> f x (tget p u) = true.
Proof.
  intros A B f t. induction t as [|l IHl v r IHr]; intros u H p x Hp; [rewrite tget_empty in Hp; discriminate|].
  cbn [tforall2] in H.
  destruct u as [|ul uv ur]; cbn [tsplit] in H; apply andb_prop in H as [H Hr]; apply andb_prop in H as [Hv Hl];
    destruct p as [p|p|]; cbn [tget] in Hp |- *.
  - pose proof (IHr TEmpty Hr p x Hp) as H'. rewrite tget_empty in H'. exact H'.
  - pose proof (IHl TEmpty Hl p x Hp) as H'. rewrite tget_empty in H'. exact H'.
  - subst v. exact Hv.
  - exact (IHr ur Hr p x Hp).
  - exact (IHl ul Hl p x Hp).
  - subst v. exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition svar (σ : tree lin) (x : positive) : lin := match tget x σ with Some l => l | None => lvar x end.
Fixpoint tsubst (σ : tree lin) (t : list (positive * Z)) : lin :=
  match t with [] => LIN 0 [] | (x, k) :: t' => ladd (lscale k (svar σ x)) (tsubst σ t') end.
Definition lsubst (σ : tree lin) (l : lin) : lin := laddc (tsubst σ (l_t l)) (l_c l).
Definition ecomp (E : valu) (σ : tree lin) : valu := fun x => lden E (svar σ x).

Lemma tsubst_sound : forall E σ t, eqm (lz E (tsubst σ t)) (tsum (ecomp E σ) t).
Proof.
  intros E σ t. induction t as [|[x k] t IH]; cbn [tsubst tsum].
  - unfold lz; cbn. apply eqm_refl.
  - eapply eqm_trans; [apply lz_ladd|]. apply eqm_add; [|exact IH].
    eapply eqm_trans; [apply lz_lscale|]. apply eqm_mul; [apply eqm_refl|].
    unfold vz, ecomp, lden. apply eqm_sym. apply eqm_u.
Qed.

Lemma lden_lsubst : forall E σ l, lden E (lsubst σ l) = lden (ecomp E σ) l.
Proof.
  intros E σ [c t]. unfold lsubst; cbn [l_c l_t]. unfold lden at 1. apply Z_to_bv_eqm.
  eapply eqm_trans; [apply lz_laddc|]. change (lz (ecomp E σ) (LIN c t)) with (c + tsum (ecomp E σ) t).
  replace (lz E (tsubst σ t) + c) with (c + lz E (tsubst σ t)) by lia. apply eqm_add; [apply eqm_refl | apply tsubst_sound].
Qed.

Definition bsubst (σ : tree lin) (v : bval) : bval := match v with BK b => BK b | BV l j => BV (lsubst σ l) j end.
Lemma bden_bsubst : forall E σ v, bden E (bsubst σ v) = bden (ecomp E σ) v.
Proof. intros E σ [b|l j]; cbn [bsubst bden]; [reflexivity | rewrite lden_lsubst; reflexivity]. Qed.

Definition fsubst (σ : tree lin) (f : fact) : fact :=
  match f with FCond c a b tk => FCond c (lsubst σ a) (lsubst σ b) tk | FRange l lo hi => FRange (lsubst σ l) lo hi
  | FMod l k r => FMod (lsubst σ l) k r | FBits l m v => FBits (lsubst σ l) m v
  | FByte x v j => FByte (lsubst σ x) (lsubst σ v) j
  | FBytes x bs => FBytes (lsubst σ x) (List.map (fun p => (lsubst σ (fst p), snd p)) bs) end.
Lemma nth_map_lsubst : forall σ (bs : list (lin * Z)) i, (i < length bs)%nat ->
  nth i (List.map (fun p => (lsubst σ (fst p), snd p)) bs) (lconst 0, 0) = (lsubst σ (fst (nth i bs (lconst 0, 0))), snd (nth i bs (lconst 0, 0))).
Proof.
  intros σ bs i Hi. rewrite (nth_indep _ _ ((fun p : lin * Z => (lsubst σ (fst p), snd p)) (lconst 0, 0))) by (rewrite length_map; exact Hi).
  apply (map_nth (fun p : lin * Z => (lsubst σ (fst p), snd p)) bs (lconst 0, 0) i).
Qed.
Lemma fact_ok_fsubst : forall E σ f, fact_ok E (fsubst σ f) <-> fact_ok (ecomp E σ) f.
Proof.
  intros E σ [c a b tk|l lo hi|l k r|l m v|x v j|x bs]; cbn [fsubst fact_ok]; rewrite ?lden_lsubst; try tauto.
  rewrite length_map. split; intros H i Hi; specialize (H i Hi); rewrite (nth_map_lsubst σ bs i Hi) in *; cbn [fst snd] in *;
    rewrite ?lden_lsubst in *; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lwf (n : positive) (l : lin) : bool := forallb (fun '(x, _) => Pos.ltb x n) (l_t l).
Lemma tsum_agree : forall n E1 E2 t, forallb (fun '(x, _) => Pos.ltb x n) t = true -> agree n E1 E2 -> tsum E1 t = tsum E2 t.
Proof.
  intros n E1 E2 t. induction t as [|[x k] t IH]; intros H Ha; cbn [tsum]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [Hx Ht]. apply Pos.ltb_lt in Hx.
  unfold vz. rewrite (Ha x Hx), IH by assumption. reflexivity.
Qed.
Lemma lden_agree : forall n E1 E2 l, lwf n l = true -> agree n E1 E2 -> lden E1 l = lden E2 l.
Proof. intros n E1 E2 [c t] H Ha. unfold lden, lz; cbn [l_c l_t]. rewrite (tsum_agree n E1 E2 t H Ha). reflexivity. Qed.

Definition bwf (n : positive) (v : bval) : bool := match v with BK _ => true | BV l _ => lwf n l end.
Lemma bden_agree : forall n E1 E2 v, bwf n v = true -> agree n E1 E2 -> bden E1 v = bden E2 v.
Proof. intros n E1 E2 [b|l j] H Ha; cbn [bden bwf] in *; [reflexivity | rewrite (lden_agree n E1 E2 l H Ha); reflexivity]. Qed.
Definition fwf (n : positive) (f : fact) : bool :=
  match f with FCond _ a b _ => (lwf n a && lwf n b)%bool | FRange l _ _ => lwf n l | FMod l _ _ => lwf n l | FBits l _ _ => lwf n l
  | FByte x v _ => (lwf n x && lwf n v)%bool
  | FBytes x bs => (lwf n x && forallb (fun p => lwf n (fst p)) bs)%bool end.
Lemma fact_ok_agree : forall n E1 E2 f, fwf n f = true -> agree n E1 E2 -> fact_ok E1 f -> fact_ok E2 f.
Proof.
  intros n E1 E2 [c a b tk|l lo hi|l k r|l m v|x v j|x bs] H Ha Hf; cbn [fwf fact_ok] in *.
  - apply andb_prop in H as [H1 H2]. rewrite <- (lden_agree n E1 E2 a H1 Ha), <- (lden_agree n E1 E2 b H2 Ha). exact Hf.
  - rewrite <- (lden_agree n E1 E2 l H Ha). exact Hf.
  - rewrite <- (lden_agree n E1 E2 l H Ha). exact Hf.
  - rewrite <- (lden_agree n E1 E2 l H Ha). exact Hf.
  - apply andb_prop in H as [H1 H2]. rewrite <- (lden_agree n E1 E2 x H1 Ha), <- (lden_agree n E1 E2 v H2 Ha). exact Hf.
  - apply andb_prop in H as [H1 H2]. rewrite forallb_forall in H2. intros i Hi. rewrite <- (lden_agree n E1 E2 x H1 Ha).
    destruct (nth_in_or_default i bs (lconst 0, 0)) as [Hin|Hdf].
    + rewrite <- (lden_agree n E1 E2 _ (H2 _ Hin) Ha). exact (Hf i Hi).
    + rewrite Hdf. cbn [fst snd]. rewrite !lden_lconst. specialize (Hf i Hi). rewrite Hdf in Hf. cbn [fst snd] in Hf. rewrite lden_lconst in Hf. exact Hf.
Qed.

Definition rwf (n : positive) (R : region) : bool :=
  (lwf n (rg_base R) && lwf n (rg_size R) && tforall (fun _ v => bwf n v) (rg_cont R))%bool.

Fixpoint regs_wf_n (n : positive) (R : tree lin) (k : nat) : bool :=
  match k with O => true | S k' => (lwf n (rget R (Pos.of_succ_nat k)) && regs_wf_n n R k')%bool end.

Definition rsv_wf (n : positive) (r : rsv) : bool := match r with RAt l => lwf n l | _ => true end.

Definition state_wf (P : sst) : bool :=
  let n := s_next P in
  (regs_wf_n n (s_regs P) 31 && forallb (rwf n) (s_rgs P) && forallb (fwf n) (s_facts P) && rsv_wf n (s_resv P))%bool.

(* [comment removed for export] *)
Lemma rkey_succ : forall r : reg, r <> 0%bv -> exists k, (1 <= k <= 31)%nat /\ rkey r = Pos.of_succ_nat k.
Proof.
  intros r Hr. pose proof (bv_unsigned_in_range _ r) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 5) with 32 in R.
  assert (Hz : bv_unsigned r <> 0) by (intros Hc; apply Hr; apply bv_eq; rewrite Hc; reflexivity).
  exists (Z.to_nat (bv_unsigned r)). split; [lia|]. unfold rkey, bv_key.
  apply Pos2Z.inj. rewrite Z2Pos.id by lia. rewrite Zpos_P_of_succ_nat, Z2Nat.id by lia. lia.
Qed.

Lemma regs_wf_n_spec : forall n R k, regs_wf_n n R k = true -> forall i, (1 <= i <= k)%nat -> lwf n (rget R (Pos.of_succ_nat i)) = true.
Proof.
  intros n R k. induction k as [|k IH]; intros H i Hi; [lia|].
  cbn [regs_wf_n] in H. apply andb_prop in H as [H1 H2]. destruct (Nat.eq_dec i (S k)) as [->|Hne]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rg_ok_agree : forall n E1 E2 m R, rwf n R = true -> agree n E1 E2 -> rg_ok segs E1 m R -> rg_ok segs E2 m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E1 E2 m R Hw Ha HR. unfold rwf in Hw. apply andb_prop in Hw as [Hb Hc]. apply andb_prop in Hb as [Hb Hs].
  unfold rg_ok, rsz in *. rewrite <- (lden_agree n E1 E2 _ Hb Ha), <- (lden_agree n E1 E2 _ Hs Ha). destruct HR as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros p v Hp. destruct (H4 p v Hp) as [Hp1 Hp2]. split; [exact Hp1|].
  rewrite <- (bden_agree n E1 E2 v (tforall_spec _ _ Hc p v Hp) Ha). exact Hp2.
Qed.

#[using="Type"] Lemma rgs_disj_agree : forall n E1 E2 rgs, forallb (rwf n) rgs = true -> agree n E1 E2 -> rgs_disj E1 rgs -> rgs_disj E2 rgs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E1 E2 rgs. induction rgs as [|R rs IH]; intros Hw Ha Hd; [exact I|].
  cbn [forallb] in Hw. apply andb_prop in Hw as [HwR Hws]. destruct Hd as [Hx Hrs]. split; [|exact (IH Hws Ha Hrs)].
  apply Forall_forall. intros R' HR'. rewrite Forall_forall in Hx. pose proof (Hx R' HR') as Hd.
  rewrite forallb_forall in Hws. pose proof (Hws R' HR') as HwR'.
  unfold rwf in HwR, HwR'. apply andb_prop in HwR as [HbR _]. apply andb_prop in HwR' as [HbR' _].
  apply andb_prop in HbR as [HbR HsR]. apply andb_prop in HbR' as [HbR' HsR'].
  unfold rg_disj, rsz in *. rewrite <- (lden_agree n E1 E2 _ HbR Ha), <- (lden_agree n E1 E2 _ HbR' Ha),
    <- (lden_agree n E1 E2 _ HsR Ha), <- (lden_agree n E1 E2 _ HsR' Ha). exact Hd.
Qed.

#[using="Type"] Lemma sden0_agree : forall P E1 E2 ms, state_wf P = true -> agree (s_next P) E1 E2 -> sden0 segs E1 P ms -> sden0 segs E2 P ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros P E1 E2 ms Hw Ha (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm). unfold state_wf in Hw.
  apply andb_prop in Hw as [Hw Hwv]. apply andb_prop in Hw as [Hw Hwf]. apply andb_prop in Hw as [Hwr Hwg].
  split; [exact Hpc|]. split; [exact Hsvc|].
  split; [destruct (s_resv P) as [|l|]; cbn [rsv_ok rsv_wf] in *; [exact Hresv | rewrite <- (lden_agree _ E1 E2 l Hwv Ha); exact Hresv | exact I]|].
  split; [|split; [|split; [|split]]].
  - intros r. rewrite (HR r). destruct (decide (r = 0%bv)) as [->|Hr0]; [reflexivity|].
    destruct (rkey_succ r Hr0) as (k & Hk & Ek). rewrite Ek.
    apply (lden_agree (s_next P)); [apply (regs_wf_n_spec _ _ 31 Hwr k Hk) | exact Ha].
  - apply Forall_forall. intros R HR'. rewrite forallb_forall in Hwg. rewrite Forall_forall in HG.
    exact (rg_ok_agree _ E1 E2 _ R (Hwg R HR') Ha (HG R HR')).
  - exact (rgs_disj_agree _ E1 E2 _ Hwg Ha HD).
  - apply Forall_forall. intros f Hf. rewrite forallb_forall in Hwf. rewrite Forall_forall in HF.
    exact (fact_ok_agree _ E1 E2 f (Hwf f Hf) Ha (HF f Hf)).
  - exact Hfrm.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sden0_sden : forall P E ms, state_wf P = true -> sden0 segs E P ms -> sden segs E P ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros P E ms Hw H E' Ha. exact (sden0_agree P E E' ms Hw Ha H). Qed.

End WithSegs.
