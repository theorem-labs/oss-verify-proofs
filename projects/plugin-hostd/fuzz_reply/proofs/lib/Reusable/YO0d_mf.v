From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK15 YM06 YM02 YO0i YO0f YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint tset_mf {S A : Type} (t : itree S A) (K : A -> TSet) : TSet :=
match t with
| IRet a => K a
| IFail _ => t_bot
| IAsk (KJunk _) _ k => t_alt (fun z : {z : Z | 0 <= z < 256} => tset_mf (k (proj1_sig z)) K)
| IAsk q _ k => if fallible q then t_alt2 (tset_mf (k 0) K) (tset_mf (k 1) K) else tset_mf (k 1) K
end.
Lemma tset_mf_mono {S A} : forall (t : itree S A) (K K' : A -> TSet) tr,
(forall a tr, K a tr -> K' a tr) -> tset_mf t K tr -> tset_mf t K' tr.
Proof.
induction t as [a | q s k IH | f]; intros K K' tr HK H.
- apply HK, H.
- destruct q; cbn in H |- *;
first [ destruct H as [[z Hz] H]; exists (exist _ z Hz); eapply IH; eauto
| destruct H as [H|H]; [left|right]; eapply IH; eauto
| eapply IH; eauto ].
- exact H.
Qed.
Lemma tset_mf_ibind {S A B} : forall (t : itree S A) (f : A -> itree S B) (K : B -> TSet),
t_eq (tset_mf (ibind t f) K) (tset_mf t (fun a => tset_mf (f a) K)).
Proof.
induction t as [a | q s k IH | e]; intros f K; cbn; [apply t_eq_refl | | apply t_eq_refl].
destruct q; cbn;
first [ intros tr; split; intros [z Hz]; exists z;
[apply (proj1 (IH (proj1_sig z) f K tr)) | apply (proj2 (IH (proj1_sig z) f K tr))]; exact Hz
| apply t_alt2_congr; apply IH
| apply IH ].
Qed.
Lemma tset_mf_mbind {A B} : forall (m : M A) (f : A -> M B) (s : astate) (K : B * astate -> TSet),
t_eq (tset_mf (bind m f s) K) (tset_mf (m s) (fun r => tset_mf (f (fst r) (snd r)) K)).
Proof.
intros m f s K. unfold bind. eapply t_eq_trans; [apply tset_mf_ibind|].
intros tr. split; apply tset_mf_mono; intros [a s'] tr' H; exact H.
Qed.
Section mf.
Variable segs : list Segment.
Local Notation realizes := (@realizes segs MayFail).
Local Notation mreal := (@mreal segs MayFail _).
Lemma rz_weak_mf : forall c T T', realizes c T -> (forall tr, T tr -> T' tr) -> realizes c T'.
Proof using.
intros c T T' H Hs. exact (@rz_weak segs MayFail c T T' eq_refl H Hs).
Qed.
Theorem mreal_tset_mf {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) (K : R -> TSet),
mreal c t Q -> safe t ->
(forall r c' tr, cpath t tr r -> Q r c' -> realizes c' (K r)) ->
realizes c (tset_mf t K).
Proof using.
induction t as [r | q s k IH | f]; intros c Q K H Hs HK; cbn in H, Hs.
- apply (@SR_realizes segs MayFail c (Q r)); [exact H |].
intros c' H'. cbn. apply (HK r c' []); [reflexivity | exact H'].
- apply (@SR_realizes segs MayFail c _ _ H). intros c1 Hk.
assert (HKz : forall z, canswer q z -> forall r c' tr, cpath (k z) tr r -> Q r c' -> realizes c' (K r)).
{ intros z Hz r c' tr Hp HQ. apply (HK r c' ((q, z) :: tr)); [cbn; auto | exact HQ]. }
destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in Hk, HKz |- *.
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
pose proof (Hc i) as Hci. rewrite (Hb i) in Hci.
eapply IH; [exact Hci | apply Hs; exact I | apply HKz; reflexivity].
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
apply (rz_weak_mf (nx i) (tset_mf (k (bit i)) K)).
* eapply IH; [apply Hc | apply Hs; exact I | apply HKz; exact (Hbits i)].
* intros tr Htr. unfold t_alt2. destruct (Hbits i) as [E|E]; rewrite E in Htr; [left|right]; exact Htr.
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
pose proof (Hc i) as Hci. rewrite (Hb i) in Hci.
eapply IH; [exact Hci | apply Hs; exact I | apply HKz; reflexivity].
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
apply (rz_weak_mf (nx i) (tset_mf (k (bit i)) K)).
* eapply IH; [apply Hc | apply Hs; exact I | apply HKz; exact (Hbits i)].
* intros tr Htr. unfold t_alt2. destruct (Hbits i) as [E|E]; rewrite E in Htr; [left|right]; exact Htr.
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
apply (rz_weak_mf (nx i) (tset_mf (k (bit i)) K)).
* eapply IH; [apply Hc | apply Hs; exact I | apply HKz; exact (Hbits i)].
* intros tr Htr. unfold t_alt2. destruct (Hbits i) as [E|E]; rewrite E in Htr; [left|right]; exact Htr.
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
apply (rz_weak_mf (nx i) (tset_mf (k (bit i)) K)).
* eapply IH; [apply Hc | apply Hs; exact I | apply HKz; exact (Hbits i)].
* intros tr Htr. unfold t_alt2. destruct (Hbits i) as [E|E]; rewrite E in Htr; [left|right]; exact Htr.
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
pose proof (Hc i) as Hci. rewrite (Hb i) in Hci.
eapply IH; [exact Hci | apply Hs; exact I | apply HKz; reflexivity].
+ destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _).
apply (@rz_silent_all segs MayFail c1 J nx i0); [exact Hn|]. intros i.
apply (rz_weak_mf (nx i) (tset_mf (k (bit i)) K)).
* eapply IH; [apply Hc | apply Hs; exact I | apply HKz; exact (Hbits i)].
* intros tr Htr. unfold t_alt2. destruct (Hbits i) as [E|E]; rewrite E in Htr; [left|right]; exact Htr.
+ destruct Hk as (z & Hz & Hc).
apply (rz_weak_mf c1 (tset_mf (k z) K)).
* eapply IH; [exact Hc | apply Hs; exact Hz | apply HKz; exact Hz].
* intros tr Htr. exists (exist _ z Hz). exact Htr.
- destruct Hs.
Qed.
End mf.
