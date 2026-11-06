From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import YK15 YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0d_mf YL0e.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable.R Require Import Cfg.
Import ListNotations.
Local Open Scope Z_scope.
Lemma mreal_tset_g {AM : AllocMode} {R} : forall segs (t : itree astate R) c (Q : R -> config -> Prop) (K : R -> TSet),
amf = true -> mreal segs c t Q -> safe t ->
(forall r c' tr, cpath t tr r -> Q r c' -> realizes segs c' (K r)) ->
realizes segs c (tset_mf t K).
Proof.
destruct AM as [b]. intros segs t c Q K Hb. cbn in Hb. subst b. exact (mreal_tset_mf segs t c Q K).
Qed.
Lemma tset_mf_congr {S A} : forall (t : itree S A) (K K' : A -> TSet),
(forall a, t_eq (K a) (K' a)) -> t_eq (tset_mf t K) (tset_mf t K').
Proof. intros t K K' HK tr. split; apply tset_mf_mono; intros a tr' H; apply (HK a); exact H. Qed.
Lemma tset_mf_bind_eq {A B} : forall (t : itree astate (B * astate)) (m : M A) (f : A -> M B) (s : astate) (K : B * astate -> TSet),
t = bind m f s -> t_eq (tset_mf t K) (tset_mf (m s) (fun r => tset_mf (f (fst r) (snd r)) K)).
Proof. intros t m f s K ->. apply tset_mf_mbind. Qed.
