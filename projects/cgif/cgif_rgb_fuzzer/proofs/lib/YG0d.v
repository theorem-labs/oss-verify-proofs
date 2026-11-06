(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YK15 YK0k YK18 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ASTACK : Z := 16384.
Definition ESTACK : Z := 4096.
Definition acallee_saved (r : Z) : Prop :=
r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27).
Definition aregs_preserved (regs regs' : bvmap 5 word) : Prop :=
forall r, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition spZ (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 2).
Definition raZ (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 1).
Definition s0Z (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 8).
Definition argZ (regs : bvmap 5 word) (i : Z) : Z := bv_unsigned (getr regs (Z_to_bv 5 (10 + i))).
Definition w64 (z : Z) : word := Z_to_bv 64 z.
Definition rdword (rd : reader) (a : Z) : option Z :=
match rd a, rd (a+1), rd (a+2), rd (a+3), rd (a+4), rd (a+5), rd (a+6), rd (a+7) with
| Some b0, Some b1, Some b2, Some b3, Some b4, Some b5, Some b6, Some b7 =>
Some (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))))
| _, _, _, _, _, _, _, _ => None
end.
Definition same_io (md md' : Model) : Prop :=
m_fd md' = m_fd md /\ m_io md' = m_io md /\ m_fsys md' = m_fsys md /\ m_proc md' = m_proc md.
Section h.
Variable segs : list Segment.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
(* [comment removed for export] *)
Definition SRrF (W : world segs) (c : config) (Q : world segs -> config -> Prop) : Prop :=
AIw W (cfg_model c) ->
forall T, (forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizesM segs false c' T) ->
srealizesM segs false c T.
Lemma SRr_F : forall W c Q, SRr segs W c Q -> SRrF W c Q.
Proof. intros W c Q H HI T HK. exact (H false HI T HK). Qed.
Lemma SRrF_ret : forall W c (Q : world segs -> config -> Prop), Q W c -> SRrF W c Q.
Proof. intros W c Q HQ HI T HK. exact (HK W c (wle_refl segs W) HI HQ). Qed.
Lemma SRrF_bind : forall W c (R Q : world segs -> config -> Prop),
SRrF W c R -> (forall W' c', wle W W' -> R W' c' -> SRrF W' c' Q) -> SRrF W c Q.
Proof.
intros W c R Q H1 H2 HI T HK. apply (H1 HI T). intros W' c' Hle HI' HR.
apply (H2 W' c' Hle HR HI' T). intros W'' c'' Hle' HI'' HQ.
exact (HK W'' c'' (wle_trans segs _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRrF_mono : forall W c (Q Q' : world segs -> config -> Prop),
SRrF W c Q -> (forall W' c', wle W W' -> Q W' c' -> Q' W' c') -> SRrF W c Q'.
Proof.
intros W c Q Q' H HQQ HI T HK. apply (H HI T). intros W' c' Hle HI' HQ.
exact (HK W' c' Hle HI' (HQQ W' c' Hle HQ)).
Qed.
Lemma SRrF_world_le : forall W W' c Q,
wle W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> SRrF W' c Q -> SRrF W c Q.
Proof.
intros W W' c Q Hle Htr H HI T HK. apply (H (Htr HI) T).
intros W'' c'' Hle' HI'' HQ. exact (HK W'' c'' (wle_trans segs _ _ _ Hle Hle') HI'' HQ).
Qed.
(* [comment removed for export] *)
Inductive ckind := KLive | KDeadF | KSpin.
Lemma SRr_node_kinds : forall (W : world segs) c (I : Type) (nx : I -> config) (kd : I -> ckind) (i0 : I) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
kd i0 = KLive ->
(forall i, kd i = KSpin -> AIw W (cfg_model (nx i)) -> srealizesM segs false (nx i) t_nil) ->
(forall i, kd i = KDeadF -> SRrF W (nx i) Q) ->
(forall i, kd i <> KLive -> fo_dead segs c (nx i)) ->
(forall i, kd i = KLive -> SRr segs W (nx i) Q) ->
SRr segs W c Q.
Proof.
intros W c I nx kd i0 Q Hnode HIt Hi0 Hspin Hdf Hdead Hk b HI T HK.
assert (HKF : forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizesM segs false c' T).
{ intros W' c' Hle HI' HQ. apply (srealizesM_mono segs b false); [destruct b; exact Logic.I | exact (HK W' c' Hle HI' HQ)]. }
assert (HT0 : T []).
{ eapply srealizesM_nonempty. apply (Hk i0 Hi0 b (HIt i0 HI) T HK). }
apply (srzM_conseq segs b c (t_alt (fun i : I => t_emit [] (match kd i with KSpin => t_nil | _ => T end)))).
- apply (srzM_node_dead segs b c I (fun _ => []) nx (fun i => match kd i with KSpin => t_nil | _ => T end) i0 (fun i => kd i <> KLive) Hnode).
+ rewrite Hi0. intros X; exact (X eq_refl).
+ intros i Hs. split; [| intros _; exact (Hdead i Hs)]. destruct (kd i) eqn:Ek; [exfalso; exact (Hs eq_refl) | |].
* exact (srealizesM_E segs _ _ _ (Hdf i Ek (HIt i HI) T HKF)).
* exact (srealizesM_E segs _ _ _ (Hspin i Ek (HIt i HI))).
+ intros i Hs. destruct (kd i) eqn:Ek; [| exfalso; apply Hs; discriminate | exfalso; apply Hs; discriminate].
exact (Hk i Ek b (HIt i HI) T HK).
- intro tr. split.
+ intros [i Hi]. destruct (kd i).
* exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
* exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
* apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. exact HT0.
+ intros Htr. exists i0. rewrite Hi0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.
(* [comment removed for export] *)
Lemma SRrF_node_kinds : forall (W : world segs) c (I : Type) (nx : I -> config) (kd : I -> ckind) (i0 : I) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
kd i0 <> KSpin ->
(forall i, kd i = KSpin -> AIw W (cfg_model (nx i)) -> srealizesM segs false (nx i) t_nil) ->
(forall i, kd i <> KSpin -> SRrF W (nx i) Q) ->
SRrF W c Q.
Proof.
intros W c I nx kd i0 Q Hnode HIt Hi0 Hspin Hk HI T HK.
assert (HT0 : T []).
{ eapply srealizesM_nonempty. apply (Hk i0 Hi0 (HIt i0 HI) T HK). }
apply (srzM_conseq segs false c (t_alt (fun i : I => t_emit [] (match kd i with KSpin => t_nil | _ => T end)))).
- apply (srzM_node segs false c I (fun _ => []) nx (fun i => match kd i with KSpin => t_nil | _ => T end) i0 Hnode).
intros i. destruct (kd i) eqn:Ek.
+ exact (Hk i ltac:(rewrite Ek; discriminate) (HIt i HI) T HK).
+ exact (Hk i ltac:(rewrite Ek; discriminate) (HIt i HI) T HK).
+ exact (Hspin i Ek (HIt i HI)).
- intro tr. split.
+ intros [i Hi]. destruct (kd i).
* exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
* exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
* apply (t_emit_nil_eq t_nil eq_refl tr) in Hi. unfold t_nil in Hi. subst tr. exact HT0.
+ intros Htr. exists i0. destruct (kd i0); [| | exfalso; exact (Hi0 eq_refl)]; exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.
(* [comment removed for export] *)
Lemma SRr_node_tnil : forall (W : world segs) c (I : Type) (nx : I -> config) (sp : I -> bool) (i0 : I) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
sp i0 = false ->
(forall i, sp i = true -> AIw W (cfg_model (nx i)) -> srealizesM segs false (nx i) t_nil) ->
(forall i, sp i = true -> fo_dead segs c (nx i)) ->
(forall i, sp i = false -> SRr segs W (nx i) Q) ->
SRr segs W c Q.
Proof.
intros W c I nx sp i0 Q Hnode HIt Hi0 Hspin Hdead Hk.
apply (SRr_node_kinds W c I nx (fun i => if sp i then KSpin else KLive) i0 Q Hnode HIt).
- rewrite Hi0. reflexivity.
- intros i Hi. destruct (sp i) eqn:Es; [exact (Hspin i Es) | discriminate Hi].
- intros i Hi. destruct (sp i); discriminate Hi.
- intros i Hi. destruct (sp i) eqn:Es; [exact (Hdead i Es) | exfalso; exact (Hi eq_refl)].
- intros i Hi. destruct (sp i) eqn:Es; [discriminate Hi | exact (Hk i Es)].
Qed.
Lemma SRrF_tnil : forall (W : world segs) c (P : world segs -> config -> Prop),
SRrF W c P -> (forall W' c', wle W W' -> P W' c' -> AIw W' (cfg_model c') -> srealizesM segs false c' t_nil) ->
AIw W (cfg_model c) -> srealizesM segs false c t_nil.
Proof. intros W c P H HP HI. apply (H HI t_nil). intros W' c' Hle HI' HP'. exact (HP W' c' Hle HP' HI'). Qed.
Lemma SRr_tnil : forall (W : world segs) c (P : world segs -> config -> Prop),
SRr segs W c P -> (forall W' c', wle W W' -> P W' c' -> AIw W' (cfg_model c') -> srealizesM segs false c' t_nil) ->
AIw W (cfg_model c) -> srealizesM segs false c t_nil.
Proof. intros W c P H HP HI. exact (SRrF_tnil W c P (SRr_F W c P H) HP HI). Qed.
Definition refusable (q : kreq) : bool :=
match q with KMapUser _ _ _ | KMapFreeArray _ _ _ | KMmapSec _ => true | _ => false end.
(* [comment removed for export] *)
Fixpoint amrealE {R : Type} (t : itree astate R) : world segs -> config -> (R -> world segs -> config -> Prop) -> Prop :=
fun W c Q =>
match t with
| IRet r => SRrF W c (Q r)
| IFail _ => True
| ISpin _ => AIw W (cfg_model c) -> srealizesM segs false c t_nil
| IAsk q snap k =>
SRrF W c (fun W1 c1 =>
match q with
| KDepot _ => exists z, aok snap q z /\ amrealE (k z) W1 c1 Q
| _ => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok segs c1 I (fun _ => []) nx /\
(forall i, AIw W1 (cfg_model c1) -> AIw W1 (cfg_model (nx i))) /\
(forall i, aok snap q (bit i)) /\
sp i0 = false /\ bit i0 = 1 /\
(refusable q = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AIw W1 (cfg_model (nx i)) -> srealizesM segs false (nx i) t_nil) /\
(forall i, sp i = false -> amrealE (k (bit i)) W1 (nx i) Q)
end)
end.
(* [comment removed for export] *)
Fixpoint amreal {R : Type} (t : itree astate R) : world segs -> config -> (R -> world segs -> config -> Prop) -> Prop :=
fun W c Q =>
match t with
| IRet r => SRr segs W c (Q r)
| IFail _ => True
| ISpin _ => AIw W (cfg_model c) -> srealizesM segs false c t_nil
| IAsk q snap k =>
SRr segs W c (fun W1 c1 =>
match q with
| KDepot _ => exists z, aok snap q z /\ amreal (k z) W1 c1 Q
| _ => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok segs c1 I (fun _ => []) nx /\
(forall i, AIw W1 (cfg_model c1) -> AIw W1 (cfg_model (nx i))) /\
(forall i, aok snap q (bit i)) /\
sp i0 = false /\ bit i0 = 1 /\
(refusable q = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AIw W1 (cfg_model (nx i)) -> srealizesM segs false (nx i) t_nil) /\
(forall i, (sp i = true \/ bit i <> 1) -> fo_dead segs c1 (nx i)) /\
(forall i, sp i = false -> if Z.eqb (bit i) 1 then amreal (k (bit i)) W1 (nx i) Q else amrealE (k (bit i)) W1 (nx i) Q)
end)
end.
Lemma amrealE_mono {R} : forall (t : itree astate R) W c (Q Q' : R -> world segs -> config -> Prop),
(forall r W' c', Q r W' c' -> Q' r W' c') -> amrealE t W c Q -> amrealE t W c Q'.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q Q' HQ H; cbn in *.
- eapply SRrF_mono; [exact H | intros W' c' _ H'; apply HQ, H'].
- eapply SRrF_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [exact HQ | apply Hc, Hi]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact HQ | exact Hc].
- exact H.
- exact I.
Qed.
Lemma amreal_E {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal t W c Q -> amrealE t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q H; cbn in *.
- apply SRr_F. exact H.
- apply SRr_F in H. eapply SRrF_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hd & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; specialize (Hc i Hi); destruct (Z.eqb (bit i) 1); [apply IH; exact Hc | exact Hc]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH. exact Hc.
- exact H.
- exact I.
Qed.
Lemma amreal_mono {R} : forall (t : itree astate R) W c (Q Q' : R -> world segs -> config -> Prop),
(forall r W' c', Q r W' c' -> Q' r W' c') -> amreal t W c Q -> amreal t W c Q'.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q Q' HQ H; cbn in *.
- eapply SRr_mono; [exact H | intros W' c' _ H'; apply HQ, H'].
- eapply SRr_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hd & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; split; [exact Hd|]; intros i Hi; specialize (Hc i Hi); destruct (Z.eqb (bit i) 1);
[eapply IH; [exact HQ | exact Hc] | eapply amrealE_mono; [exact HQ | exact Hc]]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact HQ | exact Hc].
- exact H.
- exact I.
Qed.
Lemma amrealE_SRr_pre {R} : forall (t : itree astate R) W c Q (P : world segs -> config -> Prop),
SRrF W c P -> (forall W' c', wle W W' -> P W' c' -> amrealE t W' c' Q) -> amrealE t W c Q.
Proof.
intros t W c Q P HP H. destruct t as [r | q s k | pc | f]; cbn in *.
- eapply SRrF_bind; [exact HP | exact H].
- eapply SRrF_bind; [exact HP | exact H].
- apply (SRrF_tnil W c P HP). intros W' c' Hle HP' HI'. exact (H W' c' Hle HP' HI').
- exact I.
Qed.
Lemma amreal_SRr_pre {R} : forall (t : itree astate R) W c Q (P : world segs -> config -> Prop),
SRr segs W c P -> (forall W' c', wle W W' -> P W' c' -> amreal t W' c' Q) -> amreal t W c Q.
Proof.
intros t W c Q P HP H. destruct t as [r | q s k | pc | f]; cbn in *.
- eapply SRr_bind; [exact HP | exact H].
- eapply SRr_bind; [exact HP | exact H].
- apply (SRr_tnil W c P HP). intros W' c' Hle HP' HI'. exact (H W' c' Hle HP' HI').
- exact I.
Qed.
Lemma amrealE_world_le {R} : forall (t : itree astate R) W W' c Q,
wle W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> amrealE t W' c Q -> amrealE t W c Q.
Proof.
intros t W W' c Q Hle Htr H. destruct t as [r | q s k | pc | f]; cbn in *.
- eapply SRrF_world_le; eassumption.
- eapply SRrF_world_le; eassumption.
- intros HI. exact (H (Htr HI)).
- exact I.
Qed.
Lemma amreal_world_le {R} : forall (t : itree astate R) W W' c Q,
wle W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> amreal t W' c Q -> amreal t W c Q.
Proof.
intros t W W' c Q Hle Htr H. destruct t as [r | q s k | pc | f]; cbn in *.
- eapply SRr_world_le; eassumption.
- eapply SRr_world_le; eassumption.
- intros HI. exact (H (Htr HI)).
- exact I.
Qed.
Lemma amrealE_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c
(P : A -> world segs -> config -> Prop) (Q : R -> world segs -> config -> Prop),
amrealE t W c P -> (forall a W' c', P a W' c' -> amrealE (f a) W' c' Q) -> amrealE (ibind t f) W c Q.
Proof.
induction t as [a | q s k IH | pc | e]; intros f W c P Q H Hf; cbn in *.
- eapply amrealE_SRr_pre; [exact H | intros W' c' _ HP; exact (Hf a W' c' HP)].
- eapply SRrF_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact Hf]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact Hf].
- exact H.
- exact I.
Qed.
Lemma amreal_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c
(P : A -> world segs -> config -> Prop) (Q : R -> world segs -> config -> Prop),
amreal t W c P -> (forall a W' c', P a W' c' -> amreal (f a) W' c' Q) -> amreal (ibind t f) W c Q.
Proof.
induction t as [a | q s k IH | pc | e]; intros f W c P Q H Hf; cbn in *.
- eapply amreal_SRr_pre; [exact H | intros W' c' _ HP; exact (Hf a W' c' HP)].
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hd & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; split; [exact Hd|]; intros i Hi; specialize (Hc i Hi); destruct (Z.eqb (bit i) 1);
[eapply IH; [exact Hc | exact Hf] | eapply amrealE_ibind; [exact Hc | intros a W' c' HP; apply amreal_E; exact (Hf a W' c' HP)]]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact Hf].
- exact H.
- exact I.
Qed.
Lemma amrealE_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) W c
(P : A * astate -> world segs -> config -> Prop) (Q : R * astate -> world segs -> config -> Prop),
amrealE (m s) W c P -> (forall a s' W' c', P (a, s') W' c' -> amrealE (f a s') W' c' Q) -> amrealE (bind m f s) W c Q.
Proof.
intros m f s W c P Q H Hf. unfold bind. eapply amrealE_ibind; [exact H|]. intros [a s'] W' c' HP. apply Hf, HP.
Qed.
Lemma amreal_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) W c
(P : A * astate -> world segs -> config -> Prop) (Q : R * astate -> world segs -> config -> Prop),
amreal (m s) W c P -> (forall a s' W' c', P (a, s') W' c' -> amreal (f a s') W' c' Q) -> amreal (bind m f s) W c Q.
Proof.
intros m f s W c P Q H Hf. unfold bind. eapply amreal_ibind; [exact H|]. intros [a s'] W' c' HP. apply Hf, HP.
Qed.
Lemma amrealE_ret {R} : forall (r : R) (s : astate) W c (Q : R * astate -> world segs -> config -> Prop),
Q (r, s) W c -> amrealE (ret r s) W c Q.
Proof. intros r s W c Q H. cbn. apply SRrF_ret. exact H. Qed.
Lemma amreal_ret {R} : forall (r : R) (s : astate) W c (Q : R * astate -> world segs -> config -> Prop),
Q (r, s) W c -> amreal (ret r s) W c Q.
Proof. intros r s W c Q H. cbn. apply SRr_ret. exact H. Qed.
Theorem amrealE_SRrF {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amrealE t W c Q -> asafe t -> agprog t -> is_spin t = false ->
SRrF W c (fun W' c' => exists r tr, apath t tr r /\ Q r W' c').
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q H Hs Hg Hns; cbn in *.
- eapply SRrF_mono; [exact H | intros W' c' _ H'; exists r, []; split; [reflexivity | exact H']].
- destruct Hg as [Hg1 Hg2]. eapply SRrF_bind; [exact H|]. intros W1 c1 _ Hk.
assert (STEP : forall z W2 c2, aok s q z -> is_spin (k z) = false -> amrealE (k z) W2 c2 Q ->
SRrF W2 c2 (fun W' c' => exists r tr, apath (IAsk q s k) tr r /\ Q r W' c')).
{ intros z W2 c2 Hz Hz' Hm. eapply SRrF_mono; [eapply IH; [exact Hm | apply Hs; exact Hz | apply Hg2; exact Hz | exact Hz']|].
intros W' c' _ (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
destruct q; cbn in STEP;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs0 & Hb & Hr & Hz & Hc);
apply (SRrF_node_kinds W1 c1 J nx (fun i => if (sp i || is_spin (k (bit i)))%bool then KSpin else KDeadF) i0);
[ exact Hn | exact Ht | rewrite Hs0, Hb, Hg1; discriminate
| intros i Hi HIi; destruct (sp i) eqn:Es; [exact (Hz i Es HIi)|]; cbn in Hi;
specialize (Hc i Es); destruct (k (bit i)); cbn in Hi; try discriminate; exact (Hc HIi)
| intros i Hi; destruct (sp i) eqn:Es; [exfalso; apply Hi; reflexivity|]; cbn in Hi;
destruct (is_spin (k (bit i))) eqn:Ez; [exfalso; apply Hi; reflexivity|];
eapply STEP; [apply Ha | exact Ez | apply Hc, Es] ]).
destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | apply Hg1; exact Hz | exact Hc].
- discriminate.
- destruct Hs.
Qed.
Theorem amreal_SRr {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal t W c Q -> asafe t -> agprog t -> is_spin t = false ->
SRr segs W c (fun W' c' => exists r tr, apath t tr r /\ Q r W' c').
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q H Hs Hg Hns; cbn in *.
- eapply SRr_mono; [exact H | intros W' c' _ H'; exists r, []; split; [reflexivity | exact H']].
- destruct Hg as [Hg1 Hg2]. eapply SRr_bind; [exact H|]. intros W1 c1 _ Hk.
assert (STEP : forall z W2 c2, aok s q z -> is_spin (k z) = false -> amreal (k z) W2 c2 Q ->
SRr segs W2 c2 (fun W' c' => exists r tr, apath (IAsk q s k) tr r /\ Q r W' c')).
{ intros z W2 c2 Hz Hz' Hm. eapply SRr_mono; [eapply IH; [exact Hm | apply Hs; exact Hz | apply Hg2; exact Hz | exact Hz']|].
intros W' c' _ (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
assert (STEPF : forall z W2 c2, aok s q z -> is_spin (k z) = false -> amrealE (k z) W2 c2 Q ->
SRrF W2 c2 (fun W' c' => exists r tr, apath (IAsk q s k) tr r /\ Q r W' c')).
{ intros z W2 c2 Hz Hz' Hm. eapply SRrF_mono; [eapply amrealE_SRrF; [exact Hm | apply Hs; exact Hz | apply Hg2; exact Hz | exact Hz']|].
intros W' c' _ (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
destruct q; cbn in STEP, STEPF;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs0 & Hb & Hr & Hz & Hd & Hc);
apply (SRr_node_kinds W1 c1 J nx
(fun i => if (sp i || is_spin (k (bit i)))%bool then KSpin else if Z.eqb (bit i) 1 then KLive else KDeadF) i0);
[ exact Hn | exact Ht | rewrite Hs0, Hb, Hg1; reflexivity
| intros i Hi HIi; destruct (sp i) eqn:Es; [exact (Hz i Es HIi)|]; cbn in Hi;
specialize (Hc i Es); destruct (k (bit i)); cbn in Hi; destruct (Z.eqb (bit i) 1); try discriminate; exact (Hc HIi)
| intros i Hi; destruct (sp i) eqn:Es; [discriminate Hi|]; cbn in Hi;
destruct (is_spin (k (bit i))) eqn:Ez; [discriminate Hi|]; specialize (Hc i Es);
destruct (Z.eqb (bit i) 1); [discriminate Hi|]; eapply STEPF; [apply Ha | exact Ez | exact Hc]
| intros i Hi; apply Hd; destruct (sp i) eqn:Es; [left; reflexivity | right]; cbn in Hi;
destruct (Z.eqb (bit i) 1) eqn:Eb; [| apply Z.eqb_neq in Eb; exact Eb];
apply Z.eqb_eq in Eb; rewrite Eb, Hg1 in Hi; exfalso; apply Hi; reflexivity
| intros i Hi; destruct (sp i) eqn:Es; [discriminate Hi|]; cbn in Hi;
destruct (is_spin (k (bit i))) eqn:Ez; [discriminate Hi|]; specialize (Hc i Es);
destruct (Z.eqb (bit i) 1); [| discriminate Hi]; eapply STEP; [apply Ha | exact Ez | exact Hc] ]).
destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | apply Hg1; exact Hz | exact Hc].
- discriminate.
- destruct Hs.
Qed.
End h.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.
Definition cfg_at (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
mkCfg (mkst regs (w64 pc) mem (seg_rom segs)) md.
Definition ascratch (stk : Z) (regs : bvmap 5 word) (a : Z) : Prop :=
(spZ regs - stk <= a < spZ regs) \/ (as_errno B <= a < as_errno B + 4).
Definition frame0_ok (ly : alayout) (regs : bvmap 5 word) : bool := spZ regs + 16 <? ly_top ly.
Definition chain_pre (ly : alayout) (rd : reader) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : Prop :=
4096 <= raZ regs /\
(if frame0_ok ly regs then
(if bad_next (spZ regs) (ly_top ly) (s0Z regs) then ch = []
else spZ regs + 16 <= s0Z regs /\ fpchain (rdword rd) (s0Z regs) (ly_top ly) ch)
else ch = []).
Definition call_trace (ly : alayout) (pc0 : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list Z :=
if frame0_ok ly regs then unwind_of_chain pc0 ((spZ regs, raZ regs, s0Z regs) :: ch) else [pc0].
Definition acall_pre (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
AR segs B ly S W mem md /\ aregime S   /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ASTACK <= spZ regs /\ ly_bot ly < spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
chain_pre ly (aview segs (w_H W) mem) regs ch /\
qtight S.
Definition acall_post (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
AR segs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\
aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch stk regs a -> ~ E a ->
aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).
Definition malloc_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
acall_post ASTACK ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
qtight (snd r)                                    .
Definition amalloc_realizes : Prop :=
forall ly S W regs mem md n ch,
acall_pre ly S W regs mem md ch ->
getr regs 10 = w64 n -> 0 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
In (call_trace ly (pc_malloc_ra0 code) regs ch) (as_universe B) ->
amreal segs (malloc n (call_trace ly (pc_malloc_ra0 code) regs ch) S) W
(cfg_at (pc_wrap_malloc code) regs mem md)
(malloc_leaf ly S W regs mem md n).
Definition free_leaf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
(r : unit * astate) (W' : world segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
acall_post ASTACK ly S W regs mem md
(fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' (snd r) W' regs' mem' md' /\
qtight (snd r)                                    .
Definition afree_realizes : Prop :=
forall ly S W regs mem md p n ch,
acall_pre ly S W regs mem md ch ->
(p = PNull \/ In (p, n) (blocks S)) -> getr regs 10 = w64 (sptr_addr B ly p) ->
In (call_trace ly (pc_free_ra0 code) regs ch) (as_universe B) ->
amreal segs (free p (call_trace ly (pc_free_ra0 code) regs ch) S) W
(cfg_at (pc_wrap_free code) regs mem md)
(free_leaf ly S W regs mem md p n).
Definition ecall_pre (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR segs B ly S W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Definition astack_malloc_realizes (cid : Z) : Prop :=
forall ly S W regs mem md pos S',
ecall_pre ly S W regs mem md ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at (pc_stack_malloc code cid) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Definition astack_free_law : Prop :=
forall ly S W mem md mem' md' cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
AR segs B ly (stack_free_state cid pos S) W mem' md'.
Definition shadow_hull_vis (rd : reader) (x n : Z) : Prop :=
forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s <> None.
Definition dest_ok (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (d n : Z) : Prop :=
forall a, d <= a < d + n -> writable_at segs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - ESTACK <= a < spZ regs).
Definition src_ok (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (s n : Z) : Prop :=
forall a, s <= a < s + n -> aview segs (w_H W) mem a <> None /\ ~ (spZ regs - ESTACK <= a < spZ regs).
Inductive memop := OCpy | OSet.
Definition amem_range (p n : Z) : Prop := p + n <= kLowMemEnd - 1 \/ (kHighMemBeg <= p /\ p + n <= kHighMemEnd - 1).
Definition aintrin_realizes (op : memop) (pc : Z) : Prop :=
forall ly S W regs mem md d x n,
ecall_pre ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition amemcmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y n,
ecall_pre ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok W regs mem x n -> src_ok W regs mem y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition abcmp_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x y n,
ecall_pre ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok W regs mem x n -> src_ok W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition first_byte (W : world segs) (mem : word -> option byte) (x n c k : Z) : Prop :=
0 <= k <= n /\
(forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\ b <> c) /\
(k < n -> aview segs (w_H W) mem (x + k) = Some c).
Definition rom_clean (mem : word -> option byte) : Prop :=
forall x : word, (exists sg, In sg segs /\ seg_writable sg = false /\
Z.of_N (seg_base sg) <= bv_unsigned x < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) -> mem x = None.
Definition in_rom (a : Z) : Prop :=
exists sg, In sg segs /\ seg_writable sg = false /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Definition rom_view (W : world segs) (mem : word -> option byte) : Prop :=
forall a, in_rom a -> aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition amemchr0_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte W mem x n 0 k ->
src_ok W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view W mem ->
SRr segs W (cfg_at pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition astrnlen_realizes (pc : Z) : Prop :=
forall ly S W regs mem md x n k,
ecall_pre ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte W mem x n 0 k ->
src_ok W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view W mem ->
SRr segs W (cfg_at pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition ablocks (ly : alayout) (S : astate) : list (Z * Z) :=
map (fun b => (sptr_addr B ly (fst b), snd b)) (blocks S).
Definition AR_blocks_law : Prop :=
forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks ly S)) /\
0 <= n < MALLOC_MAX.
Definition AR_shadow_law : Prop :=
forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks ly S) ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF p (req_size n) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
Definition AR_zshadow_law : Prop :=
forall ly S W mem md r,
AR segs B ly S W mem md -> In r (zero_shadow_ranges B ly) ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Definition AR_frame_law : Prop :=
forall ly S W mem md mem' md',
AR segs B ly S W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
AR segs B ly S W mem' md'.
Definition AR_frames_law : Prop :=
forall ly S W mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i) /\
~ aowned B ly S (shadow_addr (frame_addr ly cid pos) + i)).
Definition AR_flag_law : Prop :=
forall ly S (W : world segs) mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.
Definition AR_const_law : Prop :=
forall ly S W mem md,
AR segs B ly S W mem md ->
rdword (aview segs (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
rd32 (aview segs (w_H W) mem) (as_uar_cell B) 1 /\
rdword (aview segs (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
rdword (aview segs (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B).
Definition AR_stack_law : Prop :=
forall ly S W mem md a,
AR segs B ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Definition in_img (a : Z) : Prop := exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Definition AR_owned_low_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md -> aowned B ly S a -> 0 <= a < alloc_ceiling.
Definition AR_owned_image_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md -> in_img a -> (aowned B ly S a <-> Exists (in_zr a) (as_owned_static B)).
Definition AR_sep_law : Prop :=
forall ly S W mem md, AR segs B ly S W mem md ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks ly S)
++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)) /\
Forall (fun f => 4096 <= frame_addr ly (fst f) (snd f) /\ frame_addr ly (fst f) (snd f) + fs_frame_bytes (fst f) <= alloc_ceiling) (frames S).
Definition AR_layout_law : Prop :=
forall ly S W mem md ly',
AR segs B ly S W mem md -> layout_le (length (st_secs S)) ly ly' ->
ablocks ly' S = ablocks ly S /\ (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) /\
(forall a, aowned B ly' S a <-> aowned B ly S a).
Definition AR_wle_law : Prop :=
forall ly S W W' mem md,
AR segs B ly S W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) ->
A_bytes (w_A W') <= abudget S -> AR segs B ly S W' mem md.
Definition AR_client_img_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md ->
((exists p n, In (p, n) (ablocks ly S) /\ p <= a < p + req_size n) \/
(exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
(exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)) ->
~ in_zr a (ly_img ly) /\ ~ in_img a.
Record AR_laws : Prop := {
al_blocks : AR_blocks_law;
al_shadow : AR_shadow_law;
al_zshadow : AR_zshadow_law;
al_frame : AR_frame_law;
al_frames : AR_frames_law;
al_flag : AR_flag_law;
al_const : AR_const_law;
al_stack : AR_stack_law;
al_wle : AR_wle_law;
al_layout : AR_layout_law;
al_owned_low : AR_owned_low_law;
al_owned_image : AR_owned_image_law;
al_sep : AR_sep_law;
al_client_img : AR_client_img_law
}.
End j.
End g.
Record model_laws (U : list (list Z)) : Prop := {
ml_malloc : forall s n tr, Wf U s -> st_nev s < EV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr s) (malloc_post U s n);
ml_free : forall s p n tr, Wf U s -> st_nev s < EV_MAX -> (p = PNull \/ In (p, n) (blocks s)) -> In tr U ->
atok true (free p tr s) (free_post U s p n);
ml_stack_malloc : forall s cid, Wf U s -> 0 <= cid <= 10 -> atok true (stack_malloc cid s) (stack_malloc_post U s cid);
ml_stack_malloc_progress : forall s cid, Wf U s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s');
ml_stack_free : forall s cid pos, Wf U s -> In (cid, pos) (frames s) -> stack_free_post U s cid pos;
ml_malloc_big : forall s n tr, Wf U s -> regime_big s -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In tr U ->
atok true (malloc n tr s) (fun ns r => malloc_post U s n ns r /\ BigInv (snd r) /\ mgrow s n (snd r));
ml_free_big : forall s p n tr, Wf U s -> regime_big s -> (p = PNull \/ In (p, n) (blocks s)) -> In tr U ->
atok true (free p tr s) (fun ns r => free_post U s p n ns r /\ BigInv (snd r) /\ fgrow s (snd r))
}.
Section l. Context {rc : YN05.RunCeil}.
Record AsanAPI (segs : list Segment) (B : asyms) := {
aa_laws : forall {fx : YK11.FPState}, AR_laws segs B;
aa_model : model_laws (as_universe B);
aa_malloc : forall {fx : YK11.FPState}, amalloc_realizes segs B;
aa_free : forall {fx : YK11.FPState}, afree_realizes segs B;
aa_stack_malloc : forall {fx : YK11.FPState} cid, cid = 1 \/ cid = 2 -> astack_malloc_realizes segs B cid;
aa_stack_free : forall {fx : YK11.FPState}, astack_free_law segs B;
aa_asan_memcpy : forall {fx : YK11.FPState}, aintrin_realizes segs B OCpy (pc_asan_memcpy (as_code B));
aa_asan_memset : forall {fx : YK11.FPState}, aintrin_realizes segs B OSet (pc_asan_memset (as_code B));
aa_memcpy_icpt : forall {fx : YK11.FPState}, aintrin_realizes segs B OCpy (pc_wrap_memcpy (as_code B));
aa_memset_icpt : forall {fx : YK11.FPState}, aintrin_realizes segs B OSet (pc_wrap_memset (as_code B));
aa_memcmp : forall {fx : YK11.FPState}, amemcmp_realizes segs B (pc_wrap_memcmp (as_code B));
aa_bcmp : forall {fx : YK11.FPState}, abcmp_realizes segs B (pc_wrap_bcmp (as_code B));
aa_memchr : forall {fx : YK11.FPState}, amemchr0_realizes segs B (pc_wrap_memchr (as_code B));
aa_strnlen : forall {fx : YK11.FPState}, astrnlen_realizes segs B (pc_wrap_strnlen (as_code B))
}.
End l.
Arguments aa_laws {rc segs B} _ {fx}. Arguments aa_model {rc segs B}. Arguments aa_malloc {rc segs B} _ {fx}.
Arguments aa_free {rc segs B} _ {fx}. Arguments aa_stack_malloc {rc segs B} _ {fx}. Arguments aa_stack_free {rc segs B} _ {fx}.
Arguments aa_asan_memcpy {rc segs B} _ {fx}. Arguments aa_asan_memset {rc segs B} _ {fx}.
Arguments aa_memcpy_icpt {rc segs B} _ {fx}. Arguments aa_memset_icpt {rc segs B} _ {fx}.
Arguments aa_memcmp {rc segs B} _ {fx}. Arguments aa_bcmp {rc segs B} _ {fx}.
Arguments aa_memchr {rc segs B} _ {fx}. Arguments aa_strnlen {rc segs B} _ {fx}.
