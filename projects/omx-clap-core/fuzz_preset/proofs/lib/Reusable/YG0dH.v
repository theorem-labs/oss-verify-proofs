(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YG0d.v, with its module paths changed; 100 of its 189 lines of code are new or changed and 460 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YG0dH.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* amreal over a general world relation (F1, group M). YG0d.amreal realizes an allocator itree through SRr, whose
   continuation sees only wle worlds. amrealG is amreal with SRr replaced by YA0nH.SRrG segs Rel, for any preorder
   Rel; its lemmas are YG0d.v:92-167's and :189-211's (amreal_mono, amreal_SRr_pre, amreal_world_le, amreal_ibind,
   amreal_mbind, amreal_ret, amreal_SRr, amreal_SRr04) with the same proofs over SRrG. amreal_amrealG lifts every
   amreal fact to amrealG for a Rel that contains wle. amreal' is the F1 instance (Rel = wle', the hidden set may grow
   only inside the zone RZ), with the lift amreal_amreal' and the instance lemmas. Additive: no existing text changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable segs : list Segment.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).

Variable Rel : world segs -> world segs -> Prop.
Hypothesis Rel_refl : forall W, Rel W W.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.

(* YG0d.v:72, with SRrG segs Rel in place of SRr. *)
Fixpoint amrealG {R : Type} (t : itree astate R) : world segs -> config -> (R -> world segs -> config -> Prop) -> Prop :=
fun W c Q =>
match t with
| IRet r => SRrG segs Rel W c (Q r)
| IFail _ => True
| ISpin _ => AIw W (cfg_model c) -> srealizes segs c t_nil
| IAsk q snap k =>
SRrG segs Rel W c (fun W1 c1 =>
match q with
| KDepot _ => exists z, aok snap q z /\ amrealG (k z) W1 c1 Q
| _ => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok segs c1 I (fun _ => []) nx /\
(forall i, AIw W1 (cfg_model c1) -> AIw W1 (cfg_model (nx i))) /\
(forall i, aok snap q (bit i)) /\
sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AIw W1 (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) /\
(forall i, sp i = false -> amrealG (k (bit i)) W1 (nx i) Q)
end)
end.

Lemma amrealG_mono {R} : forall (t : itree astate R) W c (Q Q' : R -> world segs -> config -> Prop),
(forall r W' c', Q r W' c' -> Q' r W' c') -> amrealG t W c Q -> amrealG t W c Q'.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q Q' HQ H; cbn in *.
- eapply SRrG_mono; [exact H | intros W' c' _ H'; apply HQ, H'].
- eapply SRrG_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [exact HQ | apply Hc, Hi]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact HQ | exact Hc].
- exact H.
- exact I.
Qed.

Lemma amrealG_SRrG_pre {R} : forall (t : itree astate R) W c Q (P : world segs -> config -> Prop),
SRrG segs Rel W c P -> (forall W' c', Rel W W' -> P W' c' -> amrealG t W' c' Q) -> amrealG t W c Q.
Proof.
intros t W c Q P HP H. destruct t as [r | q s k | pc | f]; cbn in *.
- eapply (SRrG_bind segs Rel Rel_trans); [exact HP | exact H].
- eapply (SRrG_bind segs Rel Rel_trans); [exact HP | exact H].
- apply (SRrG_tnil segs Rel W c P HP). intros W' c' Hle HP' HI'. exact (H W' c' Hle HP' HI').
- exact I.
Qed.

Lemma amrealG_world_le {R} : forall (t : itree astate R) W W' c Q,
Rel W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> amrealG t W' c Q -> amrealG t W c Q.
Proof.
intros t W W' c Q Hle Htr H. destruct t as [r | q s k | pc | f]; cbn in *.
- eapply (SRrG_world_le segs Rel Rel_trans); eassumption.
- eapply (SRrG_world_le segs Rel Rel_trans); eassumption.
- intros HI. exact (H (Htr HI)).
- exact I.
Qed.

Lemma amrealG_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c
(P : A -> world segs -> config -> Prop) (Q : R -> world segs -> config -> Prop),
amrealG t W c P -> (forall a W' c', P a W' c' -> amrealG (f a) W' c' Q) -> amrealG (ibind t f) W c Q.
Proof.
induction t as [a | q s k IH | pc | e]; intros f W c P Q H Hf; cbn in *.
- eapply amrealG_SRrG_pre; [exact H | intros W' c' _ HP; exact (Hf a W' c' HP)].
- eapply SRrG_mono; [exact H|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; eapply IH; [apply Hc, Hi | exact Hf]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact Hf].
- exact H.
- exact I.
Qed.

Lemma amrealG_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) W c
(P : A * astate -> world segs -> config -> Prop) (Q : R * astate -> world segs -> config -> Prop),
amrealG (m s) W c P -> (forall a s' W' c', P (a, s') W' c' -> amrealG (f a s') W' c' Q) -> amrealG (bind m f s) W c Q.
Proof.
intros m f s W c P Q H Hf. unfold bind. eapply amrealG_ibind; [exact H|]. intros [a s'] W' c' HP. apply Hf, HP.
Qed.

Lemma amrealG_ret {R} : forall (r : R) (s : astate) W c (Q : R * astate -> world segs -> config -> Prop),
Q (r, s) W c -> amrealG (ret r s) W c Q.
Proof. intros r s W c Q H. cbn. apply (SRrG_ret segs Rel Rel_refl). exact H. Qed.

(* YG0d.v:146 amreal_SRr. *)
Theorem amrealG_SRrG {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amrealG t W c Q -> asafe t -> agprog t -> is_spin t = false ->
SRrG segs Rel W c (fun W' c' => exists r tr, apath t tr r /\ Q r W' c').
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q H Hs Hg Hns; cbn in *.
- eapply SRrG_mono; [exact H | intros W' c' _ H'; exists r, []; split; [reflexivity | exact H']].
- destruct Hg as [Hg1 Hg2]. eapply (SRrG_bind segs Rel Rel_trans); [exact H|]. intros W1 c1 _ Hk.
assert (STEP : forall z W2 c2, aok s q z -> is_spin (k z) = false -> amrealG (k z) W2 c2 Q ->
SRrG segs Rel W2 c2 (fun W' c' => exists r tr, apath (IAsk q s k) tr r /\ Q r W' c')).
{ intros z W2 c2 Hz Hz' Hm. eapply SRrG_mono; [eapply IH; [exact Hm | apply Hs; exact Hz | apply Hg2; exact Hz | exact Hz']|].
intros W' c' _ (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
destruct q; cbn in STEP;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs0 & Hb & Hr & Hz & Hc);
apply (SRrG_node_tnil segs Rel W1 c1 J nx (fun i => sp i || is_spin (k (bit i)))%bool i0);
[ exact Hn | exact Ht | rewrite Hs0, Hb, Hg1; reflexivity
| intros i Hi HIi; destruct (sp i) eqn:Es; [exact (Hz i Es HIi)|]; cbn in Hi;
specialize (Hc i Es); destruct (k (bit i)); cbn in Hi; try discriminate; exact (Hc HIi)
| intros i Hi; apply Bool.orb_false_elim in Hi as [Hi1 Hi2]; eapply STEP; [apply Ha | exact Hi2 | apply Hc, Hi1] ]).
destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | apply Hg1; exact Hz | exact Hc].
- discriminate.
- destruct Hs.
Qed.

(* YG0d.v:189 amreal_SRr04 (the gflag form). *)
Theorem amrealG_SRrG04 {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amrealG t W c Q -> asafe t -> agprog t -> is_spin t = false ->
SRrG segs Rel W c (fun W' c' => exists r tr, apath t tr r /\ gflag tr = true /\ Q r W' c').
Proof.
induction t as [r | q s k IH | pc | f]; intros W c Q H Hs Hg Hns; cbn in *.
- eapply SRrG_mono; [exact H | intros W' c' _ H'; exists r, []; split; [reflexivity | split; [reflexivity | exact H']]].
- destruct Hg as [Hg1 Hg2]. eapply (SRrG_bind segs Rel Rel_trans); [exact H|]. intros W1 c1 _ Hk.
assert (STEP : forall z W2 c2, aok s q z -> progz q z = true -> is_spin (k z) = false -> amrealG (k z) W2 c2 Q ->
SRrG segs Rel W2 c2 (fun W' c' => exists r tr, apath (IAsk q s k) tr r /\ gflag tr = true /\ Q r W' c')).
{ intros z W2 c2 Hz Hpz Hz' Hm. eapply SRrG_mono; [eapply IH; [exact Hm | apply Hs; exact Hz | apply Hg2; exact Hz | exact Hz']|].
intros W' c' _ (r & tr & Hy & Hf & HQ). exists r, ((q, z) :: tr). cbn. rewrite Hpz, Hf. auto. }
destruct q; cbn in STEP;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs0 & Hb & Hr & Hz & Hc);
apply (SRrG_node_tnil segs Rel W1 c1 J nx (fun i => sp i || is_spin (k (bit i)))%bool i0);
[ exact Hn | exact Ht | rewrite Hs0, Hb, Hg1; reflexivity
| intros i Hi HIi; destruct (sp i) eqn:Es; [exact (Hz i Es HIi)|]; cbn in Hi;
specialize (Hc i Es); destruct (k (bit i)); cbn in Hi; try discriminate; exact (Hc HIi)
| intros i Hi; apply Bool.orb_false_elim in Hi as [Hi1 Hi2]; eapply STEP;
[apply Ha | first [reflexivity | rewrite (Hr i Hi1); reflexivity] | exact Hi2 | apply Hc, Hi1] ]).
destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | reflexivity | apply Hg1; exact Hz | exact Hc].
- discriminate.
- destruct Hs.
Qed.

(* The lift: every amreal fact is an amrealG fact, for any relation containing wle. *)
Lemma amreal_amrealG {R} : (forall W W', wle W W' -> Rel W W') ->
forall (t : itree astate R) W c Q, amreal segs t W c Q -> amrealG t W c Q.
Proof.
intros Hsub t. induction t as [r | q s k IH | pc | f]; intros W c Q H; cbn in *.
- exact (SRr_SRrG segs Rel Hsub W c (Q r) H).
- eapply SRrG_mono; [exact (SRr_SRrG segs Rel Hsub _ _ _ H)|]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; apply IH, Hc, Hi).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH, Hc.
- exact H.
- exact I.
Qed.
End h.

(* ---------------------------------------------------------------------------- *)
(* The F1 instance: Rel = wle' (the hidden set may grow only inside a fixed zone RZ). *)
Section f.
Variable segs : list Segment.
Variable RZ : Z -> Prop.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).

Definition amreal' {R : Type} (t : itree astate R) : world segs -> config -> (R -> world segs -> config -> Prop) -> Prop :=
amrealG segs (wle' segs RZ) t.

Lemma amreal_amreal' {R} : forall (t : itree astate R) W c Q, amreal segs t W c Q -> amreal' t W c Q.
Proof. exact (amreal_amrealG segs (wle' segs RZ) (wle_wle' segs RZ)). Qed.

Lemma amreal'_mono {R} : forall (t : itree astate R) W c (Q Q' : R -> world segs -> config -> Prop),
(forall r W' c', Q r W' c' -> Q' r W' c') -> amreal' t W c Q -> amreal' t W c Q'.
Proof. exact (amrealG_mono segs (wle' segs RZ)). Qed.

Lemma amreal'_SRr_pre {R} : forall (t : itree astate R) W c Q (P : world segs -> config -> Prop),
SRr' segs RZ W c P -> (forall W' c', wle' segs RZ W W' -> P W' c' -> amreal' t W' c' Q) -> amreal' t W c Q.
Proof. exact (amrealG_SRrG_pre segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_world_le {R} : forall (t : itree astate R) W W' c Q,
wle' segs RZ W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> amreal' t W' c Q -> amreal' t W c Q.
Proof. exact (amrealG_world_le segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c
(P : A -> world segs -> config -> Prop) (Q : R -> world segs -> config -> Prop),
amreal' t W c P -> (forall a W' c', P a W' c' -> amreal' (f a) W' c' Q) -> amreal' (ibind t f) W c Q.
Proof. exact (amrealG_ibind segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) W c
(P : A * astate -> world segs -> config -> Prop) (Q : R * astate -> world segs -> config -> Prop),
amreal' (m s) W c P -> (forall a s' W' c', P (a, s') W' c' -> amreal' (f a s') W' c' Q) -> amreal' (bind m f s) W c Q.
Proof. exact (amrealG_mbind segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_ret {R} : forall (r : R) (s : astate) W c (Q : R * astate -> world segs -> config -> Prop),
Q (r, s) W c -> amreal' (ret r s) W c Q.
Proof. exact (amrealG_ret segs (wle' segs RZ) (wle'_refl segs RZ)). Qed.

Theorem amreal'_SRr' {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal' t W c Q -> asafe t -> agprog t -> is_spin t = false ->
SRr' segs RZ W c (fun W' c' => exists r tr, apath t tr r /\ Q r W' c').
Proof. exact (amrealG_SRrG segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Theorem amreal'_SRr'04 {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal' t W c Q -> asafe t -> agprog t -> is_spin t = false ->
SRr' segs RZ W c (fun W' c' => exists r tr, apath t tr r /\ gflag tr = true /\ Q r W' c').
Proof. exact (amrealG_SRrG04 segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.
End f.
End g.
