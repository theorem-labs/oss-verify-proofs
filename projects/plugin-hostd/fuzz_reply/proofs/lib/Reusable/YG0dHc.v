(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YG0dHc.v, with its module paths changed; 6 of its 234 lines of code are new or changed. *)
(* CARRIED from commit 65bdc7eaf4ea59c40acad896e39a3abc5c53dc95,
   proofs/cgif/cgif_file_fuzzer/lib/YG0dHc.v, sha256 a2cc2922316155f817779e0963e7b6c5e532d6b2270e2da6be951590781db9d9 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
(* The amreal combinators over a general world relation (F1, group M2). YG0dH.amrealG is YG0d.amreal over
   YA0nH.SRrG segs Rel. This file gives the generic twins of the amreal combinators that the free / drain / recycle /
   quarantine-enqueue walks use: YFfk.amreal_ibind_ext, amreal_ibind_assoc, amreal_bind_assoc, amreal_bind_assoc',
   amreal_apost, amreal_apostg; AGif0n.amreal_apath_gflag; YFeu.amreal_then_SRr (there at tfibsegs, here at any segs);
   YFfj.amreal_after_SRr, amreal_bind, amreal_mbind (named amrealG_bindK / amrealG_mbindK: the continuation forms,
   apart from YG0dH's amrealG_ibind / amrealG_mbind); YFi3.amreal_atok (YFes's recycle walk uses it);
   YFfy.amreal_ask_depot (there at tfibsegs; DGfy.amreal_ask_depot and DGg1.amreal_ask_depot_e state the same);
   DGg1.amreal_pure_e (there at tfibsegs). Each has the original's proof over SRrG, then its instance at
   Rel = wle' (YG0dH.amreal'). RGtop's local rg_amreal_apostg / rg_apath_gflag / rg_then_SRr state the same as
   amrealG_apostg / amrealG_apath_gflag / amrealG_then_SRrG. Walk theorems whose own statement has an amreal
   continuation premise (for example FGtN.tfib_efa_spec_lk) are not combinators and are not here; their amreal'
   restatements belong with their walk. Additive: no existing text changes. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK18 YK0j YP09 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0dH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Section h.
Variable segs : list Segment.
Variable Rel : world segs -> world segs -> Prop.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.

(* YFfk.v:18 *)
Lemma amrealG_ibind_ext {A R} : forall (t : itree astate A) (f g : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
(forall a W1 c1, amrealG segs Rel (f a) W1 c1 Q -> amrealG segs Rel (g a) W1 c1 Q) ->
amrealG segs Rel (ibind t f) W c Q -> amrealG segs Rel (ibind t g) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q Hfg H; cbn [ibind amrealG] in *.
- exact (Hfg a W c H).
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact Hfg | exact (H8 i Hi)]).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact Hfg | exact HR].
- exact H.
- exact I.
Qed.

(* YFfk.v:33 *)
Lemma amrealG_ibind_assoc {A B R} : forall (t : itree astate A) (f : A -> itree astate B) (g : B -> itree astate R) W c
(Q : R -> world segs -> config -> Prop),
amrealG segs Rel (ibind (ibind t f) g) W c Q <-> amrealG segs Rel (ibind t (fun a => ibind (f a) g)) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f g W c Q; cbn [ibind amrealG]; [tauto | | tauto | tauto].
split; intros H.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; apply (proj1 (IH _ f g _ _ Q)); exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. apply (proj1 (IH _ f g _ _ Q)). exact HR.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; apply (proj2 (IH _ f g _ _ Q)); exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. apply (proj2 (IH _ f g _ _ Q)). exact HR.
Qed.

(* YFfk.v:48 *)
Lemma amrealG_bind_assoc {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amrealG segs Rel (bind (bind m1 m2) m3 s) W c Q -> amrealG segs Rel (bind m1 (fun a => bind (m2 a) m3) s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
apply (proj1 (amrealG_ibind_assoc _ _ _ _ _ _)) in H.
eapply amrealG_ibind_ext; [|exact H]. intros [a s'] W1 c1 Ha. exact Ha.
Qed.

(* YFfk.v:56 *)
Lemma amrealG_bind_assoc' {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amrealG segs Rel (bind m1 (fun a => bind (m2 a) m3) s) W c Q -> amrealG segs Rel (bind (bind m1 m2) m3 s) W c Q.
Proof.
intros m1 m2 m3 s W c Q H. unfold bind in H |- *.
apply (proj2 (amrealG_ibind_assoc _ _ _ _ _ _)).
eapply amrealG_ibind_ext; [|exact H]. intros [a s'] W1 c1 Ha. exact Ha.
Qed.

(* YFfk.v:62 *)
Lemma amrealG_apost {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
apost t P -> amrealG segs Rel t W c Q -> amrealG segs Rel t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amrealG] in *.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. split; [|exact HQ]. apply (HP []). reflexivity.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ.
assert (HPk : forall z, aok snap q z -> apost (k z) P).
{ intros z Hz tr a Hp. apply (HP ((q, z) :: tr)). cbn. split; [reflexivity|]. split; [exact Hz | exact Hp]. }
destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (HPk _ (H3 i)) | exact (H8 i Hi)]).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact (HPk _ Hz) | exact HR].
- exact H.
- exact I.
Qed.

(* YFfk.v:77 *)
Lemma amrealG_apostg {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
(forall tr r, apath t tr r -> gflag tr = true -> P r) -> amrealG segs Rel t W c Q ->
amrealG segs Rel t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros P W c Q HP H; cbn [amrealG] in *.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. split; [|exact HQ]. apply (HP []); reflexivity.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ.
assert (HPk : forall z, aok snap q z -> progz q z = true -> forall tr a, apath (k z) tr a -> gflag tr = true -> P a).
{ intros z Hz Hpz tr a Hp Hg. apply (HP ((q, z) :: tr)); cbn; [split; [reflexivity|]; split; [exact Hz | exact Hp] | rewrite Hpz, Hg; reflexivity]. }
destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (HPk _ (H3 i) ltac:(rewrite (H6 i Hi); reflexivity)) | exact (H8 i Hi)]).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact (HPk _ Hz eq_refl) | exact HR].
- exact H.
- exact I.
Qed.

(* AGif0n.v:402 *)
Lemma amrealG_apath_gflag {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amrealG segs Rel t W c Q ->
amrealG segs Rel t W c (fun r W' c' => Q r W' c' /\ exists trc, apath t trc r /\ gflag trc = true).
Proof.
induction t as [r | q snap k IH | pc | f]; intros W c Q H; cbn [amrealG] in *.
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. split; [exact HQ|]. exists []. split; reflexivity.
- eapply SRrG_mono; [exact H|]. intros W1 c1 _ Hk.
  assert (STEP : forall z, aok snap q z -> progz q z = true -> forall W2 c2, amrealG segs Rel (k z) W2 c2 Q ->
    amrealG segs Rel (k z) W2 c2 (fun r W' c' => Q r W' c' /\ exists trc, apath (IAsk q snap k) trc r /\ gflag trc = true)).
  { intros z Hz Hp W2 c2 Hc. eapply amrealG_mono; [| exact (IH z W2 c2 Q Hc)].
    intros r W' c' [HQ (trc & HP & HG)]. split; [exact HQ|]. exists ((q, z) :: trc). split.
    - cbn [apath]. split; [reflexivity | split; [exact Hz | exact HP]].
    - cbn [gflag]. rewrite Hp, HG. reflexivity. }
  clear IH. destruct q;
  try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
  split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
  split; [exact Hz|]; intros i Hi; apply STEP; [exact (Ha i) | rewrite (Hr i Hi); reflexivity | exact (Hc i Hi)]).
  destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply STEP; [exact Hz | reflexivity | exact Hc].
- exact H.
- exact I.
Qed.

(* YFeu.v:20 (stated there at tfibsegs) *)
Lemma amrealG_then_SRrG {R} : forall (t : itree astate R) W c (P Q : R -> world segs -> config -> Prop),
amrealG segs Rel t W c P -> (forall r W' c', P r W' c' -> SRrG segs Rel W' c' (Q r)) -> amrealG segs Rel t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HPQ; cbn [amrealG] in *.
- eapply (SRrG_bind segs Rel Rel_trans); [exact H|]. intros W' c' _ HP. exact (HPQ r W' c' HP).
- eapply SRrG_mono; [exact H|]. intros W1 c1 _ Hk. destruct q; cbn beta iota in *;
try (destruct Hk as (J & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists J, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (H8 i Hi) | exact HPQ]).
destruct Hk as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact HR | exact HPQ].
- exact H.
- exact I.
Qed.

(* YFfj.v:18 *)
Lemma amrealG_after_SRrG {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
SRrG segs Rel W c (fun W1 c1 => amrealG segs Rel t W1 c1 Q) -> amrealG segs Rel t W c Q.
Proof.
intros t W c Q H. destruct t as [r | q snap k | pc | f]; cbn [amrealG] in *.
- eapply (SRrG_bind segs Rel Rel_trans); [exact H|]. intros W' c' _ HQ. exact HQ.
- eapply (SRrG_bind segs Rel Rel_trans); [exact H|]. intros W' c' _ HQ. exact HQ.
- intros HI. apply (H HI t_nil). intros W' c' _ HI' HQ. exact (HQ HI').
- exact I.
Qed.

(* YFfj.v:27 amreal_bind (the continuation form of ibind). *)
Lemma amrealG_bindK {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
amrealG segs Rel t W c (fun a W1 c1 => amrealG segs Rel (f a) W1 c1 Q) -> amrealG segs Rel (ibind t f) W c Q.
Proof.
intros t. induction t as [a | q snap k IH | pc | fl]; intros f W c Q H; cbn [ibind amrealG] in *.
- exact (amrealG_after_SRrG _ _ _ _ H).
- eapply SRrG_mono; [exact H|]. intros W' c' _ HQ. destruct q; cbn beta iota in *;
try (destruct HQ as (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; apply IH; exact (H8 i Hi)).
destruct HQ as (z & Hz & HR). exists z. split; [exact Hz|]. apply IH. exact HR.
- exact H.
- exact I.
Qed.

(* YFfj.v:39 amreal_mbind (the continuation form of bind). *)
Lemma amrealG_mbindK {A R} : forall (m : M A) (g : A -> M R) s W c (Q : R * astate -> world segs -> config -> Prop),
amrealG segs Rel (m s) W c (fun r W1 c1 => amrealG segs Rel (g (fst r) (snd r)) W1 c1 Q) ->
amrealG segs Rel (bind m g s) W c Q.
Proof.
intros m g s W c Q H. unfold bind. apply amrealG_bindK. eapply amrealG_mono; [|exact H]. intros [a s'] W' c' HR. exact HR.
Qed.

(* YFi3.v:131 amreal_atok (there at tfibsegs). *)
Lemma amrealG_atok {R} : forall (t : itree astate R) ns (P : bool -> R -> Prop) W c (Q : R -> world segs -> config -> Prop),
atok ns t P -> amrealG segs Rel t W c (fun r W' c' => (exists ns', P ns' r) -> Q r W' c') -> amrealG segs Rel t W c Q.
Proof.
induction t as [r | q snap k IH | pc | f]; intros ns P W c Q AT AM; cbn in *.
- eapply SRrG_mono; [exact AM|]. intros W' c' _ H. apply H. exists ns. exact AT.
- destruct AT as [_ Hk]. eapply SRrG_mono; [exact AM|]. intros W1 c1 _ H. cbv beta in H.
destruct q;
try (destruct H as (z & Hz & H); exists z; split; [exact Hz|]; eapply IH; [exact (Hk z Hz) | exact H]);
(destruct H as (I & nx & bit & sp & i0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8); exists I, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [apply Hk; apply N3 | exact (N8 i Hi)]).
- exact AM.
- exact AM.
Qed.

(* YFfy.v:32 amreal_ask_depot (there at tfibsegs). *)
Lemma amrealG_ask_depot {R} : forall trc s (k : Z -> itree astate R) Wx c Q,
SRrG segs Rel Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amrealG segs Rel (k z) W1 c1 Q) ->
amrealG segs Rel (IAsk (KDepot trc) s k) Wx c Q.
Proof. intros trc s k Wx c Q H. exact H. Qed.

(* DGg1.v:596 amreal_pure_e (there at tfibsegs). *)
Lemma amrealG_pure {A R} : forall (m : M A) (f : A -> M R) s a s' W c Q,
m s = IRet (a, s') -> amrealG segs Rel (f a s') W c Q -> amrealG segs Rel (bind m f s) W c Q.
Proof. intros m f s a s' W c Q E H. unfold bind. rewrite E. cbn [ibind]. exact H. Qed.
End h.

(* ---------------------------------------------------------------------------- *)
(* The F1 instance: Rel = wle'. *)
Section f.
Variable segs : list Segment.
Variable RZ : Z -> Prop.

Lemma amreal'_ibind_ext {A R} : forall (t : itree astate A) (f g : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
(forall a W1 c1, amreal' segs RZ (f a) W1 c1 Q -> amreal' segs RZ (g a) W1 c1 Q) ->
amreal' segs RZ (ibind t f) W c Q -> amreal' segs RZ (ibind t g) W c Q.
Proof. exact (amrealG_ibind_ext segs (wle' segs RZ)). Qed.

Lemma amreal'_ibind_assoc {A B R} : forall (t : itree astate A) (f : A -> itree astate B) (g : B -> itree astate R) W c
(Q : R -> world segs -> config -> Prop),
amreal' segs RZ (ibind (ibind t f) g) W c Q <-> amreal' segs RZ (ibind t (fun a => ibind (f a) g)) W c Q.
Proof. exact (amrealG_ibind_assoc segs (wle' segs RZ)). Qed.

Lemma amreal'_bind_assoc {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amreal' segs RZ (bind (bind m1 m2) m3 s) W c Q -> amreal' segs RZ (bind m1 (fun a => bind (m2 a) m3) s) W c Q.
Proof. exact (amrealG_bind_assoc segs (wle' segs RZ)). Qed.

Lemma amreal'_bind_assoc' {A B R} : forall (m1 : M A) (m2 : A -> M B) (m3 : B -> M R) s W c
(Q : R * astate -> world segs -> config -> Prop),
amreal' segs RZ (bind m1 (fun a => bind (m2 a) m3) s) W c Q -> amreal' segs RZ (bind (bind m1 m2) m3 s) W c Q.
Proof. exact (amrealG_bind_assoc' segs (wle' segs RZ)). Qed.

Lemma amreal'_apost {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
apost t P -> amreal' segs RZ t W c Q -> amreal' segs RZ t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof. exact (amrealG_apost segs (wle' segs RZ)). Qed.

Lemma amreal'_apostg {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
(forall tr r, apath t tr r -> gflag tr = true -> P r) -> amreal' segs RZ t W c Q ->
amreal' segs RZ t W c (fun r W1 c1 => P r /\ Q r W1 c1).
Proof. exact (amrealG_apostg segs (wle' segs RZ)). Qed.

Lemma amreal'_apath_gflag {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal' segs RZ t W c Q ->
amreal' segs RZ t W c (fun r W' c' => Q r W' c' /\ exists trc, apath t trc r /\ gflag trc = true).
Proof. exact (amrealG_apath_gflag segs (wle' segs RZ)). Qed.

Lemma amreal'_then_SRr' {R} : forall (t : itree astate R) W c (P Q : R -> world segs -> config -> Prop),
amreal' segs RZ t W c P -> (forall r W' c', P r W' c' -> SRr' segs RZ W' c' (Q r)) -> amreal' segs RZ t W c Q.
Proof. exact (amrealG_then_SRrG segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

(* The same bind with a plain SRr continuation (a machine-only segment that re-hides nothing), lifted by SRr_SRr'. *)
Lemma amreal'_then_SRr {R} : forall (t : itree astate R) W c (P Q : R -> world segs -> config -> Prop),
amreal' segs RZ t W c P -> (forall r W' c', P r W' c' -> SRr segs W' c' (Q r)) -> amreal' segs RZ t W c Q.
Proof.
intros t W c P Q H HPQ. apply (amreal'_then_SRr' t W c P Q H).
intros r W' c' HP. exact (SRr_SRr' segs RZ W' c' (Q r) (HPQ r W' c' HP)).
Qed.

Lemma amreal'_after_SRr' {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
SRr' segs RZ W c (fun W1 c1 => amreal' segs RZ t W1 c1 Q) -> amreal' segs RZ t W c Q.
Proof. exact (amrealG_after_SRrG segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_bindK {A R} : forall (t : itree astate A) (f : A -> itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal' segs RZ t W c (fun a W1 c1 => amreal' segs RZ (f a) W1 c1 Q) -> amreal' segs RZ (ibind t f) W c Q.
Proof. exact (amrealG_bindK segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_mbindK {A R} : forall (m : M A) (g : A -> M R) s W c (Q : R * astate -> world segs -> config -> Prop),
amreal' segs RZ (m s) W c (fun r W1 c1 => amreal' segs RZ (g (fst r) (snd r)) W1 c1 Q) ->
amreal' segs RZ (bind m g s) W c Q.
Proof. exact (amrealG_mbindK segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.

Lemma amreal'_atok {R} : forall (t : itree astate R) ns (P : bool -> R -> Prop) W c (Q : R -> world segs -> config -> Prop),
atok ns t P -> amreal' segs RZ t W c (fun r W' c' => (exists ns', P ns' r) -> Q r W' c') -> amreal' segs RZ t W c Q.
Proof. exact (amrealG_atok segs (wle' segs RZ)). Qed.

Lemma amreal'_ask_depot {R} : forall trc s (k : Z -> itree astate R) Wx c Q,
SRr' segs RZ Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amreal' segs RZ (k z) W1 c1 Q) ->
amreal' segs RZ (IAsk (KDepot trc) s k) Wx c Q.
Proof. exact (amrealG_ask_depot segs (wle' segs RZ)). Qed.

Lemma amreal'_pure {A R} : forall (m : M A) (f : A -> M R) s a s' W c Q,
m s = IRet (a, s') -> amreal' segs RZ (f a s') W c Q -> amreal' segs RZ (bind m f s) W c Q.
Proof. exact (amrealG_pure segs (wle' segs RZ)). Qed.
End f.
End b.
