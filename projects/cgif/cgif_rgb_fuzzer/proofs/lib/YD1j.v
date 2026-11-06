(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK00 YK0s YK15 YK18 YN02 YQ0j YQ0b YK05 YA0i YA0l YA0e YG00 YG01 YG0m YG0h YG10 YG0u YG0d YCcz YB1u YF9i YF9j YD2i YD1p YD1v YD1q YD1f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Lemma krefusable_refusable : forall q, krefusable q = true -> refusable q = true.
Proof. intros q. destruct q; intro H; (exact H || discriminate H). Qed.
Lemma aGranted_one : forall z, aGranted z = true -> z = 1.
Proof. intros z H. unfold aGranted in H. apply Z.eqb_eq in H. exact H. Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Hypothesis ARL : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Section g.
Variables (ly : alayout) (S : astate) (W0 : world trbsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z).
Variables (KA KB : TSet) (t0 : itree astate (sptr * astate)) (trc : list Z).
Hypothesis Htrc : In trc (as_universe B).
Hypothesis KNULL : forall ly' S' W' regs' mem' md' tr,
apath t0 tr (PNull, S') ->
acall_post trbsegs B ASTACK ly S W0 regs mem md (fun _ => False) ly' S' W' regs' mem' md' ->
getr regs' 10%bv = w64 0 -> wle W0 W' -> AI trbsegs (w_H W') (w_A W') md' ->
srealizes trbsegs (cfg_at trbsegs (raZ regs) regs' mem' md') KA.
Hypothesis KBLK : forall ly' S' W' regs' mem' md' tr (p : sptr),
p <> PNull -> apath t0 tr (p, S') ->
acall_post trbsegs B ASTACK ly S W0 regs mem md
(fun a => sptr_addr B ly' p <= a < sptr_addr B ly' p + req_size n) ly' S' W' regs' mem' md' ->
getr regs' 10%bv = w64 (sptr_addr B ly' p) -> wle W0 W' -> AI trbsegs (w_H W') (w_A W') md' ->
srealizes trbsegs (cfg_at trbsegs (raZ regs) regs' mem' md') KB.
Definition interp (m : md3) : TSet := match m with MA => KA | MB => KB | MAB => t_alt2 KA KB end.
#[local] Notation Q := (malloc_leaf trbsegs B ly S W0 regs mem md n).
Lemma interp_mle : forall a b tr, mle a b -> interp a tr -> interp b tr.
Proof. intros a b tr [-> | ->] H; [exact H|]. destruct a; cbn in *; unfold t_alt2; tauto. Qed.
Lemma interp_nil : forall a b, mle a b -> interp a [] -> interp b [].
Proof. intros a b tr H. exact (interp_mle a b [] tr H). Qed.
Lemma mle_join_l : forall a b, mle a (join a b). Proof. intros [] []; cbv; auto. Qed.
Lemma mle_join_r : forall a b, mle b (join a b). Proof. intros [] []; cbv; auto. Qed.
Lemma interp_join : forall a b tr, interp (join a b) tr -> interp a tr \/ interp b tr.
Proof. intros [] [] tr; cbn; unfold t_alt2; tauto. Qed.
(* [comment removed for export] *)
Definition SRrB (b : bool) (W : world trbsegs) (c : config) (P : world trbsegs -> config -> Prop) : Prop :=
if b then SRr trbsegs W c P else SRrF trbsegs W c P.
Definition amrealB (b : bool) (t : itree astate (sptr * astate)) (W : world trbsegs) (c : config)
(P : sptr * astate -> world trbsegs -> config -> Prop) : Prop :=
if b then amreal trbsegs t W c P else amrealE trbsegs t W c P.
Lemma SRrB_srealizesM : forall b W c P T,
SRrB b W c P -> AI trbsegs (w_H W) (w_A W) (cfg_model c) ->
(forall W' c', wle W W' -> AI trbsegs (w_H W') (w_A W') (cfg_model c') -> P W' c' -> srealizesM trbsegs b c' T) ->
srealizesM trbsegs b c T.
Proof. intros [|] W c P T H HI HK; [exact (H true HI T HK) | exact (H HI T HK)]. Qed.
Lemma SRrB_mono : forall b W c (P P' : world trbsegs -> config -> Prop),
SRrB b W c P -> (forall W' c', wle W W' -> P W' c' -> P' W' c') -> SRrB b W c P'.
Proof. intros [|] W c P P'; [apply SRr_mono | apply SRrF_mono]. Qed.
Lemma leaf_srz : forall b m p S' W c pre,
tm m (IRet (p, S')) -> wle W0 W -> AI trbsegs (w_H W) (w_A W) (cfg_model c) ->
(forall tr r, apath (IRet (p, S')) tr r -> apath t0 (pre ++ tr) r) ->
SRrB b W c (Q (p, S')) -> srealizesM trbsegs b c (interp m).
Proof.
intros b m p S' W c pre Htm Hle HAI Hpath HS.
apply (SRrB_srealizesM b W c _ _ HS HAI). intros W' c' Hle' HAI' (ly' & regs' & mem' & md' & -> & HPOST & Ha0 & _). cbn [fst snd] in HPOST, Ha0.
cbn [cfg_model] in HAI'. apply srealizesM_weaken.
assert (Hp0 : apath t0 (pre ++ []) (p, S')) by (apply Hpath; reflexivity).
inversion Htm as [r m' HL | | | |]; subst. destruct HL as [[Hp ->] | [Hp ->]]; cbn [fst] in Hp; [subst p|].
- cbn [interp]. apply (KNULL ly' S' W' regs' mem' md' (pre ++ []) Hp0); [| rewrite Ha0; reflexivity | exact (wle_trans _ _ _ _ Hle Hle') | exact HAI'].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs _. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs |]. intros [X _]. exact (X eq_refl).
- cbn [interp]. apply (KBLK ly' S' W' regs' mem' md' (pre ++ []) p Hp Hp0); [| exact Ha0 | exact (wle_trans _ _ _ _ Hle Hle') | exact HAI'].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs HE. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs |]. intros [_ X]. exact (HE X).
Qed.
(* [comment removed for export] *)
Lemma node_exactM : forall (b : bool) (I : Type) (c1 : config) (nx : I -> config) (bm : I -> bool) (T : I -> TSet) (i0 : I) (R : TSet),
node_ok trbsegs c1 I (fun _ => []) nx -> (forall i, srealizesM trbsegs (bm i) (nx i) (T i)) ->
bm i0 = b -> (forall i, b = true -> bm i = false -> fo_dead trbsegs c1 (nx i)) ->
R [] -> (forall i tr, T i tr -> tr = [] \/ R tr) -> (forall tr, R tr -> exists i, T i tr) ->
srealizesM trbsegs b c1 R.
Proof.
intros b I c1 nx bm T i0 R Hnode HT Hi0 Hdead HR0 Hsub Hcov.
apply (srzM_conseq trbsegs b c1 (t_alt (fun i => t_emit [] (T i)))).
{ destruct b.
- apply (srzM_node_dead trbsegs true c1 I (fun _ => []) nx T i0 (fun i => bm i = false) Hnode).
+ rewrite Hi0. discriminate.
+ intros i Hi. split; [exact (srealizesM_E trbsegs _ _ _ (HT i)) | intros _; exact (Hdead i eq_refl Hi)].
+ intros i Hi. pose proof (HT i) as X. destruct (bm i); [exact X | exfalso; exact (Hi eq_refl)].
- apply (srzM_node trbsegs false c1 I (fun _ => []) nx T i0 Hnode).
intros i. apply (srealizesM_mono trbsegs (bm i) false); [exact Logic.I | exact (HT i)]. }
intros tr. split.
- intros [i Hi]. apply (proj1 (t_emit_nil_eq (T i) (srealizesM_nonempty trbsegs _ _ _ (HT i)) tr)) in Hi.
destruct (Hsub i tr Hi) as [-> | H]; [exact HR0 | exact H].
- intros Htr. destruct (Hcov tr Htr) as [i Hi]. exists i.
apply (proj2 (t_emit_nil_eq (T i) (srealizesM_nonempty trbsegs _ _ _ (HT i)) tr)). exact Hi.
Qed.
Lemma amreal_tm : forall t b m W c pre,
tm m t -> asafe t -> amrealB b t W c Q -> AI trbsegs (w_H W) (w_A W) (cfg_model c) -> wle W0 W ->
(forall tr r, apath t tr r -> apath t0 (pre ++ tr) r) ->
srealizesM trbsegs b c (interp m).
Proof.
induction t as [[p S'] | q snap k IH | pc | f]; intros b m W c pre Htm Hsafe HR HAI Hle Hpath.
- apply (leaf_srz b m p S' W c pre Htm Hle HAI Hpath). destruct b; exact HR.
- cbn in Hsafe.
assert (KN : iskernel q = true ->
SRrB b W c (fun W1 c1 => exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok trbsegs c1 I (fun _ => []) nx /\
(forall i, AI trbsegs (w_H W1) (w_A W1) (cfg_model c1) -> AI trbsegs (w_H W1) (w_A W1) (cfg_model (nx i))) /\
(forall i, aok snap q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(refusable q = true -> exists i1, sp i1 = false /\ bit i1 = 0) /\
(forall i, sp i = true -> AI trbsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> srealizesM trbsegs false (nx i) t_nil) /\
(forall i, b = true -> (sp i = true \/ bit i <> 1) -> fo_dead trbsegs c1 (nx i)) /\
(forall i, sp i = false -> amrealB (b && (bit i =? 1))%bool (k (bit i)) W1 (nx i) Q))).
{ intros KQ. destruct b; cbn [amrealB amreal amrealE] in HR; destruct q; try discriminate KQ.
all: cbn [SRrB].
all: lazymatch goal with
| |- SRr _ _ _ _ => eapply SRr_mono; [exact HR|];
intros W1 c1 _ (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9);
exists I, nx, bit, sp, i0; refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj _ _))))))));
[intros i _; exact (H8 i) | intros i Es; exact (H9 i Es)]
| |- SRrF _ _ _ _ => eapply SRrF_mono; [exact HR|];
intros W1 c1 _ (I & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8);
exists I, nx, bit, sp, i0; refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj _ _))))))));
[intros i HF; discriminate HF | intros i Es; exact (H8 i Es)]
end. }
assert (BR : forall b' W1 (I : Type) (nx : I -> config) (bit : I -> Z) (i : I) mi,
wle W W1 -> AI trbsegs (w_H W1) (w_A W1) (cfg_model (nx i)) -> aok snap q (bit i) ->
tm mi (k (bit i)) -> amrealB b' (k (bit i)) W1 (nx i) Q -> srealizesM trbsegs b' (nx i) (interp mi)).
{ intros b' W1 I nx bit i mi Hle1 HAIi Hz Hti HRi.
apply (IH (bit i) b' mi W1 (nx i) (pre ++ [(q, bit i)]) Hti (Hsafe _ Hz) HRi HAIi (wle_trans _ _ _ _ Hle Hle1)).
intros tr r Hp. rewrite <- app_assoc. apply Hpath. cbn. split; [reflexivity|]. split; [exact Hz | exact Hp]. }
inversion Htm as [| | m' q' snap' k' KQ T1 SP | m0 m1 q' snap' k' KQ RQ T1 T0 | m' tr snap' k' TD]; subst.
+
apply (SRrB_srealizesM b W c _ _ (KN KQ) HAI).
intros W1 c1 Hle1 HAI1 (I & nx & bit & sp & i0 & Hnode & HAIs & Haok & Hsp0 & Hbit0 & Href & Hspins & Hdead & Hk).
set (T := fun i : I => if sp i then t_nil else if aGranted (bit i) then interp m else t_nil).
set (bm := fun i : I => if sp i then false else (b && (bit i =? 1))%bool).
assert (HT : forall i, srealizesM trbsegs (bm i) (nx i) (T i)).
{ intros i. subst T bm. cbn beta. destruct (sp i) eqn:Es; [apply Hspins; [exact Es | apply HAIs; exact HAI1] |].
pose proof (Hk i Es) as HRi. destruct (aGranted (bit i)) eqn:Eg.
- apply (BR _ W1 I nx bit i m Hle1 (HAIs i HAI1) (Haok i)); [| exact HRi]. rewrite (aGranted_one _ Eg). exact T1.
- assert (Eb : (b && (bit i =? 1))%bool = false) by (unfold aGranted in Eg; rewrite Eg; apply andb_false_r).
rewrite Eb in HRi |- *. specialize (SP (bit i) (Haok i) Eg). destruct (k (bit i)); try discriminate SP. cbn [amrealB amrealE] in HRi. apply HRi. apply HAIs. exact HAI1. }
assert (N1 : interp m []).
{ pose proof (srealizesM_nonempty trbsegs _ _ _ (HT i0)) as X. subst T. cbn beta in X. rewrite Hsp0, Hbit0 in X. exact X. }
apply (node_exactM b I c1 nx bm T i0 (interp m) Hnode HT).
* subst bm. cbn beta. rewrite Hsp0, Hbit0. destruct b; reflexivity.
* intros i Hb Hbm. apply (Hdead i Hb). subst bm. cbn beta in Hbm. destruct (sp i); [left; reflexivity | right].
subst b. intros E. rewrite E in Hbm. cbn in Hbm. discriminate Hbm.
* exact N1.
* intros i tr' Hi. subst T. cbn beta in Hi. destruct (sp i); [left; unfold t_nil in Hi; (exact Hi || (symmetry; exact Hi))|].
destruct (aGranted (bit i)); [right; exact Hi | left; unfold t_nil in Hi; (exact Hi || (symmetry; exact Hi))].
* intros tr' Htr. exists i0. subst T. cbn beta. rewrite Hsp0, Hbit0. cbn. exact Htr.
+
apply (SRrB_srealizesM b W c _ _ (KN KQ) HAI).
intros W1 c1 Hle1 HAI1 (I & nx & bit & sp & i0 & Hnode & HAIs & Haok & Hsp0 & Hbit0 & Href & Hspins & Hdead & Hk).
set (T := fun i : I => if sp i then t_nil else if aGranted (bit i) then interp m1 else interp m0).
set (bm := fun i : I => if sp i then false else (b && (bit i =? 1))%bool).
assert (HT : forall i, srealizesM trbsegs (bm i) (nx i) (T i)).
{ intros i. subst T bm. cbn beta. destruct (sp i) eqn:Es; [apply Hspins; [exact Es | apply HAIs; exact HAI1] |].
pose proof (Hk i Es) as HRi. destruct (aGranted (bit i)) eqn:Eg.
- apply (BR _ W1 I nx bit i m1 Hle1 (HAIs i HAI1) (Haok i)); [| exact HRi]. rewrite (aGranted_one _ Eg). exact T1.
- apply (BR _ W1 I nx bit i m0 Hle1 (HAIs i HAI1) (Haok i)); [| exact HRi]. exact (T0 (bit i) (Haok i) Eg). }
assert (N1 : interp m1 []).
{ pose proof (srealizesM_nonempty trbsegs _ _ _ (HT i0)) as X. subst T. cbn beta in X. rewrite Hsp0, Hbit0 in X. exact X. }
apply (node_exactM b I c1 nx bm T i0 (interp (join m0 m1)) Hnode HT).
* subst bm. cbn beta. rewrite Hsp0, Hbit0. destruct b; reflexivity.
* intros i Hb Hbm. apply (Hdead i Hb). subst bm. cbn beta in Hbm. destruct (sp i); [left; reflexivity | right].
subst b. intros E. rewrite E in Hbm. cbn in Hbm. discriminate Hbm.
* exact (interp_nil _ _ (mle_join_r m0 m1) N1).
* intros i tr' Hi. subst T. cbn beta in Hi. destruct (sp i); [left; unfold t_nil in Hi; (exact Hi || (symmetry; exact Hi))|]. right.
destruct (aGranted (bit i)); [exact (interp_mle _ _ _ (mle_join_r m0 m1) Hi) | exact (interp_mle _ _ _ (mle_join_l m0 m1) Hi)].
* intros tr' Htr. apply interp_join in Htr as [H0 | H1].
-- destruct (Href (krefusable_refusable q RQ)) as (i1 & Hsp1 & Hbit1).
exists i1. subst T. cbn beta. rewrite Hsp1, Hbit1. cbn. exact H0.
-- exists i0. subst T. cbn beta. rewrite Hsp0, Hbit0. cbn. exact H1.
+
assert (KD : SRrB b W c (fun W1 c1 => exists z, aok snap (KDepot tr) z /\ amrealB b (k z) W1 c1 Q)).
{ destruct b; cbn [amrealB amreal amrealE] in HR; exact HR. }
apply (SRrB_srealizesM b W c _ _ KD HAI).
intros W1 c1 Hle1 HAI1 (z & Hz & HRz).
apply (IH z b m W1 c1 (pre ++ [(KDepot tr, z)]) (TD z Hz) (Hsafe z Hz) HRz HAI1 (wle_trans _ _ _ _ Hle Hle1)).
intros tr' r Hp. rewrite <- app_assoc. apply Hpath. cbn. split; [reflexivity|]. split; [exact Hz | exact Hp].
- inversion Htm.
- cbn in Hsafe. destruct Hsafe.
Qed.
End g.
Theorem trb_malloc_site : malloc_site_tfa B.
Proof.
intros ly S W regs mem md n KA KB HPRE Ha0 Hn Hlive Htr2 Htr1 Hshape HAI KNULL KBLK.
pose proof (acall_pre_of_drv B _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & Hnev & _). pose proof (proj1 (drv_pre_regime B _ _ _ _ _ _ HPRE)) as HRB.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
set (trc := call_trace ly (pc_malloc_ra0 (as_code B)) regs []).
assert (Htr : In trc (as_universe B)).
{ subst trc. destruct (call_trace_drv ly regs (pc_malloc_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (AMALLOC ly S W regs mem md n [] HAP Ha0 Hn Hlive Htr) as HREAL. fold trc in HREAL.
pose proof (malloc_tm_shape (as_universe B) n trc S HWF Hn Hshape) as HTM.
pose proof (atok_asafe _ _ _ (ml_malloc_big _ ML S n trc HWF HRB Hn Hlive Htr)) as HSAFE.
change (t_alt2 KA KB) with (interp KA KB MAB). change (srealizes ?s ?c ?T) with (srealizesM s true c T).
apply (amreal_tm ly S W regs mem md n KA KB (malloc n trc S)
(fun ly' S' W' regs' mem' md' tr Hp => KNULL ly' S' W' regs' mem' md' trc tr Htr Hp)
(fun ly' S' W' regs' mem' md' tr p Hp Hpath => KBLK ly' S' W' regs' mem' md' trc tr p Hp Htr Hpath)
(malloc n trc S) true MAB W _ [] HTM HSAFE HREAL HAI (wle_refl _ W)).
intros tr r Hp. exact Hp.
Qed.
End e.
End d.
