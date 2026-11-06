(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma shadow_ok_patch : forall rho f A,
  shadow_ok rho A ->
  (forall a, outside_all rho (ss_objs (ax_S A)) a -> f a = rm rho a) ->
  shadow_ok (rho_patch rho f) A.
Proof.
  intros rho f A H Hf. unfold shadow_ok in *. rewrite eval_patch.
  apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) H r Hr) as X.
  unfold xr_ok in *. rewrite !eval_patch. destruct X as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|].
  intros a Ha. destruct (X3 a Ha) as (Y1 & Y2 & Y3 & v & Y4 & Y5).
  split; [exact Y1|]. split; [apply outside_all_patch; exact Y2|].
  split.
  - intros j Hj. destruct (Y3 j Hj) as [Z1 Z2]. split; [apply outside_all_patch; exact Z1|].
    cbn [rho_patch rm]. rewrite (Hf _ Z1). exact Z2.
  - exists v. split; [|exact Y5]. cbn [rho_patch rm]. rewrite (Hf _ Y2). exact Y4.
Qed.

Inductive amode : Type :=
| ANone
| AHead (hd : sv) (pot : bool)
| AOpen (hd nx cap : sv) (slots : list (sv * sv))
| AHeadN (hd g : sv).

Definition pl_below (n : positive) (l : list (sv * sv)) : bool :=
  forallb (fun t => sv_below n (fst t) && sv_below n (snd t)) l.
Definition pl_subst (s : wsub) (l : list (sv * sv)) : list (sv * sv) :=
  map (fun t => (sv_subst s (fst t), sv_subst s (snd t))) l.
Fixpoint pl_eqb (l l' : list (sv * sv)) : bool :=
  match l, l' with
  | [], [] => true
  | t :: r, t' :: r' => sv_eqb (fst t) (fst t') && sv_eqb (snd t) (snd t') && pl_eqb r r'
  | _, _ => false
  end.
Lemma pl_eqb_sound : forall l l', pl_eqb l l' = true -> l = l'.
Proof.
  induction l as [|[a b] r IH]; intros [|[a' b'] r'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. cbn in H1, H2. rewrite H1, H2, (IH r' H3). reflexivity.
Qed.
Definition am_below (n : positive) (am : amode) : bool :=
  match am with
  | ANone => true
  | AHead hd _ => sv_below n hd
  | AOpen hd nx cap sl => sv_below n hd && sv_below n nx && sv_below n cap && pl_below n sl
  | AHeadN hd g => sv_below n hd && sv_below n g
  end.
Definition am_subst (s : wsub) (am : amode) : amode :=
  match am with
  | ANone => ANone
  | AHead hd p => AHead (sv_subst s hd) p
  | AOpen hd nx cap sl => AOpen (sv_subst s hd) (sv_subst s nx) (sv_subst s cap) (pl_subst s sl)
  | AHeadN hd g => AHeadN (sv_subst s hd) (sv_subst s g)
  end.
Definition am_eqb (a b : amode) : bool :=
  match a, b with
  | ANone, ANone => true
  | AHead h p, AHead h' p' => sv_eqb h h' && Bool.eqb p p'
  | AOpen h n c sl, AOpen h' n' c' sl' => sv_eqb h h' && sv_eqb n n' && sv_eqb c c' && pl_eqb sl sl'
  | AHeadN h g, AHeadN h' g' => sv_eqb h h' && sv_eqb g g'
  | _, _ => false
  end.
Lemma am_eqb_sound : forall a b, am_eqb a b = true -> a = b.
Proof.
  intros [|h p|h n c sl|h g] [|h' p'|h' n' c' sl'|h' g'] H; cbn -[pl_eqb sv_eqb] in H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply Bool.eqb_prop in H2. congruence.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. apply pl_eqb_sound in H4. congruence.
  - apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. congruence.
Qed.

Definition am_svs (am : amode) : list sv :=
  match am with
  | ANone => []
  | AHead hd _ => [hd]
  | AOpen hd nx cap sl => [hd; nx; cap] ++ flat_map (fun ps => [fst ps; snd ps]) sl
  | AHeadN hd g => [hd; g]
  end.

Definition AV0 : Z := 65568.
Definition AK0 : Z := 2 * KU.
Definition potV (u : Z) : Z := Z.min (2 * u + 66) AV0.
Definition potK (u : Z) : Z := Z.min (4 * u + 4) AK0.

Definition areq (m : word -> option byte) (h : Z) : Z * Z :=
  if h =? 0 then (AV0, AK0)
  else match rd64 m (h + 16) with Some u => (potV u, potK u) | None => (0, 0) end.
Lemma potV_range : forall u, 0 <= u -> 0 <= potV u <= AV0.
Proof. intros u Hu. unfold potV, AV0. lia. Qed.
Lemma potK_range : forall u, 0 <= u -> 0 <= potK u <= AK0.
Proof. intros u Hu. unfold potK, AK0, KU. lia. Qed.
Lemma areq_range : forall m h, 0 <= fst (areq m h) <= AV0 /\ 0 <= snd (areq m h) <= AK0.
Proof.
  intros m h. unfold areq. destruct (h =? 0); [cbn; unfold AV0, AK0, KU; lia|].
  destruct (rd64 m (h + 16)) as [u|] eqn:E; cbn [fst snd]; [|unfold AV0, AK0, KU; lia].
  pose proof (rd64_range _ _ _ E). split; [apply potV_range | apply potK_range]; lia.
Qed.

Inductive amz : Type :=
| ANz
| AHz (h : Z) (pot : bool)
| AOz (h nx cap : Z) (sl : list (Z * Z))
| AHNz (h g : Z).
Definition am_eval (rho : valuation) (am : amode) : amz :=
  match am with
  | ANone => ANz
  | AHead hd p => AHz (uval rho hd) p
  | AOpen hd nx cap sl => AOz (uval rho hd) (uval rho nx) (uval rho cap) (map (fun ps => (uval rho (fst ps), uval rho (snd ps))) sl)
  | AHeadN hd g => AHNz (uval rho hd) (uval rho g)
  end.
Definition apotz (a : amz) (m : word -> option byte) : Z * Z :=
  match a with
  | AHz h true => areq m h
  | _ => (0, 0)
  end.
Definition apot (am : amode) (rho : valuation) : Z * Z := apotz (am_eval rho am) (rm rho).
Lemma apot_range : forall am rho, 0 <= fst (apot am rho) <= AV0 /\ 0 <= snd (apot am rho) <= AK0.
Proof. intros [|hd [|]|h n c sl|h g] rho; cbn -[areq AV0 AK0]; try apply areq_range; unfold AV0, AK0, KU; lia. Qed.

Lemma am_eval_subst : forall s am rho, am_eval rho (am_subst s am) = am_eval (rho_sub rho s) am.
Proof.
  intros s [|hd p|hd nx cap sl|hd g] rho; cbn -[uval]; unfold uval; rewrite <- ?eval_subst; try reflexivity.
  f_equal. unfold pl_subst. rewrite map_map. apply map_ext. intros [a b]. cbn [fst snd]. rewrite <- !eval_subst. reflexivity.
Qed.
Lemma am_eval_agree : forall am n rho rho', agree_vals n rho rho' -> am_below n am = true -> am_eval rho' am = am_eval rho am.
Proof.
  intros [|hd p|hd nx cap sl|hd g] n rho rho' Hag Hb; cbn -[pl_below uval] in Hb |- *; unfold uval.
  - reflexivity.
  - rewrite (eval_agree_vals n rho rho' hd Hag Hb). reflexivity.
  - apply andb_prop in Hb as [Hb Hsl]. apply andb_prop in Hb as [Hb Hc]. apply andb_prop in Hb as [Hh Hn].
    rewrite (eval_agree_vals n rho rho' hd Hag Hh), (eval_agree_vals n rho rho' nx Hag Hn), (eval_agree_vals n rho rho' cap Hag Hc). f_equal.
    apply map_ext_in. intros [a b] Hin. pose proof (proj1 (forallb_forall _ _) Hsl _ Hin) as X. apply andb_prop in X as [X1 X2]. cbn [fst snd] in *.
    rewrite (eval_agree_vals n rho rho' a Hag X1), (eval_agree_vals n rho rho' b Hag X2). reflexivity.
  - apply andb_prop in Hb as [Hh Hg]. rewrite (eval_agree_vals n rho rho' hd Hag Hh), (eval_agree_vals n rho rho' g Hag Hg). reflexivity.
Qed.

Lemma am_eval_ext : forall (f : sv -> sv) am rho1 rho2,
  (forall e, In e (am_svs am) -> eval rho2 (f e) = eval rho1 e) ->
  am_eval rho2 (match am with
                | ANone => ANone | AHead hd p => AHead (f hd) p
                | AOpen hd nx cap sl => AOpen (f hd) (f nx) (f cap) (map (fun t => (f (fst t), f (snd t))) sl)
                | AHeadN hd g => AHeadN (f hd) (f g) end) = am_eval rho1 am.
Proof.
  intros f [|hd p|hd nx cap sl|hd g] rho1 rho2 HE; cbn -[uval]; unfold uval.
  - reflexivity.
  - rewrite (HE hd ltac:(left; reflexivity)). reflexivity.
  - rewrite (HE hd ltac:(left; reflexivity)), (HE nx ltac:(right; left; reflexivity)), (HE cap ltac:(right; right; left; reflexivity)). f_equal.
    rewrite map_map. apply map_ext_in. intros [a b] Hin. cbn [fst snd].
    assert (Hin2 : forall e, In e [a; b] -> In e ([hd; nx; cap] ++ flat_map (fun ps => [fst ps; snd ps]) sl)).
    { intros e He. apply in_or_app. right. apply in_flat_map. exists (a, b). split; [exact Hin | exact He]. }
    rewrite (HE a (Hin2 a ltac:(left; reflexivity))), (HE b (Hin2 b ltac:(right; left; reflexivity))). reflexivity.
  - rewrite (HE hd ltac:(left; reflexivity)), (HE g ltac:(right; left; reflexivity)). reflexivity.
Qed.
Lemma am_eval_exteq : forall am rho1 rho2,
  (forall e, In e (am_svs am) -> eval rho2 e = eval rho1 e) -> am_eval rho2 am = am_eval rho1 am.
Proof.
  intros [|hd p|hd nx cap sl|hd g] rho1 rho2 HE; cbn -[uval]; unfold uval.
  - reflexivity.
  - rewrite (HE hd ltac:(left; reflexivity)). reflexivity.
  - rewrite (HE hd ltac:(left; reflexivity)), (HE nx ltac:(right; left; reflexivity)), (HE cap ltac:(right; right; left; reflexivity)). f_equal.
    apply map_ext_in. intros [a b] Hin. cbn [fst snd].
    assert (Hin2 : forall e, In e [a; b] -> In e ([hd; nx; cap] ++ flat_map (fun ps => [fst ps; snd ps]) sl)).
    { intros e He. apply in_or_app. right. apply in_flat_map. exists (a, b). split; [exact Hin | exact He]. }
    rewrite (HE a (Hin2 a ltac:(left; reflexivity))), (HE b (Hin2 b ltac:(right; left; reflexivity))). reflexivity.
  - rewrite (HE hd ltac:(left; reflexivity)), (HE g ltac:(right; left; reflexivity)). reflexivity.
Qed.
Lemma am_subst_as_map : forall s am,
  am_subst s am = match am with
                  | ANone => ANone | AHead hd p => AHead (sv_subst s hd) p
                  | AOpen hd nx cap sl => AOpen (sv_subst s hd) (sv_subst s nx) (sv_subst s cap) (map (fun t => (sv_subst s (fst t), sv_subst s (snd t))) sl)
                  | AHeadN hd g => AHeadN (sv_subst s hd) (sv_subst s g) end.
Proof. intros s [| | |]; reflexivity. Qed.

Definition capK (BX : bxt) (A : AA) : Prop := LARGE_MIN * large_live A <= bxS BX + aa_V A.

Definition bxa (BX : Z * Z) (p : Z * Z) (kc : Z) : Z * Z := (fst BX + fst p, snd BX + snd p + kc).

Definition xmemA (m : word -> option byte) (B L : Z) : Prop :=
  B mod 8 = 0 /\
  forall a, B <= a < B + L ->
    (forall j, 0 <= j < 8 -> m (word_byte (SHADOW_OFF + a / 8) j) <> None)
    /\ exists v, m (shadow_addr SHADOW_OFF a) = Some v
         /\ (bv_unsigned v = 0 \/ (bv_unsigned v = (B + L) mod 8 /\ a / 8 = (B + L) / 8)).

Lemma xmemA_frame : forall m m' B L,
  xmemA m B L ->
  (forall a, B <= a < B + L -> m (shadow_addr SHADOW_OFF a) <> None -> m' (shadow_addr SHADOW_OFF a) = m (shadow_addr SHADOW_OFF a)) ->
  (forall a j, B <= a < B + L -> 0 <= j < 8 -> m (word_byte (SHADOW_OFF + a / 8) j) <> None -> m' (word_byte (SHADOW_OFF + a / 8) j) <> None) ->
  xmemA m' B L.
Proof.
  intros m m' B L [H0 H] E D. split; [exact H0|]. intros a Ha. destruct (H a Ha) as [H1 (v & H2 & H3)]. split.
  - intros j Hj. apply (D a j Ha Hj). exact (H1 j Hj).
  - exists v. split; [|exact H3]. rewrite (E a Ha ltac:(rewrite H2; discriminate)). exact H2.
Qed.
Lemma shadow_addr_word_byte : forall a,
  shadow_addr SHADOW_OFF a = word_byte (SHADOW_OFF + a / 8) ((SHADOW_OFF + a / 8) mod 8).
Proof. intros a. unfold shadow_addr, word_byte. f_equal. pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)). lia. Qed.
Lemma xmemA_frame_eq : forall m m' B L,
  xmemA m B L ->
  (forall a j, B <= a < B + L -> 0 <= j < 8 -> m' (word_byte (SHADOW_OFF + a / 8) j) = m (word_byte (SHADOW_OFF + a / 8) j)) ->
  xmemA m' B L.
Proof.
  intros m m' B L H E. eapply xmemA_frame; [exact H| |].
  - intros a Ha _. rewrite shadow_addr_word_byte. apply E; [exact Ha | apply Z.mod_pos_bound; lia].
  - intros a j Ha Hj Hd. rewrite (E a j Ha Hj). exact Hd.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma smatchA_patch : forall rho f tp A w,
  smatchA segs rho tp A w ->
  (forall a, outside_all rho (ss_objs (ax_S A)) a -> f a = rm rho a) ->
  smatchA segs (rho_patch rho f) tp A w.
Proof using .
  intros rho f tp A w (Hsm & HMI & Hwf & Hsh & Hhz) Hf.
  split; [apply smatch_patch; [exact Hsm | exact Hf]|]. split; [exact HMI|]. split; [exact Hwf|].
  split; [apply shadow_ok_patch; [exact Hsh | exact Hf] | exact Hhz].
Qed.

Lemma Kc_ok_mat_blind : forall Kc, Kc_ok Kc -> mat_blind Kc.
Proof using .
  intros Kc HK tr md l p. split; intros H; eapply Kc_ok_mat; eauto.
Qed.

Variable E : aentry.
Variable AInv : AA -> valuation -> list word -> Model -> Prop.
Variables CST XGL : list (Z * Z).

Definition caddrA (Ai : AA) (x : option Z) (a : Z) : Prop :=
  (topG (aa_geom Ai) <= a < 2 ^ 47) \/ in_rangesZ CST a
  \/ (exists b n, In (b, n) (aa_live Ai) /\ x <> Some b /\ b <= a < b + n)
  \/ (exists f s, In (f, s) (aa_frames Ai) /\ f <= a < f + s)
  \/ (exists fs, In fs (aa_frames Ai) /\ a = frame_flag (aa_geom Ai) fs).

Lemma caddrA_weaken : forall Ai x a, caddrA Ai (Some x) a -> caddrA Ai None a.
Proof using .
  intros Ai x a [H|[H|[(b & n & Hin & _ & Hr)|[H|H]]]]; [left; exact H | right; left; exact H | | right; right; right; left; exact H | do 4 right; exact H].
  right; right; left. exists b, n. repeat split; [exact Hin | discriminate | lia | lia].
Qed.

Lemma caddrA_client : forall Ai x a, caddrA Ai x a -> client_addrA CST Ai a.
Proof using .
  intros Ai x a [H|[H|[(b & n & Hin & _ & Hr)|[(f & s & Hin & Hr)|(fs & Hin & Ha)]]]].
  - left. left. exact H.
  - left. right; right; right. exact H.
  - left. right; left. exists b, n. auto.
  - left. right; right; left. exists f, s. auto.
  - right. exists fs. auto.
Qed.

Definition robjs_okA (Ai : AA) (x : option Z) (rho : valuation) (R : list sobj) : Prop :=
  forall o a, In o R -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> caddrA Ai x a.

Lemma robjs_okA_in_ranges : forall Ai x rho R a,
  robjs_okA Ai x rho R -> in_ranges rho R a -> caddrA Ai x (bv_unsigned a).
Proof using . intros Ai x rho R a H (o & Hin & Hr). exact (H o _ Hin Hr). Qed.

Section Sum.

Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.

Variable P0f : valuation -> Prop.

Variable FB : list (Z * Z).

Variable FF : list (Z * Z * Z).

Variable BX : bxt.

Variable PA : AA -> Prop.

Ltac clear_sec0 := try clear BX; try clear FF; try clear FB; try clear P0f; try clear rho0; try clear Kc; try clear NP.

Record ndesc := NDA { nd_tv : list (sv * sv); nd_fr : list (sv * Z * sv); nd_bd : list bitem; nd_am : amode }.
Definition ND (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (bd : list bitem) : ndesc := NDA tv fr bd ANone.

Definition fbinA (Ai : AA) : Prop := forall bn, In bn FB -> In bn (aa_live Ai).
Definition ffinA (Ai : AA) : Prop :=
  forall f s fl, In (f, s, fl) FF -> In (f, s) (aa_frames Ai) /\ fl = frame_flag (aa_geom Ai) (f, s).

Definition tvinA (Ai : AA) (rho : valuation) (tv : list (sv * sv)) : Prop :=
  Forall (fun t => tnz rho t -> 0 < snd (tvv rho t) /\ In (tvv rho t) (aa_live Ai) /\ ~ In (tvv rho t) FB) tv.

Definition frv (rho : valuation) (x : sv * Z * sv) : Z * Z := (uval rho (fst (fst x)), fs_frame_size (snd (fst x))).
Definition frinA0 (Ai : AA) (rho : valuation) (fr : list (sv * Z * sv)) : Prop :=
  Forall (fun x => In (frv rho x) (aa_frames Ai)
                   /\ uval rho (snd x) = frame_flag (aa_geom Ai) (frv rho x)
                   /\ (forall y, In y FF -> fst (fst y) <> fst (frv rho x))) fr.

Definition fcensus (Ai : AA) (rho : valuation) (fr : list (sv * Z * sv)) : Prop :=
  forall x, In x (aa_frames Ai) -> (exists fl, In (fst x, snd x, fl) FF) \/ In x (map (frv rho) fr).

Definition frinA (Ai : AA) (rho : valuation) (fr : list (sv * Z * sv)) : Prop :=
  frinA0 Ai rho fr /\ (fcensus Ai rho fr /\ List.NoDup (map (frv rho) fr)).

Lemma fcensus_map : forall Ai Ai' rho rho' fr fr',
  aa_frames Ai' = aa_frames Ai -> map (frv rho') fr' = map (frv rho) fr -> fcensus Ai rho fr -> fcensus Ai' rho' fr'.
Proof using . intros Ai Ai' rho rho' fr fr' EA EM H x Hx. rewrite EA in Hx. rewrite EM. exact (H x Hx). Qed.
Lemma frinA_rest_map : forall Ai Ai' rho rho' fr fr',
  aa_frames Ai' = aa_frames Ai -> map (frv rho') fr' = map (frv rho) fr ->
  fcensus Ai rho fr /\ List.NoDup (map (frv rho) fr) -> fcensus Ai' rho' fr' /\ List.NoDup (map (frv rho') fr').
Proof using . intros Ai Ai' rho rho' fr fr' EA EM [H1 H2]. split; [eapply fcensus_map; eauto | rewrite EM; exact H2]. Qed.

Definition tvals (rho : valuation) (tv : list (sv * sv)) : list (Z * Z) := map (tvv rho) tv.

Definition cntS (rho : valuation) (tv : list (sv * sv)) : Z := cntSZ (tvals rho tv).
Definition capN (BX : bxt) (A : AA) (rho : valuation) (tv : list (sv * sv)) : Prop := small_live A <= bxN BX + cntS rho tv.
Definition untrackedZ (tvs : list (Z * Z)) (bn : Z * Z) : Prop := forall v, In v tvs -> fst v <> 0 -> v <> bn.
Definition untracked (rho : valuation) (tv : list (sv * sv)) (bn : Z * Z) : Prop := untrackedZ (tvals rho tv) bn.
Definition node_okZ (F : list (Z * Z)) (Ai : AA) (m : word -> option byte) (tvs : list (Z * Z)) (bc : Z * Z) : Prop :=
  In (fst bc, HDR + snd bc) (aa_live Ai) /\ ~ In (fst bc, HDR + snd bc) F /\ untrackedZ tvs (fst bc, HDR + snd bc)
  /\ 65536 <= snd bc /\ HDR + snd bc < 2 ^ 40 /\ xmemA m (fst bc) (HDR + snd bc).
Definition chainZ (F : list (Z * Z)) (Ai : AA) (m : word -> option byte) (tvs : list (Z * Z)) (h : Z) (ns : list (Z * Z)) : Prop :=
  achain m h ns /\ Forall (node_okZ F Ai m tvs) ns /\ NoDup (map fst ns).
Definition XAz0 (F : list (Z * Z)) (a : amz) (Ai : AA) (m : word -> option byte) (tvs : list (Z * Z)) (kc : Z) : Prop :=
  match a with
  | ANz => kc = 0
  | AHz h _ => exists ns, chainZ F Ai m tvs h ns /\ kc = KU * Z.of_nat (length ns)
  | AOz h nx c sl =>
      h <> 0 /\ In (h, HDR + c) (aa_live Ai) /\ ~ In (h, HDR + c) F /\ untrackedZ tvs (h, HDR + c)
      /\ 65536 <= c /\ HDR + c < 2 ^ 40
      /\ (forall z, h + 24 <= z < h + HDR + c -> m (Z_to_bv 64 z) <> None)
      /\ Forall (fun ps => h + 24 <= fst ps /\ fst ps + snd ps <= h + HDR + c) sl
      /\ exists ns, chainZ F Ai m tvs nx ns /\ ~ In h (map fst ns) /\ kc = KU * (1 + Z.of_nat (length ns))
  | AHNz h g => exists ns, chainZ F Ai m tvs h ns /\ kc = KU * Z.of_nat (length ns) /\ 16 * Z.of_nat (length ns) + 15 <= g <= 2 ^ 52
  end.

Definition cblk (bc : Z * Z) : Z * Z := (fst bc, HDR + snd bc).
Lemma ZZ_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof using . clear. decide equality; apply Z.eq_dec. Defined.
Definition amblkZ (a : amz) (m : word -> option byte) (bn : Z * Z) : Prop :=
  match a with
  | ANz => False
  | AHz h _ => exists ns, achain m h ns /\ In bn (map cblk ns)
  | AOz h nx c sl => bn = (h, HDR + c) \/ exists ns, achain m nx ns /\ In bn (map cblk ns)
  | AHNz h g => exists ns, achain m h ns /\ In bn (map cblk ns)
  end.
Definition lcenZ (F : list (Z * Z)) (a : amz) (Ai : AA) (m : word -> option byte) (tvs : list (Z * Z)) : Prop :=
  forall bn, In bn (aa_live Ai) -> LARGE_MIN <= snd bn -> ~ In bn F -> untrackedZ tvs bn -> amblkZ a m bn.
Definition XAz (F : list (Z * Z)) (a : amz) (Ai : AA) (m : word -> option byte) (tvs : list (Z * Z)) (kc : Z) : Prop :=
  XAz0 F a Ai m tvs kc /\ lcenZ F a Ai m tvs.
Definition XA (am : amode) (Ai : AA) (rho : valuation) (tv : list (sv * sv)) (kc : Z) : Prop :=
  XAz FB (am_eval rho am) Ai (rm rho) (tvals rho tv) kc.

Lemma XAz_kc_nonneg : forall F a Ai m tvs kc, XAz F a Ai m tvs kc -> 0 <= kc.
Proof using .
  clear_sec0. intros F [|h p|h nx c sl|h g] Ai m tvs kc [H _]; cbn -[chainZ KU] in H; unfold KU in *.
  - lia.
  - destruct H as (ns & _ & ->). lia.
  - destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & ns & _ & _ & ->). lia.
  - destruct H as (ns & _ & -> & _). lia.
Qed.
Lemma XA_kc_nonneg : forall am Ai rho tv kc, XA am Ai rho tv kc -> 0 <= kc.
Proof using . intros. eapply XAz_kc_nonneg. exact H. Qed.

Lemma chainZ_transport : forall F1 F2 Ai A2 m1 m2 tvs1 tvs2 h ns,
  chainZ F1 Ai m1 tvs1 h ns ->
  (forall b n, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) ->
      In (b, n) (aa_live A2) /\ ~ In (b, n) F2 /\ untrackedZ tvs2 (b, n)) ->
  (forall b n z, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) -> b <= z < b + n -> m2 (Z_to_bv 64 z) = m1 (Z_to_bv 64 z)) ->
  (forall b n a, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) -> b <= a < b + n ->
       (m1 (shadow_addr SHADOW_OFF a) <> None -> m2 (shadow_addr SHADOW_OFF a) = m1 (shadow_addr SHADOW_OFF a))
       /\ (forall j, 0 <= j < 8 -> m1 (word_byte (SHADOW_OFF + a / 8) j) <> None -> m2 (word_byte (SHADOW_OFF + a / 8) j) <> None)) ->
  chainZ F2 A2 m2 tvs2 h ns.
Proof using .
  clear_sec0. intros F1 F2 Ai A2 m1 m2 tvs1 tvs2 h ns [HA [HF HD]] HL HM HS.
  assert (NODE : forall b c, In (b, c) ns -> In (b, HDR + c) (aa_live Ai) /\ ~ In (b, HDR + c) F1 /\ untrackedZ tvs1 (b, HDR + c)).
  { intros b c Hin. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3 & _). cbn [fst snd] in *. auto. }
  pose proof (achain_caps _ _ _ HA) as CAPS.
  split; [|split; [|exact HD]].
  - eapply achain_frame; [exact HA| |].
    + intros z (b & c & Hin & Hz). destruct (NODE b c Hin) as (N1 & N2 & N3).
      pose proof (proj1 (Forall_forall _ _) CAPS _ Hin) as [Hc _]. cbn [snd] in Hc.
      apply (HM _ _ z N1 N2 N3). unfold HDR. lia.
    + intros z (b & c & Hin & Hz) Hdef. destruct (NODE b c Hin) as (N1 & N2 & N3).
      rewrite (HM _ _ z N1 N2 N3 ltac:(lia)). exact Hdef.
  - apply Forall_forall. intros [b c] Hin. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3 & H4 & H5 & H6). cbn [fst snd] in *.
    destruct (HL b _ H1 H2 H3) as (N1 & N2 & N3).
    split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact H4|]. split; [exact H5|].
    eapply xmemA_frame; [exact H6| |].
    + intros a Ha. exact (proj1 (HS _ _ a H1 H2 H3 Ha)).
    + intros a j Ha Hj. exact (proj2 (HS _ _ a H1 H2 H3 Ha) j Hj).
Qed.

Lemma XAz0_transport : forall F1 F2 a Ai A2 m1 m2 tvs1 tvs2 kc,
  XAz0 F1 a Ai m1 tvs1 kc ->
  (forall b n, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) ->
      In (b, n) (aa_live A2) /\ ~ In (b, n) F2 /\ untrackedZ tvs2 (b, n)) ->
  (forall b n z, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) -> b <= z < b + n -> m2 (Z_to_bv 64 z) = m1 (Z_to_bv 64 z)) ->
  (forall b n a, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) -> b <= a < b + n ->
       (m1 (shadow_addr SHADOW_OFF a) <> None -> m2 (shadow_addr SHADOW_OFF a) = m1 (shadow_addr SHADOW_OFF a))
       /\ (forall j, 0 <= j < 8 -> m1 (word_byte (SHADOW_OFF + a / 8) j) <> None -> m2 (word_byte (SHADOW_OFF + a / 8) j) <> None)) ->
  XAz0 F2 a A2 m2 tvs2 kc /\ apotz a m2 = apotz a m1.
Proof using .
  clear_sec0. intros F1 F2 a Ai A2 m1 m2 tvs1 tvs2 kc HX HL HM HS.
  destruct a as [|h p|h nx c sl|h g]; cbn -[chainZ KU areq] in HX |- *.
  - split; [exact HX | reflexivity].
  - destruct HX as (ns & HC & Hk). split.
    + exists ns. split; [eapply chainZ_transport; eauto | exact Hk].
    + destruct p; [|reflexivity]. unfold areq.
      destruct (Z.eqb_spec h 0) as [E0|NE]; [reflexivity|].
      destruct HC as [HA [HF _]]. destruct (achain_cons _ _ _ HA NE) as (c & r & ->).
      destruct (proj1 (Forall_forall _ _) HF _ ltac:(left; reflexivity)) as (H1 & H2 & H3 & H4 & _). cbn [fst snd] in *.
      rewrite (rd64_ext m1 m2); [reflexivity|]. intros z Hz. apply (HM _ _ z H1 H2 H3). unfold HDR. lia.
  - destruct HX as (X1 & X2 & X3 & X4 & X5 & X5b & X6 & X7 & ns & HC & Hnin & Hk).
    destruct (HL _ _ X2 X3 X4) as (N2 & N3 & N4). split; [|reflexivity].
    split; [exact X1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact X5|]. split; [exact X5b|]. split.
    + intros z Hz. rewrite (HM _ _ z X2 X3 X4); [exact (X6 z Hz) | unfold HDR in *; lia].
    + split; [exact X7|]. exists ns. split; [eapply chainZ_transport; eauto|]. split; [exact Hnin | exact Hk].
  - destruct HX as (ns & HC & Hk & HLg). split; [|reflexivity]. exists ns. split; [eapply chainZ_transport; eauto|]. split; [exact Hk | exact HLg].
Qed.

Lemma achain_det : forall m ns ns' h, achain m h ns -> achain m h ns' -> ns' = ns.
Proof using .
  clear_sec0. intros m ns. induction ns as [|[b cap] r IH]; intros ns' h H H'.
  - cbn in H. subst h. exact (achain_nil _ _ H').
  - cbn in H. destruct H as (-> & Hb & Hc & Hcap & _ & _ & nx & Hnx & Hr).
    destruct ns' as [|[b' cap'] r']; [cbn in H'; contradiction|].
    cbn in H'. destruct H' as (Eb & _ & _ & Hcap' & _ & _ & nx' & Hnx' & Hr'). subst b'.
    rewrite Hcap in Hcap'. injection Hcap' as <-. rewrite Hnx in Hnx'. injection Hnx' as <-.
    f_equal. exact (IH r' nx Hr Hr').
Qed.

Lemma amblkZ_open_iff : forall m h p nx c sl r, achain m h ((h, c) :: r) -> achain m nx r ->
  forall bn, amblkZ (AHz h p) m bn <-> amblkZ (AOz h nx c sl) m bn.
Proof using .
  clear_sec0. intros m h p nx c sl r HA HR bn. cbn [amblkZ]. split.
  - intros (ns & HA' & Hin). rewrite (achain_det _ _ _ _ HA HA') in Hin. cbn [map In cblk fst snd] in Hin.
    destruct Hin as [<-|Hin]; [left; reflexivity | right; exists r; split; [exact HR | exact Hin]].
  - intros [->|(ns & HA' & Hin)].
    + exists ((h, c) :: r). split; [exact HA | left; reflexivity].
    + rewrite (achain_det _ _ _ _ HR HA') in Hin. exists ((h, c) :: r). split; [exact HA | right; exact Hin].
Qed.

Lemma lcenZ_mode : forall F a a' Ai m tvs, (forall bn, amblkZ a m bn -> amblkZ a' m bn) -> lcenZ F a Ai m tvs -> lcenZ F a' Ai m tvs.
Proof using . clear_sec0. intros F a a' Ai m tvs H HC bn H1 H2 H3 H4. exact (H bn (HC bn H1 H2 H3 H4)). Qed.

Lemma XAz_blocks : forall F a Ai m tvs kc, XAz F a Ai m tvs kc ->
  exists bl, KU * Z.of_nat (length bl) = kc /\ forall bn, amblkZ a m bn -> In bn bl.
Proof using .
  clear_sec0. intros F [|h p|h nx c sl|h g] Ai m tvs kc [HX _]; cbn -[chainZ KU] in HX |- *.
  - exists []. split; [cbn; lia | intros bn []].
  - destruct HX as (ns & HC & ->). exists (map cblk ns). split; [rewrite length_map; reflexivity|].
    intros bn (ns' & HA' & Hin). rewrite (achain_det _ _ _ _ (proj1 HC) HA') in Hin. exact Hin.
  - destruct HX as (_ & _ & _ & _ & _ & _ & _ & _ & ns & HC & _ & ->). exists ((h, HDR + c) :: map cblk ns).
    split; [cbn [length]; rewrite length_map; lia|].
    intros bn [->|(ns' & HA' & Hin)]; [left; reflexivity|]. right. rewrite (achain_det _ _ _ _ (proj1 HC) HA') in Hin. exact Hin.
  - destruct HX as (ns & HC & -> & _). exists (map cblk ns). split; [rewrite length_map; reflexivity|].
    intros bn (ns' & HA' & Hin). rewrite (achain_det _ _ _ _ (proj1 HC) HA') in Hin. exact Hin.
Qed.

Lemma XAz_transport : forall F1 F2 a Ai A2 m1 m2 tvs1 tvs2 kc,
  XAz F1 a Ai m1 tvs1 kc ->
  (forall b n, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) ->
      In (b, n) (aa_live A2) /\ ~ In (b, n) F2 /\ untrackedZ tvs2 (b, n)) ->
  (forall b n z, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) -> b <= z < b + n -> m2 (Z_to_bv 64 z) = m1 (Z_to_bv 64 z)) ->
  (forall b n a, In (b, n) (aa_live Ai) -> ~ In (b, n) F1 -> untrackedZ tvs1 (b, n) -> b <= a < b + n ->
       (m1 (shadow_addr SHADOW_OFF a) <> None -> m2 (shadow_addr SHADOW_OFF a) = m1 (shadow_addr SHADOW_OFF a))
       /\ (forall j, 0 <= j < 8 -> m1 (word_byte (SHADOW_OFF + a / 8) j) <> None -> m2 (word_byte (SHADOW_OFF + a / 8) j) <> None)) ->
  (forall bn, In bn (aa_live A2) -> LARGE_MIN <= snd bn -> ~ In bn F2 -> untrackedZ tvs2 bn ->
      In bn (aa_live Ai) /\ ~ In bn F1 /\ untrackedZ tvs1 bn) ->
  XAz F2 a A2 m2 tvs2 kc /\ apotz a m2 = apotz a m1.
Proof using .
  clear_sec0. intros F1 F2 a Ai A2 m1 m2 tvs1 tvs2 kc [HX HC0] HL HM HS HC.
  destruct (XAz0_transport F1 F2 a Ai A2 m1 m2 tvs1 tvs2 kc HX HL HM HS) as [HX2 HP].
  split; [|exact HP]. split; [exact HX2|].
  intros bn H1 H2 H3 H4. destruct (HC bn H1 H2 H3 H4) as (G1 & G2 & G3). pose proof (HC0 bn G1 H2 G2 G3) as HB.

  destruct a as [|h p|h nx c sl|h g]; cbn -[chainZ KU areq] in HX, HB |- *.
  - exact HB.
  - destruct HB as (ns' & HA' & Hin). destruct HX as (ns & HCh & _).
    rewrite (achain_det _ _ _ _ (proj1 HCh) HA') in Hin. exists ns. split; [|exact Hin].
    exact (proj1 (chainZ_transport F1 F2 Ai A2 m1 m2 tvs1 tvs2 h ns HCh HL HM HS)).
  - destruct HB as [HB|(ns' & HA' & Hin)]; [left; exact HB|]. right.
    destruct HX as (_ & _ & _ & _ & _ & _ & _ & _ & ns & HCh & _).
    rewrite (achain_det _ _ _ _ (proj1 HCh) HA') in Hin. exists ns. split; [|exact Hin].
    exact (proj1 (chainZ_transport F1 F2 Ai A2 m1 m2 tvs1 tvs2 nx ns HCh HL HM HS)).
  - destruct HB as (ns' & HA' & Hin). destruct HX as (ns & HCh & _).
    rewrite (achain_det _ _ _ _ (proj1 HCh) HA') in Hin. exists ns. split; [|exact Hin].
    exact (proj1 (chainZ_transport F1 F2 Ai A2 m1 m2 tvs1 tvs2 h ns HCh HL HM HS)).
Qed.

Lemma tvals_agree : forall n rho rho' tv, agree_vals n rho rho' -> tv_below n tv = true -> tvals rho' tv = tvals rho tv.
Proof using .
  clear_sec0. intros n rho rho' tv Hag Hb. unfold tvals. apply map_ext_in. intros t Ht.
  apply (tvv_agree n rho rho' t Hag). exact (proj1 (forallb_forall _ _) Hb t Ht).
Qed.

Lemma cntS_agree : forall n rho rho' tv, agree_vals n rho rho' -> tv_below n tv = true -> cntS rho' tv = cntS rho tv.
Proof using . clear_sec0. intros n rho rho' tv Hag Hb. unfold cntS. rewrite (tvals_agree n rho rho' tv Hag Hb). reflexivity. Qed.
Lemma cntS_map : forall rho rho' tv tv', map (tvv rho') tv' = map (tvv rho) tv -> cntS rho' tv' = cntS rho tv.
Proof using . clear_sec0. intros rho rho' tv tv' EQm. unfold cntS, tvals. rewrite EQm. reflexivity. Qed.
Lemma cntS_nil : forall rho, cntS rho [] = 0.
Proof using . reflexivity. Qed.
Lemma cntS_cons : forall rho t tv, cntS rho (t :: tv) = (if is_smallZ (tvv rho t) then 1 else 0) + cntS rho tv.
Proof using . clear_sec0. intros rho t tv. unfold cntS, tvals. cbn [map]. apply cntSZ_cons. Qed.
Lemma cntS_app : forall rho tv1 tv2, cntS rho (tv1 ++ tv2) = cntS rho tv1 + cntS rho tv2.
Proof using . clear_sec0. intros rho tv1 tv2. unfold cntS, tvals. rewrite map_app. apply cntSZ_app. Qed.
Lemma cntS_bounds : forall rho tv, 0 <= cntS rho tv <= Z.of_nat (length tv).
Proof using . clear_sec0. intros rho tv. unfold cntS, tvals. pose proof (cntSZ_bounds (map (tvv rho) tv)) as H. rewrite length_map in H. exact H. Qed.
Lemma cntS_perm : forall rho tv tv', Permutation.Permutation tv tv' -> cntS rho tv = cntS rho tv'.
Proof using . clear_sec0. intros rho tv tv' H. unfold cntS, tvals. apply cntSZ_perm. apply Permutation.Permutation_map. exact H. Qed.

Lemma is_smallZ_tnz : forall rho t, ~ tnz rho t -> is_smallZ (tvv rho t) = false.
Proof using .
  clear_sec0. intros rho t H. apply is_smallZ_null. unfold tnz in H. unfold tvv. cbn [fst].
  destruct (Z.eq_dec (bv_unsigned (eval rho (fst t))) 0) as [EQz|EQz]; [exact EQz | contradiction].
Qed.
Lemma cntS_remove_nth : forall rho tv i t, nth_error tv i = Some t ->
  cntS rho (remove_nth i tv) = cntS rho tv - (if is_smallZ (tvv rho t) then 1 else 0).
Proof using .
  clear_sec0. intros rho tv. induction tv as [|x r IH]; intros [|i] t H; cbn [nth_error] in H; try discriminate.
  - injection H as ->. cbn [remove_nth]. rewrite cntS_cons. lia.
  - cbn [remove_nth]. rewrite !cntS_cons, (IH i t H). lia.
Qed.
Lemma remove_nth_none {T} : forall (l : list T) i, nth_error l i = None -> remove_nth i l = l.
Proof using . clear_sec0. intros l. induction l as [|x r IH]; intros [|i] H; cbn [nth_error remove_nth] in *; try reflexivity; try discriminate. rewrite (IH i H). reflexivity. Qed.

Lemma cntS_remove_nth_null : forall rho tv i, (forall t, nth_error tv i = Some t -> ~ tnz rho t) -> cntS rho (remove_nth i tv) = cntS rho tv.
Proof using .
  clear_sec0. intros rho tv i H. destruct (nth_error tv i) as [t|] eqn:En.
  - rewrite (cntS_remove_nth rho tv i t En), (is_smallZ_tnz rho t (H t eq_refl)). lia.
  - rewrite (remove_nth_none tv i En). reflexivity.
Qed.
Lemma length_remove_nth_le {T} : forall (l : list T) i, (length (remove_nth i l) <= length l)%nat.
Proof using . clear_sec0. intros l. induction l as [|x r IH]; intros [|i]; cbn [remove_nth length]; try lia. specialize (IH i). lia. Qed.
Lemma cntS_le_TVMAX : forall rho tv, (length tv <= TVMAXn)%nat -> cntS rho tv <= TVMAX.
Proof using . clear_sec0. intros rho tv H. pose proof (cntS_bounds rho tv). unfold TVMAX, TVMAXn in *. lia. Qed.
Lemma capN_agree : forall n BX' A rho rho' tv, agree_vals n rho rho' -> tv_below n tv = true -> capN BX' A rho tv -> capN BX' A rho' tv.
Proof using . clear_sec0. intros n BX' A rho rho' tv Hag Hb H. unfold capN in *. rewrite (cntS_agree n rho rho' tv Hag Hb). exact H. Qed.
Lemma capN_map : forall BX' A rho rho' tv tv', map (tvv rho') tv' = map (tvv rho) tv -> capN BX' A rho tv -> capN BX' A rho' tv'.
Proof using . clear_sec0. intros BX' A rho rho' tv tv' EQm H. unfold capN in *. rewrite (cntS_map rho rho' tv tv' EQm). exact H. Qed.
Lemma cntS_ext : forall rho rho' tv, (forall e, eval rho' e = eval rho e) -> cntS rho' tv = cntS rho tv.
Proof using . clear_sec0. intros rho rho' tv EV. apply cntS_map. apply map_ext. intros t. unfold tvv. rewrite !EV. reflexivity. Qed.
Lemma capN_ext : forall BX' A rho rho' tv, (forall e, eval rho' e = eval rho e) -> capN BX' A rho tv -> capN BX' A rho' tv.
Proof using . clear_sec0. intros BX' A rho rho' tv EV H. unfold capN in *. rewrite (cntS_ext rho rho' tv EV). exact H. Qed.

Lemma JA_tail_le : forall (PA' : AA -> Prop) BX' A rho rho' tv tv',
  cntS rho tv <= cntS rho' tv' -> PA' A /\ capK BX' A /\ capN BX' A rho tv -> PA' A /\ capK BX' A /\ capN BX' A rho' tv'.
Proof using . clear_sec0. intros PA' BX' A rho rho' tv tv' H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. unfold capN in *. lia. Qed.
Lemma JA_tail_ext : forall (PA' : AA -> Prop) BX' A rho rho' tv,
  (forall e, eval rho' e = eval rho e) -> PA' A /\ capK BX' A /\ capN BX' A rho tv -> PA' A /\ capK BX' A /\ capN BX' A rho' tv.
Proof using . clear_sec0. intros PA' BX' A rho rho' tv EV. apply JA_tail_le. rewrite (cntS_ext rho rho' tv EV). lia. Qed.

Lemma capN_le : forall BX' A A' rho rho' tv tv',
  small_live A' - small_live A <= cntS rho' tv' - cntS rho tv -> capN BX' A rho tv -> capN BX' A' rho' tv'.
Proof using . clear_sec0. intros BX' A A' rho rho' tv tv' H HC. unfold capN in *. lia. Qed.
Lemma capN_same : forall BX' A A' rho rho' tv tv',
  aa_live A' = aa_live A -> tvals rho' tv' = tvals rho tv -> capN BX' A rho tv -> capN BX' A' rho' tv'.
Proof using .
  clear_sec0. intros BX' A A' rho rho' tv tv' EL ET HC. unfold capN, cntS in *. rewrite (small_live_same A A' EL), ET. exact HC.
Qed.

Lemma prim_room_capN : forall d BX' A rho tv,
  BXok_d d BX' -> capN BX' A rho tv -> (length tv <= TVMAXn)%nat -> prim_room A.
Proof using .
  clear_sec0. intros d BX' A rho tv HB HC HL. exact (prim_room_of_capN d BX' A (cntS rho tv) HB HC (cntS_le_TVMAX rho tv HL)).
Qed.

Definition pclFA (a : Z) : Prop :=
  (T0 rho0 <= a < 2 ^ 47) \/ (in_rangesZ CST a /\ ~ errno_addrA a)
  \/ (exists b n, In (b, n) FB /\ b <= a < b + n)
  \/ (exists f s fl, In (f, s, fl) FF /\ (f <= a < f + s \/ a = fl)).

Definition pclSA (a : Z) : Prop := exists x, 0 <= x /\ (pclFA x \/ in_rangesZ XGL x) /\ a = Sh x.

Definition keptFA (m0 m1 : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> pclFA a \/ (pclSA a /\ m0 (Z_to_bv 64 a) <> None) -> m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a))
  /\ (forall a j, 0 <= a < 2 ^ 64 -> pclSA a -> 0 <= j < 8 -> m0 (word_byte a j) <> None -> m1 (word_byte a j) <> None).

Lemma keptFA_refl : forall m, keptFA m m.
Proof using . clear_sec0. intros m. split; intros; auto. Qed.
Lemma keptFA_trans : forall m0 m1 m2, keptFA m0 m1 -> keptFA m1 m2 -> keptFA m0 m2.
Proof using .
  clear_sec0. intros m0 m1 m2 [A1 A2] [B1 B2]. split.
  - intros a Ha Hp. pose proof (A1 a Ha Hp) as E1. rewrite <- E1. apply B1; [exact Ha|].
    destruct Hp as [Hp|[Hp Hd]]; [left; exact Hp | right; split; [exact Hp | rewrite E1; exact Hd]].
  - intros a j Ha Hp Hj H. apply B2; try assumption. apply A2; assumption.
Qed.
Lemma keptFA_eq_r : forall m0 m1 m2, keptFA m0 m1 -> (forall a, m2 a = m1 a) -> keptFA m0 m2.
Proof using .
  clear_sec0. intros m0 m1 m2 [A1 A2] E0. split.
  - intros a Ha Hp. rewrite E0. apply A1; assumption.
  - intros a j Ha Hp Hj H. rewrite E0. apply A2; assumption.
Qed.

Definition TPA (Ai : AA) : Prop := bv_unsigned (rw rho0 24%positive) = ag_tp (aa_geom Ai) /\ topG (aa_geom Ai) = T0 rho0.

Lemma TPA_kept : forall Ai A', aa_geom A' = aa_geom Ai -> TPA Ai -> TPA A'.
Proof using . clear. intros Ai A' HG [H1 H2]. unfold TPA. rewrite HG. split; assumption. Qed.
Lemma TPA_tp : forall Ai, TPA Ai -> bv_unsigned (rw rho0 24%positive) = ag_tp (aa_geom Ai).
Proof using . clear. intros Ai [H _]. exact H. Qed.
Lemma TPA_top : forall Ai, TPA Ai -> topG (aa_geom Ai) = T0 rho0.
Proof using . clear. intros Ai [_ H]. exact H. Qed.

Lemma T_of_TPA : forall rho Ai, agree_vals NP rho0 rho -> (V_TOP < NP)%positive -> TPA Ai -> T_ok rho (topG (aa_geom Ai)).
Proof using .
  clear. intros rho Ai [Hw _] Hn [_ Ht].
  split; [exact (eq_trans (f_equal bv_unsigned (eq_sym (Hw _ Hn))) (eq_sym Ht))|].
  pose proof (topG_range (aa_geom Ai)). lia.
Qed.

Definition JAi (nd : ndesc) (Ai : AA) (kc : Z) : jpredA :=
  fun rho tp tr md =>
    agree_vals NP rho0 rho /\ Kc tr md /\ AInv Ai rho tp md /\ TPA Ai /\ fbinA Ai /\ ffinA Ai
    /\ (tvinA Ai rho (nd_tv nd) /\ tvd rho (nd_tv nd) /\ tvz rho (nd_tv nd)) /\ frinA Ai rho (nd_fr nd)
    /\ keptFA (rm rho0) (rm rho) /\ P0f rho0
    /\ XA (nd_am nd) Ai rho (nd_tv nd) kc
    /\ BUD (nd_bd nd) (bxa (bx2 BX) (apot (nd_am nd) rho) kc) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho
    /\ PA Ai /\ capK BX Ai /\ capN BX Ai rho (nd_tv nd).

Definition JA (nd : ndesc) : jpredA := fun rho tp tr md => exists Ai kc, JAi nd Ai kc rho tp tr md.

Definition JAk (nd : ndesc) (Ai : AA) : jpredA := fun rho tp tr md => exists kc, JAi nd Ai kc rho tp tr md.

Lemma untracked_sub : forall rho tv tv' bn, (forall t, In t tv' -> In t tv) -> untracked rho tv bn -> untracked rho tv' bn.
Proof using .
  clear_sec0. intros rho tv tv' bn Hs H v Hv. unfold tvals in Hv. apply in_map_iff in Hv as (t & <- & Ht).
  apply H. unfold tvals. apply in_map. apply Hs. exact Ht.
Qed.
Lemma untracked_tv : forall rho tv bn, untracked rho tv bn <-> forall t, In t tv -> tnz rho t -> tvv rho t <> bn.
Proof using .
  clear_sec0. intros rho tv bn. unfold untracked, untrackedZ, tvals. split.
  - intros H t Ht Hnz. apply H; [apply in_map; exact Ht | exact Hnz].
  - intros H v Hv Hnz. apply in_map_iff in Hv as (t & <- & Ht). apply H; [exact Ht | exact Hnz].
Qed.

Lemma pclFA_caddrA : forall Ai a, fbinA Ai -> ffinA Ai -> TPA Ai -> pclFA a -> caddrA Ai None a.
Proof using .
  intros Ai a HB HFF HT [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & [Hr| ->])]]].
  - left. rewrite (TPA_top Ai HT). exact H.
  - right; left; exact (proj1 H).
  - right; right; left. exists b, n. split; [exact (HB _ Hin)|]. split; [discriminate | exact Hr].
  - right; right; right; left. exists f, s. split; [exact (proj1 (HFF _ _ _ Hin)) | exact Hr].
  - do 4 right. exists (f, s). destruct (HFF _ _ _ Hin) as [H1 H2]. auto.
Qed.

Definition fr_below (n : positive) (fr : list (sv * Z * sv)) : bool :=
  forallb (fun x => sv_below n (fst (fst x)) && sv_below n (snd x)) fr.

Definition nd_below (n : positive) (nd : ndesc) : bool :=
  tv_below n (nd_tv nd) && fr_below n (nd_fr nd) && bd_below n (nd_bd nd) && am_below n (nd_am nd) && (length (nd_tv nd) <=? TVMAXn)%nat.
Lemma nd_below_split : forall n nd, nd_below n nd = true ->
  tv_below n (nd_tv nd) = true /\ fr_below n (nd_fr nd) = true /\ bd_below n (nd_bd nd) = true /\ am_below n (nd_am nd) = true.
Proof using .
  clear_sec0. intros n nd H. unfold nd_below in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. auto.
Qed.
Lemma nd_below_len : forall n nd, nd_below n nd = true -> (length (nd_tv nd) <= TVMAXn)%nat.
Proof using . clear_sec0. intros n nd H. unfold nd_below in H. apply andb_prop in H as [_ H]. apply Nat.leb_le. exact H. Qed.
Lemma nd_below_intro : forall n nd, tv_below n (nd_tv nd) = true -> fr_below n (nd_fr nd) = true -> bd_below n (nd_bd nd) = true ->
  am_below n (nd_am nd) = true -> (length (nd_tv nd) <= TVMAXn)%nat -> nd_below n nd = true.
Proof using . clear_sec0. intros n nd H1 H2 H3 H4 H5. unfold nd_below. rewrite H1, H2, H3, H4. cbn [andb]. apply Nat.leb_le. exact H5. Qed.

Lemma frv_agree : forall n rho rho' x,
  agree_vals n rho rho' -> sv_below n (fst (fst x)) && sv_below n (snd x) = true -> frv rho' x = frv rho x /\ uval rho' (snd x) = uval rho (snd x).
Proof using .
  clear_sec0. intros n rho rho' x Hag Hb. apply andb_prop in Hb as [H1 H2]. unfold frv, uval.
  rewrite (eval_agree_vals n rho rho' _ Hag H1), (eval_agree_vals n rho rho' _ Hag H2). auto.
Qed.

Lemma frv_map_agree : forall n rho rho' fr,
  agree_vals n rho rho' -> fr_below n fr = true -> map (frv rho') fr = map (frv rho) fr.
Proof using .
  intros n rho rho' fr Hag Hb. apply map_ext_in. intros x Hx.
  destruct (frv_agree n rho rho' x Hag (proj1 (forallb_forall _ _) Hb x Hx)) as [E1 _]. exact E1.
Qed.
Lemma frinA_agree : forall Ai n rho rho' fr,
  agree_vals n rho rho' -> fr_below n fr = true -> frinA Ai rho fr -> frinA Ai rho' fr.
Proof using .
  intros Ai n rho rho' fr Hag Hb [H HC]. split.
  - unfold frinA0 in *. apply Forall_forall. intros x Hx.
    pose proof (proj1 (Forall_forall _ _) H x Hx) as (X1 & X2 & X3).
    destruct (frv_agree n rho rho' x Hag (proj1 (forallb_forall _ _) Hb x Hx)) as [E1 E2]. rewrite E1, E2. auto.
  - eapply frinA_rest_map; [reflexivity | eapply frv_map_agree; eauto | exact HC].
Qed.

Lemma tvinA_agree : forall Ai n rho rho' tv,
  agree_vals n rho rho' -> tv_below n tv = true -> tvinA Ai rho tv -> tvinA Ai rho' tv.
Proof using .
  intros Ai n rho rho' tv Hag Hb H. unfold tvinA in *. apply Forall_forall. intros t Ht.
  pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt.
  rewrite (tvv_agree n rho rho' t Hag Hbt). intros Hnz. apply (proj1 (tnz_agree n rho rho' t Hag Hbt)) in Hnz.
  exact (proj1 (Forall_forall _ _) H t Ht Hnz).
Qed.

Lemma untracked_agree : forall n rho rho' tv bn,
  agree_vals n rho rho' -> tv_below n tv = true -> untracked rho tv bn -> untracked rho' tv bn.
Proof using .
  clear_sec0. intros n rho rho' tv bn Hag Hb H. unfold untracked. rewrite (tvals_agree n rho rho' tv Hag Hb). exact H.
Qed.

Lemma XA_agree : forall am Ai n rho rho' tv kc,
  agree_vals n rho rho' -> (forall a, rm rho' a = rm rho a) -> am_below n am = true -> tv_below n tv = true ->
  XA am Ai rho tv kc -> XA am Ai rho' tv kc.
Proof using .
  intros am Ai n rho rho' tv kc Hag Hrm Hamb Hb HX. unfold XA in *.
  rewrite (am_eval_agree am n rho rho' Hag Hamb), (tvals_agree n rho rho' tv Hag Hb).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; exact Hrm). rewrite Erm. exact HX.
Qed.

Lemma am_svs_agree : forall am n rho rho', agree_vals n rho rho' -> am_below n am = true ->
  forall e, In e (am_svs am) -> eval rho' e = eval rho e.
Proof using .
  clear_sec0. intros [|hd p|hd nx cap sl|hd g] n rho rho' Hag Hb e He; cbn -[pl_below] in Hb, He.
  - destruct He.
  - destruct He as [<-|[]]. symmetry. apply (eval_agree_vals n); assumption.
  - apply andb_prop in Hb as [Hb Hsl]. apply andb_prop in Hb as [Hb Hc]. apply andb_prop in Hb as [Hh Hn].
    destruct He as [<-|[<-|[<-|He]]]; try (symmetry; apply (eval_agree_vals n); assumption).
    apply in_flat_map in He as (ps & Hps & He). pose proof (proj1 (forallb_forall _ _) Hsl ps Hps) as X. apply andb_prop in X as [X1 X2].
    destruct He as [<-|[<-|[]]]; symmetry; apply (eval_agree_vals n); assumption.
  - apply andb_prop in Hb as [Hh Hg]. destruct He as [<-|[<-|[]]]; symmetry; apply (eval_agree_vals n); assumption.
Qed.

Lemma apot_agree : forall am n rho rho',
  agree_vals n rho rho' -> (forall a, rm rho' a = rm rho a) -> am_below n am = true -> apot am rho' = apot am rho.
Proof using .
  clear_sec0. intros am n rho rho' Hag Hrm Hamb. unfold apot. rewrite (am_eval_agree am n rho rho' Hag Hamb).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; exact Hrm). rewrite Erm. reflexivity.
Qed.

Lemma BUD_bx_eq : forall b BX BX' V Km Kf rho, BX' = BX -> BUD b BX V Km Kf rho -> BUD b BX' V Km Kf rho.
Proof using . clear_sec0. intros; subst; assumption. Qed.

Hypothesis HKc : Kc_ok Kc.
Hypothesis ALA : alloc_lawsA segs AInv CST.

Lemma JAi_stable : forall n nd Ai kc rho rho' tp tr md md', (NP <= n)%positive -> nd_below n nd = true ->
  agree_below n rho rho' -> mat_equiv segs tp md md' -> JAi nd Ai kc rho tp tr md -> JAi nd Ai kc rho' tp tr md'.
Proof using ALA HKc.
  intros n nd Ai kc rho rho' tp tr md md' Hn Hb Hag Hme HJ.
  destruct (nd_below_split n nd Hb) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'. destruct Hag as (_ & _ & Hrm).
  assert (Hrm' : forall a, rm rho' a = rm rho a) by (intros a; symmetry; apply Hrm).
  split; [eapply agree_vals_trans; [exact Hav | eapply agree_vals_le; [exact Hn | exact Hav']]|].
  split; [eapply mat_blind_equiv; [apply Kc_ok_mat_blind; exact HKc | exact Hme | exact Hk]|].
  split; [eapply (law_mat _ _ _ ALA); [|exact Hme]; eapply (law_vars _ _ _ ALA); [exact HM|]; apply functional_extensionality; intros a; symmetry; apply Hrm|].
  split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [split; [eapply tvinA_agree; eauto | split; [eapply tvd_agree; eauto | eapply tvz_agree; eauto]]|].
  split; [eapply frinA_agree; eauto|].
  split; [eapply keptFA_eq_r; [exact HK | exact Hrm']|].
  split; [exact HP0|]. split; [eapply XA_agree; eauto|].
  split; [|split; [exact HPA|split; [exact HCK | exact (capN_agree n BX Ai rho rho' _ Hav' Hbt HCN)]]].
  rewrite (apot_agree (nd_am nd) n rho rho' Hav' Hrm' Hba). eapply BUD_agree; eauto.
Qed.

Lemma stableA_JA : forall n nd, (NP <= n)%positive -> nd_below n nd = true -> stableA segs n (JA nd).
Proof using ALA HKc.
  intros n nd Hn Hb rho rho' tp tr md md' Hag Hme (Ai & kc & HJ). exists Ai, kc. eapply JAi_stable; eauto.
Qed.

Definition ok_frameKA (ok : world -> Prop) : Prop := ok_frameA segs ok (liftKA Kc) /\ ok_pframeA segs ok (liftKA Kc).

Lemma ok_frameA_JA : forall ok nd, ok_frameKA ok -> ok_frameA segs ok (JA nd).
Proof using .
  intros ok nd H rho tp tr ms md msv' (Ai & kc & HJ) HMI Hh Hp Hs. eapply (proj1 H rho tp tr ms md msv'); eauto.
  exact (proj1 (proj2 HJ)).
Qed.

Lemma JA_Kc : forall nd rho tp tr md, JA nd rho tp tr md -> Kc tr md.
Proof using . intros nd rho tp tr md (Ai & kc & HJ). exact (proj1 (proj2 HJ)). Qed.

Fixpoint fr_sub_eqb (s : wsub) (fr fr' : list (sv * Z * sv)) : bool :=
  match fr, fr' with
  | [], [] => true
  | x :: r, x' :: r' => sv_eqb (sv_subst s (fst (fst x'))) (fst (fst x)) && Z.eqb (snd (fst x')) (snd (fst x))
                        && sv_eqb (sv_subst s (snd x')) (snd x) && fr_sub_eqb s r r'
  | _, _ => false
  end.

Lemma fr_sub_eqb_sound0 : forall s fr fr' rho Ai,
  fr_sub_eqb s fr fr' = true -> frinA0 Ai rho fr -> frinA0 Ai (rho_sub rho s) fr' /\ map (frv (rho_sub rho s)) fr' = map (frv rho) fr.
Proof using .
  intros s fr. induction fr as [|x r IH]; intros [|x' r'] rho Ai H HF; cbn in H; try discriminate.
  - split; constructor.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply sv_eqb_sound in H1. apply sv_eqb_sound in H3. apply Z.eqb_eq in H2.
    inversion HF as [|x0 r0 [X1 [X2 X3]] HR]; subst x0 r0.
    assert (E1 : frv (rho_sub rho s) x' = frv rho x).
    { unfold frv, uval. rewrite <- eval_subst, H1, H2. reflexivity. }
    assert (E2 : uval (rho_sub rho s) (snd x') = uval rho (snd x)).
    { unfold uval. rewrite <- eval_subst, H3. reflexivity. }
    destruct (IH r' rho Ai H4 HR) as [IH1 IH2].
    split; [constructor; [rewrite E1, E2; auto | exact IH1] | cbn [map]; rewrite E1, IH2; reflexivity].
Qed.
Lemma fr_sub_eqb_sound : forall s fr fr' rho Ai,
  fr_sub_eqb s fr fr' = true -> frinA Ai rho fr -> frinA Ai (rho_sub rho s) fr'.
Proof using .
  intros s fr fr' rho Ai H [HF HC]. destruct (fr_sub_eqb_sound0 s fr fr' rho Ai H HF) as [A B].
  split; [exact A | eapply frinA_rest_map; [reflexivity | exact B | exact HC]].
Qed.

Lemma tvinA_map : forall Ai rho rho' tv tv',
  map (tvv rho') tv' = map (tvv rho) tv ->
  (forall k t t', nth_error tv k = Some t -> nth_error tv' k = Some t' -> (tnz rho' t' <-> tnz rho t)) ->
  tvinA Ai rho tv -> tvinA Ai rho' tv'.
Proof using .
  intros Ai rho rho' tv. induction tv as [|t r IH]; intros [|t' r'] H Hz HN; cbn [map] in H; try discriminate.
  - constructor.
  - assert (H1 : tvv rho' t' = tvv rho t) by congruence. assert (H2 : map (tvv rho') r' = map (tvv rho) r) by congruence.
    inversion HN; subst. constructor.
    + intros Hnz'. rewrite H1. match goal with Ht : tnz rho t -> _ |- _ => apply Ht end.
      apply (proj1 (Hz 0%nat t t' eq_refl eq_refl)). exact Hnz'.
    + apply IH; [exact H2 | | assumption]. intros k. exact (Hz (S k)).
Qed.

Definition echeckJA (nodes : list (axst * ndesc)) (e : edgeA) : bool :=
  match nth_error nodes (ea_src e), nth_error nodes (ea_tgt e) with
  | Some (Ti, ndi), Some (Tj, ndj) =>
      wsub_id_below (ea_sub e) NP && (NP <=? ss_next (ax_S Ti))%positive && nd_below (ss_next (ax_S Ti)) ndi
      && tv_sub_eqb (ea_sub e) (nd_tv ndi) (nd_tv ndj)
      && fr_sub_eqb (ea_sub e) (nd_fr ndi) (nd_fr ndj)
      && bud_le (ss_facts (ax_S (ea_leaf e))) (bd_subst (ea_sub e) (nd_bd ndj)) (nd_bd ndi)
      && am_eqb (am_subst (ea_sub e) (nd_am ndj)) (nd_am ndi)
  | _, _ => false
  end.

Definition bud_le_pf (pf : pfacts) (facts : list sprop) (bto bfrom : list bitem) : bool :=
  bud_le_pos_lz pf facts bfrom bto bfrom ||| bud_pay_lz pf facts (SLit 0) 0 bfrom bto.
Lemma bud_le_pf_eq : forall facts bto bfrom, bud_le_pf (DigFastA.mk_pf_f facts) facts bto bfrom = bud_le facts bto bfrom.
Proof using . intros. reflexivity. Qed.
Definition echeckJA_pf (pf : pfacts) (nodes : list (axst * ndesc)) (e : edgeA) : bool :=
  match nth_error nodes (ea_src e), nth_error nodes (ea_tgt e) with
  | Some (Ti, ndi), Some (Tj, ndj) =>
      wsub_id_below (ea_sub e) NP && (NP <=? ss_next (ax_S Ti))%positive && nd_below (ss_next (ax_S Ti)) ndi
      && tv_sub_eqb (ea_sub e) (nd_tv ndi) (nd_tv ndj)
      && fr_sub_eqb (ea_sub e) (nd_fr ndi) (nd_fr ndj)
      && bud_le_pf pf (ss_facts (ax_S (ea_leaf e))) (bd_subst (ea_sub e) (nd_bd ndj)) (nd_bd ndi)
      && am_eqb (am_subst (ea_sub e) (nd_am ndj)) (nd_am ndi)
  | _, _ => false
  end.
Lemma echeckJA_pf_eq : forall nodes e, echeckJA_pf (DigFastA.mk_pf_f (ss_facts (ax_S (ea_leaf e)))) nodes e = echeckJA nodes e.
Proof using . intros. reflexivity. Qed.

Lemma XA_subst : forall s am Ai rho tv tv' kc,
  map (tvv (rho_sub rho s)) tv' = map (tvv rho) tv ->
  XA (am_subst s am) Ai rho tv kc -> XA am Ai (rho_sub rho s) tv' kc.
Proof using .
  intros s am Ai rho tv tv' kc M1 HX. unfold XA, tvals in *. rewrite M1, <- am_eval_subst. exact HX.
Qed.

Lemma apot_subst : forall s am rho, apot (am_subst s am) rho = apot am (rho_sub rho s).
Proof using . clear_sec0. clear HKc ALA. intros s am rho. unfold apot. rewrite am_eval_subst. reflexivity. Qed.

Lemma XA_frame : forall am Ai A2 rho rhoX tv tv' kc,
  XA am Ai rho tv kc ->
  (forall b n, In (b, n) (aa_live Ai) -> ~ In (b, n) FB -> untracked rho tv (b, n) -> In (b, n) (aa_live A2) /\ untracked rhoX tv' (b, n)) ->
  (forall b n z, In (b, n) (aa_live Ai) -> In (b, n) (aa_live A2) -> b <= z < b + n -> rm rhoX (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)) ->
  (forall b n a, In (b, n) (aa_live Ai) -> In (b, n) (aa_live A2) -> b <= a < b + n ->
       (rm rho (shadow_addr SHADOW_OFF a) <> None -> rm rhoX (shadow_addr SHADOW_OFF a) = rm rho (shadow_addr SHADOW_OFF a))
       /\ (forall j, 0 <= j < 8 -> rm rho (word_byte (SHADOW_OFF + a / 8) j) <> None -> rm rhoX (word_byte (SHADOW_OFF + a / 8) j) <> None)) ->
  (forall e, In e (am_svs am) -> eval rhoX e = eval rho e) ->
  (forall bn, In bn (aa_live A2) -> LARGE_MIN <= snd bn -> ~ In bn FB -> untracked rhoX tv' bn -> In bn (aa_live Ai) /\ untracked rho tv bn) ->
  XA am A2 rhoX tv' kc /\ apot am rhoX = apot am rho.
Proof using .
  intros am Ai A2 rho rhoX tv tv' kc HX HL HM HS HE HC. unfold XA, apot in *.
  assert (EA : am_eval rhoX am = am_eval rho am) by (apply am_eval_exteq; exact HE).
  rewrite EA. eapply (XAz_transport FB FB); [exact HX| | | |].
  - intros b n H1 H2 H3. destruct (HL b n H1 H2 H3) as [H4 H5]. auto.
  - intros b n z H1 H2 H3 Hz. apply (HM b n z H1 (proj1 (HL b n H1 H2 H3)) Hz).
  - intros b n a H1 H2 H3 Ha. apply (HS b n a H1 (proj1 (HL b n H1 H2 H3)) Ha).
  - intros bn H1 H2 H3 H4. destruct (HC bn H1 H2 H3 H4) as [G1 G2]. auto.
Qed.

Lemma JAi_transfer : forall s n facts ndi ndj Ai kc rho rho' tp tr md,
  wsub_id_below s NP = true -> (NP <= n)%positive -> nd_below n ndi = true ->
  tv_sub_eqb s (nd_tv ndi) (nd_tv ndj) = true -> fr_sub_eqb s (nd_fr ndi) (nd_fr ndj) = true ->
  bud_le facts (bd_subst s (nd_bd ndj)) (nd_bd ndi) = true ->
  am_subst s (nd_am ndj) = nd_am ndi ->
  agree_below n rho rho' -> Forall (holds rho') facts ->
  JAi ndi Ai kc rho tp tr md -> JAi ndj Ai kc (rho_sub rho' s) tp tr md.
Proof using ALA.
  intros s n facts ndi ndj Ai kc rho rho' tp tr md H1 H2 H3 H5 H6 H7 Ham Hag HF HJ.
  destruct (nd_below_split n ndi H3) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  pose proof (rho_sub_agree s NP rho' H1) as Hids.
  destruct (tv_sub_eqb_sound s _ _ rho' H5) as [M1 M2].
  assert (Hrm0 : forall a, rm rho' a = rm rho a).
  { intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm. }
  assert (Hrm : forall a, rm (rho_sub rho' s) a = rm rho a).
  { intros a. cbn [rho_sub rm]. apply Hrm0. }
  split; [|split; [exact Hk|split; [|split; [exact HT|split; [exact HB|split; [exact HFF|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [|split; [|split; [exact HPA|split; [exact HCK|]]]]]]]]]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact H2|exact Hav']|].
    apply agree_below_vals. exact Hids.
  - eapply (law_vars _ _ _ ALA); [exact HM|]. apply functional_extensionality. exact Hrm.
  - eapply tvinA_map; [exact M1 | exact M2 |]. eapply tvinA_agree; [exact Hav' | exact Hbt | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact Hbt | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact Hbt | exact HZ].
  - eapply fr_sub_eqb_sound; [exact H6|]. eapply frinA_agree; [exact Hav' | exact Hbf | exact HFR].
  - eapply keptFA_eq_r; [exact HK | exact Hrm].
  - eapply XA_subst; [exact M1 |]. rewrite Ham. eapply XA_agree; [exact Hav' | exact Hrm0 | exact Hba | exact Hbt | exact HXA].
  - rewrite <- apot_subst, Ham, (apot_agree (nd_am ndi) n rho rho' Hav' Hrm0 Hba).
    eapply BUD_transfer; [exact HF | exact H7 |]. eapply BUD_agree; [exact Hav' | exact Hbb | exact HBU].
  - eapply capN_map; [exact M1|]. exact (capN_agree n BX Ai rho rho' _ Hav' Hbt HCN).
Qed.

Lemma JA_transfer : forall s n facts ndi ndj rho rho' tp tr md,
  wsub_id_below s NP = true -> (NP <= n)%positive -> nd_below n ndi = true ->
  tv_sub_eqb s (nd_tv ndi) (nd_tv ndj) = true -> fr_sub_eqb s (nd_fr ndi) (nd_fr ndj) = true ->
  bud_le facts (bd_subst s (nd_bd ndj)) (nd_bd ndi) = true ->
  am_subst s (nd_am ndj) = nd_am ndi ->
  agree_below n rho rho' -> Forall (holds rho') facts ->
  JA ndi rho tp tr md -> JA ndj (rho_sub rho' s) tp tr md.
Proof using ALA.
  intros s n facts ndi ndj rho rho' tp tr md H1 H2 H3 H5 H6 H7 Ham Hag HF (Ai & kc & HJ). exists Ai, kc. eapply JAi_transfer; eauto.
Qed.

Definition nodeIA (n : axst * ndesc) : jnodeA := (fst n, JA (snd n)).

Lemma echeckJA_sound : forall nodes e, echeckJA nodes e = true -> edge_okA (map nodeIA nodes) e.
Proof using ALA.
  intros nodes e H Ti Tj Hi Hj rho rho' tp tr md Hag HJ HF.
  unfold echeckJA in H. rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [[Si ndi]|]; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [[Sj ndj]|]; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-. cbn [nodeIA fst snd] in *.
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H2. apply am_eqb_sound in H8.
  eapply JA_transfer; eauto.
Qed.

Lemma echeckJA_all : forall nodes es,
  forallb (echeckJA nodes) es = true -> Forall (edge_okA (map nodeIA nodes)) es.
Proof using ALA.
  intros nodes es H. apply Forall_forall. intros e He. apply echeckJA_sound.
  exact (proj1 (forallb_forall _ _) H e He).
Qed.

Definition jcertA_ref (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list (axst * ndesc)) : bool :=
  forallb (fun n => negb (ss_lenient (ax_S (fst n))) && nd_below (ss_next (ax_S (fst n))) (snd n) && (NP <=? ss_next (ax_S (fst n)))%positive) cutsD &&
  match cfg_edgesA segs fuel cutpcs g (map fst cutsD) (map fst exitsD) with
  | Some es => forallb (echeckJA (cutsD ++ exitsD)) es
  | None => false
  end.

Definition jcertA (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list (axst * ndesc)) : bool :=
  forallb (fun n => negb (ss_lenient (ax_S (fst n))) && nd_below (ss_next (ax_S (fst n))) (snd n) && (NP <=? ss_next (ax_S (fst n)))%positive) cutsD &&
  match cfg_edgesA_pf segs fuel cutpcs g (map fst cutsD) (map fst exitsD) with
  | Some eps => forallb (fun ep => echeckJA_pf (snd ep) (cutsD ++ exitsD) (fst ep)) eps
  | None => false
  end.
Lemma jcertA_ref_eq : forall fuel cutpcs g cutsD exitsD, jcertA fuel cutpcs g cutsD exitsD = jcertA_ref fuel cutpcs g cutsD exitsD.
Proof using .
  intros. unfold jcertA, jcertA_ref. rewrite cfg_edgesA_pf_eq.
  destruct (cfg_edgesA segs fuel cutpcs g (map fst cutsD) (map fst exitsD)) as [es|]; cbn [option_map]; [|reflexivity].
  rewrite (forallb_map_addpf (echeckJA (cutsD ++ exitsD)) (fun pf e => echeckJA_pf pf (cutsD ++ exitsD) e) es (echeckJA_pf_eq (cutsD ++ exitsD))). reflexivity.
Qed.

Lemma map_fst_nodeIA : forall l, map fst (map nodeIA l) = map fst l.
Proof using . clear_sec0. clear HKc ALA. intros l. rewrite map_map. apply map_ext. intros [a b]. reflexivity. Qed.

Theorem cfg_sound_JA : forall fuel cutpcs g cutsD exitsD ok (Q : assn),
  ok_frameKA ok ->
  jcertA fuel cutpcs g cutsD exitsD = true ->
  (forall X ndX rho tp, In (X, ndX) exitsD ->
     triple segs ok (SPA segs (JA ndX) X rho tp) (fun w => SPfamGTA segs (map nodeIA cutsD) w \/ Q w)) ->
  forall T ndT rho tp, In (T, ndT) cutsD -> triple segs ok (SPA segs (JA ndT) T rho tp) Q.
Proof using ALA HKc.
  intros fuel cutpcs g cutsD exitsD ok Q Hok Hc Hexits T ndT rho tp HinT.
  rewrite jcertA_ref_eq in Hc. unfold jcertA_ref in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edgesA segs fuel cutpcs g (map fst cutsD) (map fst exitsD)) as [es|] eqn:Hes; [|discriminate].
  apply (cfg_sound_genTA segs fuel cutpcs g (map nodeIA cutsD) (map nodeIA exitsD) es ok Q).
  - intros T' J' Hin. apply in_map_iff in Hin as ([S k] & Heq & _). cbn in Heq. injection Heq as <- <-.
    apply ok_frameA_JA. exact Hok.
  - intros T' J' Hin. apply in_map_iff in Hin as ([S k] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. cbn [fst snd] in X.
    apply andb_prop in X as [X Hn]. apply andb_prop in X as [_ Hb]. apply Pos.leb_le in Hn.
    apply stableA_JA; [exact Hn | exact Hb].
  - rewrite !map_fst_nodeIA. exact Hes.
  - rewrite <- map_app. apply echeckJA_all. exact Hc.
  - intros X JX rho' tp' Hin. apply in_map_iff in Hin as ([S k] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    exact (Hexits S k rho' tp' Hin).
  - exact (in_map nodeIA cutsD (T, ndT) HinT).
Qed.

Definition edescA : Type := (axst * ndesc * (Z * sv))%type.
Definition eda_state (n : edescA) : axst := fst (fst n).
Definition eda_nd (n : edescA) : ndesc := snd (fst n).
Definition eda_rank (n : edescA) : Z := fst (snd n).
Definition eda_var (n : edescA) : sv := snd (snd n).
Definition emeasA (n : edescA) (rho : valuation) : Z := eda_rank n * 2 ^ 64 + bv_unsigned (eval rho (eda_var n)).
Definition enodeIA (n : edescA) : enodeA := (eda_state n, JA (eda_nd n), emeasA n).
Definition edropA (n : edescA) : axst * ndesc := (eda_state n, eda_nd n).

Definition eecheckJA_ref (nodes : list edescA) (e : edgeA) : bool :=
  echeckJA (map edropA nodes) e &&
  match nth_error nodes (ea_src e), nth_error nodes (ea_tgt e) with
  | Some ni, Some nj =>
      sv_below (ss_next (ax_S (eda_state ni))) (eda_var ni) && (0 <=? eda_rank nj)
      && ((eda_rank nj <? eda_rank ni)
          || ((eda_rank nj =? eda_rank ni)
              && prove_sprop (ss_facts (ax_S (ea_leaf e))) (SPUlt (sv_subst (ea_sub e) (eda_var nj)) (eda_var ni))))
  | _, _ => false
  end.

Definition eecheckJA (nodes : list edescA) (e : edgeA) : bool :=
  if echeckJA (map edropA nodes) e then
    match nth_error nodes (ea_src e), nth_error nodes (ea_tgt e) with
    | Some ni, Some nj =>
        if sv_below (ss_next (ax_S (eda_state ni))) (eda_var ni) then
          if (0 <=? eda_rank nj) then
            if (eda_rank nj <? eda_rank ni) then true
            else if (eda_rank nj =? eda_rank ni)
                 then prove_sprop_pf (DigFastA.mk_pf_f (ss_facts (ax_S (ea_leaf e)))) (SPUlt (sv_subst (ea_sub e) (eda_var nj)) (eda_var ni))
                 else false
          else false
        else false
    | _, _ => false
    end
  else false.

Definition eecheckJA_pf (pf : pfacts) (nodes : list edescA) (e : edgeA) : bool :=
  if echeckJA_pf pf (map edropA nodes) e then
    match nth_error nodes (ea_src e), nth_error nodes (ea_tgt e) with
    | Some ni, Some nj =>
        if sv_below (ss_next (ax_S (eda_state ni))) (eda_var ni) then
          if (0 <=? eda_rank nj) then
            if (eda_rank nj <? eda_rank ni) then true
            else if (eda_rank nj =? eda_rank ni)
                 then prove_sprop_pf pf (SPUlt (sv_subst (ea_sub e) (eda_var nj)) (eda_var ni))
                 else false
          else false
        else false
    | _, _ => false
    end
  else false.
Lemma eecheckJA_pf_eq : forall nodes e, eecheckJA_pf (DigFastA.mk_pf_f (ss_facts (ax_S (ea_leaf e)))) nodes e = eecheckJA nodes e.
Proof using . intros. reflexivity. Qed.
Lemma eecheckJA_ref_eq : forall nodes e, eecheckJA nodes e = eecheckJA_ref nodes e.
Proof using .
  intros nodes e. unfold eecheckJA, eecheckJA_ref.
  destruct (echeckJA (map edropA nodes) e); [|reflexivity]. cbn [andb].
  destruct (nth_error nodes (ea_src e)) as [ni|]; [|reflexivity]. destruct (nth_error nodes (ea_tgt e)) as [nj|]; [|reflexivity].
  rewrite DigFastA.mk_pf_f_eq, prove_sprop_pf_eq.
  destruct (sv_below (ss_next (ax_S (eda_state ni))) (eda_var ni)); [|reflexivity]. destruct (0 <=? eda_rank nj); [|reflexivity].
  destruct (eda_rank nj <? eda_rank ni); [reflexivity|]. destruct (eda_rank nj =? eda_rank ni); reflexivity.
Qed.

Lemma eecheckJA_sound : forall nodes e, eecheckJA nodes e = true -> eedge_okA (map enodeIA nodes) e.
Proof using ALA.
  intros nodes e H ni nj Hi Hj rho rho' tp tr md Hag HJ HF.
  rewrite eecheckJA_ref_eq in H. unfold eecheckJA_ref in H. apply andb_prop in H as [HE H].
  rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (ea_src e)) as [di|] eqn:Ei; [|discriminate].
  destruct (nth_error nodes (ea_tgt e)) as [dj|] eqn:Ej; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [Hvb Hr0]. apply Z.leb_le in Hr0.
  pose proof (echeckJA_sound (map edropA nodes) e HE) as EOK.
  assert (Hi' : nth_error (map nodeIA (map edropA nodes)) (ea_src e) = Some (eda_state di, JA (eda_nd di))).
  { rewrite !nth_error_map, Ei. reflexivity. }
  assert (Hj' : nth_error (map nodeIA (map edropA nodes)) (ea_tgt e) = Some (eda_state dj, JA (eda_nd dj))).
  { rewrite !nth_error_map, Ej. reflexivity. }
  cbn [enodeIA ena_state ena_pred ena_meas fst snd] in *.
  split; [exact (EOK _ _ Hi' Hj' rho rho' tp tr md Hag HJ HF)|].
  unfold emeasA. rewrite <- eval_subst.
  pose proof (bv_urange (eval (rho) (eda_var di))) as R1.
  pose proof (bv_urange (eval rho' (sv_subst (ea_sub e) (eda_var dj)))) as R2.
  assert (EV : eval rho' (eda_var di) = eval rho (eda_var di)).
  { symmetry. eapply eval_agree_vals; [apply agree_below_vals; exact Hag | exact Hvb]. }
  apply orb_prop in Hdec as [Hlt|Heq].
  - apply Z.ltb_lt in Hlt. nia.
  - apply andb_prop in Heq as [Heq Hp]. apply Z.eqb_eq in Heq. rewrite Heq.
    pose proof (prove_sprop_sound rho' _ _ HF Hp) as X. cbn [holds] in X. rewrite EV in X. nia.
Qed.

Definition ejcertA_ref (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list edescA) : bool :=
  forallb (fun n => negb (ss_lenient (ax_S (eda_state n))) && nd_below (ss_next (ax_S (eda_state n))) (eda_nd n)
                    && (NP <=? ss_next (ax_S (eda_state n)))%positive && sv_below (ss_next (ax_S (eda_state n))) (eda_var n)) cutsE &&
  match cfg_edgesA segs fuel cutpcs g (map eda_state cutsE) (map eda_state exitsE) with
  | Some es => forallb (eecheckJA (cutsE ++ exitsE)) es
  | None => false
  end.

Definition ejcertA (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list edescA) : bool :=
  forallb (fun n => negb (ss_lenient (ax_S (eda_state n))) && nd_below (ss_next (ax_S (eda_state n))) (eda_nd n)
                    && (NP <=? ss_next (ax_S (eda_state n)))%positive && sv_below (ss_next (ax_S (eda_state n))) (eda_var n)) cutsE &&
  match cfg_edgesA_pf segs fuel cutpcs g (map eda_state cutsE) (map eda_state exitsE) with
  | Some eps => forallb (fun ep => eecheckJA_pf (snd ep) (cutsE ++ exitsE) (fst ep)) eps
  | None => false
  end.
Lemma ejcertA_ref_eq : forall fuel cutpcs g cutsE exitsE, ejcertA fuel cutpcs g cutsE exitsE = ejcertA_ref fuel cutpcs g cutsE exitsE.
Proof using .
  intros. unfold ejcertA, ejcertA_ref. rewrite cfg_edgesA_pf_eq.
  destruct (cfg_edgesA segs fuel cutpcs g (map eda_state cutsE) (map eda_state exitsE)) as [es|]; cbn [option_map]; [|reflexivity].
  rewrite (forallb_map_addpf (eecheckJA (cutsE ++ exitsE)) (fun pf e => eecheckJA_pf pf (cutsE ++ exitsE) e) es (eecheckJA_pf_eq (cutsE ++ exitsE))). reflexivity.
Qed.

Lemma map_eda_state : forall l, map ena_state (map enodeIA l) = map eda_state l.
Proof using . clear_sec0. clear HKc ALA. intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. Qed.

Theorem cfg_complete_JA : forall fuel cutpcs g cutsE exitsE (Q : world -> Prop),
  ejcertA fuel cutpcs g cutsE exitsE = true ->
  (forall X ndX rv rho tp, In (X, ndX, rv) exitsE ->
     etriple segs (SPA segs (JA ndX) X rho tp) (fun w => SPfamETA segs (map enodeIA cutsE) (emeasA (X, ndX, rv) rho) w \/ Q w)) ->
  forall T ndT rv rho tp, In (T, ndT, rv) cutsE -> etriple segs (SPA segs (JA ndT) T rho tp) Q.
Proof using ALA HKc.
  intros fuel cutpcs g cutsE exitsE Q Hc Hexits T ndT rv rho tp HinT.
  rewrite ejcertA_ref_eq in Hc. unfold ejcertA_ref in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edgesA segs fuel cutpcs g (map eda_state cutsE) (map eda_state exitsE)) as [es|] eqn:Hes; [|discriminate].
  apply (cfg_complete_genTA segs fuel cutpcs g (map enodeIA cutsE) (map enodeIA exitsE) es Q) with (n := enodeIA (T, ndT, rv)).
  - intros n Hin. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X.
    apply andb_prop in X as [X _]. apply andb_prop in X as [X Hn]. apply andb_prop in X as [_ Hb]. apply Pos.leb_le in Hn.
    cbn [enodeIA ena_state ena_pred fst snd]. apply stableA_JA; [exact Hn | exact Hb].
  - intros n rho1 rho2 Hin Hag. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. apply andb_prop in X as [_ Hvb].
    cbn [enodeIA ena_state ena_meas fst snd] in *. unfold emeasA.
    rewrite (eval_agree_vals _ rho1 rho2 _ (agree_below_vals _ _ _ Hag) Hvb). reflexivity.
  - rewrite !map_eda_state. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He. apply eecheckJA_sound. exact (proj1 (forallb_forall _ _) Hc e He).
  - intros X rho' tp' Hin. apply in_map_iff in Hin as ([[S k] r] & <- & Hin). cbn [enodeIA ena_state ena_pred ena_meas eda_state eda_nd fst snd].
    exact (Hexits S k r rho' tp' Hin).
  - exact (in_map enodeIA cutsE _ HinT).
Qed.

Lemma ejcertA_jcertA : forall fuel cutpcs g cutsE exitsE,
  ejcertA fuel cutpcs g cutsE exitsE = true -> jcertA fuel cutpcs g (map edropA cutsE) (map edropA exitsE) = true.
Proof using .
  clear HKc ALA. intros fuel cutpcs g cutsE exitsE H. rewrite ejcertA_ref_eq in H. rewrite jcertA_ref_eq. unfold ejcertA_ref in H. unfold jcertA_ref.
  apply andb_prop in H as [Hs H].
  assert (E1 : forall l, map fst (map edropA l) = map eda_state l).
  { intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. }
  rewrite !E1.
  destruct (cfg_edgesA segs fuel cutpcs g (map eda_state cutsE) (map eda_state exitsE)) as [es|]; [|discriminate].
  apply andb_true_intro. split.
  - apply forallb_forall. intros n Hin. apply in_map_iff in Hin as (d & <- & Hin).
    pose proof (proj1 (forallb_forall _ _) Hs d Hin) as X. apply andb_prop in X as [X _]. exact X.
  - rewrite <- map_app. apply forallb_forall. intros e He. pose proof (proj1 (forallb_forall _ _) H e He) as X.
    rewrite eecheckJA_ref_eq in X. unfold eecheckJA_ref in X. apply andb_prop in X as [X _]. exact X.
Qed.

Lemma reenter_cutJA : forall ok (cutsD : list (axst * ndesc)) (T : axst) nd (Q : assn) rho tp,
  In (T, nd) cutsD -> triple segs ok (SPA segs (JA nd) T rho tp) (fun w => SPfamGTA segs (map nodeIA cutsD) w \/ Q w).
Proof using .
  clear HKc ALA. intros ok cutsD T nd Q rho tp Hin. apply reenter_cutGTA. exact (in_map nodeIA cutsD (T, nd) Hin).
Qed.

Lemma ereenter_cutJA : forall (cutsE : list edescA) (T : axst) nd rv (Q : world -> Prop) (bound : Z) rho tp,
  In (T, nd, rv) cutsE -> 0 <= emeasA (T, nd, rv) rho < bound ->
  etriple segs (SPA segs (JA nd) T rho tp) (fun w => SPfamETA segs (map enodeIA cutsE) bound w \/ Q w).
Proof using .
  clear HKc ALA. intros cutsE T nd rv Q bound rho tp Hin Hm.
  apply (ereenter_cutETA segs (map enodeIA cutsE) (enodeIA (T, nd, rv)) Q bound rho tp (in_map enodeIA cutsE _ Hin) Hm).
Qed.

Lemma SPA_refacts_JA : forall (J : jpredA) rho (S : axst) f tp w,
  SPA segs J S rho tp w ->
  forallb (sprop_below (ss_next (ax_S S))) f = true ->
  (forall tr md, J rho tp tr md -> Forall (holds rho) (ss_facts (ax_S S)) -> Forall (holds rho) f) ->
  SPA segs J (ax_with_facts S f) rho tp w.
Proof using .
  clear HKc ALA. intros J rho S f tp w HS Hb Hf. apply SPA_refacts; [exact HS | exact Hb |].
  intros HF. destruct w as [tr [ms md]]. apply (Hf tr md (proj2 HS) HF).
Qed.

Definition tv_factsA (t : sv * sv) : list sprop :=
  [SPUle (fst t) (SLit atop_hi); SPUle (snd t) (SLit atop_hi);
   SPUle (SAlu ALU_ADD (fst t) (snd t)) (SLit atop_hi); SPUle (SLit 4096) (fst t); SPUle (SLit 1) (snd t);
   SPUle (SLit IMG_HI) (fst t);

   SPUle (fst t) (SVar V_TOP); SPUle (SAlu ALU_ADD (fst t) (snd t)) (SVar V_TOP)].

Lemma tv_factsA_hold : forall nd Ai kc rho tp tr md t, (V_TOP <? NP)%positive = true ->
  JAi nd Ai kc rho tp tr md -> In t (nd_tv nd) -> tnz rho t -> Forall (holds rho) (tv_factsA t).
Proof using ALA.
  intros nd Ai kc rho tp tr md [d sz] HNP (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _) Hin Hnz.
  apply Pos.ltb_lt in HNP. destruct (T_of_TPA rho Ai Hav HNP HT) as [ET0 _].
  assert (ET : bv_unsigned (rw rho V_TOP) = topG (aa_geom Ai)) by exact ET0.
  destruct (proj1 (Forall_forall _ _) HN _ Hin Hnz) as (Hpos & Hb & _). unfold tvv in Hb, Hpos. cbn [fst snd] in Hb, Hpos.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HG & _).
  destruct (HG _ _ Hb) as (G1 & G2 & G3 & G4 & G5). pose proof (topG_range (aa_geom Ai)) as TG.
  pose proof (bv_urange (eval rho d)) as R1. pose proof (bv_urange (eval rho sz)) as R2.
  unfold tv_factsA. cbn [fst snd]. unfold IMG_HI in *.
  repeat constructor; cbn [holds]; rewrite ?U_add, ?U_lit; unfold M64v; cbn [eval]; rewrite ?ET;
    rewrite ?(Z.mod_small 140737479966720) by lia; rewrite ?(Z.mod_small 4096) by lia; rewrite ?(Z.mod_small 1) by lia;
    rewrite ?(Z.mod_small 6578176) by lia; rewrite ?(Z.mod_small 6578176) by lia; try lia;
    rewrite Z.mod_small by lia; lia.
Qed.

Lemma JA_tv_facts : forall nd rho tp tr md t, (V_TOP <? NP)%positive = true ->
  JA nd rho tp tr md -> In t (nd_tv nd) -> tnz rho t -> Forall (holds rho) (tv_factsA t).
Proof using ALA. intros nd rho tp tr md t HNP (Ai & kc & H) Hin Hnz. eapply tv_factsA_hold; eauto. Qed.

Definition frozen (nd : ndesc) (rho : valuation) : jpredA := fun _ p t m => JA nd rho p t m.

Lemma frozen_stableA : forall n nd rho, nd_below NP nd = true -> stableA segs n (frozen nd rho).
Proof using ALA HKc.
  intros n nd rho Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable NP nd Ai kc rho rho tp tr md md'); [lia | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma frozen_ok_frameA : forall ok nd rho, ok_frameKA ok -> ok_frameA segs ok (frozen nd rho).
Proof using .
  clear HKc ALA. intros ok nd rho H r tp tr ms md msv' (Ai & kc & HJ) HMI Hh Hp Hs. eapply (proj1 H r tp tr ms md msv'); eauto.
  exact (proj1 (proj2 HJ)).
Qed.

Theorem pure_callA : forall ok (Cl Pre : axst) s R (Posts : list leafA) rho tp nd (Q : assn),
  (forall rho1 tp1, triple segs ok (SPA segs (frozen nd rho) Pre rho1 tp1) (LQA segs (frozen nd rho) (ss_next (ax_S Pre)) rho1 tp1 Posts)) ->
  entails_frA Cl Pre s = Some R ->
  call_checkA Cl Pre s R (map la_state Posts) = true ->
  (NP <=? ss_next (ax_S Cl))%positive = true -> nd_below (ss_next (ax_S Cl)) nd = true ->
  forallb (sprop_below (ss_next (ax_S Cl))) (ss_facts (ax_S Cl)) = true ->
  (forall L rho', In L Posts -> agree_below (ss_next (ax_S Cl)) rho rho' ->
     triple segs ok (SPA segs (JA nd) (ax_add_facts (ss_facts (ax_S Cl)) (import_postA s Pre (la_state L) Cl R)) rho' tp) Q) ->
  triple segs ok (SPA segs (JA nd) Cl rho tp) Q.
Proof using ALA HKc.
  intros ok Cl Pre s R Posts rho tp nd Q Hsum He Hchk Hnf Hnb Hfb Hcont. apply Pos.leb_le in Hnf.
  apply triple_factsA. intros HF.
  intros n HgQ w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  apply (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp n); [|split; [exact HsmPre|exact Hk]].
  intros w' (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  apply (Hcont L rho' HinL HAG n HgQ). split.
  - apply smatchA_add_facts; [exact HSP | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
  - destruct Hk' as (Ai & kc & HJ'). exists Ai, kc.
    eapply (JAi_stable (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ').
Qed.

Theorem pure_callA_ex : forall (Cl Pre : axst) s R (Posts : list leafA) rho tp nd (Q : world -> Prop),
  (forall rho1 tp1, etriple segs (SPA segs (frozen nd rho) Pre rho1 tp1) (LQA segs (frozen nd rho) (ss_next (ax_S Pre)) rho1 tp1 Posts)) ->
  entails_frA Cl Pre s = Some R ->
  call_checkA Cl Pre s R (map la_state Posts) = true ->
  (NP <=? ss_next (ax_S Cl))%positive = true -> nd_below (ss_next (ax_S Cl)) nd = true ->
  forallb (sprop_below (ss_next (ax_S Cl))) (ss_facts (ax_S Cl)) = true ->
  (forall L rho', In L Posts -> agree_below (ss_next (ax_S Cl)) rho rho' ->
     etriple segs (SPA segs (JA nd) (ax_add_facts (ss_facts (ax_S Cl)) (import_postA s Pre (la_state L) Cl R)) rho' tp) Q) ->
  etriple segs (SPA segs (JA nd) Cl rho tp) Q.
Proof using ALA HKc.
  intros Cl Pre s R Posts rho tp nd Q Hsum He Hchk Hnf Hnb Hfb Hcont. apply Pos.leb_le in Hnf.
  apply etriple_factsA. intros HF.
  intros w [Hsm Hk]. destruct w as [tr [ms md]].
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (HsmPre & _).
  destruct (Hsum (rho_sub (rho_absorb rho R (vms md tp ms)) s) tp _ (conj HsmPre Hk)) as (w' & Hsteps & HLQ).
  destruct HLQ as (L & rhoL & HinL & HagL & HsmL & Hk'). destruct w' as [tr' [ms' md']].
  cbn [w_tr w_cfg fst snd cfg_model] in Hk'.
  destruct (import_post_linkA segs Cl Pre s R (map la_state Posts) rho tp tr ms md tr' ms' md' (la_state L) rhoL tp He Hchk Hsm
              ltac:(apply in_map_iff; exists L; auto) HagL HsmL) as (rho' & HLK & HSP).
  pose proof (proj1 HLK) as HAG.
  destruct (Hcont L rho' HinL HAG (tr', mkCfg ms' md')) as (w'' & Hsteps' & HQ).
  { split.
    - apply smatchA_add_facts; [exact HSP | |].
      + apply Forall_forall. intros q Hq.
        apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' q (agree_below_vals _ _ _ HAG)).
        * exact (proj1 (forallb_forall _ _) Hfb q Hq).
        * exact (proj1 (Forall_forall _ _) HF q Hq).
      + apply forallb_forall. intros q Hq.
        eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
        unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
    - destruct Hk' as (Ai & kc & HJ'). exists Ai, kc.
      eapply (JAi_stable (ss_next (ax_S Cl)) nd Ai kc rho rho' tp tr' md' md' Hnf Hnb HAG (mat_equiv_refl _ _ _) HJ'). }
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

End Sum.

Section Posts.
Variable NP : positive.
Variable Kc : KcA.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : list (Z * Z * Z).
Variable BX : bxt.
Variable PA : AA -> Prop.

Definition JLA (nd : ndesc) : jpostA :=
  fun r0 _ rho tp tr md =>
    Kc tr md /\ exists Ai kc, AInv Ai rho tp md /\ TPA r0 Ai /\ fbinA FB Ai /\ ffinA FF Ai
                /\ (tvinA FB Ai rho (nd_tv nd) /\ tvd rho (nd_tv nd) /\ tvz rho (nd_tv nd)) /\ frinA FF Ai rho (nd_fr nd)
                /\ keptFA r0 FB FF (rm r0) (rm rho) /\ P0f r0
                /\ XA FB (nd_am nd) Ai rho (nd_tv nd) kc
                /\ BUD (nd_bd nd) (bxa (bx2 BX) (apot (nd_am nd) rho) kc) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho
                /\ PA Ai /\ capK BX Ai /\ capN BX Ai rho (nd_tv nd).

Lemma exit_postGA : forall ok rho0 tp0 nd Posts (P : axst) (X : assn),
  In (P, JLA nd) Posts ->
  forall rho tp, triple segs ok (SPA segs (JA NP Kc rho0 P0f FB FF BX PA nd) P rho tp) (fun w => X w \/ LQPA segs NP rho0 tp0 Posts w).
Proof using .
  intros ok rho0 tp0 nd Posts P X Hin. apply (exit_postPA segs ok _ NP rho0 tp0 Posts P (JLA nd) X Hin).
  intros rho tp tr md (Ai & kc & Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK & HP0 & HXA & HBU & HPA). split; [exact Hav|].
  split; [exact Hk|]. exists Ai, kc. repeat (split; [assumption|]). exact HPA.
Qed.

Lemma eexit_postGA : forall rho0 tp0 nd Posts (P : axst) (X : world -> Prop),
  In (P, JLA nd) Posts ->
  forall rho tp, etriple segs (SPA segs (JA NP Kc rho0 P0f FB FF BX PA nd) P rho tp) (fun w => X w \/ LQPA segs NP rho0 tp0 Posts w).
Proof using .
  intros rho0 tp0 nd Posts P X Hin. apply (eexit_postPA segs _ NP rho0 tp0 Posts P (JLA nd) X Hin).
  intros rho tp tr md (Ai & kc & Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK & HP0 & HXA & HBU & HPA). split; [exact Hav|].
  split; [exact Hk|]. exists Ai, kc. repeat (split; [assumption|]). exact HPA.
Qed.

Definition JA_pre (nd : ndesc) : jpredA := fun rho tp tr md => JLA nd rho tp rho tp tr md.

Lemma JA_pre_intro : forall rho0 nd S tp w,
  SPA segs (JA_pre nd) S rho0 tp w -> SPA segs (JA NP Kc rho0 P0f FB FF BX PA nd) S rho0 tp w.
Proof using .
  intros rho0 nd S tp w [Hsm (Hk & Ai & kc & HM & HT & HB & HFF & HN & HFR & HK & HP0 & HXA & HBU & HPA)]. split; [exact Hsm|].
  exists Ai, kc. split; [apply agree_vals_refl|]. repeat (split; [assumption|]). exact HPA.
Qed.

Lemma JA_pre_Kc : forall nd rho tp tr md, JA_pre nd rho tp tr md -> Kc tr md.
Proof using . intros nd rho tp tr md [Hk _]. exact Hk. Qed.

Lemma ok_frameA_JA_pre : forall ok nd, ok_frameA segs ok (liftKA Kc) -> ok_frameA segs ok (JA_pre nd).
Proof using .
  intros ok nd H rho tp tr ms md msv' HJ HMI Hh Hp Hs. eapply (H rho tp tr ms md msv'); eauto. exact (proj1 HJ).
Qed.
End Posts.

Lemma JA_reKc : forall NP (Kc Kc' : KcA) rho0 P0f FB FF BX PA nd rho tp tr md,
  (Kc tr md -> Kc' tr md) ->
  JA NP Kc rho0 P0f FB FF BX PA nd rho tp tr md -> JA NP Kc' rho0 P0f FB FF BX PA nd rho tp tr md.
Proof using .
  intros NP Kc Kc' rho0 P0f FB FF BX PA nd rho tp tr md HK (Ai & kc & Hav & Hk & REST).
  exists Ai, kc. split; [exact Hav|]. split; [exact (HK Hk)|]. exact REST.
Qed.
Lemma SPA_JA_reKc : forall NP (Kc Kc' : KcA) rho0 P0f FB FF BX PA nd S rho tp w,
  (forall tr md, Kc tr md -> Kc' tr md) ->
  SPA segs (JA NP Kc rho0 P0f FB FF BX PA nd) S rho tp w -> SPA segs (JA NP Kc' rho0 P0f FB FF BX PA nd) S rho tp w.
Proof using .
  intros NP Kc Kc' rho0 P0f FB FF BX PA nd S rho tp [tr [ms md]] HK [Hsm HJ]. split; [exact Hsm|].
  exact (JA_reKc NP Kc Kc' rho0 P0f FB FF BX PA nd rho tp tr md (HK tr md) HJ).
Qed.
Lemma JLA_reKc : forall (Kc Kc' : KcA) P0f FB FF BX PA nd r0 tp0 rho tp tr md,
  (Kc tr md -> Kc' tr md) ->
  JLA Kc P0f FB FF BX PA nd r0 tp0 rho tp tr md -> JLA Kc' P0f FB FF BX PA nd r0 tp0 rho tp tr md.
Proof using .
  intros Kc Kc' P0f FB FF BX PA nd r0 tp0 rho tp tr md HK (Hk & REST). split; [exact (HK Hk)|]. exact REST.
Qed.
Lemma JA_pre_reKc : forall (Kc Kc' : KcA) P0f FB FF BX PA nd rho tp tr md,
  (Kc tr md -> Kc' tr md) ->
  JA_pre Kc P0f FB FF BX PA nd rho tp tr md -> JA_pre Kc' P0f FB FF BX PA nd rho tp tr md.
Proof using . intros Kc Kc' P0f FB FF BX PA nd rho tp tr md HK H. exact (JLA_reKc Kc Kc' P0f FB FF BX PA nd rho tp rho tp tr md HK H). Qed.

Definition PTrue : AA -> Prop := fun _ => True.
Lemma JA_PA_weaken : forall NP Kc rho0 P0f FB FF BX (PA PA' : AA -> Prop) nd rho tp tr md,
  (forall A, PA A -> PA' A) ->
  JA NP Kc rho0 P0f FB FF BX PA nd rho tp tr md -> JA NP Kc rho0 P0f FB FF BX PA' nd rho tp tr md.
Proof using .
  intros NP Kc rho0 P0f FB FF BX PA PA' nd rho tp tr md HW (Ai & kc & HJ).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK & HP0 & HXA & HBU & HPA & HCK).
  exists Ai, kc. repeat (split; [assumption|]). split; [exact (HW _ HPA) | exact HCK].
Qed.
Lemma SPA_JA_PA_weaken : forall NP Kc rho0 P0f FB FF BX (PA PA' : AA -> Prop) nd S rho tp w,
  (forall A, PA A -> PA' A) ->
  SPA segs (JA NP Kc rho0 P0f FB FF BX PA nd) S rho tp w -> SPA segs (JA NP Kc rho0 P0f FB FF BX PA' nd) S rho tp w.
Proof using .
  intros NP Kc rho0 P0f FB FF BX PA PA' nd S rho tp [tr [ms md]] HW [Hsm HJ]. split; [exact Hsm|].
  exact (JA_PA_weaken NP Kc rho0 P0f FB FF BX PA PA' nd rho tp tr md HW HJ).
Qed.

Lemma JAi_proj_BUD : forall NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md,
  JAi NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md ->
  BUD (nd_bd nd) (bxa (bx2 BX) (apot (nd_am nd) rho) kc) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho /\ capK BX Ai /\ 0 <= kc.
Proof using .
  intros NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXA & HBU & _ & HCK & _).
  split; [exact HBU|]. split; [exact HCK|]. exact (XA_kc_nonneg _ _ _ _ _ _ HXA).
Qed.

Lemma JAi_proj_capN : forall NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md,
  JAi NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md -> capN BX Ai rho (nd_tv nd).
Proof using .
  intros NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCN). exact HCN.
Qed.
Lemma JAi_rebx : forall NP Kc rho0 P0f FB FF BX BX' PA nd bd' Ai kc rho tp tr md,
  (BUD (nd_bd nd) (bxa (bx2 BX) (apot (nd_am nd) rho) kc) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho -> capK BX Ai -> 0 <= kc ->
     BUD bd' (bxa (bx2 BX') (apot (nd_am nd) rho) kc) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho /\ capK BX' Ai) ->
  bxN BX <= bxN BX' ->
  JAi NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md ->
  JAi NP Kc rho0 P0f FB FF BX' PA (NDA (nd_tv nd) (nd_fr nd) bd' (nd_am nd)) Ai kc rho tp tr md.
Proof using .
  intros NP Kc rho0 P0f FB FF BX BX' PA nd bd' Ai kc rho tp tr md HI HNle HJ.
  destruct (JAi_proj_BUD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HBU0 & HCK0 & Hkc0). destruct (HI HBU0 HCK0 Hkc0) as [HBU' HCK'].
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HP0|]. split; [exact HXA|]. split; [exact HBU'|]. split; [exact HPA|]. split; [exact HCK'|].
  unfold capN in *. cbn [nd_tv]. lia.
Qed.
Definition bx_tight (BX : bxt) (nd : ndesc) (Ai : AA) (rho : valuation) : bxt :=
  mkBX (VMAX - aa_V Ai - bsumV (nd_bd nd) rho - fst (apot (nd_am nd) rho), bxK BX) (LARGE_MIN * large_live Ai - aa_V Ai) (bxN BX).
Lemma JAi_tight : forall NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md,
  BXnn BX ->
  JAi NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md ->
  JAi NP Kc rho0 P0f FB FF (bx_tight BX nd Ai rho) PA nd Ai kc rho tp tr md
  /\ bxV BX <= bxV (bx_tight BX nd Ai rho) /\ bxK (bx_tight BX nd Ai rho) = bxK BX
  /\ (LARGE_MIN * large_live Ai + bsumV (nd_bd nd) rho + fst (apot (nd_am nd) rho) <= SECCAP -> BXok (bx_tight BX nd Ai rho))
  /\ bxN (bx_tight BX nd Ai rho) = bxN BX.
Proof using .
  intros NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md [HV0 HK0] HJ.
  destruct (JAi_proj_BUD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HBU0 & HCK0 & Hkc0).
  pose proof (apot_range (nd_am nd) rho) as [[R1 _] [R2 _]].
  pose proof HBU0 as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2). unfold bxa in A1, A2, B1, B2. cbn [fst snd] in A1, A2, B1, B2.
  assert (HX1 : bxV BX <= bxV (bx_tight BX nd Ai rho)) by (unfold bx_tight, bxV; cbn [bx2 fst]; lia).
  destruct (bsum_nonneg (nd_bd nd) rho Hw Hnn) as [S1 S2].
  split; [|split; [exact HX1|split; [reflexivity|split; [|reflexivity]]]].
  - destruct nd as [tv fr bd am]. apply (JAi_rebx NP Kc rho0 P0f FB FF BX (bx_tight BX (NDA tv fr bd am) Ai rho) PA (NDA tv fr bd am) bd Ai kc rho tp tr md); [|cbn [bx_tight bxN]; lia|exact HJ].
    intros _ _ _. cbn [nd_bd nd_am] in *. split.
    + unfold BUD, bxa, bx_tight. cbn [bx2 fst snd nd_bd nd_am]. unfold bxK in *. repeat split; try assumption; lia.
    + unfold capK, bx_tight. cbn [bxS]. lia.
  - intros HS. unfold BXok, BXnn. unfold bx_tight in *. unfold bxV, bxK in *. cbn [bx2 bxS fst snd] in *. repeat split; lia.
Qed.
End WithSegs.
