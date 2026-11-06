(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Cf_iface.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac accok_fp_on ::= idtac.

Section CfKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_apart : forall Σ m p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> p <> q ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ m p n q k HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E). rewrite E in H2. apply in_app_or in H2. apply in_or_app.
  destruct H2 as [X|[X|X]]; [left; exact X| injection X as X1 X2; congruence | right; exact X].
Qed.

(* [comment removed for export] *)
Lemma removed_chunk_apart : forall Σ (m : mem) p n live0 usp a,
  ART RT Σ m -> In (p, n) (rt_live RT Σ) -> (forall e, In e live0 -> In e (rt_live RT Σ) /\ fst e <> p) ->
  rt_sp0 RT Σ - STACK_WIN <= usp ->
  aclient live0 (rt_frames RT Σ) usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ m p n live0 usp a HA INL SUB SPL Ha.
  pose proof (af_live_range RT AF Σ m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUB _ Hin) as [HinL NE]. cbn [fst] in NE.
    destruct (in_split _ _ INL) as (l1 & l2 & EL).
    assert (IN2 : In (p', n') (l1 ++ l2)).
    { rewrite EL in HinL. apply in_app_or in HinL. apply in_or_app. destruct HinL as [X|[X|X]]; [left; exact X| congruence| right; exact X]. }
    pose proof (af_live_disj RT AF Σ m p n p' n' l1 l2 HA EL IN2) as D. lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_frames_range RT AF Σ m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_fshadow_apart RT AF Σ m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma fresh_chunk_apart : forall Σ' (m : mem) l1 p n live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: live0 -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n live0 frs usp a HA LV FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    assert (Hin' : In (p', n') (l1 ++ live0)) by (apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 live0 HA LV Hin') as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma nodup_of_apart : forall l : list (Z * Z),
  (forall l1 p n l2 q k, l = l1 ++ (p, n) :: l2 -> In (q, k) (l1 ++ l2) -> p + n <= q \/ q + k <= p) ->
  (forall p n, In (p, n) l -> 0 < n) -> List.NoDup (map fst l).
Proof.
  induction l as [|[p n] l IH]; intros D P; cbn [map fst]; [constructor|]. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as ([q k] & E & Hq). cbn [fst] in E. subst q.
    pose proof (D [] p n l p k eq_refl Hq) as A. pose proof (P p n ltac:(left; reflexivity)). pose proof (P p k ltac:(right; exact Hq)). lia.
  - apply IH; [| intros q k Hq; apply (P q k); right; exact Hq].
    intros l1 q k l2 r j E Hr. apply (D ((p, n) :: l1) q k l2 r j); [rewrite E; reflexivity| right; exact Hr].
Qed.
Lemma live_nodup : forall Σ m, ART RT Σ m -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
  intros Σ m HA P. apply nodup_of_apart; [| exact P]. intros l1 p n l2 q k E Hq. exact (af_live_disj RT AF Σ m p n q k l1 l2 HA E Hq).
Qed.

(* [comment removed for export] *)
Lemma pix_obj_rc_agree : forall Σ (m m' : mem) frs sp live' pix v cv rc rc',
  ART RT Σ m -> pix_obj_rc (rt_live RT Σ) m pix v cv rc ->
  agree_on (fun a => aclient (rt_live RT Σ) frs sp a /\ outside [(pix + 20, pix + 24)] a) m m' ->
  rw_cells asegs m' pix (pix_cells_rc v rc') -> (forall e, In e (rt_live RT Σ) -> In e live') ->
  pix_obj_rc live' m' pix v cv rc'.
Proof using AF.
  intros Σ m m' frs sp live' pix v cv rc rc' HA (Hc & CH & HOK & HD & HCM) AG Hc' SUB.
  assert (CHM : forall p n, chunk (rt_live RT Σ) p n -> chunk live' p n) by (intros p n (I1 & R); exact (conj (SUB _ I1) R)).
  split; [exact Hc'|]. split; [exact (CHM _ _ CH)|]. split; [exact HOK|]. split.
  - destruct HD as [HD|(HD & R)]; [left; exact HD| right; exact (conj (CHM _ _ HD) R)].
  - destruct HCM as [HCM|(((pad & CC) & CH1 & CH2 & R1) & NE1 & R2)]; [left; exact HCM| right].
    split; [| exact (conj NE1 R2)]. split; [exists pad| exact (conj (CHM _ _ CH1) (conj (CHM _ _ CH2) R1))].
    apply (rw_cells_agree_nw asegs m m' _ _ CC). intros a Ha. cbn in Ha. apply AG.
    destruct CH1 as (I1 & _). destruct CH as (I0 & _).
    pose proof (live_apart Σ m (p_cmap v) 24 pix 64 HA I1 I0 NE1) as AP.
    split; [right; right; left; exists (p_cmap v), 24; split; [exact I1| lia]| cbn [outside]; split; [lia| exact I]].
Qed.
End CfKit.

(* [comment removed for export] *)
Lemma live_remove_in : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l /\ fst e <> p.
Proof.
  intros l p e He. split; [exact (live_remove_sub l p e He)|]. unfold live_remove in He.
  apply stdpp.base.list_elem_of_In in He. apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as [Hf _].
  intro E. rewrite E, Z.eqb_refl in Hf. exact Hf.
Qed.
Lemma cf_live_destroy_in : forall cf c live e, In e (cf_live_destroy cf c live) -> In e live /\ fst e <> cf.
Proof.
  intros cf c live e He. unfold cf_live_destroy in He. apply live_remove_in in He. destruct He as [He NE]. split; [| exact NE].
  repeat apply live_remove_sub in He. exact He.
Qed.
(* [comment removed for export] *)
Ltac lrm_sub_tac :=
  let e := fresh "e" in let He := fresh "He" in intros e He;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
  unfold cf_live_destroy in He;
  repeat first [ exact He | apply live_remove_sub in He ].

(* [comment removed for export] *)
Lemma chunk_in : forall live live' p n, chunk live p n -> In (p, n) live' -> chunk live' p n.
Proof. intros live live' p n (_ & R) H. exact (conj H R). Qed.

(* [comment removed for export] *)
Lemma keeps_live_sub : forall L L' (m m' : mem), keeps_live L m m' -> (forall e, In e L' -> In e L) -> keeps_live L' m m'.
Proof. intros L L' m m' K S b k Hin. exact (K b k (S _ Hin)). Qed.

(* [comment removed for export] *)
Lemma box_obj_keep : forall live live' (m m' : mem) b x y w h, box_obj live m b x y w h ->
  keeps_live [(b, 20)] m m' -> In (b, 20) live' -> box_obj live' m' b x y w h.
Proof.
  intros live live' m m' b x y w h (C & CH) K I1. split; [| exact (chunk_in _ _ _ _ CH I1)].
  apply (keeps_live_cells [(b, 20)] m m' b 20 b _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
Qed.

Lemma boxa_empty_keep : forall live live' (m m' : mem) ba nalloc arr, boxa_empty live m ba nalloc arr ->
  keeps_live [(ba, 24)] m m' -> In (ba, 24) live' -> In (arr, 8 * nalloc) live' -> boxa_empty live' m' ba nalloc arr.
Proof.
  intros live live' m m' ba nalloc arr ((pad & C) & CH1 & CH2 & R) K I1 I2.
  split; [exists pad| split; [exact (chunk_in _ _ _ _ CH1 I1)| split; [exact (chunk_in _ _ _ _ CH2 I2)| exact R]]].
  apply (keeps_live_cells [(ba, 24)] m m' ba 24 ba _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
Qed.

Lemma boxa_one_keep : forall live live' (m m' : mem) ba arr b x y w h, boxa_one live m ba arr b x y w h ->
  keeps_live [(ba, 24); (arr, 8); (b, 20)] m m' -> In (ba, 24) live' -> In (arr, 8) live' -> In (b, 20) live' ->
  boxa_one live' m' ba arr b x y w h.
Proof.
  intros live live' m m' ba arr b x y w h ((pad & C) & CH1 & CH2 & CA & BO & R) K I1 I2 I3.
  split; [exists pad| split; [exact (chunk_in _ _ _ _ CH1 I1)| split; [exact (chunk_in _ _ _ _ CH2 I2)| split; [| split; [| exact R]]]]].
  - apply (keeps_live_cells _ m m' ba 24 ba _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
  - apply (keeps_live_cells _ m m' arr 8 arr _ K ltac:(right; left; reflexivity)); [lia| cbn; lia| exact CA].
  - apply (box_obj_keep live live' m m' b x y w h BO); [| exact I3].
    apply (keeps_live_sub _ _ m m' K). intros e [E|[]]. right; right; left. exact E.
Qed.

Lemma parr16_obj_keep : forall live live' (m m' : mem) o nalloc arr, parr16_obj live m o nalloc arr ->
  keeps_live [(o, 16)] m m' -> In (o, 16) live' -> In (arr, 8 * nalloc) live' -> parr16_obj live' m' o nalloc arr.
Proof.
  intros live live' m m' o nalloc arr (C & CH1 & CH2 & R) K I1 I2.
  split; [| split; [exact (chunk_in _ _ _ _ CH1 I1)| split; [exact (chunk_in _ _ _ _ CH2 I2)| exact R]]].
  apply (keeps_live_cells _ m m' o 16 o _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
Qed.

Lemma pixa_obj_keep : forall live live' (m m' : mem) pa nalloc parr ba barr, pixa_obj live m pa nalloc parr ba barr ->
  keeps_live [(pa, 32); (ba, 24)] m m' -> In (pa, 32) live' -> In (parr, 8 * nalloc) live' -> In (ba, 24) live' -> In (barr, 8 * nalloc) live' ->
  pixa_obj live' m' pa nalloc parr ba barr.
Proof.
  intros live live' m m' pa nalloc parr ba barr ((pad & C) & CH1 & CH2 & BE & R) K I1 I2 I3 I4.
  split; [exists pad| split; [exact (chunk_in _ _ _ _ CH1 I1)| split; [exact (chunk_in _ _ _ _ CH2 I2)| split; [| exact R]]]].
  - apply (keeps_live_cells _ m m' pa 32 pa _ K ltac:(left; reflexivity)); [lia| cbn; lia| exact C].
  - apply (boxa_empty_keep live live' m m' ba nalloc barr BE); [| exact I3| exact I4].
    apply (keeps_live_sub _ _ m m' K). intros e [E|[]]. right; left. exact E.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma keeps_in : forall live (m m' : mem) L, keeps_live live m m' -> (forall e, In e L -> In e live) -> keeps_live L m m'.
Proof. intros live m m' L K S. exact (keeps_live_sub live L m m' K S). Qed.

Lemma boxa_one_keep_all : forall live (m m' : mem) ba arr b x y w h, boxa_one live m ba arr b x y w h -> keeps_live live m m' ->
  boxa_one live m' ba arr b x y w h.
Proof.
  intros live m m' ba arr b x y w h H K. pose proof H as (_ & (I1 & _) & (I2 & _) & _ & (_ & (I3 & _)) & _).
  apply (boxa_one_keep live live m m' ba arr b x y w h H); try assumption.
  apply (keeps_in live m m' _ K). intros e [E|[E|[E|[]]]]; subst e; assumption.
Qed.
Lemma parr16_obj_keep_all : forall live (m m' : mem) o nalloc arr, parr16_obj live m o nalloc arr -> keeps_live live m m' ->
  parr16_obj live m' o nalloc arr.
Proof.
  intros live m m' o nalloc arr H K. pose proof H as (_ & (I1 & _) & (I2 & _) & _).
  apply (parr16_obj_keep live live m m' o nalloc arr H); try assumption.
  apply (keeps_in live m m' _ K). intros e [E|[]]; subst e; assumption.
Qed.
Lemma pixa_obj_keep_all : forall live (m m' : mem) pa nalloc parr ba barr, pixa_obj live m pa nalloc parr ba barr -> keeps_live live m m' ->
  pixa_obj live m' pa nalloc parr ba barr.
Proof.
  intros live m m' pa nalloc parr ba barr H K. pose proof H as (_ & (I1 & _) & (I2 & _) & (_ & (I3 & _) & (I4 & _) & _) & _).
  apply (pixa_obj_keep live live m m' pa nalloc parr ba barr H); try assumption.
  apply (keeps_in live m m' _ K). intros e [E|[E|[]]]; subst e; assumption.
Qed.
Lemma pix_obj_rc_keep_all : forall live (m m' : mem) pix v cv rc, pix_obj_rc live m pix v cv rc -> keeps_live live m m' ->
  pix_obj_rc live m' pix v cv rc.
Proof.
  intros live m m' pix v cv rc (Hc & CH & HOK & HD & HCM) K.
  split; [| split; [exact CH| split; [exact HOK| split; [exact HD|]]]].
  - destruct CH as (Hin & _). apply (keeps_live_cells live m m' pix 64 pix _ K Hin); [lia| | exact Hc]. cbn. lia.
  - destruct HCM as [HCM|(HCM & R)]; [left; exact HCM| right]. split; [exact (cmap_obj_keep live m m' _ cv K HCM)| exact R].
Qed.

Lemma cf_obj_keep_all : forall live (m m' : mem) cf c, cf_obj live m cf c -> keeps_live live m m' -> cf_obj live m' cf c.
Proof.
  intros live m m' cf c ((pad & C) & CH & BO & NA & DN & PA & ND) K.
  split; [exists pad| split; [exact CH| split; [exact (boxa_one_keep_all _ _ _ _ _ _ _ _ _ _ BO K)|
          split; [exact (parr16_obj_keep_all _ _ _ _ _ _ NA K)| split; [exact (parr16_obj_keep_all _ _ _ _ _ _ DN K)|
          split; [exact (pixa_obj_keep_all _ _ _ _ _ _ _ _ PA K)| exact ND]]]]]].
  destruct CH as (Hin & _). apply (keeps_live_cells live m m' cf 88 cf _ K Hin); [lia| cbn; lia| exact C].
Qed.

(* [comment removed for export] *)
Lemma keeps_live_of_agree : forall lv frs sp W (m m' : mem) L,
  agree_on (fun a => aclient lv frs sp a /\ outside W a) m m' ->
  (forall e, In e L -> In e lv) -> (forall b k x, In (b, k) L -> b <= x < b + k -> outside W x) -> keeps_live L m m'.
Proof.
  intros lv frs sp W m m' L AG S O b k Hin a Ha. apply AG. split; [| exact (O b k _ Hin Ha)].
  right; right; left. exists b, k. split; [exact (S _ Hin)| exact Ha].
Qed.

(* [comment removed for export] *)
Definition neqp (x y : Z) : Prop := x <> y.
Ltac pose_neqs_one x l N :=
  lazymatch l with
  | nil => idtac
  | ?y :: ?l' =>
      assert (neqp x y) by (let E := fresh "E" in unfold neqp; intro E; apply N; symmetry in E; clear - E; cbn [In]; tauto);
      assert (neqp y x) by (let E := fresh "E" in unfold neqp; intro E; apply N; clear - E; cbn [In]; tauto);
      pose_neqs_one x l' N
  end.
Ltac pose_neqs ND :=
  lazymatch type of ND with
  | List.NoDup (?x :: ?l) =>
      let N := fresh "NI" in let ND' := fresh "ND" in
      pose proof (proj1 (List.NoDup_cons_iff x l) ND) as [N ND'];
      pose_neqs_one x l N; clear N; pose_neqs ND'; clear ND'
  | List.NoDup nil => idtac
  end.
Ltac neq_tac :=
  lazymatch goal with
  | |- ?a <> ?b => first [ match goal with H : neqp a b |- _ => exact H end | lia ]
  end.

(* [comment removed for export] *)
Definition apartp (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

(* [comment removed for export] *)
Ltac kl_out Hx :=
  cbn [outside]; repeat split; try exact I;
  lazymatch type of Hx with ?q <= _ < _ =>
    repeat match goal with A : apartp q _ _ _ |- _ => unfold apartp in A end end;
  let HH := fresh "HH" in intro HH; lia.
Ltac kl_side_fp AG :=
  eapply keeps_live_of_agree;
  [ exact AG
  | let e := fresh "e" in let He := fresh "He" in intros e He; cbn [In] in He;
    repeat (destruct He as [He|He]; [subst e; solve [in_live_tac]|]); destruct He
  | let b := fresh "b" in let k := fresh "k" in let x := fresh "x" in let Hi := fresh "Hi" in let Hx := fresh "Hx" in
    intros b k x Hi Hx; cbn [In] in Hi;
    repeat (destruct Hi as [Hi|Hi]; [injection Hi as <- <-; kl_out Hx|]); destruct Hi ].
(* [comment removed for export] *)
Ltac kl_side AG :=
  lazymatch type of AG with
  | agree_on (aclient ?lv ?frs ?sp) ?ma ?mb =>
      let AG' := fresh "AGW" in
      assert (AG' : agree_on (fun a => aclient lv frs sp a /\ outside [] a) ma mb)
        by (let a := fresh "a" in let H := fresh "H" in intros a H; exact (AG a (proj1 H)));
      kl_side_fp AG'
  | _ => kl_side_fp AG
  end.
(* [comment removed for export] *)
Ltac obj_keep RT S H AG :=
  lazymatch type of H with
  | boxa_one ?lv ?m ?ba ?arr ?b ?x ?y ?w ?h =>
      eapply (boxa_one_keep lv (rt_live RT S) m _ ba arr b x y w h) in H; [ | kl_side AG | solve [in_live_tac] ..]
  | boxa_empty ?lv ?m ?ba ?na ?arr =>
      eapply (boxa_empty_keep lv (rt_live RT S) m _ ba na arr) in H; [ | kl_side AG | solve [in_live_tac] ..]
  | parr16_obj ?lv ?m ?o ?na ?arr =>
      eapply (parr16_obj_keep lv (rt_live RT S) m _ o na arr) in H; [ | kl_side AG | solve [in_live_tac] ..]
  | pixa_obj ?lv ?m ?pa ?na ?parr ?ba ?barr =>
      eapply (pixa_obj_keep lv (rt_live RT S) m _ pa na parr ba barr) in H; [ | kl_side AG | solve [in_live_tac] ..]
  end.
(* [comment removed for export] *)
Ltac lvp_tac LVP :=
  let p := fresh "p" in let n := fresh "n" in let Hin := fresh "Hin" in intros p n Hin;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in Hin end;
  repeat apply live_remove_sub in Hin; exact (LVP _ _ Hin).

(* [comment removed for export] *)
Ltac local_acc FSH fr idx off FR64 NAME :=
  let T := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let B := fresh "B" in
  pose proof FSH as T; split_at T idx T2; split_at T2 1%nat T3; clear T T3;
  lazymatch type of T2 with rw_cells _ ?mm _ _ =>
    assert (NAME : acc asegs mm (fr + off) 4)
      by (destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + off) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
          let c := eval vm_compute in (2147450880 + Z.of_nat idx) in
          replace (shad (fr + off)) with (fr / 8 + c) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          exact B) end; clear T2.

(* [comment removed for export] *)
Lemma v_divw_1 : forall w, 0 <= w < 2^31 -> v_divw (Z_to_bv 64 w) (Z_to_bv 64 1) = Z_to_bv 64 w.
Proof.
  intros w Hw. unfold v_divw. rewrite !unsigned_lit by lia.
  change (bv_wrap 32 1) with 1. change (1 =? 0) with false. cbv iota. change (bv_swrap 32 1) with 1.
  rewrite (bv_swrap_small 32 w) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite Z.quot_1_r. rewrite (bv_swrap_small 32 w) by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac kl_side_mu MU side :=
  let b := fresh "b" in let k := fresh "k" in let Hi := fresh "Hi" in let a := fresh "a" in let Ha := fresh "Ha" in
  intros b k Hi a Ha; apply MU; cbn [In] in Hi;
  repeat (destruct Hi as [Hi|Hi]; [injection Hi as <- <-; side Ha|]); destruct Hi.
Ltac obj_keep_mu RT S H MU side :=
  lazymatch type of H with
  | boxa_one ?lv ?m ?ba ?arr ?b ?x ?y ?w ?h =>
      eapply (boxa_one_keep lv (rt_live RT S) m _ ba arr b x y w h) in H; [ | kl_side_mu MU side | solve [in_live_tac] ..]
  | boxa_empty ?lv ?m ?ba ?na ?arr =>
      eapply (boxa_empty_keep lv (rt_live RT S) m _ ba na arr) in H; [ | kl_side_mu MU side | solve [in_live_tac] ..]
  | parr16_obj ?lv ?m ?o ?na ?arr =>
      eapply (parr16_obj_keep lv (rt_live RT S) m _ o na arr) in H; [ | kl_side_mu MU side | solve [in_live_tac] ..]
  | pixa_obj ?lv ?m ?pa ?na ?parr ?ba ?barr =>
      eapply (pixa_obj_keep lv (rt_live RT S) m _ pa na parr ba barr) in H; [ | kl_side_mu MU side | solve [in_live_tac] ..]
  end.

(* [comment removed for export] *)
Lemma lrm_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.
Lemma lrm_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l. induction l as [|e l IH]; intros H; [reflexivity|]. rewrite lrm_cons.
  replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; apply H; left; reflexivity).
  f_equal. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma cf_live_roundtrip : forall cf c (L : list (Z * Z)),
  List.NoDup (map fst (cf_live cf c [])) -> (forall e, In e L -> ~ In (fst e) (map fst (cf_live cf c []))) ->
  cf_live_destroy cf c (cf_live cf c L) = L.
Proof.
  intros cf c L ND FR. cbn [map fst cf_live] in ND, FR. pose_neqs ND.
  assert (FRP : forall p, In p [cf_pbarr c; cf_pba c; cf_parr c; cf_pixa c; cf_dnarr c; cf_dnaa c; cf_naarr c; cf_naa c; cf; cf_box c;
                                 cf_barr c; cf_boxas c] -> live_remove p L = L).
  { intros p Hp. apply lrm_notin. intros e He E. apply (FR e He). rewrite E. exact Hp. }
  unfold cf_live_destroy, cf_live.
  repeat (rewrite lrm_cons; cbn [fst];
          repeat match goal with
          | |- context [?x =? ?x] => rewrite (Z.eqb_refl x)
          | |- context [?x =? ?y] => replace (x =? y) with false by (symmetry; apply Z.eqb_neq; neq_tac)
          end; cbv iota).
  repeat (rewrite FRP by (cbn [In]; tauto)). reflexivity.
Qed.
