(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutAuto CutLib CutHeap.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CH2.
Definition model_ok (model : Model) : Prop := m_halted model = None /\ m_vm_lazy model = [] /\ m_vm_materialized model = [].
Definition mem := (word -> option byte).

Definition den (E : env) (bl : CA.blocks) : list (Z * Z) :=
  map (fun b : expr * expr => (bv_unsigned (edenot E (fst b)), bv_unsigned (edenot E (snd b)))) bl.

Lemma den_agree : forall b E E' bl, env_agree b E E' ->
  forallb (fun x : expr * expr => (APC.expr_vars_lt b (fst x) && APC.expr_vars_lt b (snd x))%bool) bl = true -> den E' bl = den E bl.
Proof.
  intros b E E' bl Hag H. unfold den. apply map_ext_in. intros [x y] Hin. rewrite forallb_forall in H. specialize (H _ Hin).
  cbn [fst snd] in *. apply andb_prop in H as [H1 H2].
  rewrite <- (SR.edenot_agree_AP b E E' x Hag H1), <- (SR.edenot_agree_AP b E E' y Hag H2). reflexivity.
Qed.

Lemma lb_remove_notin : forall A LB, ~ In A (map fst LB) -> lb_remove A LB = LB.
Proof.
  intros A LB. induction LB as [|b r IH]; intros H; [reflexivity|]. cbn [lb_remove].
  destruct (Z.eqb_spec (fst b) A) as [e|ne]; [exfalso; apply H; left; exact e|].
  rewrite IH; [reflexivity|]. intros X. apply H. right. exact X.
Qed.
Lemma lb_remove_app : forall A L1 L2, In A (map fst L1) -> lb_remove A (L1 ++ L2) = lb_remove A L1 ++ L2.
Proof.
  intros A L1 L2. induction L1 as [|b r IH]; intros H; [destruct H|]. cbn [lb_remove app].
  destruct (Z.eqb_spec (fst b) A) as [e|ne]; [reflexivity|].
  destruct H as [H|H]; [contradiction|]. rewrite (IH H). reflexivity.
Qed.

Lemma nodup_app_disj : forall (l1 l2 : list Z) x, base.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1 l2 x H H1 H2. apply list_relations.list.NoDup_app in H as (_ & H & _).
  apply (H x); apply list_elem_of_In; assumption.
Qed.

Section LeavesAll.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable P : nat -> CC.cutpoint -> nat -> SR.post_spec -> CC.tag -> bool.
Fixpoint leaves_go (i : nat) (c : CC.cutpoint) (k : nat) (pss : list SR.post_spec) (tags : list CC.tag) : bool :=
  match pss, tags with
  | ps :: pr, t :: tr => (P i c k ps t && leaves_go i c (S k) pr tr)%bool
  | [], [] => true
  | _, _ => false
  end.
Fixpoint cuts_go (i : nat) (cps : list CC.cutpoint) (tgs : list (list CC.tag)) : bool :=
  match cps, tgs with
  | c :: cr, t :: tr => (leaves_go i c 0 (CC.cp_PSS c) t && cuts_go (S i) cr tr)%bool
  | [], [] => true
  | _, _ => false
  end.
Definition leaves_all : bool := cuts_go 0 CPS TAGS.

Lemma leaves_go_sound : forall i c pss tags k0 k ps t, leaves_go i c k0 pss tags = true ->
  nth_error pss k = Some ps -> nth_error tags k = Some t -> P i c (k0 + k) ps t = true.
Proof.
  intros i c pss. induction pss as [|p pr IH]; intros tags k0 k ps t H Hps Ht; [destruct k; discriminate|].
  destruct tags as [|t0 tr]; [discriminate|]. cbn [leaves_go] in H. apply andb_prop in H as [H1 H2].
  destruct k as [|k]; cbn [nth_error] in *.
  - injection Hps as <-. injection Ht as <-. rewrite Nat.add_0_r. exact H1.
  - replace (k0 + S k)%nat with (S k0 + k)%nat by lia. exact (IH tr (S k0) k ps t H2 Hps Ht).
Qed.
Lemma cuts_go_sound : forall cps tgs i0 i c tags k ps t, cuts_go i0 cps tgs = true ->
  nth_error cps i = Some c -> nth_error tgs i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some t ->
  P (i0 + i) c k ps t = true.
Proof.
  intros cps. induction cps as [|c0 cr IH]; intros tgs i0 i c tags k ps t H Hc Htg Hps Ht; [destruct i; discriminate|].
  destruct tgs as [|t0 tr]; [discriminate|]. cbn [cuts_go] in H. apply andb_prop in H as [H1 H2].
  destruct i as [|i]; cbn [nth_error] in *.
  - injection Hc as <-. injection Htg as <-. rewrite Nat.add_0_r. exact (leaves_go_sound _ _ _ _ 0%nat k ps t H1 Hps Ht).
  - replace (i0 + S i)%nat with (S i0 + i)%nat by lia. exact (IH tr (S i0) i c tags k ps t H2 Hc Htg Hps Ht).
Qed.
Lemma leaves_all_nth : leaves_all = true -> forall i c tags k ps t,
  nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some t ->
  P i c k ps t = true.
Proof. intros H i c tags k ps t Hc Htg Hps Ht. exact (cuts_go_sound CPS TAGS 0%nat i c tags k ps t H Hc Htg Hps Ht). Qed.

Definition is_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : Prop :=
  exists tags, nth_error CPS i = Some c /\ nth_error TAGS i = Some tags /\ nth_error (CC.cp_PSS c) k = Some ps /\ nth_error tags k = Some t.

Lemma leaves_all_sound : leaves_all = true -> forall i c k ps t, is_leaf i c k ps t -> P i c k ps t = true.
Proof. intros H i c k ps t (tags & Hc & Htg & Hps & Ht). exact (leaves_all_nth H i c tags k ps t Hc Htg Hps Ht). Qed.

End LeavesAll.

Section Heap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Lemma nodup_fst_eq : forall (LB : list (Z * Z)) b b', base.NoDup (map fst LB) -> In b LB -> In b' LB -> fst b = fst b' -> b = b'.
Proof.
  induction LB as [|x r IH]; intros b b' Hnd Hb Hb' He; [destruct Hb|].
  cbn [map] in Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hni Hnd].
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
  - reflexivity.
  - exfalso. apply Hni. apply list_elem_of_In. rewrite He. apply in_map. exact Hb'.
  - exfalso. apply Hni. apply list_elem_of_In. rewrite <- He. apply in_map. exact Hb.
  - exact (IH b b' Hnd Hb Hb' He).
Qed.
Lemma lb_remove_fst_notin : forall A (LB : list (Z * Z)), base.NoDup (map fst LB) -> ~ In A (map fst (lb_remove A LB)).
Proof.
  intros A LB. induction LB as [|x r IH]; intros Hnd; [intros []|].
  cbn [map] in Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hni Hnd]. cbn [lb_remove].
  destruct (Z.eqb_spec (fst x) A) as [e|ne].
  - subst A. intros H. apply Hni. apply list_elem_of_In. exact H.
  - cbn [map]. intros [H|H]; [exact (ne H) | exact (IH Hnd H)].
Qed.
Lemma lb_remove_nodup : forall A (LB : list (Z * Z)), base.NoDup (map fst LB) -> base.NoDup (map fst (lb_remove A LB)).
Proof.
  intros A LB. induction LB as [|x r IH]; intros Hnd; [exact Hnd|].
  cbn [map] in Hnd. pose proof Hnd as Hnd0. apply list_relations.list.NoDup_cons in Hnd as [Hni Hnd]. cbn [lb_remove].
  destruct (Z.eqb (fst x) A); [exact Hnd|]. cbn [map]. apply list_relations.list.NoDup_cons. split; [|exact (IH Hnd)].
  intros H. apply Hni. apply list_elem_of_In in H. apply list_elem_of_In. apply in_map_iff in H as (y & Hy & Hin).
  apply in_map_iff. exists y. split; [exact Hy | exact (L5C.in_lb_remove A y r Hin)].
Qed.
Lemma heap_own_front : forall LB cr M VM A n, hi_heap HI LB cr M VM -> In (A, n) LB -> hi_heap HI ((A, n) :: lb_remove A LB) cr M VM.
Proof.
  intros LB cr M VM A n HH Hin. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & Hnd & _).
  apply (hio_perm L SCFG HI HIok LB _ cr M VM HH).
  - intros b. split.
    + intros Hb. destruct (Z.eq_dec (fst b) A) as [e|ne].
      * left. symmetry. apply (nodup_fst_eq LB b (A, n) Hnd Hb Hin). exact e.
      * right. destruct b as [B m]. exact (L5C.in_lb_remove_neq A B m LB Hb ne).
    + intros [<-|Hb]; [exact Hin | exact (L5C.in_lb_remove A b LB Hb)].
  - cbn [map fst]. apply list_relations.list.NoDup_cons. split; [|exact (lb_remove_nodup A LB Hnd)].
    intros H. apply list_elem_of_In in H. exact (lb_remove_fst_notin A LB Hnd H).
Qed.
Lemma heap_own_back : forall LB cr M VM A n, hi_heap HI ((A, n) :: lb_remove A LB) cr M VM -> In (A, n) LB -> base.NoDup (map fst LB) -> hi_heap HI LB cr M VM.
Proof.
  intros LB cr M VM A n HH Hin Hnd. apply (hio_perm L SCFG HI HIok _ LB cr M VM HH); [|exact Hnd].
  intros b. split.
  - intros [<-|Hb]; [exact Hin | exact (L5C.in_lb_remove A b LB Hb)].
  - intros Hb. destruct (Z.eq_dec (fst b) A) as [e|ne].
    + left. apply (nodup_fst_eq LB (A, n) b Hnd Hin Hb). symmetry. exact e.
    + right. destruct b as [B m]. exact (L5C.in_lb_remove_neq A B m LB Hb ne).
Qed.

Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000.
Hypothesis LY_errno : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L.
Hypothesis LY_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a.
Hypothesis LY_stack : 0 <= hl_stack L.

Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.

Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + SCR <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis HSTK_eq : hl_stack L = CH.hd_hstk d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).

Definition wclient (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ((sp0 <= a < hl_sptop L) \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ hl_alloc_ro L a /\ ~ in_errno L a)).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> wclient a.

Definition sclient (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ((sp0 <= a) \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a) \/ in_block LBrest a).

Definition client0 (a : Z) : Prop := client_addr L LBrest sp0 0 a /\ ~ in_errno L a.

Definition cur (i : nat) (E : env) : list (Z * Z) := den E (nth i BLS []) ++ LBrest.

Definition heap_amb (i : nat) (E : env) (M : mem) (model : Model) : Prop :=
  model_ok model /\ model_but_vm model0 model /\ env_agree NF E0 E /\
  (exists cr, hi_heap HI (cur i E) cr M (m_vmmaps model) /\ Cred i E cr) /\
  (forall a, L5C.kept L LBrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) /\
  (forall a, 0 <= a < 2 ^ 64 -> client0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None).

Lemma heap_amb_model : forall i E M model, heap_amb i E M model -> m_halted model = None /\ m_vm_lazy model = [].
Proof. intros i E M model ((H1 & H2 & _) & _). split; assumption. Qed.

Definition foot_sem (LBown : list (Z * Z)) (a : Z) : Prop :=
  (sp0 - SCR <= a < sp0) \/ (exists r, In r W /\ L5.in_rng r a) \/ in_block LBown a.

Lemma ceil_lo : 0x7fff7f800000 <= hl_ceil L.
Proof. destruct STK as (_ & _ & _ & H & _). lia. Qed.

Lemma blocks_facts : forall LBown cr M VM, hi_heap HI (LBown ++ LBrest) cr M VM ->
  (forall b, In b (LBown ++ LBrest) -> block_range L (fst b) (snd b) /\ HeapIface.defined M (fst b) (snd b))
  /\ (forall b b', In b LBown -> In b' LBrest -> fst b + snd b <= fst b' \/ fst b' + snd b' <= fst b)
  /\ base.NoDup (map fst (LBown ++ LBrest)).
Proof.
  intros LBown cr M VM HH. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hb & Hnd & _).
  split; [intros b Hin; destruct (Hb b Hin) as (X & Y & _); split; assumption|]. split; [|exact Hnd].
  intros b b' Hin Hin'. destruct (Hb b (in_or_app _ _ _ (or_introl Hin))) as (_ & _ & Hap).
  assert (Hne : fst b' <> fst b).
  { intros e. rewrite map_app in Hnd. eapply (nodup_app_disj _ _ (fst b) Hnd); [apply in_map; exact Hin | rewrite <- e; apply in_map; exact Hin']. }
  destruct b' as [B m]. cbn [fst snd] in *.
  exact (Hap (B, m) (L5C.in_lb_remove_neq (fst b) B m _ (in_or_app _ _ _ (or_intror Hin')) Hne)).
Qed.

Lemma in_block_app : forall L1 L2 a, in_block (L1 ++ L2) a <-> in_block L1 a \/ in_block L2 a.
Proof.
  intros L1 L2 a. unfold in_block. split.
  - intros (b & Hin & Hr). apply in_app_or in Hin as [H|H]; [left|right]; exists b; split; assumption.
  - intros [(b & Hin & Hr)|(b & Hin & Hr)]; exists b; (split; [apply in_or_app; auto | exact Hr]).
Qed.

Lemma foot_not_private : forall LBown cr M VM a, hi_heap HI (LBown ++ LBrest) cr M VM -> 0 <= a < 2 ^ 64 ->
  foot_sem LBown a -> ~ alloc_private L (LBown ++ LBrest) a.
Proof.
  intros LBown cr M VM a HH Ha HF HP. pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  destruct (blocks_facts _ _ _ _ HH) as (Hbr & _ & _).
  destruct HF as [Hs | [(r & Hr & Hin) | Hb]].
  - destruct HP as [(P1 & _) | P]; [lia|]. apply LY_ro in P. lia.
  - destruct (W_ok r a Hr Hin) as (_ & [Hst | (Him & Hns & Hnr)]).
    + destruct HP as [(P1 & _) | P]; [lia|]. apply LY_ro in P. lia.
    + destruct HP as [(_ & _ & P3) | P]; [apply P3; split; assumption | exact (proj1 Hnr P)].
  - destruct HP as [(_ & P2 & _) | P]; [apply P2; apply in_block_app; left; exact Hb|].
    destruct Hb as (b & Hin & Hr). destruct (Hbr b (in_or_app _ _ _ (or_introl Hin))) as ((B0 & B1 & B2 & B3 & B4) & _).
    apply LY_ro in P. lia.
Qed.

Lemma foot_not_kept : forall LBown cr M VM a, hi_heap HI (LBown ++ LBrest) cr M VM ->
  foot_sem LBown a -> ~ L5C.kept L LBrest sp0 SCR W a.
Proof.
  intros LBown cr M VM a HH HF (Ha & HC & HE & HW). pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  destruct (blocks_facts _ _ _ _ HH) as (Hbr & Hap & _).
  destruct HF as [Hs | [(r & Hr & Hin) | Hb]].
  - destruct HC as [(b & Hin & Hr) | [(C1 & C2) | (C1 & _)]]; [|lia|lia].
    destruct (Hbr b (in_or_app _ _ _ (or_intror Hin))) as ((B0 & B1 & B2 & B3 & B4) & _). lia.
  - exact (HW r Hr Hin).
  - destruct Hb as (b & Hin & Hr). destruct (Hbr b (in_or_app _ _ _ (or_introl Hin))) as ((B0 & B1 & B2 & B3 & B4) & _).
    destruct HC as [(b' & Hin' & Hr') | [(C1 & C2) | (C1 & _)]]; [|lia|lia].
    destruct (Hap b b' Hin Hin'); lia.
Qed.

Lemma amb_pure_step : forall i j E E2 M M' model,
  heap_amb i E M model ->
  (forall a : word, ~ foot_sem (den E (nth i BLS [])) (bv_unsigned a) -> M' a = M a) ->
  mem_grows M M' ->
  env_agree NF E E2 -> den E2 (nth j BLS []) = den E (nth i BLS []) ->
  (forall cr, Cred i E cr -> Cred j E2 cr) ->
  heap_amb j E2 M' model.
Proof.
  intros i j E E2 M M' model (Hmo & Hbv & Hag & (cr & HH & HC) & Hfr & Hdf) Hch Hgr Hag2 Hden HCr.
  split; [exact Hmo|]. split; [exact Hbv|]. split; [eapply CC.env_agree_trans; eassumption|].
  assert (U : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a) by (intros a Ha; apply L5.unsigned_lit; exact Ha).
  split; [|split].
  - exists cr. split; [|apply HCr; exact HC]. unfold cur. rewrite Hden.
    eapply (hio_frame L SCFG HI HIok); [exact HH | | exact Hgr].
    intros a Ha HP. apply Hch. rewrite (U a Ha). intros HF. exact (foot_not_private _ _ _ _ a HH Ha HF HP).
  - intros a HK. rewrite <- (Hfr a HK). apply Hch. rewrite (U a (proj1 HK)). intros HF. exact (foot_not_kept _ _ _ _ a HH HF HK).
  - intros a Ha Hc Hd. apply Hgr. exact (Hdf a Ha Hc Hd).
Qed.

Lemma kept_client : forall LBown sp a, sp0 - SCR <= sp - hl_stack L -> sp <= sp0 ->
  L5C.kept L LBrest sp0 SCR W a -> client_addr L (LBown ++ LBrest) sp (hl_stack L) a /\ ~ in_errno L a.
Proof.
  intros LBown sp a H1 H2 (Ha & HC & HE & _). split; [|exact HE].
  destruct HC as [Hb | [(C1 & C2) | C]]; [left; apply in_block_app; right; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C].
Qed.
Lemma client0_cases : forall LBown sp a, sp <= sp0 -> client0 a ->
  (sp - hl_stack L <= a < sp) \/ (client_addr L (LBown ++ LBrest) sp (hl_stack L) a /\ ~ in_errno L a).
Proof.
  intros LBown sp a H2 (HC & HE).
  destruct (Z_le_dec (sp - hl_stack L) a) as [H3|H3]; [destruct (Z_lt_dec a sp) as [H4|H4]; [left; lia|]|]; right; (split; [|exact HE]);
    (destruct HC as [Hb | [(C1 & C2) | C]]; [left; apply in_block_app; right; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C]).
Qed.

Lemma amb_alloc_frame : forall LBown sp M M',
  heap_pres_core L (LBown ++ LBrest) sp M M' -> sp0 - SCR <= sp - hl_stack L -> sp <= sp0 ->
  (forall a, L5C.kept L LBrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> client0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None) ->
  (forall a, L5C.kept L LBrest sp0 SCR W a -> M' (Z_to_bv 64 a) = M0 (Z_to_bv 64 a))
  /\ (forall a, 0 <= a < 2 ^ 64 -> client0 a -> M0 (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).
Proof.
  intros LBown sp M M' [Hp Hs] H1 H2 Hfr Hdf. split.
  - intros a HK. rewrite <- (Hfr a HK). destruct (kept_client LBown sp a H1 H2 HK) as [C NE]. exact (Hp a (proj1 HK) C NE).
  - intros a Ha Hc Hd. destruct (client0_cases LBown sp a H2 Hc) as [Hsc | [C NE]]; [exact (Hs a Hsc)|].
    rewrite (Hp a Ha C NE). exact (Hdf a Ha Hc Hd).
Qed.

Lemma model_ok_but_vm : forall m m', model_but_vm m m' -> model_ok m -> model_ok m'.
Proof.
  intros m m' H (A & B & C). split; [rewrite (L5C.halted_but_vm _ _ H); exact A|].
  split; [rewrite (L5C.lazy_but_vm _ _ H); exact B | rewrite (L5C.materialized_but_vm _ _ H); exact C].
Qed.

Lemma amb_malloc : forall i j E E2 M M' model model' sp A n cr,
  model_ok model -> model_but_vm model0 model -> env_agree NF E0 E ->
  (forall a, L5C.kept L LBrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> client0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None) ->
  heap_pres_core L (cur i E) sp M M' -> sp0 - SCR <= sp - hl_stack L -> sp <= sp0 ->
  model_but_vm model model' ->
  hi_heap HI ((A, n) :: cur i E) (debit L cr n) M' (m_vmmaps model') ->
  env_agree NF E E2 -> den E2 (nth j BLS []) = (A, n) :: den E (nth i BLS []) ->
  Cred j E2 (debit L cr n) ->
  heap_amb j E2 M' model'.
Proof.
  intros i j E E2 M M' model model' sp A n cr Hmo Hbv Hag Hfr Hdf Hpres H1 H2 Hbv' HH' Hag2 Hden HC.
  split; [exact (model_ok_but_vm _ _ Hbv' Hmo)|]. split; [exact (L5C.model_but_vm_trans _ _ _ Hbv Hbv')|].
  split; [eapply CC.env_agree_trans; eassumption|].
  split; [exists (debit L cr n); split; [unfold cur in *; rewrite Hden; exact HH' | exact HC]|].
  exact (amb_alloc_frame _ sp M M' Hpres H1 H2 Hfr Hdf).
Qed.

Lemma amb_free : forall i j E E2 M M' model model' sp A cr,
  model_ok model -> model_but_vm model0 model -> env_agree NF E0 E ->
  (forall a, L5C.kept L LBrest sp0 SCR W a -> M (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> client0 a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None) ->
  heap_pres L (lb_remove A (cur i E)) sp M M' -> sp0 - SCR <= sp - hl_stack L -> sp <= sp0 ->
  model_but_vm model model' ->
  hi_heap HI (lb_remove A (cur i E)) cr M' (m_vmmaps model') ->
  env_agree NF E E2 -> den E2 (nth j BLS []) ++ LBrest = lb_remove A (cur i E) ->
  Cred j E2 cr ->
  heap_amb j E2 M' model'.
Proof.
  intros i j E E2 M M' model model' sp A cr Hmo Hbv Hag Hfr Hdf [Hpres _] H1 H2 Hbv' HH' Hag2 Hden HC.
  split; [exact (model_ok_but_vm _ _ Hbv' Hmo)|]. split; [exact (L5C.model_but_vm_trans _ _ _ Hbv Hbv')|].
  split; [eapply CC.env_agree_trans; eassumption|].
  split; [exists cr; split; [unfold cur in *; rewrite Hden; exact HH' | exact HC]|].
  rewrite <- Hden in Hpres. exact (amb_alloc_frame _ sp M M' Hpres H1 H2 Hfr Hdf).
Qed.

Lemma amb_hpres : forall i E M model, heap_amb i E M model -> L5.defined M0 (sp0 - SCR) SCR ->
  L5C.hpres L LBrest sp0 SCR W M0 M.
Proof.
  intros i E M model (_ & _ & _ & _ & Hfr & Hdf) Hd0. pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  apply L5C.hpres_intro.
  - exact Hfr.
  - intros k Hk. assert (Ha : 0 <= sp0 - SCR + k < 2 ^ 64) by lia. apply (Hdf _ Ha); [|exact (Hd0 k Hk)].
    split; [right; left; lia | unfold in_errno; lia].
  - intros a Ha HC HE Hd. apply (Hdf a Ha); [|exact Hd]. split; [|exact HE].
    destruct HC as [Hb | [(C1 & C2) | C]]; [left; exact Hb | right; left; split; [exact C1 | lia] | right; right; exact C].
Qed.

Definition in_reg (E : env) (r : SGP.region) (a : Z) : Prop :=
  let '(rb, rlo, rlen) := r in estart E (SA rb rlo) <= a < estart E (SA rb rlo) + elenZ E rlen.

Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, in_reg E0 r a -> sclient a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r ->
  hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.

Lemma in_reg_agree : forall b E E' r a, env_agree b E E' -> SGP.region_vars_lt b r = true -> in_reg E' r a -> in_reg E r a.
Proof.
  intros b E E' [[rb rlo] rlen] a Hag Hv H. cbn [SGP.region_vars_lt] in Hv. apply andb_prop in Hv as [V1 V2].
  unfold in_reg, estart, elenZ in *. cbn [a_base a_off] in *.
  rewrite (SR.edenot_agree_AP b E E' rb Hag V1), (SR.edenot_agree_AP b E E' rlen Hag V2). exact H.
Qed.

Lemma within_sem : forall E M kn REGS b k n, know_ok (hl_segs L) E M kn -> CH.within kn REGS b k n = true ->
  exists r, In r REGS /\ forall a, estart E (SA b k) <= a < estart E (SA b k) + elenZ E n -> in_reg E r a.
Proof.
  intros E M kn REGS b k n HK H. unfold CH.within in H. destruct (SGP.withinE kn REGS b k n) eqn:H1.
  - unfold SGP.withinE in H1. apply existsb_exists in H1 as ([[rb rlo] rlen] & Hin & Hx).
    destruct (xinside_sound (hl_segs L) E M kn b k n rb rlo rlen HK Hx) as [X1 X2].
    exists (rb, rlo, rlen). split; [exact Hin|]. intros a Ha. unfold in_reg. lia.
  - apply existsb_exists in H as ([[rb rlo] rlen] & Hin & Hx).
    destruct (CX.xinside2_sound (hl_segs L) E M kn b k n rb rlo rlen HK Hx) as [X1 X2].
    exists (rb, rlo, rlen). split; [exact Hin|]. intros a Ha. unfold in_reg. lia.
Qed.

Lemma sp0_range : 0x7fff7f800000 <= sp0 - SCR /\ sp0 <= 2 ^ 47.
Proof. pose proof ceil_lo. destruct STK as (_ & S2 & S3 & S4 & S5). lia. Qed.

Lemma ev2 : forall E, env_agree NF E0 E -> bv_unsigned (ev E 2) = sp0.
Proof. intros E [H _]. rewrite <- (H 2%nat) by lia. exact SP0. Qed.

Lemma stack_reg_sem : forall E lo len a, env_agree NF E0 E -> 0 <= len < 2 ^ 64 ->
  in_reg E (EVar 2, lo, ELit len) a -> sp0 + lo <= a < sp0 + lo + len.
Proof.
  intros E lo len a Hag Hl H. unfold in_reg, estart, elenZ in H. cbn [a_base a_off edenot] in H.
  rewrite (ev2 E Hag) in H. rewrite u64_of_Z in H by lia. exact H.
Qed.

Lemma blk_reg_sem : forall E BL r a, In r (CH.blk_regs BL) -> in_reg E r a -> in_block (den E BL) a.
Proof.
  intros E BL r a Hin H. unfold CH.blk_regs in Hin. apply in_map_iff in Hin as ([x y] & <- & Hb). cbn [fst snd] in H.
  exists (bv_unsigned (edenot E x), bv_unsigned (edenot E y)). split.
  - unfold den. apply in_map_iff. exists (x, y). split; [reflexivity | exact Hb].
  - unfold in_reg, estart, elenZ in H. cbn [a_base a_off fst snd] in *. lia.
Qed.

Lemma foot_regs_sem : forall E BL r a, env_agree NF E0 E -> In r (CH.foot_regs d BL) -> in_reg E r a -> foot_sem (den E BL) a.
Proof.
  intros E BL r a Hag Hin H. pose proof sp0_range as SR0. unfold CH.foot_regs in Hin. destruct Hin as [<-|Hin].
  - left. apply (stack_reg_sem E _ _ a Hag) in H; lia.
  - apply in_app_or in Hin as [Hw|Hb].
    + right; left. destruct (WRS_ok r Hw) as [Hv Hs]. apply Hs. exact (in_reg_agree NF E0 E r a Hag Hv H).
    + right; right. exact (blk_reg_sem E BL r a Hb H).
Qed.

Definition blocks_in_range (LB : list (Z * Z)) : Prop := forall b, In b LB -> block_range L (fst b) (snd b).
Lemma blocks_in_range_of : forall LBown cr M VM, hi_heap HI (LBown ++ LBrest) cr M VM -> blocks_in_range (LBown ++ LBrest).
Proof. intros LBown cr M VM HH b Hb. exact (proj1 (proj1 (blocks_facts _ _ _ _ HH) b Hb)). Qed.

Lemma sclient_client : forall LBown sp a, blocks_in_range (LBown ++ LBrest) -> sp <= sp0 ->
  sclient a -> client_addr L (LBown ++ LBrest) sp (hl_stack L) a /\ ~ in_errno L a.
Proof.
  intros LBown sp a Hbr Hsp (Ha & HS). pose proof sp0_range as SR0.
  destruct HS as [H1 | [(H1 & H2 & H3) | H1]].
  - split; [right; left; split; [lia | lia] | unfold in_errno; lia].
  - split; [right; right; split; assumption | exact H3].
  - split; [left; apply in_block_app; right; exact H1|]. destruct H1 as (b & Hin & Hr).
    destruct (Hbr b (in_or_app _ _ _ (or_intror Hin))) as (B0 & B1 & B2 & B3 & B4). unfold in_errno. lia.
Qed.

Lemma keep_regs_sem : forall E BL c r a, env_agree NF E0 E -> blocks_in_range (den E BL ++ LBrest) ->
  c <= 0 -> - SCR <= c - hl_stack L -> 0 <= a < 2 ^ 64 ->
  In r (CH.keep_regs d c BL) -> in_reg E r a ->
  client_addr L (den E BL ++ LBrest) (sp0 + c) (hl_stack L) a /\ ~ in_errno L a.
Proof.
  intros E BL c r a Hag Hbr Hc Hc2 Ha Hin H. pose proof sp0_range as SR0. pose proof ceil_lo as CL.
  destruct STK as (_ & S2 & S3 & S4 & S5).
  unfold CH.keep_regs in Hin. destruct Hin as [<-|[<-|Hin]].
  - apply (stack_reg_sem E _ _ a Hag) in H; [|lia]. split; [right; left; split; lia | unfold in_errno; lia].
  - rewrite <- HSTK_eq in H. apply (stack_reg_sem E _ _ a Hag) in H; [|lia]. split; [right; left; split; lia | unfold in_errno; lia].
  - apply in_app_or in Hin as [Hcr|Hin]; [|apply in_app_or in Hin as [Hw|Hb]].
    + destruct (CRS_ok r Hcr) as [Hv Hs]. apply (sclient_client _ _ a Hbr); [lia|]. apply Hs. exact (in_reg_agree NF E0 E r a Hag Hv H).
    + destruct (WRS_ok r Hw) as [Hv Hs]. destruct (Hs a (in_reg_agree NF E0 E r a Hag Hv H)) as (w & Hw1 & Hw2).
      destruct (W_ok w a Hw1 Hw2) as (_ & [Hst | (Him & Hns & _ & Hne)]).
      * split; [right; left; split; lia | unfold in_errno; lia].
      * split; [right; right; split; assumption | exact Hne].
    + pose proof (blk_reg_sem E BL r a Hb H) as IB. split; [left; apply in_block_app; left; exact IB|].
      destruct IB as (b & Hinb & Hr). destruct (Hbr b (in_or_app _ _ _ (or_introl Hinb))) as (B0 & B1 & B2 & B3 & B4). unfold in_errno. lia.
Qed.

Lemma entry_reg_support : forall E M K b k n, kentry_ok (hl_segs L) E M K -> CH.entry_reg K = Some (b, k, n) ->
  forall x, CH.ksupport E K x -> 0 <= x < 2 ^ 64 /\ estart E (SA b k) <= x < estart E (SA b k) + elenZ E n.
Proof.
  intros E M K b k n HK He x Hx.
  destruct K as [[kb kk] w v|[kb kk] m|[kb kk] m id|lo hi|e m|e lo hi|[kb kk] m|a1 n1 a2 n2|[kb kk] m c|[kb kk] m]; cbn [CH.entry_reg] in He; try discriminate;
    injection He as <- <- <-; cbn [CH.ksupport kentry_ok] in *.
  - destruct HK as (Hw & (F1 & F2 & F3 & F4) & _). unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
  - destruct HK as ((F1 & F2 & F3 & F4) & _). lia.
Qed.

Lemma survive_sound : forall E M BL kn c K, env_agree NF E0 E -> blocks_in_range (den E BL ++ LBrest) ->
  c <= 0 -> - SCR <= c - hl_stack L ->
  know_ok (hl_segs L) E M kn -> kentry_ok (hl_segs L) E M K -> CH.survive_chk d kn c BL K = true ->
  CH.entry_survives L (den E BL ++ LBrest) (sp0 + c) E K.
Proof.
  intros E M BL kn c K Hag HH Hc Hc2 Hkn HK H. pose proof sp0_range as SR0.
  assert (PURE : (forall x, ~ CH.ksupport E K x) -> CH.entry_survives L (den E BL ++ LBrest) (sp0 + c) E K).
  { intros Hn. left. intros x Hx. exfalso. exact (Hn x Hx). }
  assert (REG : forall b k n, CH.entry_reg K = Some (b, k, n) ->
            (if CH.within kn (CH.keep_regs d c BL) b k n then true else if CH.def_only K then CH.within kn [CH.stack_reg d] b k n else false) = true ->
            CH.entry_survives L (den E BL ++ LBrest) (sp0 + c) E K).
  { intros b k n He Hw. destruct (CH.within kn (CH.keep_regs d c BL) b k n) eqn:W1.
    - left. intros x Hx. destruct (entry_reg_support E M K b k n HK He x Hx) as [Hx0 Hx1].
      destruct (within_sem E M kn _ b k n Hkn W1) as (r & Hr & Hs).
      destruct (keep_regs_sem E BL c r x Hag HH Hc Hc2 Hx0 Hr (Hs x Hx1)) as [C NE]. split; [exact Hx0 | split; assumption].
    - destruct (CH.def_only K) eqn:Hd; [|discriminate]. right. split; [exact Hd|]. intros x Hx.
      destruct (entry_reg_support E M K b k n HK He x Hx) as [Hx0 Hx1].
      destruct (within_sem E M kn _ b k n Hkn Hw) as (r & [<-|[]] & Hs).
      assert (Hst : sp0 + - SCR <= x < sp0 + - SCR + SCR) by (apply (stack_reg_sem E (- SCR) SCR x Hag); [lia | exact (Hs x Hx1)]). pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
      destruct (Z_le_dec (sp0 + c - hl_stack L) x) as [G1|G1]; [destruct (Z_lt_dec x (sp0 + c)) as [G2|G2]; [right; split; [exact Hx0 | lia]|]|];
        left; (split; [exact Hx0|]); (split; [right; left; split; lia | unfold in_errno; lia]). }
  destruct K as [[kb kk] w v|[kb kk] m|[kb kk] m id|lo hi|e m|e lo hi|[kb kk] m|a1 n1 a2 n2|[kb kk] m c0|[kb kk] m]; cbn [CH.survive_chk] in H;
    try (apply PURE; intros x Hx; exact Hx); try (eapply REG; [reflexivity | exact H]).

  left. intros x Hx. cbn [CH.ksupport] in Hx. cbn [kentry_ok] in HK. destruct HK as (K1 & K2 & _).
  apply existsb_exists in H as ([rlo rhi] & Hin & Hb). cbn [fst snd] in Hb. apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1, B2.
  destruct (IMG_ok (rlo, rhi) x Hin ltac:(cbn [fst snd]; lia)) as (I1 & I2 & I3).
  split; [lia|]. split; [right; right; split; assumption | exact I3].
Qed.

Lemma survive_know : forall E M M' BL kn c ks, env_agree NF E0 E -> blocks_in_range (den E BL ++ LBrest) ->
  c <= 0 -> - SCR <= c - hl_stack L ->
  know_ok (hl_segs L) E M kn -> know_ok (hl_segs L) E M ks -> forallb (CH.survive_chk d kn c BL) ks = true ->
  heap_pres_core L (den E BL ++ LBrest) (sp0 + c) M M' ->
  know_ok (hl_segs L) E M' ks.
Proof.
  intros E M M' BL kn c ks Hag HH Hc Hc2 Hkn Hks Hall Hp.
  apply (CH.heap_pres_know L (den E BL ++ LBrest) (sp0 + c) E M M' ks Hp); [|exact Hks].
  intros X HX. rewrite forallb_forall in Hall. unfold know_ok in Hks. rewrite Forall_forall in Hks.
  exact (survive_sound E M BL kn c X Hag HH Hc Hc2 Hkn (Hks X HX) (Hall X HX)).
Qed.

Definition blocks_vars_lt (b : nat) (BL : CA.blocks) : bool :=
  forallb (fun x : expr * expr => (APC.expr_vars_lt b (fst x) && APC.expr_vars_lt b (snd x))%bool) BL.
Definition foot_chk (c : CC.cutpoint) (BL : CA.blocks) : bool :=
  (forallb (fun r : SGP.region => let '(rb, rlo, rlen) := r in CH.within (CC.cp_know c) (CH.foot_regs d BL) rb rlo rlen) (CC.cp_F c)
   && forallb (SGP.region_vars_lt (CC.cp_nx c)) (CC.cp_F c) && blocks_vars_lt (CC.cp_nx c) BL && Nat.leb NF (CC.cp_nx c))%bool.

Lemma foot_chk_sound : forall c BL E E' R M (a : word),
  foot_chk c BL = true -> CC.At (hl_segs L) c E R M -> env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' ->
  ~ foot_sem (den E BL) (bv_unsigned a) -> SGP.outside E' (CC.cp_F c) a.
Proof.
  intros c BL E E' R M a H [_ HK] Hag Hag' Hnf. unfold foot_chk in H. repeat (apply andb_prop in H as [H ?X]).
  unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  rewrite forallb_forall in H, X1. specialize (H _ Hin). specialize (X1 _ Hin). cbn beta iota in H.
  cbn [SGP.region_vars_lt] in X1. apply andb_prop in X1 as [V1 V2].
  unfold estart, elenZ. cbn [a_base a_off].
  rewrite <- (SR.edenot_agree_AP _ E E' rb Hag' V1), <- (SR.edenot_agree_AP _ E E' rlen Hag' V2).
  destruct (Z_lt_dec (bv_unsigned a) (bv_unsigned (edenot E rb) + rlo)) as [G1|G1]; [left; exact G1|].
  destruct (Z_le_dec (bv_unsigned (edenot E rb) + rlo + bv_unsigned (edenot E rlen)) (bv_unsigned a)) as [G2|G2]; [right; exact G2|].
  exfalso. apply Hnf. destruct (within_sem E M _ _ rb rlo rlen HK H) as (r & Hr & Hs).
  apply (foot_regs_sem E BL r _ Hag Hr). apply Hs. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma leaf_amb : forall i c ps E E' R R' M M' model,
  foot_chk c (nth i BLS []) = true -> CC.At (hl_segs L) c E R M -> heap_amb i E M model ->
  env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
  heap_amb i E M' model.
Proof.
  intros i c ps E E' R R' M M' model Hf HAt HA Hag HLF.
  apply (amb_pure_step i i E E M M' model HA); [| exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | apply CC.env_agree_refl | reflexivity | auto].
  intros a Hn. apply (CC.lf_frame _ _ _ _ _ _ _ HLF). destruct HA as (_ & _ & Hag0 & _).
  exact (foot_chk_sound c _ E E' R M a Hf HAt Hag0 Hag Hn).
Qed.

Fixpoint blocks_eqb (a b : CA.blocks) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (expr_eqb (fst x) (fst y) && expr_eqb (snd x) (snd y) && blocks_eqb a' b')%bool
  | _, _ => false
  end.
Lemma blocks_eqb_eq : forall a b, blocks_eqb a b = true -> a = b.
Proof.
  induction a as [|[x1 x2] a IH]; intros [|[y1 y2] b] H; cbn [blocks_eqb fst snd] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1, H2. subst. rewrite (IH b H3). reflexivity.
Qed.
Definition bsubst (s : CC.subst) (BL : CA.blocks) : CA.blocks := map (fun b : expr * expr => (CC.esubstL NF s (fst b), CC.esubstL NF s (snd b))) BL.
Lemma den_bsubst : forall s E BL, den E (bsubst s BL) = den (CC.env_over NF s E) BL.
Proof.
  intros s E BL. unfold den, bsubst. rewrite map_map. apply map_ext. intros [x y]. cbn [fst snd]. rewrite !CC.esubstL_denot. reflexivity.
Qed.

Definition goto_amb_chk (c : CC.cutpoint) (BLi BLj : CA.blocks) (s : CC.subst) : bool :=
  (foot_chk c BLi && blocks_eqb (bsubst s BLj) BLi)%bool.

Lemma goto_amb : forall i c ps j s,
  goto_amb_chk c (nth i BLS []) (nth j BLS []) s = true ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  CC.amb_goto (hl_segs L) heap_amb NF i c ps j s.
Proof.
  intros i c ps j s H HCr E R M model E' R' M' HAt HA Hag HLF. unfold goto_amb_chk in H. apply andb_prop in H as [Hf Hb].
  apply blocks_eqb_eq in Hb. pose proof (leaf_amb i c ps E E' R R' M M' model Hf HAt HA Hag HLF) as HA'.
  assert (Hnf : (NF <= CC.cp_nx c)%nat).
  { unfold foot_chk in Hf. apply andb_prop in Hf as [_ X]. apply Nat.leb_le in X. exact X. }
  assert (Hbv : blocks_vars_lt (CC.cp_nx c) (nth i BLS []) = true).
  { unfold foot_chk in Hf. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [_ X]. exact X. }
  apply (amb_pure_step i j E (CC.env_over NF s E') M' M' model HA'); [reflexivity | apply mem_grows_refl | | |].
  - eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact Hnf] | apply CC.env_over_agree].
  - rewrite <- den_bsubst, Hb. exact (den_agree _ E E' _ Hag Hbv).
  - intros cr HC. destruct HA as (_ & _ & Hag0 & _). exact (HCr E E' R' M M' cr Hag0 Hag HLF HC).
Qed.

Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable FPI : FPState -> Prop.

Definition all_regs_chk (ps : SR.post_spec) : bool :=
  forallb (fun r => existsb (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps)) (seq 1 31).

Lemma leaf_regs_ok : forall c ps E' R' M M', all_regs_chk ps = true -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
  regs_ok E' (CA.ps_reglist ps) R'.
Proof.
  intros c ps E' R' M M' H HLF r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
    cbn [edenot]. replace (0%bv : bv 5) with (Z_to_bv 5 0) by (apply bv_eq; reflexivity). exact (CC.lf_x0 _ _ _ _ _ _ _ HLF).
  - assert (Hr : (1 <= ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
      unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
    unfold CA.ps_reglist. destruct (ridx r) as [|m] eqn:Em; [lia|]. cbn [nth].
    rewrite (nth_indep _ (ELit 0) (CA.ps_reg ps 0%nat)) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (CA.ps_reg ps) (seq 1 31) 0%nat m). rewrite seq_nth by lia.
    unfold all_regs_chk in H. rewrite forallb_forall in H. specialize (H (1 + m)%nat ltac:(apply in_seq; lia)).
    unfold CA.ps_reg. destruct (find (fun ie : nat * expr => Nat.eqb (fst ie) (1 + m)) (SR.ps_regs ps)) as [[i e]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hi]. cbn [fst snd] in *. apply Nat.eqb_eq in Hi. subst i.
      destruct (CC.lf_regs _ _ _ _ _ _ _ HLF _ _ Hin) as [_ Hg]. rewrite <- Hg. f_equal. rewrite <- (CC.reg_of_ridx r). rewrite Em. reflexivity.
    + exfalso. apply existsb_exists in H as (ie & Hin & Hb). rewrite (find_none _ _ Hf ie Hin) in Hb. discriminate.
Qed.

Record cinfo : Type := CI { ci_regs : list expr; ci_nx : nat; ci_csp : Z; ci_ra : Z }.
Definition HSTK := CH.hd_hstk d.
Definition common_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) : option cinfo :=
  let regs := CA.ps_reglist ps in
  let nx := (CC.cp_nx cj - APC.NCS)%nat in
  let cells := SR.ps_cells ps in
  match nth 1 regs (ELit 0), split_lit (nth 2 regs (ELit 0)) with
  | ELit ra, (EVar 2, csp) =>
      if (foot_chk c BLi && all_regs_chk ps && Nat.leb APC.NCS (CC.cp_nx cj) && Nat.leb (CC.cp_nx c) nx
          && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx cells
          && Z.eqb ra (CC.cp_pc cj) && Z.eqb (ra mod 2) 0 && Z.leb 0 ra && Z.ltb ra (2 ^ 64)
          && expr_eqb (nth 4 regs (ELit 0)) (EVar 4)
          && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1)) && CC.has_cell cells (KRange (CC.cp_meas c) 1 CC.MB)
          && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
          && Z.eqb (csp mod 16) 0 && Z.leb csp 0 && Z.leb (- SCR) (csp - HSTK)
          && existsb (fun X => match X with KWr (SA b k) n => xinside cells (EVar 2) (csp - HSTK) (ELit HSTK) b k n | _ => false end) cells)%bool
      then Some (CI regs nx csp ra) else None
  | _, _ => None
  end.

Record common_facts (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (ci : cinfo) (i : nat) (E E' : env) (R' : bvmap 5 word) (M' : mem) (model : Model) : Prop := CF {
  cf_amb : heap_amb i E M' model;
  cf_regs : regs_ok E' (ci_regs ci) R';
  cf_regs_eq : ci_regs ci = CA.ps_reglist ps;
  cf_vars : APC.sr_vars_lt (ci_nx ci) (ci_regs ci) = true /\ APC.kn_vars_lt (ci_nx ci) (SR.ps_cells ps) = true /\ (CC.cp_nx c <= ci_nx ci)%nat
            /\ (NF <= CC.cp_nx c)%nat /\ CC.cp_nx cj = (ci_nx ci + APC.NCS)%nat;
  cf_know : know_ok (hl_segs L) E' M' (SR.ps_cells ps);
  cf_ra : getr R' 1%bv = Z_to_bv 64 (CC.cp_pc cj) /\ Hoare.ret_ok (getr R' 1%bv);
  cf_sp : bv_unsigned (getr R' 2%bv) = sp0 + ci_csp ci /\ ci_csp ci <= 0 /\ - SCR <= ci_csp ci - hl_stack L;
  cf_stack : stack_ok L M' (sp0 + ci_csp ci);
  cf_tp : getr R' 4%bv = Z_to_bv 64 (hl_tp L);
  cf_agE' : env_agree NF E0 E';
  cf_den : den E' (nth i BLS []) = den E (nth i BLS []);
  cf_meas : forall E2, env_agree (ci_nx ci) E' E2 -> CC.meas cj E2 < CC.meas c E
}.

Lemma reg_lit : forall n : Z, 0 <= n < 32 -> Z_to_bv 5 (Z.of_nat (Z.to_nat n)) = Z_to_bv 5 n.
Proof. intros n Hn. rewrite Z2Nat.id by lia. reflexivity. Qed.

Lemma common_sound : forall i c ps cj ci E R M model E' R' M',
  common_chk c ps cj (nth i BLS []) = Some ci ->
  CC.At (hl_segs L) c E R M -> heap_amb i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
  common_facts c ps cj ci i E E' R' M' model.
Proof.
  intros i c ps cj ci E R M model E' R' M' H HAt HA Hag HLF. unfold common_chk in H.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |] eqn:Hra; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp] eqn:Hsp.
  destruct spb as [|v| | | | | |]; try discriminate. destruct v as [|[|[|v]]]; cbv beta iota in H; try discriminate.
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as <-.
  remember (foot_chk c (nth i BLS [])) as fc eqn:Hfc. remember (all_regs_chk ps) as arc eqn:Harc.
  repeat (apply andb_prop in Hb as [Hb ?X]). subst fc arc.
  apply Nat.leb_le in X14, X13. apply Z.eqb_eq in X10, X9, X2. apply Z.leb_le in X8, X1, X0. apply Z.ltb_lt in X7.
  apply expr_eqb_eq in X6, X5. apply CC.has_cell_In in X4.
  assert (Hnf : (NF <= CC.cp_nx c)%nat).
  { unfold foot_chk in Hb. apply andb_prop in Hb as [_ Y]. apply Nat.leb_le in Y. exact Y. }
  assert (Hbv : blocks_vars_lt (CC.cp_nx c) (nth i BLS []) = true).
  { unfold foot_chk in Hb. apply andb_prop in Hb as [Hb' _]. apply andb_prop in Hb' as [_ Y]. exact Y. }
  pose proof (leaf_amb i c ps E E' R R' M M' model Hb HAt HA Hag HLF) as HA'.
  pose proof (leaf_regs_ok c ps E' R' M M' X15 HLF) as HR.
  assert (HagE' : env_agree NF E0 E').
  { destruct HA as (_ & _ & Hag0 & _). eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact Hnf]]. }
  assert (HK : know_ok (hl_segs L) E' M' (SR.ps_cells ps)).
  { unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). }
  pose proof sp0_range as SR0. pose proof ceil_lo as CL. destruct STK as (S1 & S2 & S3 & S4 & S5).
  assert (G1 : getr R' 1%bv = Z_to_bv 64 ra).
  { rewrite (HR 1%bv). unfold sr_get. change (bv_eqb (1%bv : bv 5) 0) with false. cbv iota. change (ridx 1%bv) with 1%nat. rewrite Hra. reflexivity. }
  assert (G2 : bv_unsigned (getr R' 2%bv) = sp0 + csp).
  { rewrite (HR 2%bv). unfold sr_get. change (bv_eqb (2%bv : bv 5) 0) with false. cbv iota. change (ridx 2%bv) with 2%nat.
    rewrite (APS.split_lit_denot E' _ _ _ Hsp). cbn [edenot]. rewrite (ev2 E' HagE'). apply u64_of_Z. unfold HSTK in X0. rewrite <- HSTK_eq in X0. lia. }
  unfold HSTK in *. rewrite <- HSTK_eq in *.
  constructor; cbn [ci_regs ci_nx ci_csp ci_ra].
  - exact HA'.
  - exact HR.
  - reflexivity.
  - split; [exact X12|]. split; [exact X11|]. split; [exact X13|]. split; [exact Hnf | lia].
  - exact HK.
  - split; [rewrite G1, X10; reflexivity|]. rewrite G1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact X9.
  - split; [exact G2 | split; assumption].
  -
    split; [rewrite Z.add_mod by lia; rewrite S1, X2; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros dd mm Hdd Hmm. apply existsb_exists in X as (Y & HY & Hx). destruct Y as [| | | | | |[b k] n| | |]; try discriminate.
    pose proof (proj1 (Forall_forall _ _) HK _ HY) as HW. cbn [kentry_ok] in HW. destruct HW as [Hfl HW].
    destruct (xinside_sound (hl_segs L) E' M' _ _ _ _ _ _ _ HK Hx) as [I1 I2].
    unfold estart, elenZ in I1, I2. cbn [a_base a_off edenot] in I1, I2. rewrite (ev2 E' HagE') in I1, I2.
    rewrite u64_of_Z in I2 by lia.
    replace (sp0 + csp - hl_stack L + dd) with (estart E' (SA b k) + (sp0 + csp - hl_stack L + dd - estart E' (SA b k))) by lia.
    apply HW; unfold estart, elenZ in *; cbn [a_base a_off] in *; lia.
  - rewrite (HR 4%bv). unfold sr_get. change (bv_eqb (4%bv : bv 5) 0) with false. cbv iota. change (ridx 4%bv) with 4%nat. rewrite X6. cbn [edenot].
    destruct HagE' as [Y _]. rewrite <- (Y 4%nat) by lia. exact TP0.
  - exact HagE'.
  - exact (den_agree _ E E' _ Hag Hbv).
  - intros E2 Hag2. unfold CC.meas. rewrite X5. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 X13) X3). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X3). }
    rewrite Em. pose proof (proj1 (Forall_forall _ _) HK _ X4) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X3) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma reg_partition : forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> In (bv_unsigned r) callee_saved_idx.
Proof.
  intros r Hr Hn.
  assert (T : forallb (fun n => (Nat.eqb n 0 || existsb (Nat.eqb n) APC.caller_saved || existsb (Z.eqb (Z.of_nat n)) callee_saved_idx)%bool) (seq 0 32) = true) by reflexivity.
  rewrite forallb_forall in T. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
  specialize (T (ridx r) ltac:(apply in_seq; unfold ridx; lia)).
  apply orb_prop in T as [T|T]; [apply orb_prop in T as [T|T]|].
  - exfalso. apply Hr. apply bv_eq. apply Nat.eqb_eq in T. unfold ridx in T. change (bv_unsigned (0%bv : bv 5)) with 0. lia.
  - exfalso. apply Hn. apply existsb_exists in T as (x & Hx & He). apply Nat.eqb_eq in He. subst x. exact Hx.
  - apply existsb_exists in T as (x & Hx & He). apply Z.eqb_eq in He. subst x. unfold ridx in Hx. rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

Definition retE (E' : env) (nx : nat) (R2 : bvmap 5 word) : env :=
  APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved).

Lemma ret_regs : forall E' regs nx (R' R2 : bvmap 5 word),
  regs_ok E' regs R' -> APC.sr_vars_lt nx regs = true ->
  (forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r) ->
  regs_ok (retE E' nx R2) (APC.sr_fresh regs APC.caller_saved nx) R2.
Proof.
  intros E' regs nx R' R2 HR Hv Hk. unfold retE. apply CH.fresh_regs_ok; [| exact Hv | repeat constructor; lia].
  intros r Hn. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
    unfold sr_get. change (bv_eqb (0%bv : bv 5) 0) with true. cbv iota. cbn [edenot]. apply getr_zero.
  - assert (Hr : r <> 0%bv) by (intros ->; unfold bv_eqb in Er; rewrite Z.eqb_refl in Er; discriminate).
    rewrite (Hk r Hr Hn). apply HR.
Qed.
Lemma regs_preserved_kept : forall R' R2, regs_preserved R' R2 ->
  forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> getr R2 r = getr R' r.
Proof. intros R' R2 H r Hr Hn. apply H. exact (reg_partition r Hr Hn). Qed.

Lemma retE_agree : forall E' nx R2, env_agree nx E' (retE E' nx R2).
Proof. intros. apply APS.ext_list_agree. Qed.
Lemma retE_a0 : forall E' nx R2, ev (retE E' nx R2) (nx + 4) = getr R2 10%bv.
Proof.
  intros E' nx R2. unfold retE. rewrite APS.ext_list_at by (cbn; lia). cbn [APC.caller_saved map nth].
  f_equal.
Qed.

Lemma regs_eqb_eq : forall a b, CA.regs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [CA.regs_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. subst. rewrite (IH b H2). reflexivity.
Qed.

Lemma entry_across : forall E' E2 nx M' M2 BL cells kn1 c X,
  env_agree NF E0 E' -> blocks_in_range (den E' BL ++ LBrest) -> c <= 0 -> - SCR <= c - hl_stack L ->
  know_ok (hl_segs L) E' M' cells -> know_ok (hl_segs L) E' M' kn1 ->
  heap_pres_core L (den E' BL ++ LBrest) (sp0 + c) M' M2 -> env_agree nx E' E2 ->
  (CC.has_cell kn1 X && CH.survive_chk d cells c BL X && APC.kentry_vars_lt nx X)%bool = true ->
  kentry_ok (hl_segs L) E2 M2 X.
Proof.
  intros E' E2 nx M' M2 BL cells kn1 c X Hag HH Hc Hc2 Hcells Hkn1 Hp Hag2 H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply CC.has_cell_In in H1.
  pose proof (proj1 (Forall_forall _ _) Hkn1 _ H1) as HX.
  assert (G : know_ok (hl_segs L) E' M2 [X]).
  { apply (survive_know E' M' M2 BL cells c [X] Hag HH Hc Hc2 Hcells); [constructor; [exact HX | constructor] | cbn [forallb]; rewrite H2; reflexivity | exact Hp]. }
  assert (G2 : know_ok (hl_segs L) E2 M2 [X]).
  { apply (APS.know_ok_agree' (hl_segs L) nx E' E2 M2 [X] Hag2); [cbn [APC.kn_vars_lt]; rewrite H3; reflexivity | exact G]. }
  inversion G2; assumption.
Qed.

Lemma scratch_unk : forall E2 M2 c, env_agree NF E0 E2 -> c <= 0 -> - SCR <= c - hl_stack L ->
  (forall a, sp0 + c - hl_stack L <= a < sp0 + c -> M2 (Z_to_bv 64 a) <> None) ->
  kentry_ok (hl_segs L) E2 M2 (KUnk (SA (EVar 2) (c - HSTK)) (ELit HSTK)).
Proof.
  intros E2 M2 c Hag Hc Hc2 Hd. pose proof sp0_range as SR0. unfold HSTK. rewrite <- HSTK_eq.
  cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite (ev2 E2 Hag). rewrite u64_of_Z by lia.
  split; [lia|]. intros k Hk. apply Hd. lia.
Qed.

Variable IMG_LO IMG_HI : Z.
Hypothesis IMG_LO_eq : hl_img_lo L = IMG_LO.
Hypothesis IMG_HI_eq : hl_img_hi L = IMG_HI.

Definition nonempty (cells : list kentry) (m : expr) : bool :=
  match m with ELit z => (Z.ltb 0 z && Z.ltb z (2 ^ 64))%bool | _ => APC.fact_ok cells (KRange m 1 18446744073709551615) end.
Definition apart_regs (BL : CA.blocks) : list SGP.region := CH.stack_reg d :: CH.hd_crs d ++ CH.hd_wrs d ++ CH.blk_regs BL.
Definition fresh_fact_ok (cells : list kentry) (nx : nat) (BLi : CA.blocks) (a0v : nat) (n : expr) (X : kentry) : bool :=
  match X with
  | KRange (EVar v) lo hi => (Nat.eqb v a0v && Z.eqb lo 4096 && Z.eqb hi 140737488355328)%bool
  | KAlign (EVar v) m => (Nat.eqb v a0v && Z.eqb m 16)%bool
  | KUnk (SA (EVar v) 0) m | KWr (SA (EVar v) 0) m => (Nat.eqb v a0v && expr_eqb m n)%bool
  | KDisj (SA (EVar v) 0) m (SA b o) m2 =>
      (Nat.eqb v a0v && expr_eqb m n &&
       ((expr_eqb b (ELit 0) && Z.eqb o IMG_LO && expr_eqb m2 (ELit (IMG_HI - IMG_LO)))
        || (nonempty cells m2 && APC.expr_vars_lt nx b && APC.expr_vars_lt nx m2 && CH.within cells (apart_regs BLi) b o m2)))%bool
  | _ => false
  end.

Lemma nonempty_sound : forall E M cells m, know_ok (hl_segs L) E M cells -> nonempty cells m = true -> 0 < elenZ E m.
Proof.
  intros E M cells m HK H. unfold nonempty in H.
  assert (G : APC.fact_ok cells (KRange m 1 18446744073709551615) = true -> 0 < elenZ E m).
  { intros F. pose proof (APS.fact_ok_sound (hl_segs L) E M cells _ HK F) as X. cbn [kentry_ok] in X. unfold elenZ. lia. }
  destruct m; try exact (G H). apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1, H2. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
Qed.

Lemma apart_regs_sem : forall E BL cr M VM r a A n, env_agree NF E0 E -> hi_heap HI (den E BL ++ LBrest) cr M VM ->
  block_range L A n -> blocks_apart A n (den E BL ++ LBrest) ->
  In r (apart_regs BL) -> in_reg E r a -> ~ (A <= a < A + n).
Proof.
  intros E BL cr M VM r a A n Hag HH (B0 & B1 & B2 & B3 & B4) Hap Hin H Ha. pose proof sp0_range as SR0. pose proof ceil_lo as CL.
  destruct STK as (_ & S2 & S3 & S4 & S5).
  assert (NB : forall LB', (forall b, In b LB' -> In b (den E BL ++ LBrest)) -> ~ in_block LB' a).
  { intros LB' Hsub (b & Hb & Hr). destruct (Hap b (Hsub b Hb)); lia. }
  unfold apart_regs in Hin. destruct Hin as [<-|Hin].
  - apply (stack_reg_sem E _ _ a Hag) in H; lia.
  - apply in_app_or in Hin as [Hcr|Hin]; [|apply in_app_or in Hin as [Hw|Hb]].
    + destruct (CRS_ok r Hcr) as [Hv Hs]. destruct (Hs a (in_reg_agree NF E0 E r a Hag Hv H)) as (_ & [G | [(G & _) | G]]); [lia | lia |].
      apply (NB LBrest); [intros b Hb; apply in_or_app; right; exact Hb | exact G].
    + destruct (WRS_ok r Hw) as [Hv Hs]. destruct (Hs a (in_reg_agree NF E0 E r a Hag Hv H)) as (w & Hw1 & Hw2).
      destruct (W_ok w a Hw1 Hw2) as (_ & [G | (G & _)]); lia.
    + apply (NB (den E BL)); [intros b Hb'; apply in_or_app; left; exact Hb' | exact (blk_reg_sem E BL r a Hb H)].
Qed.

Lemma fresh_fact_sound : forall E' E2 nx M' M2 BL cr VM cells a0v ne A n X,
  env_agree NF E0 E' -> hi_heap HI (den E' BL ++ LBrest) cr M' VM -> know_ok (hl_segs L) E' M' cells ->
  env_agree nx E' E2 -> bv_unsigned (ev E2 a0v) = A -> APC.expr_vars_lt nx ne = true -> elenZ E' ne = n ->
  block_range L A n -> blocks_apart A n (den E' BL ++ LBrest) -> HeapIface.defined M2 A n ->
  fresh_fact_ok cells nx BL a0v ne X = true -> kentry_ok (hl_segs L) E2 M2 X.
Proof.
  intros E' E2 nx M' M2 BL cr VM cells a0v ne A n X Hag HH HK Hag2 HA Hvn Hn HBR Hap Hdef H.
  pose proof sp0_range as SR0. pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  pose proof HBR as (B0 & B1 & B2 & B3 & B4).
  assert (Hn2 : elenZ E2 ne = n) by (unfold elenZ in *; rewrite <- (SR.edenot_agree_AP nx E' E2 ne Hag2 Hvn); exact Hn).
  assert (UNK : kentry_ok (hl_segs L) E2 M2 (KUnk (SA (EVar a0v) 0) ne)).
  { cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite HA, Hn2. split; [lia|]. intros k Hk. rewrite Z.add_0_r. apply Hdef. exact Hk. }
  destruct X as [| | | |e m|e lo hi|[wb wk] m|[b1 k1] m [b o] m2| |[ub uk] m]; cbn [fresh_fact_ok] in H; try discriminate.
  -   destruct e as [|v| | | | | |]; try discriminate. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst v m.
    cbn [kentry_ok edenot]. rewrite HA. split; [lia | exact B2].
  -   destruct e as [|v| | | | | |]; try discriminate. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2, H3. subst v lo hi. cbn [kentry_ok edenot]. rewrite HA. lia.
  -   destruct wb as [|v| | | | | |]; try discriminate. destruct wk; try discriminate. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. subst v m. exact (CH.fresh_block_wr L E2 M2 _ _ UNK).
  -   destruct b1 as [|v| | | | | |]; try discriminate. destruct k1; try discriminate. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. subst v m. cbn [kentry_ok].
    assert (EA : estart E2 (SA (EVar a0v) 0) = A) by (unfold estart; cbn [a_base a_off edenot]; rewrite HA; lia). rewrite EA, Hn2.
    apply orb_prop in H3 as [H3|H3].
    + apply andb_prop in H3 as [H3 H5]. apply andb_prop in H3 as [H3 H4]. apply expr_eqb_eq in H3, H5. apply Z.eqb_eq in H4. subst b o m2.
      unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite <- IMG_LO_eq, <- IMG_HI_eq. rewrite !u64_of_Z by lia. lia.
    + apply andb_prop in H3 as [H3 H7]. apply andb_prop in H3 as [H3 H6]. apply andb_prop in H3 as [H4 H5].
      pose proof (nonempty_sound E' M' cells m2 HK H4) as NE. destruct (within_sem E' M' cells _ b o m2 HK H7) as (r & Hr & Hs).
      assert (Eb : estart E2 (SA b o) = estart E' (SA b o)) by (unfold estart; cbn [a_base a_off]; rewrite <- (SR.edenot_agree_AP nx E' E2 b Hag2 H5); reflexivity).
      assert (Em : elenZ E2 m2 = elenZ E' m2) by (unfold elenZ; rewrite <- (SR.edenot_agree_AP nx E' E2 m2 Hag2 H6); reflexivity).
      rewrite Eb, Em. set (s0 := estart E' (SA b o)) in *. set (l0 := elenZ E' m2) in *.
      assert (OUT : forall a, s0 <= a < s0 + l0 -> ~ (A <= a < A + n)).
      { intros a Ha. exact (apart_regs_sem E' BL cr M' VM r a A n Hag HH HBR Hap Hr (Hs a Ha)). }
      destruct (Z_le_dec (A + n) s0) as [G|G]; [left; exact G|]. right.
      destruct (Z_le_dec (s0 + l0) A) as [G2|G2]; [exact G2|]. exfalso.
      destruct (Z_lt_dec s0 A) as [G3|G3]; [apply (OUT A); lia | apply (OUT s0); lia].
  -   destruct ub as [|v| | | | | |]; try discriminate. destruct uk; try discriminate. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. subst v m. exact UNK.
Qed.

Definition malloc_entry_ok (cells kn1 : list kentry) (nx : nat) (csp : Z) (BLi : CA.blocks) (a0v : nat) (n : expr) (X : kentry) : bool :=
  if (CC.has_cell kn1 X && CH.survive_chk d cells csp BLi X && APC.kentry_vars_lt nx X)%bool then true
  else if APC.kentry_eqb X (KUnk (SA (EVar 2) (csp - HSTK)) (ELit HSTK)) then true
  else fresh_fact_ok cells nx BLi a0v n X.

Definition malloc_chk (MALLOC : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match common_chk c ps cj BLi with
  | Some ci =>
      let cells := SR.ps_cells ps in let regs := ci_regs ci in let nx := ci_nx ci in
      let a0e := nth 10 regs (ELit 0) in let a0v := (nx + 4)%nat in
      let kn1 := cells ++ APC.kn_havoc cells (EVar 2) (ci_csp ci - HSTK) (ELit HSTK) in
      (Z.eqb (SR.ps_pc ps) MALLOC
       && CA.regs_eqb (CC.cp_regs cj) (APC.sr_fresh regs APC.caller_saved nx)
       && APC.fact_ok cells (KRange a0e 1 134217728)
       && blocks_eqb BLj ((EVar a0v, a0e) :: BLi) && blocks_vars_lt nx BLi
       && forallb (malloc_entry_ok cells kn1 nx (ci_csp ci) BLi a0v a0e) (CC.cp_know cj))%bool
  | None => false
  end.

Lemma malloc_leaf_ok : forall i c ps j cj MALLOC,
  hl_malloc L = MALLOC -> nth_error CPS j = Some cj ->
  malloc_chk MALLOC c ps cj (nth i BLS []) (nth j BLS []) = true ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
       let n := bv_unsigned (edenot E' (CA.ps_reg ps 10)) in
       credit_ok L cr n /\ forall E2, env_agree (CC.cp_nx cj - APC.NCS) E' E2 -> Cred j E2 (debit L cr n)) ->
  CC.leaf_ok (hl_segs L) CPS heap_amb K FPI i c ps.
Proof.
  intros i c ps j cj MALLOC HM Hcj Hchk HCred fx' E R M model E' R' M' HAt HA HFP Hag HLF HIH.
  unfold malloc_chk in Hchk. destruct (common_chk c ps cj (nth i BLS [])) as [ci|] eqn:Hc; [|discriminate].
  destruct (common_sound i c ps cj ci E R M model E' R' M' Hc HAt HA Hag HLF)
    as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hc2) Hstk Htp HagE' Hden Hmeas].
  repeat (apply andb_prop in Hchk as [Hchk ?X]). apply Z.eqb_eq in Hchk. apply regs_eqb_eq in X3. apply blocks_eqb_eq in X1.
  set (nx := ci_nx ci) in *. set (a0e := nth 10 (ci_regs ci) (ELit 0)) in *.
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Ha0e : a0e = CA.ps_reg ps 10) by (unfold a0e; rewrite Hreq; reflexivity).
  destruct (HCred E E' R' M M' cr HagE Hag HLF HC) as [Hcok HC2]. rewrite <- Ha0e in Hcok, HC2. set (n := bv_unsigned (edenot E' a0e)) in *.
  unfold cur in HH. rewrite <- Hden in HH.
  pose proof (APS.fact_ok_sound (hl_segs L) E' M' _ _ HK X2) as Hn. cbn [kentry_ok] in Hn. fold n in Hn.
  rewrite Hchk, <- HM.
  eapply (hio_malloc L SCFG HI HIok fx' R' M' model _ cr n K HH (proj1 Hmo) (proj1 (proj2 Hmo)) (proj2 (proj2 Hmo))); [| lia | exact Hcok | exact Htp | exact Hret | rewrite Hsp; exact Hstk | exact K_nil |].
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. fold a0e. unfold n.
    symmetry. apply Z_to_bv_bv_unsigned. }
  intros R2 M2 model2 A HA0 HRP HBR Hap Hdef Hpc Hbv2 HH2. rewrite Hsp in Hpc. rewrite Hra.
  pose proof HBR as (B0 & B1 & B2 & B3 & B4). pose proof sp0_range as SR0. pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  set (E2 := retE E' nx R2). pose proof (retE_agree E' nx R2 : env_agree nx E' E2) as Hag2.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  assert (HA2 : bv_unsigned (ev E2 (nx + 4)) = A) by (unfold E2; rewrite retE_a0, HA0; apply u64_of_Z; lia).
  assert (Hva0 : APC.expr_vars_lt nx a0e = true) by (apply CH.nth_vars_lt; exact V1).
  apply (HIH j cj fx' E2 R2 M2 model2 Hcj).
  -
    split.
    + rewrite X3. apply (ret_regs E' _ nx R' R2 HR V1). exact (regs_preserved_kept R' R2 HRP).
    + unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in X. specialize (X Y HY). unfold malloc_entry_ok in X.
      lazymatch type of X with (if ?b then _ else _) = _ => destruct b eqn:C1 end.
      { eapply (entry_across E' E2 nx M' M2 _ _ _ (ci_csp ci) Y HagE' (blocks_in_range_of _ _ _ _ HH) Hc1 Hc2 HK); [| exact Hpc | exact Hag2 | exact C1].
        unfold know_ok. apply Forall_app. split; [exact HK|].
        apply (APS.know_ok_havoc (hl_segs L) E' M' M' _ _ _ _ HK); [reflexivity | apply mem_grows_refl]. }
      destruct (APC.kentry_eqb Y _) eqn:C2.
      { apply APS.kentry_eqb_eq in C2. subst Y. apply (scratch_unk E2 M2 (ci_csp ci) HagE2 Hc1 Hc2). exact (proj2 Hpc). }
      exact (fresh_fact_sound E' E2 nx M' M2 _ cr _ _ _ a0e A n Y HagE' HH HK Hag2 HA2 Hva0 eq_refl HBR Hap Hdef X).
  -
    apply (amb_malloc i j E E2 M' M2 model model2 (sp0 + ci_csp ci) A n cr Hmo Hbv HagE Hfr Hdf);
      [unfold cur; rewrite <- Hden; exact Hpc | lia | lia | exact Hbv2 | unfold cur; rewrite <- Hden; exact HH2 | | |].
    + eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4] | eapply CC.env_agree_le; [exact Hag2 | lia]].
    + rewrite X1. unfold den at 1. cbn [map fst snd edenot]. rewrite HA2. fold (den E2 (nth i BLS [])).
      rewrite <- (SR.edenot_agree_AP nx E' E2 a0e Hag2 Hva0). fold n. rewrite (den_agree nx E' E2 _ Hag2 X0). rewrite Hden. reflexivity.
    + apply HC2. replace (CC.cp_nx cj - APC.NCS)%nat with nx by lia. exact Hag2.
  - exact HFP.
  - apply Hmeas. exact Hag2.
Qed.

Lemma den_remove : forall E p BL q sz, find (fun b : expr * expr => expr_eqb (fst b) p) BL = Some (q, sz) ->
  base.NoDup (map fst (den E BL ++ LBrest)) ->
  In (bv_unsigned (edenot E p), bv_unsigned (edenot E sz)) (den E BL)
  /\ lb_remove (bv_unsigned (edenot E p)) (den E BL ++ LBrest) = den E (CH.remove_first p BL) ++ LBrest.
Proof.
  intros E p BL. induction BL as [|[x y] r IH]; intros q sz Hf Hnd; [discriminate|].
  cbn [find fst] in Hf. cbn [CH.remove_first fst]. destruct (expr_eqb x p) eqn:Ex.
  - injection Hf as <- <-. apply expr_eqb_eq in Ex. subst x. split; [left; reflexivity|].
    cbn [den map app lb_remove fst snd]. rewrite Z.eqb_refl. reflexivity.
  - cbn [den map app fst snd] in Hnd. apply list_relations.list.NoDup_cons in Hnd as [Hni Hnd].
    destruct (IH q sz Hf Hnd) as [I1 I2]. split; [right; exact I1|].
    cbn [den map app lb_remove fst snd]. destruct (Z.eqb_spec (bv_unsigned (edenot E x)) (bv_unsigned (edenot E p))) as [e|ne].
    + exfalso. apply Hni. apply list_elem_of_In. rewrite e. rewrite map_app. apply in_or_app. left.
      change (bv_unsigned (edenot E p)) with (fst (bv_unsigned (edenot E p), bv_unsigned (edenot E sz))). apply in_map. exact I1.
    + fold (den E r). rewrite I2. reflexivity.
Qed.

Definition free_entry_ok (cells kn2 : list kentry) (nx : nat) (csp : Z) (BLj : CA.blocks) (X : kentry) : bool :=
  if (CC.has_cell kn2 X && CH.survive_chk d cells csp BLj X && APC.kentry_vars_lt nx X)%bool then true
  else APC.kentry_eqb X (KUnk (SA (EVar 2) (csp - HSTK)) (ELit HSTK)).

Definition free_chk (FREE : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match common_chk c ps cj BLi with
  | Some ci =>
      let cells := SR.ps_cells ps in let regs := ci_regs ci in let nx := ci_nx ci in
      let p := nth 10 regs (ELit 0) in
      match find (fun b : expr * expr => expr_eqb (fst b) p) BLi with
      | Some (_, sz) =>
          let kn1 := cells ++ APC.kn_havoc cells (EVar 2) (ci_csp ci - HSTK) (ELit HSTK) in
          let kn2 := kn1 ++ APC.kn_cutout kn1 p 0 sz in
          (Z.eqb (SR.ps_pc ps) FREE
           && CA.regs_eqb (CC.cp_regs cj) (APC.sr_fresh regs APC.caller_saved nx)
           && blocks_eqb BLj (CH.remove_first p BLi) && blocks_vars_lt nx BLi
           && forallb (free_entry_ok cells kn2 nx (ci_csp ci) BLj) (CC.cp_know cj))%bool
      | None => false
      end
  | None => false
  end.

Lemma remove_first_incl : forall p BL b, In b (CH.remove_first p BL) -> In b BL.
Proof.
  intros p BL. induction BL as [|x r IH]; intros b H; [destruct H|]. cbn [CH.remove_first] in H.
  destruct (expr_eqb (fst x) p); [right; exact H|]. destruct H as [H|H]; [left; exact H | right; exact (IH b H)].
Qed.

Lemma free_leaf_ok : forall i c ps j cj FREE,
  hl_free L = FREE -> nth_error CPS j = Some cj ->
  free_chk FREE c ps cj (nth i BLS []) (nth j BLS []) = true ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
       forall E2, env_agree (CC.cp_nx cj - APC.NCS) E' E2 -> Cred j E2 cr) ->
  CC.leaf_ok (hl_segs L) CPS heap_amb K FPI i c ps.
Proof.
  intros i c ps j cj FREE HM Hcj Hchk HCred fx' E R M model E' R' M' HAt HA HFP Hag HLF HIH.
  unfold free_chk in Hchk. destruct (common_chk c ps cj (nth i BLS [])) as [ci|] eqn:Hc; [|discriminate].
  destruct (common_sound i c ps cj ci E R M model E' R' M' Hc HAt HA Hag HLF)
    as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := ci_nx ci) in *. set (p := nth 10 (ci_regs ci) (ELit 0)) in *.
  destruct (find (fun b : expr * expr => expr_eqb (fst b) p) (nth i BLS [])) as [[q sz]|] eqn:Hfind; [|discriminate].
  repeat (apply andb_prop in Hchk as [Hchk ?X]). apply Z.eqb_eq in Hchk. apply regs_eqb_eq in X2. apply blocks_eqb_eq in X1.
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof (HCred E E' R' M M' cr HagE Hag HLF HC) as HC2.
  unfold cur in HH. rewrite <- Hden in HH.
  destruct (blocks_facts _ _ _ _ HH) as (Hbf & _ & Hnd).
  destruct (den_remove E' p _ q sz Hfind Hnd) as [Hin Hrm].
  set (A := bv_unsigned (edenot E' p)) in *. set (n := bv_unsigned (edenot E' sz)) in *.
  rewrite Hchk, <- HM.
  eapply (hio_free L SCFG HI HIok fx' R' M' model _ cr A n K HH (proj1 Hmo) (proj1 (proj2 Hmo)) (proj2 (proj2 Hmo)));
    [apply in_or_app; left; exact Hin | | exact Htp | exact Hret | rewrite Hsp; exact Hstk | exact K_nil |].
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. fold p. unfold A.
    symmetry. apply Z_to_bv_bv_unsigned. }
  intros R2 M2 model2 HRP Hpres Hbv2 HH2. rewrite Hsp in Hpres. rewrite Hra. rewrite Hrm in Hpres, HH2.
  pose proof sp0_range as SR0. pose proof ceil_lo as CL. destruct STK as (_ & S2 & S3 & S4 & S5).
  set (E2 := retE E' nx R2). pose proof (retE_agree E' nx R2 : env_agree nx E' E2) as Hag2.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  assert (Hbr' : blocks_in_range (den E' (CH.remove_first p (nth i BLS [])) ++ LBrest)).
  { intros b Hb. rewrite <- Hrm in Hb. apply L5C.in_lb_remove in Hb. exact (proj1 (Hbf b Hb)). }
  assert (Hbvj : blocks_vars_lt nx (CH.remove_first p (nth i BLS [])) = true).
  { unfold blocks_vars_lt in *. apply forallb_forall. intros b Hb. rewrite forallb_forall in X0. exact (X0 b (remove_first_incl _ _ _ Hb)). }
  apply (HIH j cj fx' E2 R2 M2 model2 Hcj).
  - split.
    + rewrite X2. apply (ret_regs E' _ nx R' R2 HR V1). exact (regs_preserved_kept R' R2 HRP).
    + unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in X. specialize (X Y HY). unfold free_entry_ok in X. rewrite X1 in X.
      lazymatch type of X with (if ?b then _ else _) = _ => destruct b eqn:C1 end.
      { eapply (entry_across E' E2 nx M' M2 _ _ _ (ci_csp ci) Y HagE' Hbr' Hc1 Hc2 HK); [| exact (proj1 Hpres) | exact Hag2 | exact C1].
        assert (Hk1 : know_ok (hl_segs L) E' M' (SR.ps_cells ps ++ APC.kn_havoc (SR.ps_cells ps) (EVar 2) (ci_csp ci - HSTK) (ELit HSTK))).
        { unfold know_ok. apply Forall_app. split; [exact HK|]. apply (APS.know_ok_havoc (hl_segs L) E' M' M' _ _ _ _ HK); [reflexivity | apply mem_grows_refl]. }
        unfold know_ok. apply Forall_app. split; [exact Hk1|]. apply (APS.know_ok_cutout (hl_segs L) E' M' M'); [exact Hk1 | reflexivity]. }
      apply APS.kentry_eqb_eq in X. subst Y. apply (scratch_unk E2 M2 (ci_csp ci) HagE2 Hc1 Hc2). exact (proj2 (proj1 Hpres)).
  - apply (amb_free i j E E2 M' M2 model model2 (sp0 + ci_csp ci) A cr Hmo Hbv HagE Hfr Hdf);
      [unfold cur; rewrite <- Hden, Hrm; exact Hpres | lia | lia | exact Hbv2 | unfold cur; rewrite <- Hden, Hrm; exact HH2 | | |].
    + eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4] | eapply CC.env_agree_le; [exact Hag2 | lia]].
    + unfold cur. rewrite <- Hden, Hrm, X1. rewrite (den_agree nx E' E2 _ Hag2 Hbvj). reflexivity.
    + apply HC2. replace (CC.cp_nx cj - APC.NCS)%nat with nx by lia. exact Hag2.
  - exact HFP.
  - apply Hmeas. exact Hag2.
Qed.

Definition copy1_spec (pc : Z) : Prop :=
  forall (fx : FPState) mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    1 <= n -> length bs = Z.to_nat n ->
    rdn (hl_segs L) mem0 src (length bs) = Some bs ->
    store_ok (hl_segs L) mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    Hoare.ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps (hl_segs L) (@mkst fx regs (Z_to_bv 64 pc) mem0 (seg_rom (hl_segs L)))
                         (@mkst fx regs' ret (wbytes mem0 dst bs) (seg_rom (hl_segs L)))
      /\ APSX.kept_ok regs regs' /\ getr regs' 10%bv = dst.
Lemma copy1_of_copy_spec : forall pc, (forall fx : FPState, @APSX.copy_spec fx (hl_segs L) pc) -> copy1_spec pc.
Proof using L.
  intros pc H fx mem0 dst src n bs regs ret Hn Hl Hr Hs Hd H1 H2 Hret G1 G10 G11 G12.
  exact (H fx mem0 dst src n bs regs ret (Z.lt_le_incl 0 n (Z.lt_le_trans 0 1 n Z.lt_0_1 Hn)) Hl Hr Hs Hd H1 H2 Hret G1 G10 G11 G12).
Qed.

Lemma rdn_defined : forall (M : mem) (n : nat) (a : Z),
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn (hl_segs L) M (Z_to_bv 64 a) n = Some bs /\ length bs = n
             /\ forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros M. induction n as [|n IH]; intros a H.
  - exists []. split; [reflexivity|]. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
  - destruct (IH (a + 1)) as (bs & Hr & Hl & Hp). { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 a)) as [b|] eqn:Hb; [|contradiction].
    exists (b :: bs). cbn [rdn]. rewrite Hb. rewrite CH.bv_succ_Z, Hr. split; [reflexivity|]. split; [cbn [length]; rewrite Hl; reflexivity|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r; exact Hb|].
    replace (a + i) with (a + 1 + (i - 1)) by lia. rewrite Hp by lia. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Definition copy_entry_ok (cells kn1 : list kentry) (db : expr) (dk : Z) (sb : expr) (sk : Z) (n : expr) (nx : nat) (X : kentry) : bool :=
  if (CC.has_cell kn1 X && APC.kentry_vars_lt nx X)%bool then true
  else if APC.kentry_eqb X (KUnk (SA db dk) n) then true
  else match X with
       | KBlob (SA b k) m id => (expr_eqb b db && Z.eqb k dk && expr_eqb m n && CC.has_cell cells (KBlob (SA sb sk) n id))%bool
       | _ => false
       end.

Definition copy_chk (PC : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : bool :=
  match common_chk c ps cj BLi with
  | Some ci =>
      let cells := SR.ps_cells ps in let regs := ci_regs ci in let nx := ci_nx ci in
      let dst := nth 10 regs (ELit 0) in let src := nth 11 regs (ELit 0) in let n := nth 12 regs (ELit 0) in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      let kn1 := APC.kn_havoc cells db dk n in
      (Z.eqb (SR.ps_pc ps) PC
       && CA.regs_eqb (CC.cp_regs cj) (sr_upd (APC.sr_fresh regs APC.caller_saved nx) 10 dst)
       && blocks_eqb BLj BLi && blocks_vars_lt nx BLi
       && CH.within cells (CH.foot_regs d BLi) db dk n
       && existsb (fun X => match X with KWr (SA b k) m => xinside cells db dk n b k m | _ => false end) cells
       && existsb (fun X => match X with KUnk (SA b k) m | KBlob (SA b k) m _ => xinside cells sb sk n b k m | _ => false end) cells
       && APC.fact_ok cells (KDisj (SA db dk) n (SA sb sk) n)
       && APC.fact_ok cells (KRange n 1 4611686018427387904)
       && APC.fact_ok cells (KRange dst 0 4611686018427387904) && APC.fact_ok cells (KRange src 0 4611686018427387904)
       && forallb (copy_entry_ok cells kn1 db dk sb sk n nx) (CC.cp_know cj))%bool
  | None => false
  end.

Lemma regs_ok_upd_same : forall E sr (R : bvmap 5 word) e, regs_ok E sr R -> getr R 10%bv = edenot E e -> regs_ok E (sr_upd sr 10 e) R.
Proof.
  intros E sr R e HR He r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb_spec (ridx r) 10) as [e10|ne].
    + assert (r = 10%bv) as -> by (rewrite <- (CC.reg_of_ridx r), e10; apply bv_eq; reflexivity). exact He.
    + specialize (HR r). unfold sr_get in HR. rewrite Er in HR. exact HR.
Qed.

Lemma split_start : forall E e b k, split_lit e = (b, k) -> 0 <= estart E (SA b k) < 2 ^ 64 -> bv_unsigned (edenot E e) = estart E (SA b k).
Proof.
  intros E e b k Hs Hr. rewrite (APS.split_lit_denot E e b k Hs). unfold estart in *. cbn [a_base a_off] in *. apply u64_of_Z. exact Hr.
Qed.

Lemma split_lit_vars : forall nx e b k, split_lit e = (b, k) -> APC.expr_vars_lt nx e = true -> APC.expr_vars_lt nx b = true.
Proof.
  intros nx e b k Hs Y. unfold split_lit in Hs. destruct e as [z|v|op a1 a2| | | | |]; try (injection Hs as <- <-; first [exact Y | reflexivity]).
  destruct op; try (injection Hs as <- <-; exact Y). destruct a2; try (injection Hs as <- <-; exact Y).
  injection Hs as <- <-. cbn [APC.expr_vars_lt] in Y. apply andb_prop in Y as [Y _]. exact Y.
Qed.

Lemma copy_leaf_ok : forall i c ps j cj PC,
  copy1_spec PC -> nth_error CPS j = Some cj ->
  copy_chk PC c ps cj (nth i BLS []) (nth j BLS []) = true ->
  (forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
       forall E2, env_agree (CC.cp_nx cj - APC.NCS) E' E2 -> Cred j E2 cr) ->
  CC.leaf_ok (hl_segs L) CPS heap_amb K FPI i c ps.
Proof.
  intros i c ps j cj PC HSPEC Hcj Hchk HCred fx' E R M model E' R' M' HAt HA HFP Hag HLF HIH.
  unfold copy_chk in Hchk. destruct (common_chk c ps cj (nth i BLS [])) as [ci|] eqn:Hc; [|discriminate].
  destruct (common_sound i c ps cj ci E R M model E' R' M' Hc HAt HA Hag HLF)
    as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hret] (Hsp & Hc1 & Hc2) Hstk Htp HagE' Hden Hmeas].
  set (nx := ci_nx ci) in *. set (dste := nth 10 (ci_regs ci) (ELit 0)) in *. set (srce := nth 11 (ci_regs ci) (ELit 0)) in *.
  set (ne := nth 12 (ci_regs ci) (ELit 0)) in *.
  destruct (split_lit dste) as [db dk] eqn:Hsd. destruct (split_lit srce) as [sb sk] eqn:Hss.
  repeat (apply andb_prop in Hchk as [Hchk ?X]). apply Z.eqb_eq in Hchk. apply regs_eqb_eq in X9. apply blocks_eqb_eq in X8.
  pose proof (APS.fact_ok_sound (hl_segs L) E' M' _ _ HK X3) as Fdisj. pose proof (APS.fact_ok_sound (hl_segs L) E' M' _ _ HK X2) as Fn.
  pose proof (APS.fact_ok_sound (hl_segs L) E' M' _ _ HK X1) as Fd. pose proof (APS.fact_ok_sound (hl_segs L) E' M' _ _ HK X0) as Fs.
  cbn [kentry_ok] in Fdisj, Fn, Fd, Fs. unfold elenZ in Fdisj.
  set (n := bv_unsigned (edenot E' ne)) in *. set (D := bv_unsigned (edenot E' dste)) in *. set (S := bv_unsigned (edenot E' srce)) in *.
  assert (Hva : APC.expr_vars_lt nx dste = true /\ APC.expr_vars_lt nx ne = true) by (split; apply CH.nth_vars_lt; exact V1).
  assert (G10 : getr R' 10%bv = edenot E' dste).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. reflexivity. }
  assert (G11 : getr R' 11%bv = edenot E' srce).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. reflexivity. }
  assert (G12 : getr R' 12%bv = Z_to_bv 64 n).
  { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. unfold n. symmetry. apply Z_to_bv_bv_unsigned. }

  apply existsb_exists in X5 as (YW & HYW & HxW). destruct YW as [| | | | | |[wb wk] wm| | |]; try discriminate.
  pose proof (proj1 (Forall_forall _ _) HK _ HYW) as HW. cbn [kentry_ok] in HW. destruct HW as [(W1 & W2 & W3 & W4) HW].
  destruct (xinside_sound (hl_segs L) E' M' _ _ _ _ _ _ _ HK HxW) as [IW1 IW2]. fold n in IW2. change (elenZ E' ne) with n in IW2.
  assert (ED : estart E' (SA db dk) = D) by (symmetry; apply (split_start E' dste db dk Hsd); unfold n in *; lia).
  assert (HsrcD : exists sa sm, (kentry_ok (hl_segs L) E' M' (KUnk sa sm)) /\ estart E' sa <= estart E' (SA sb sk) /\ estart E' (SA sb sk) + n <= estart E' sa + elenZ E' sm).
  { apply existsb_exists in X4 as (YS & HYS & HxS). pose proof (proj1 (Forall_forall _ _) HK _ HYS) as HS.
    destruct YS as [| |[ub uk] um uid| | | | | | |[ub uk] um]; try discriminate;
      destruct (xinside_sound (hl_segs L) E' M' _ _ _ _ _ _ _ HK HxS) as [IS1 IS2]; exists (SA ub uk), um; (split; [|split; [exact IS1 | exact IS2]]).
    - cbn [kentry_ok] in HS |- *. destruct HS as (F & Hl & Hz). split; [exact F|]. intros k Hk. rewrite (Hz k Hk). discriminate.
    - exact HS. }
  destruct HsrcD as (sa & sm & [(U1 & U2 & U3 & U4) HU] & IS1 & IS2).
  assert (ES : estart E' (SA sb sk) = S) by (symmetry; apply (split_start E' srce sb sk Hss); unfold n in *; lia).
  rewrite ED, ES in *.
  destruct (rdn_defined M' (Z.to_nat n) S) as (bs & Hrd & Hlen & Hbs).
  { intros k Hk. replace (S + k) with (estart E' sa + (S - estart E' sa + k)) by lia. apply HU. lia. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof (HCred E E' R' M M' cr HagE Hag HLF HC) as HC2.
  assert (Dw : Z_to_bv 64 D = getr R' 10%bv) by (rewrite G10; unfold D; apply Z_to_bv_bv_unsigned).
  destruct (HSPEC fx' M' (getr R' 10%bv) (getr R' 11%bv) n bs R' (getr R' 1%bv)) as (R2 & Hms & Hkept & Ha0); try reflexivity.
  { unfold n in *; lia. } { exact Hlen. } { rewrite Hlen, G11. unfold S in Hrd. rewrite Z_to_bv_bv_unsigned in Hrd. exact Hrd. }
  { rewrite Hlen, <- Dw. replace D with (estart E' (SA wb wk) + (D - estart E' (SA wb wk))) by lia. apply HW; lia. }
  { rewrite G10, G11. fold D S. lia. } { rewrite G11. fold S. lia. } { rewrite G10. fold D. lia. } { exact Hret. } { exact G12. }
  rewrite Hchk. eapply L5.cps_of_msteps; [exact (proj1 Hmo) | exact (proj1 (proj2 Hmo)) | exact Hms |]. rewrite Hra.
  set (M2 := wbytes M' (getr R' 10%bv) bs) in *.
  assert (UD : bv_unsigned (getr R' 10%bv) = D) by (rewrite G10; reflexivity).
  assert (Hlz : Z.of_nat (length bs) = n) by (rewrite Hlen; unfold n in *; lia).
  assert (Hout : forall x : word, bv_unsigned x < D \/ D + n <= bv_unsigned x -> M2 x = M' x).
  { intros x [Hx|Hx]; unfold M2; [apply wbytes_below; rewrite ?UD, ?Hlz; lia | apply wbytes_above; rewrite UD, Hlz; lia]. }
  assert (Hin2 : forall k, 0 <= k < n -> M2 (Z_to_bv 64 (D + k)) = Some (nth (Z.to_nat k) bs (Z_to_bv 8 0))).
  { intros k Hk. unfold M2. replace (D + k) with (bv_unsigned (getr R' 10%bv) + Z.of_nat (Z.to_nat k)) by (rewrite UD; lia).
    apply wbytes_nth; [rewrite UD, Hlz; lia | lia]. }
  set (E2 := retE E' nx R2). pose proof (retE_agree E' nx R2 : env_agree nx E' E2) as Hag2.
  assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  assert (Hkn1 : know_ok (hl_segs L) E' M2 (APC.kn_havoc (SR.ps_cells ps) db dk ne)).
  { apply (APS.know_ok_havoc (hl_segs L) E' M' M2 _ _ _ _ HK); [| unfold M2; apply wbytes_grows]. intros x Hx. apply Hout. rewrite ED in Hx. exact Hx. }
  assert (UNK2 : kentry_ok (hl_segs L) E' M2 (KUnk (SA db dk) ne)).
  { cbn [kentry_ok]. rewrite ED. change (elenZ E' ne) with n. split; [unfold flat; rewrite ED; unfold n in *; lia|]. intros k Hk. rewrite (Hin2 k Hk). discriminate. }
  assert (TR : forall Y, APC.kentry_vars_lt nx Y = true -> kentry_ok (hl_segs L) E' M2 Y -> kentry_ok (hl_segs L) E2 M2 Y).
  { intros Y Hv HY. assert (G : know_ok (hl_segs L) E2 M2 [Y]).
    { apply (APS.know_ok_agree' (hl_segs L) nx E' E2 M2 [Y] Hag2); [cbn [APC.kn_vars_lt]; rewrite Hv; reflexivity | constructor; [exact HY | constructor]]. }
    inversion G; assumption. }
  assert (Vd : APC.expr_vars_lt nx db = true) by exact (split_lit_vars nx dste db dk Hsd (proj1 Hva)).
  apply (HIH j cj fx' E2 R2 M2 model Hcj).
  - split.
    + rewrite X9. apply regs_ok_upd_same; [apply (ret_regs E' _ nx R' R2 HR V1); intros r Hr Hn; exact (Hkept r Hr Hn)|].
      rewrite Ha0, G10. exact (SR.edenot_agree_AP nx E' E2 dste Hag2 (proj1 Hva)).
    + unfold know_ok. apply Forall_forall. intros Y HY. rewrite forallb_forall in X. specialize (X Y HY). unfold copy_entry_ok in X.
      lazymatch type of X with (if ?b then _ else _) = _ => destruct b eqn:C1 end.
      { apply andb_prop in C1 as [C1 C2]. apply CC.has_cell_In in C1. exact (TR Y C2 (proj1 (Forall_forall _ _) Hkn1 _ C1)). }
      destruct (APC.kentry_eqb Y _) eqn:C2.
      { apply APS.kentry_eqb_eq in C2. subst Y. apply TR; [|exact UNK2]. unfold APC.kentry_vars_lt, APC.saddr_vars_lt. cbn [a_base]. rewrite Vd, (proj2 Hva). reflexivity. }
      destruct Y as [| |[yb yk] ym yid| | | | | | |]; try discriminate. repeat (apply andb_prop in X as [X ?Z]).
      apply expr_eqb_eq in X, Z0. apply Z.eqb_eq in Z1. subst yb yk ym. apply CC.has_cell_In in Z.
      apply TR; [unfold APC.kentry_vars_lt, APC.saddr_vars_lt; cbn [a_base]; rewrite Vd, (proj2 Hva); reflexivity|].
      pose proof (proj1 (Forall_forall _ _) HK _ Z) as HB. cbn [kentry_ok] in HB |- *. rewrite ED, ES in *. change (elenZ E' ne) with n in *.
      destruct HB as (FB & LB & PB). split; [unfold flat; rewrite ED; unfold n in *; lia|]. split; [exact LB|].
      intros k Hk. rewrite (Hin2 k Hk). rewrite <- (PB k Hk). symmetry. apply Hbs. lia.
  - apply (amb_pure_step i j E E2 M' M2 model (conj Hmo (conj Hbv (conj HagE (conj (ex_intro _ cr (conj HH HC)) (conj Hfr Hdf)))))).
    + intros a Hn. apply Hout. destruct (Z_lt_dec (bv_unsigned a) D) as [G1|G1]; [left; exact G1|].
      destruct (Z_le_dec (D + n) (bv_unsigned a)) as [G2|G2]; [right; exact G2|]. exfalso. apply Hn.
      destruct (within_sem E' M' _ _ db dk ne HK X6) as (r & Hr & Hs). rewrite <- Hden.
      apply (foot_regs_sem E' _ r _ HagE' Hr). apply Hs. rewrite ED. change (elenZ E' ne) with n. lia.
    + unfold M2. apply wbytes_grows.
    + eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4] | eapply CC.env_agree_le; [exact Hag2 | lia]].
    + rewrite X8. rewrite (den_agree nx E' E2 _ Hag2 X7). exact Hden.
    + intros cr' HC'. apply (HCred E E' R' M M' cr' HagE Hag HLF HC'). replace (CC.cp_nx cj - APC.NCS)%nat with nx by lia. exact Hag2.
  - exact HFP.
  - apply Hmeas. exact Hag2.
Qed.

Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable MALLOC FREE : Z.
Variable COPIES : list Z.
Local Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Definition ret_of (i k : nat) : option nat :=
  match find (fun r : nat * nat * nat * Z => let '(_, i', k', _) := r in (Nat.eqb i i' && Nat.eqb k k')%bool) RETS with
  | Some (j, _, _, _) => Some j
  | None => None
  end.
Definition is_call (pc : Z) : bool := (Z.eqb pc MALLOC || Z.eqb pc FREE || existsb (Z.eqb pc) COPIES)%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => goto_amb_chk c (nth i BLS []) (nth j BLS []) s
  | CC.TOther pc =>
      if is_call pc then
        match ret_of i k with
        | Some j => match nth_error CPS j with
                    | Some cj => if Z.eqb pc MALLOC then malloc_chk MALLOC c ps cj (nth i BLS []) (nth j BLS [])
                                 else if Z.eqb pc FREE then free_chk FREE c ps cj (nth i BLS []) (nth j BLS [])
                                 else copy_chk pc c ps cj (nth i BLS []) (nth j BLS [])
                    | None => false
                    end
        | None => false
        end
      else foot_chk c (nth i BLS [])
  end.
Definition heap_chk : bool := leaves_all CPS TAGS leaf_chk.
Lemma heap_chk_sound : heap_chk = true -> forall i c tags k ps t,
  nth_error CPS i = Some c -> nth_error TAGS i = Some tags -> nth_error (CC.cp_PSS c) k = Some ps -> nth_error tags k = Some t ->
  leaf_chk i c k ps t = true.
Proof. exact (leaves_all_nth CPS TAGS leaf_chk). Qed.

Lemma exit_amb : heap_chk = true -> forall i c k ps pc, is_leaf i c k ps (CC.TOther pc) -> is_call pc = false ->
  forall E E' R R' M M' model, CC.At (hl_segs L) c E R M -> heap_amb i E M model -> env_agree (CC.cp_nx c) E E' ->
    CC.leaf_facts (hl_segs L) c ps E' R' M M' -> heap_amb i E M' model.
Proof.
  intros HC i c k ps pc (tags & Hc & Htg & Hps & Ht) Hnc E E' R R' M M' model HAt HA Hag HLF.
  pose proof (heap_chk_sound HC i c tags k ps _ Hc Htg Hps Ht) as X. cbn [leaf_chk] in X. rewrite Hnc in X.
  exact (leaf_amb i c ps E E' R R' M M' model X HAt HA Hag HLF).
Qed.

Theorem heap_cert_sound :
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps (hl_segs L) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> CC.plan_sound (hl_segs L) c) ->
  CC.tags_chk CPS TAGS NF = true ->
  heap_chk = true ->
  hl_malloc L = MALLOC -> hl_free L = FREE -> (forall pc, In pc COPIES -> copy1_spec pc) ->

  (forall i c k ps j s, is_leaf i c k ps (CC.TGoto j s) -> forall E E' R' M M' cr, env_agree NF E0 E ->
       env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr -> Cred j (CC.env_over NF s E') cr) ->
  (forall i c k ps j cj, is_leaf i c k ps (CC.TOther MALLOC) -> ret_of i k = Some j -> nth_error CPS j = Some cj -> forall E E' R' M M' cr, env_agree NF E0 E ->
       env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
       let n := bv_unsigned (edenot E' (CA.ps_reg ps 10)) in
       credit_ok L cr n /\ forall E2, env_agree (CC.cp_nx cj - APC.NCS) E' E2 -> Cred j E2 (debit L cr n)) ->
  (forall i c k ps pc j cj, is_leaf i c k ps (CC.TOther pc) -> is_call pc = true -> pc <> MALLOC -> ret_of i k = Some j -> nth_error CPS j = Some cj ->
       forall E E' R' M M' cr, env_agree NF E0 E -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> Cred i E cr ->
       forall E2, env_agree (CC.cp_nx cj - APC.NCS) E' E2 -> Cred j E2 cr) ->

  (forall i c k ps pc, is_leaf i c k ps (CC.TOther pc) -> is_call pc = false -> CC.leaf_ok (hl_segs L) CPS heap_amb K FPI i c ps) ->
  forall i c (fx : FPState) E R M model,
    nth_error CPS i = Some c -> CC.At (hl_segs L) c E R M -> heap_amb i E M model -> FPI fx ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M (seg_rom (hl_segs L))) model) K.
Proof.
  intros FPM PLANS TCHK HCHK HMAL HFREE HCOPY CG CM CR EXITS.
  apply (CC.cutcert_sound_tagged (hl_segs L) CPS TAGS NF heap_amb K FPI FPM PLANS TCHK heap_amb_model).
  - intros i c tags k ps j s Hc Htg Hps Ht.
    pose proof (heap_chk_sound HCHK i c tags k ps _ Hc Htg Hps Ht) as X. cbn [leaf_chk] in X.
    apply (goto_amb i c ps j s X). exact (CG i c k ps j s (ex_intro _ tags (conj Hc (conj Htg (conj Hps Ht))))).
  - intros i c tags k ps pc Hc Htg Hps Ht.
    assert (IL : is_leaf i c k ps (CC.TOther pc)) by (exists tags; repeat split; assumption).
    pose proof (heap_chk_sound HCHK i c tags k ps _ Hc Htg Hps Ht) as X. cbn [leaf_chk] in X.
    destruct (is_call pc) eqn:Hcall; [|exact (EXITS i c k ps pc IL Hcall)].
    destruct (ret_of i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate].
    destruct (Z.eqb_spec pc MALLOC) as [->|Hnm].
    { exact (malloc_leaf_ok i c ps j cj MALLOC HMAL Hcj X (CM i c k ps j cj IL Hret Hcj)). }
    destruct (Z.eqb_spec pc FREE) as [->|Hnf].
    { exact (free_leaf_ok i c ps j cj FREE HFREE Hcj X (CR i c k ps FREE j cj IL Hcall Hnm Hret Hcj)). }
    assert (Hcp : In pc COPIES).
    { unfold is_call in Hcall. apply orb_prop in Hcall as [Hcall|Hcall]; [apply orb_prop in Hcall as [Y|Y]; apply Z.eqb_eq in Y; contradiction|].
      apply existsb_exists in Hcall as (x & Hx & He). apply Z.eqb_eq in He. subst x. exact Hx. }
    exact (copy_leaf_ok i c ps j cj pc (HCOPY pc Hcp) Hcj X (CR i c k ps pc j cj IL Hcall Hnm Hret Hcj)).
Qed.

End Heap.
End CH2.
