(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages LazyModel NodesA Shadow NodesA_mm NodesA_mmW NodesA_madv BackingAlgebraA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase KLiveCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanRep AsanFakeStack AsanPS AsanKern AsanClient AsanDepot AsanBudget AsanBudget2 AsanRepFrame AsanFrame AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_balloc5 B_mmchk5 B_bevents5 B_bevents5b BF_fakestack_rep BF_place.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Ltac mproj := rewrite ?m_vmmaps_vm_add_lazy, ?m_vm_lazy_vm_add_lazy, ?m_vm_materialized_vm_add_lazy,
                      ?m_vmmaps_vm_forget_range, ?m_vm_lazy_vm_forget_range, ?m_vm_materialized_vm_forget_range,
                      ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps, ?m_vm_materialized_with_vmmaps,
                      ?m_vmmaps_with_vm_backing, ?m_vm_lazy_with_vm_backing, ?m_vm_materialized_with_vm_backing in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma filter_nth2 : forall {A} (f : A -> bool) l i j e1 e2,
  (i < j)%nat -> nth_error (List.filter f l) i = Some e1 -> nth_error (List.filter f l) j = Some e2 ->
  exists i' j', (i' < j')%nat /\ nth_error l i' = Some e1 /\ nth_error l j' = Some e2.
Proof.
  intros A f l. induction l as [|x l IH]; intros i j e1 e2 Hij H1 H2.
  - cbn in H1. destruct i; discriminate.
  - cbn [List.filter] in H1, H2. destruct (f x).
    + destruct i as [|i]; destruct j as [|j]; try lia.
      * cbn in H1. injection H1 as ->. cbn in H2.
        assert (exists j', nth_error l j' = Some e2) as (j' & Hj').
        { clear -H2. revert j H2. induction l as [|y l IH]; intros j H2; [cbn in H2; destruct j; discriminate|].
          cbn [List.filter] in H2. destruct (f y).
          - destruct j as [|j]; [exists 0%nat; exact H2|]. destruct (IH j H2) as (j' & Hj'). exists (Datatypes.S j'). exact Hj'.
          - destruct (IH j H2) as (j' & Hj'). exists (Datatypes.S j'). exact Hj'. }
        exists 0%nat, (Datatypes.S j'). split; [lia|]. split; [reflexivity| exact Hj'].
      * cbn in H1, H2. destruct (IH i j e1 e2 ltac:(lia) H1 H2) as (i' & j' & Q & Q1 & Q2).
        exists (Datatypes.S i'), (Datatypes.S j'). split; [lia|]. split; assumption.
    + destruct (IH i j e1 e2 Hij H1 H2) as (i' & j' & Q & Q1 & Q2). exists (Datatypes.S i'), (Datatypes.S j'). split; [lia|]. split; assumption.
Qed.

Lemma mwf_filter : forall f l, mwf l -> mwf (List.filter f l).
Proof.
  intros f l [D W]. split.
  - intros i j e1 e2 Hi Hj NE.
    destruct (Nat.lt_ge_cases i j) as [LT|GE].
    + destruct (filter_nth2 f l i j e1 e2 LT Hi Hj) as (i' & j' & Q & Q1 & Q2). exact (D i' j' e1 e2 Q1 Q2 ltac:(lia)).
    + destruct (filter_nth2 f l j i e2 e1 ltac:(lia) Hj Hi) as (j' & i' & Q & Q1 & Q2).
      destruct (D j' i' e2 e1 Q1 Q2 ltac:(lia)); lia.
  - apply Forall_forall. intros e He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) W e He).
Qed.

Lemma sum_count_filter_split : forall P f l,
  sum_count P l = sum_count P (List.filter f l) + sum_count P (List.filter (fun e => negb (f e)) l).
Proof.
  intros P f l. induction l as [|e l IH]; [reflexivity|]. cbn [List.filter sum_count]. destruct (f e); cbn [negb sum_count]; lia.
Qed.

Lemma sum_count_In_le : forall P l e, In e l -> iv_count P e <= sum_count P l.
Proof.
  intros P l e Hin. induction l as [|x l IH]; [destruct Hin|]. cbn [sum_count].
  pose proof (sum_count_nonneg P l). pose proof (zcount_nonneg P (B x) (Z.to_nat (S x))). unfold iv_count in *.
  destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). lia.
Qed.

Lemma Permutation_fold_add : forall {A} (g : A -> Z) l l',
  Permutation l l' -> fold_right (fun x acc => g x + acc) 0 l = fold_right (fun x acc => g x + acc) 0 l'.
Proof. intros A g l l' P. induction P; cbn [fold_right] in *; lia. Qed.

Lemma fold_add_app : forall {A} (g : A -> Z) l1 l2,
  fold_right (fun x acc => g x + acc) 0 (l1 ++ l2) = fold_right (fun x acc => g x + acc) 0 l1 + fold_right (fun x acc => g x + acc) 0 l2.
Proof. intros A g l1 l2. induction l1 as [|x l1 IH]; cbn [fold_right app]; [lia| rewrite IH; lia]. Qed.

Lemma nth_lt : forall {A} (l : list A) n x, nth_error l n = Some x -> (n < length l)%nat.
Proof. intros A l n x H. apply (proj1 (nth_error_Some l n)). rewrite H. discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section U.
Variables (m : Model) (R L : Z).
Hypothesis WF : model_ivs_wf m.
Hypothesis HR : 0 <= R.
Hypothesis HL : 0 < L.
Hypothesis HE : R + L < 2^64.
Let r : word := Z_to_bv 64 R.
Let n : word := Z_to_bv 64 L.
Hypothesis INM : In (r, n) (vm_maps (m_vmmaps m)).
Hypothesis UNC : forall x, R <= x < R + L -> covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x = false.
Hypothesis DJ : forall e, In e (map_remove (vm_maps (m_vmmaps m)) r) -> ehi e <= R \/ R + L <= elo e.

Lemma unmap_eager_exact : eager_used (m_unmap m R L) <= eager_used m - L.
Proof.
  assert (ur : bv_unsigned r = R) by (apply u64_small; lia).
  assert (un : bv_unsigned n = L) by (apply u64_small; lia).
  rewrite (eager_used_sem _ (unmap_wf m R L WF HR HL HE)), (eager_used_sem _ WF).
  rewrite unmap_maps, (unmap_noaccess m R L), (unmap_lazy m R L HR HL HE).
  pose proof WF as (Wm & Wn & Wl & Wsp).
  destruct (maps_subtract_sem _ R (R + L) Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ R (R + L) Wl ltac:(lia)) as (_ & _ & Cl).
  set (P := fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)).
  rewrite (sum_count_filter_split P (fun p => negb (bv_eqb (fst p) r)) (vm_maps (m_vmmaps m))).
  assert (REM : L <= sum_count P (List.filter (fun e => negb (negb (bv_eqb (fst e) r))) (vm_maps (m_vmmaps m)))).
  { transitivity (iv_count P (r, n)).
    - unfold iv_count, B, S. cbn [fst snd]. rewrite ur, un. rewrite zcount_true; [lia|].
      intros x Hx. unfold P. rewrite UNC; [reflexivity|]. lia.
    - apply sum_count_In_le. apply filter_In. split; [exact INM|]. cbn [fst]. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. }
  assert (KEEP : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps m)) R (R + L) ++ maps_subtract (m_vm_lazy m) R (R + L)) x))
                   (map_remove (vm_maps (m_vmmaps m)) r)
                 = sum_count P (List.filter (fun p => negb (bv_eqb (fst p) r)) (vm_maps (m_vmmaps m)))).
  { unfold map_remove. revert DJ. unfold map_remove. generalize (List.filter (fun p => negb (bv_eqb (fst p) r)) (vm_maps (m_vmmaps m))) as l.
    induction l as [|e l IH]; intros DJ; [reflexivity|]. cbn [sum_count]. rewrite (IH ltac:(intros e' He'; apply DJ; right; exact He')). f_equal.
    unfold iv_count. apply zcount_ext. intros x Hx. pose proof (DJ e (or_introl eq_refl)) as De.
    unfold elo, ehi, B, S, P in *. rewrite Z2Nat.id in Hx by (pose proof (bv_unsigned_in_range 64 (snd e)); lia).
    rewrite !covered_app, Cn, Cl. unfold in_rng.
    assert (FR : (R <=? x) && (x <? R + L) = false).
    { apply Bool.andb_false_iff. clear -De Hx. destruct De as [De|De]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia]. }
    rewrite FR. cbn [negb]. rewrite !Bool.andb_true_r. reflexivity. }
  rewrite KEEP. lia.
Qed.
End U.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AKern_sec_incl : forall E a a2 mo,
  AKern E a mo ->
  (forall sc, In sc (as_sec a2) -> In sc (as_sec a)) ->
  (forall c, get_region a2 c = get_region a c) -> as_ptr_committed a2 = as_ptr_committed a ->
  as_node_blocks a2 = as_node_blocks a -> as_store_blocks a2 = as_store_blocks a ->
  AKern E a2 mo.
Proof.
  intros E a a2 mo K INCL Ereg Eptr Enb Esb. destruct K.
  constructor; rewrite ?Ereg, ?Eptr, ?Enb, ?Esb; try assumption.
  - intros c Hc Hu. rewrite Ereg in Hu |- *. exact (ak_user c Hc Hu).
  - intros c Hc Hu. rewrite Ereg in Hu |- *. exact (ak_fa c Hc Hu).
  - intros sc Hsc. exact (ak_sec sc (INCL sc Hsc)).
  - intros b len Hb. destruct (ak_blocks_sep b len Hb) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    repeat split; try assumption. intros sc Hsc. exact (Q5 sc (INCL sc Hsc)).
  - intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| do 3 right; left| do 4 right]; try exact X.
    destruct X as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; intros c Hc Hu; rewrite Ereg in Hu |- *; [exact (X3 c Hc Hu)| exact (X4 c Hc Hu)].
  - destruct ak_store_sep as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3]. intros sc Hsc. exact (Q2 sc (INCL sc Hsc)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ev3.
Variable StdioRep : stdout_st -> mem -> Prop.
Variable RTMisc : aenv -> mem -> Prop.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis ENV0 : env0_ok5 E0.

#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aNzc := (B_bundle.aNz E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
Ltac cstat := try clear HR0_ok.

Definition KVMu (mo : Model) (a : astate) (A L : Z) : Prop :=
  vm_reserved (m_vmmaps mo) = RES0
  /\ (exists fog, Permutation (vm_maps (m_vmmaps mo)) (L0 ++ fog ++ amaps a ++ [went A L])
                 /\ Forall (fun e => bv_unsigned (snd e) <= 8192) fog /\ (length fog <= 2)%nat)
  /\ mwf (vm_maps (m_vmmaps mo))
  /\ model_ivs_wf mo
  /\ nao (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))
  /\ alloc_top (m_vmmaps mo) = alloc_ceiling.

Definition ATOKu (R R' : Z) (s : aps) (A L : Z) (mo : Model) : Prop :=
  KIA (aSc s) (aNc s) (aEBc s + L) mo
  /\ (0 <= R /\ aEBc s + L + 4096 * aNzc s + 4096 * R <= vm_limit (m_vmmaps mo))
  /\ ENVOK E0 FSB0 s /\ vm_limit (m_vmmaps mo) = 2^39 /\ KVMu mo (aps_alloc s) A L
  /\ eager_rw mo A L
  /\ (0 <= R' /\ PSL R' (m_vmmaps mo)).

Lemma ATOKu_KIA : forall R R' s A L mo, ATOKu R R' s A L mo -> KIA (aSc s) (aNc s) (aEBc s + L) mo.
Proof. cstat. intros R R' s A L mo (K & _). exact K. Qed.

Lemma KVMu_frame : forall mo mo' a A L, m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> KVMu mo a A L -> KVMu mo' a A L.
Proof. cstat. intros mo mo' a A L HV HL K. unfold KVMu, model_ivs_wf in *. rewrite HV, HL. exact K. Qed.

Lemma ATOKu_magree : forall R R' s A L mo mo',
  ATOKu R R' s A L mo -> magree mo mo' -> KIA (aSc s) (aNc s) (aEBc s + L) mo' -> ATOKu R R' s A L mo'.
Proof.
  cstat. intros R R' s A L mo mo' (K & O & EV & LIM & KV & ER & PS) Hag K'.
  pose proof (magree_vmmaps _ _ Hag) as Fvm. pose proof (magree_lazy _ _ Hag) as Flz.
  split; [exact K'|]. split; [rewrite Fvm; exact O|]. split; [exact EV|]. split; [rewrite Fvm; exact LIM|]. split.
  - eapply KVMu_frame; [exact Fvm| exact Flz| exact KV].
  - split; [unfold eager_rw in *; rewrite Fvm, Flz; exact ER| rewrite Fvm; exact PS].
Qed.

(* [comment removed for export] *)
Section Drop.
Variables (s : aps) (a2 : astate) (sc : secchunk).
Let a := aps_alloc s.
Let A := sc_map_beg sc.
Let L := sc_map_size sc.
Hypothesis PERM : Permutation (as_sec a) (as_sec a2 ++ [sc]).
Hypothesis Eres : as_residue a2 = as_residue a.
Hypothesis Ereg : forall c, get_region a2 c = get_region a c.
Hypothesis Eptr : as_ptr_committed a2 = as_ptr_committed a.
Hypothesis Enb : as_node_blocks a2 = as_node_blocks a.
Hypothesis Esb : as_store_blocks a2 = as_store_blocks a.
Hypothesis HL : 0 < L.

Lemma regions_bytes_d : regions_bytes a2 = regions_bytes a.
Proof. cstat. unfold regions_bytes. induction classes30 as [|c l IH]; [reflexivity|]. cbn [fold_right]. rewrite Ereg, IH. reflexivity. Qed.

Lemma aEB_drop : aEBc (sA a2 s) + L = aEBc s.
Proof.
  cstat. unfold B_bundle.aEB, B_policy5.aEB, aEBa, a_eager_bytes, sA, aps_set_alloc. cbn [aps_alloc]. rewrite regions_bytes_d, Eptr, Enb.
  unfold AsanState.sec_bytes. fold a. rewrite (Permutation_fold_add sc_map_size _ _ PERM), fold_add_app. cbn [fold_right]. unfold L. lia.
Qed.

Lemma aNz_drop : aNzc (sA a2 s) <= aNzc s.
Proof.
  cstat. unfold B_bundle.aNz, B_policy5.aNz, aNza, interiors_bound, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite Eres, Esb.
  rewrite (Permutation_fold_add (fun c => if kBigMapSize <=? sc_map_size c then sc_map_size c / 32768 else 0) _ _ PERM), fold_add_app.
  cbn [fold_right]. pose proof (Z.div_pos (sc_map_size sc) 32768 ltac:(unfold L in HL; lia) ltac:(lia)). destruct (kBigMapSize <=? sc_map_size sc); lia.
Qed.

Lemma aS_drop_mono : forall w, aSc (sA a2 s) w -> aSc s w.
Proof.
  cstat. intros w [M H]. unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *. cbn [aps_alloc] in *.
  split; [exact M|]. fold a. fold a in H. rewrite Eres, Esb in H.
  destruct H as [H|[H|[H|H]]]; [left; exact H| | right; right; left; exact H| right; right; right; exact H].
  right; left. destruct H as (sc' & Hin & X). exists sc'. split; [| exact X].
  apply (Permutation_in _ (Permutation_sym PERM)). apply in_app_iff. left. exact Hin.
Qed.

Definition sc_interior (p : Z) : Prop :=
  kBigMapSize <= L /\ fst (remap_range A L) <= p < fst (remap_range A L) + snd (remap_range A L).

(* [comment removed for export] *)
Lemma sc_interior_empty : forall p, snd (remap_range A L) <= 0 -> ~ sc_interior p.
Proof. cstat. intros p H [_ X]. lia. Qed.
Lemma madv_drop_NI : forall mo1 p, 0 <= A -> A + L < 2^63 ->
  In p (m_vm_materialized (m_madv mo1 (fst (remap_range A L)) (snd (remap_range A L)))) -> ~ sc_interior (bv_unsigned p).
Proof.
  cstat. intros mo1 p HA HB Hin [_ X].
  assert (G : 0 <= fst (remap_range A L) < 2^64 /\ snd (remap_range A L) < 2^64).
  { unfold remap_range, mem_to_shadow, kShadowBase, round_up, round_down, kPageSize in *. cbn [fst snd] in *. clear -HA HB HL.
    Z.div_mod_to_equations. lia. }
  destruct (Z_le_dec (snd (remap_range A L)) 0) as [E|NE]; [lia|].
  assert (G2 : 0 <= snd (remap_range A L) < 2^64) by lia.
  exact (m_madv_not_in mo1 _ _ p (proj1 G) G2 Hin X).
Qed.

Lemma aS_drop_keep : forall w, aSc s w -> ~ sc_interior (bv_unsigned w) -> aSc (sA a2 s) w.
Proof.
  cstat. intros w [M H] NI. unfold B_bundle.aS, B_policy5.aS, aSa, sA, aps_set_alloc, in_interiors, in_stores in *. cbn [aps_alloc] in *.
  split; [exact M|]. fold a. fold a in H. rewrite Eres, Esb.
  destruct H as [H|[H|[H|H]]]; [left; exact H| | right; right; left; exact H| right; right; right; exact H].
  destruct H as (sc' & Hin & X1 & X2).
  apply (Permutation_in _ PERM) in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|[<-|[]]].
  - right; left. exists sc'. auto.
  - exfalso. apply NI. split; assumption.
Qed.

Lemma ATOKu_intro : forall R R' mo,
  ATOKc R R' s mo -> AKern E0 a mo ->
  (forall p, In p (m_vm_materialized mo) -> ~ sc_interior (bv_unsigned p)) ->
  ATOKu R R' (sA a2 s) A L mo.
Proof.
  intros R R' mo ((LI1 & MI1 & HH1) & [O0 O1] & EV1 & LIM1 & KV1 & PS1) K NI.
  pose proof aEB_drop as EB2. pose proof aNz_drop as NZ. pose proof (AHK_aN_bound E0 FSB0 HR0 HR0_ok (sA a2 s)) as NB.
  change (B_bundle.aN E0 FSB0 HR0 (sA a2 s)) with (aNc (sA a2 s)) in NB. change (B_bundle.aNz E0 FSB0 HR0 (sA a2 s)) with (aNzc (sA a2 s)) in NB.
  assert (INsc : In sc (as_sec a)) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_app_iff; right; left; reflexivity).
  unfold OSL in O1.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - split; [| split; [exact MI1| exact HH1]]. rewrite EB2.
    destruct LI1 as [Q1 Q2 Q3 Q4 Q5]. constructor.
    + exact Q1.
    + apply Forall_forall. intros p Hp. apply aS_drop_keep; [exact (proj1 (Forall_forall _ _) Q2 p Hp)| exact (NI p Hp)].
    + intros l ND HF. exact (aS_card (A0 E0 FSB0 HR0) (aps_alloc (sA a2 s)) l ND HF).
    + exact Q4.
    + rewrite LIM1, page_size_val. rewrite LIM1 in O1. clear -O0 O1 NZ NB. nia.
  - rewrite EB2. split; [exact O0| clear -O1 NZ O0; nia].
  - unfold ENVOK, sA, aps_set_alloc in *. cbn [aps_env aps_fsbase] in *. exact EV1.
  - exact LIM1.
  - destruct KV1 as (KR & (fog & PM & FG1 & FG2) & KW & KWF & KNA & KT).
    unfold KVMu. split; [exact KR|]. split; [| split; [exact KW|]; split; [exact KWF|]; split; [exact KNA| exact KT]].
    exists fog. split; [| split; [exact FG1| exact FG2]].
    eapply Permutation_trans; [exact PM|]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    unfold amaps, sA, aps_set_alloc. cbn [aps_alloc]. fold a. rewrite Enb, Esb.
    eapply Permutation_trans.
    { apply Permutation_app_tail. apply Permutation_map. exact PERM. }
    rewrite map_app. cbn [map]. rewrite <- !app_assoc. apply Permutation_app_head.
    cbn [app]. rewrite (app_assoc (map (fun b => went b kDepotNodeBlockBytes) (as_node_blocks a))).
    apply Permutation_cons_append.
  - exact (proj2 (ak_sec _ _ _ K sc INsc)).
  - exact PS1.
Qed.

(* [comment removed for export] *)
Section Rel.
Variables (mo1 : Model) (Pq : list Z) (Dq : list batch).
Hypothesis K1 : AKern E0 a mo1.
Hypothesis WF1 : AWf E0 Pq Dq a.

Let INsc : In sc (as_sec a).
Proof. apply (Permutation_in _ (Permutation_sym PERM)). apply in_app_iff. right. left. reflexivity. Qed.

Lemma sc_geom : A mod 4096 = 0 /\ app_mem A L /\ A + L <= alloc_ceiling /\ L mod 4096 = 0
  /\ (A + L <= ae_space_beg E0 \/ ae_space_beg E0 + kSpaceSize <= A)
  /\ (forall r, In r (ae_reserved E0) -> A + L <= fst r \/ fst r + snd r <= A).
Proof.
  cstat. destruct WF1 as (_ & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
  destruct (WS3 sc INsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). change kPageSize with 4096 in *.
  unfold A, L. repeat split; try assumption.
Qed.

Lemma sc_vs_sec : forall sc', In sc' (as_sec a2) -> A + L <= sc_map_beg sc' \/ sc_map_beg sc' + sc_map_size sc' <= A.
Proof.
  cstat. intros sc' Hsc'. destruct WF1 as (_ & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & _ & ND & WS5).
  assert (In sc' (as_sec a)) as IN' by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_app_iff; left; exact Hsc').
  assert (NE : sc' <> sc).
  { intros ->. apply (Permutation_map sc_map_beg) in PERM. pose proof (Permutation_NoDup PERM ND) as ND2.
    rewrite map_app in ND2. cbn [map] in ND2. apply NoDup_remove in ND2. destruct ND2 as [_ NIn]. apply NIn. apply in_app_iff. left. apply in_map. exact Hsc'. }
  destruct (WS5 sc' sc IN' INsc NE); unfold A, L; lia.
Qed.

Lemma sc_vs_blocks : forall b len,
  (In b (as_node_blocks a) /\ len = kDepotNodeBlockBytes) \/ (In b (as_store_blocks a) /\ len = kStoreBlockBytes) ->
  A + L <= b \/ b + len <= A.
Proof. cstat. intros b len Hb. destruct (ak_blocks_sep _ _ _ K1 b len Hb) as (_ & _ & _ & _ & Q5 & _). destruct (Q5 sc INsc); unfold A, L; lia. Qed.

Lemma sc_vs_resv : A + L <= ae_resv_beg E0 \/ ae_resv_beg E0 + kResvLen <= A.
Proof.
  cstat. pose proof (proj1 WF1) as (_ & _ & _ & _ & _ & _ & E7 & _). destruct sc_geom as (_ & _ & _ & _ & _ & M7).
  destruct (M7 _ E7); cbn [fst snd] in *; unfold kResvLen; lia.
Qed.
Lemma sc_vs_ptr : A + L <= ae_ptr_array E0 \/ ae_ptr_array E0 + kPtrArrayLen <= A.
Proof.
  cstat. pose proof (proj1 WF1) as (_ & _ & _ & _ & _ & _ & _ & E8 & _). destruct sc_geom as (_ & _ & _ & _ & _ & M7).
  destruct (M7 _ E8); cbn [fst snd] in *; unfold kPtrArrayLen; lia.
Qed.
Lemma sc_vs_thread : A + L <= ae_thread E0 \/ ae_thread E0 + 4096 <= A.
Proof.
  cstat. pose proof (proj1 WF1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E13 & _). destruct sc_geom as (_ & _ & _ & _ & _ & M7).
  destruct (M7 _ E13); cbn [fst snd] in *; lia.
Qed.
Lemma sc_vs_dn0 : A + L <= ae_depot_nodes E0 \/ ae_depot_nodes E0 + kDepotNodeBlockBytes <= A.
Proof. cstat. destruct ENV0 as (N1 & _). destruct sc_geom as (_ & _ & _ & _ & _ & M7). destruct (M7 _ N1); cbn [fst snd] in *; lia. Qed.
Lemma sc_vs_st0 : A + L <= ae_store_blk E0 \/ ae_store_blk E0 + kStoreBlockBytes <= A.
Proof. cstat. destruct ENV0 as (_ & N2 & _). destruct sc_geom as (_ & _ & _ & _ & _ & M7). destruct (M7 _ N2); cbn [fst snd] in *; lia. Qed.
End Rel.

(* [comment removed for export] *)
Lemma mwf_base_unique : forall l e1 e2, mwf l -> In e1 l -> In e2 l -> elo e1 = elo e2 -> e1 = e2.
Proof.
  cstat. intros l e1 e2 [D W] H1 H2 EQ.
  destruct (In_nth_error _ _ H1) as (i & Hi). destruct (In_nth_error _ _ H2) as (j & Hj).
  destruct (Nat.eq_dec i j) as [->|NE]; [congruence|].
  exfalso. pose proof (proj1 (Forall_forall _ _) W e1 H1) as (P1 & _). pose proof (proj1 (Forall_forall _ _) W e2 H2) as (P2 & _).
  destruct (D i j e1 e2 Hi Hj NE); unfold elo, ehi in *; lia.
Qed.

Lemma In_map_remove : forall l e b, In e l -> fst e <> b -> In e (map_remove l b).
Proof.
  cstat. intros l e b Hin NE. unfold map_remove. apply filter_In. split; [exact Hin|]. apply Bool.negb_true_iff. apply PropExec.bv_eqb_neq. exact NE.
Qed.

Lemma map_remove_In : forall l e b, In e (map_remove l b) -> In e l /\ fst e <> b.
Proof.
  cstat. intros l e b Hin. unfold map_remove in Hin. apply filter_In in Hin as [H1 H2]. split; [exact H1|].
  intros E. rewrite E in H2. unfold bv_eqb in H2. rewrite Z.eqb_refl in H2. discriminate.
Qed.

(* [comment removed for export] *)
Section AKU.
Variables (mo1 mo' : Model) (Pq : list Z) (Dq : list batch).
Hypothesis K1 : AKern E0 a mo1.
Hypothesis WF1 : AWf E0 Pq Dq a.
Hypothesis KW : mwf (vm_maps (m_vmmaps mo1)).
Hypothesis KWF : model_ivs_wf mo1.
Hypothesis INw : In (went A L) (vm_maps (m_vmmaps mo1)).
Hypothesis MAPS : vm_maps (m_vmmaps mo') = map_remove (vm_maps (m_vmmaps mo1)) (kwz A).
Hypothesis NOACC : vm_noaccess (m_vmmaps mo') = maps_subtract (vm_noaccess (m_vmmaps mo1)) A (A + L).
Hypothesis LAZY : m_vm_lazy mo' = maps_subtract (m_vm_lazy mo1) A (A + L).

Let G := sc_geom Pq Dq WF1.

Lemma w_ext : elo (went A L) = A /\ ehi (went A L) = A + L.
Proof.
  cstat. destruct G as (M1 & M2 & M3 & M4 & _). unfold app_mem in M2. rewrite kLowAppEnd_val, kHighMemBeg_val in M2. pose proof alloc_ceiling_range as ACR.
  unfold elo, ehi, went, kwz. cbn [fst snd]. rewrite !u64_small by (unfold L in HL; lia). lia.
Qed.

Lemma inside_keep : forall x n, 0 < n -> (x + n <= A \/ A + L <= x) -> inside (vm_maps (m_vmmaps mo1)) x n -> inside (vm_maps (m_vmmaps mo')) x n.
Proof.
  cstat. intros x n Hn D (e & He & R1 & R2). exists e. split; [| split; assumption]. rewrite MAPS. apply In_map_remove; [exact He|].
  intros EQ. pose proof w_ext as [W1 W2].
  assert (e = went A L) as ->.
  { apply (mwf_base_unique _ _ _ KW He INw). unfold elo. rewrite EQ. unfold went, kwz. cbn [fst]. reflexivity. }
  rewrite W1 in R1. rewrite W2 in R2. lia.
Qed.

Lemma In_keep : forall e, In e (vm_maps (m_vmmaps mo1)) -> 0 < bv_unsigned (snd e) -> (ehi e <= A \/ A + L <= elo e) -> In e (vm_maps (m_vmmaps mo')).
Proof.
  cstat. intros e He Hp D. rewrite MAPS. apply In_map_remove; [exact He|]. intros EQ. pose proof w_ext as [W1 W2].
  assert (e = went A L) as ->.
  { apply (mwf_base_unique _ _ _ KW He INw). unfold elo. rewrite EQ. unfold went, kwz. cbn [fst]. reflexivity. }
  unfold L in HL. lia.
Qed.

Lemma noacc_pieces_u : forall e', In e' (vm_noaccess (m_vmmaps mo')) ->
  exists e, In e (vm_noaccess (m_vmmaps mo1)) /\ elo e <= elo e' /\ ehi e' <= ehi e.
Proof.
  cstat. intros e' He'. rewrite NOACC in He'. destruct G as (_ & M2 & _). unfold app_mem in M2. rewrite kHighMemBeg_val in M2.
  destruct (maps_subtract_incl _ A (A + L) e' (proj1 (proj2 KWF)) ltac:(lia) He') as (e & He & R1 & R2 & _). exists e. auto.
Qed.
Lemma lazy_pieces_u : forall e', In e' (m_vm_lazy mo') ->
  exists e, In e (m_vm_lazy mo1) /\ elo e <= elo e' /\ ehi e' <= ehi e.
Proof.
  cstat. intros e' He'. rewrite LAZY in He'. destruct G as (_ & M2 & _). unfold app_mem in M2. rewrite kHighMemBeg_val in M2.
  destruct (maps_subtract_incl _ A (A + L) e' (proj1 (proj2 (proj2 KWF))) ltac:(lia) He') as (e & He & R1 & R2 & _). exists e. auto.
Qed.

Lemma eager_rw_keep_u : forall x n, 0 < n -> (x + n <= A \/ A + L <= x) -> eager_rw mo1 x n -> eager_rw mo' x n.
Proof.
  cstat. intros x n Hn D (I1 & I2 & I3). split; [| split].
  - exact (inside_keep x n Hn D I1).
  - eapply clear_ofp_pieces; [exact I2| exact noacc_pieces_u].
  - intros e' He'. destruct (lazy_pieces_u e' He') as (e & He & R1 & R2). pose proof (I3 e He). lia.
Qed.

Lemma AKern_unmap : AKern E0 a2 mo'.
Proof.
  cstat. pose proof (sc_vs_resv Pq Dq WF1) as DR. pose proof (sc_vs_ptr Pq Dq WF1) as DP. pose proof (sc_vs_thread Pq Dq WF1) as DT.
  pose proof (sc_vs_dn0 Pq Dq WF1) as DD. pose proof (sc_vs_st0 Pq Dq WF1) as DS.
  pose proof (sc_vs_sec Pq Dq WF1) as DSC. pose proof (sc_vs_blocks mo1 K1) as DB.
  pose proof G as (M1 & M2 & M3 & M4 & M6 & M7). unfold app_mem in M2. rewrite kLowAppEnd_val, kHighMemBeg_val in M2.
  pose proof (proj1 WF1) as WE. pose proof alloc_ceiling_range as ACR.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & _).
  rewrite kHighMemBeg_val in E2. unfold app_mem in E16. rewrite kLowAppEnd_val, kHighMemBeg_val in E16.
  assert (K2 : AKern E0 a2 mo1).
  { eapply AKern_sec_incl; [exact K1| | exact Ereg| exact Eptr| exact Enb| exact Esb].
    intros sc' H'. apply (Permutation_in _ (Permutation_sym PERM)). apply in_app_iff. left. exact H'. }
  pose proof (ak_resv_geom _ _ _ K2) as (G1 & G2 & G3). change kPageSize with 4096 in *.
  unfold kResvLen in *. unfold kPtrArrayLen in *. change kSpaceSize with (2^37) in *.
  unfold kDepotNodeBlockBytes in DD. unfold kStoreBlockBytes in DS.
  assert (UR : bv_unsigned (Z_to_bv 64 (ae_resv_beg E0)) = ae_resv_beg E0) by (apply u64_small; clear -E2 E5 ACR; lia).
  assert (UK : bv_unsigned (Z_to_bv 64 137439023104) = 137439023104) by (apply u64_small; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 (ae_ptr_array E0)) = ae_ptr_array E0) by (apply u64_small; clear -E16 E17 ACR; lia).
  assert (U8 : bv_unsigned (Z_to_bv 64 8388608) = 8388608) by (apply u64_small; lia).
  assert (U20 : bv_unsigned (Z_to_bv 64 1048576) = 1048576) by (apply u64_small; lia).
  constructor.
  - apply In_keep; [exact (ak_resv _ _ _ K2)| |]; unfold went, kwz, elo, ehi; cbn [fst snd]; rewrite ?UR, ?UK; clear -DR; lia.
  - exact (ak_resv_geom _ _ _ K2).
  - destruct (ak_reginfo _ _ _ K2) as [I1 I2]. split; [apply inside_keep; [change kPageSize with 4096; lia| change kSpaceSize with (2^37); change kPageSize with 4096; clear -DR G1 G3; lia| exact I1]| eapply clear_ofp_pieces; [exact I2| exact noacc_pieces_u]].
  - intros c Hc Hm. pose proof (proj2 (proj1 (proj2 WF1)) c Hc) as RG. cbv zeta in RG. unfold region_of in RG. rewrite <- Ereg in RG.
    destruct RG as (_ & _ & R3 & _). unfold kFreeArrayOffset in R3. unfold kLargestClassID in Hc.
    apply eager_rw_keep_u; [exact Hm| | exact (ak_user _ _ _ K2 c Hc Hm)].
    unfold region_beg. change kRegionSize with 4294967296. clear -Hc R3 Hm DR G1 G3. nia.
  - intros c Hc Hm. pose proof (proj2 (proj1 (proj2 WF1)) c Hc) as RG. cbv zeta in RG. unfold region_of in RG. rewrite <- Ereg in RG.
    destruct RG as (_ & _ & _ & _ & _ & _ & F3 & _). unfold kFreeArraySize in F3. unfold kLargestClassID in Hc.
    apply eager_rw_keep_u; [exact Hm| | exact (ak_fa _ _ _ K2 c Hc Hm)].
    unfold free_array, region_beg, kFreeArrayOffset. change kRegionSize with 4294967296. clear -Hc F3 Hm DR G1 G3. nia.
  - apply In_keep; [exact (ak_ptr _ _ _ K2)| |]; unfold went, kwz, elo, ehi; cbn [fst snd]; rewrite ?UP, ?U8; clear -DP; lia.
  - intros Hp. apply eager_rw_keep_u; [unfold kPtrArrayCommit; lia| unfold kPtrArrayCommit; clear -DP; lia| exact (ak_ptr_head _ _ _ K2 Hp)].
  - intros p H1 H2 H3. rewrite NOACC. apply inside_subtract; [exact (proj1 (proj2 KWF))| clear -M2 HL; unfold L in *; lia| change kPageSize with 4096; lia| exact (ak_ptr_tail _ _ _ K2 p H1 H2 H3)|].
    clear -DP H1 H2. destruct (as_ptr_committed a2 =? 0); unfold kPtrArrayCommit, kPageSize, kPtrArrayLen in *; lia.
  - intros sc' Hsc'. destruct (ak_sec _ _ _ K2 sc' Hsc') as [S1 S2]. pose proof (DSC sc' Hsc') as D'.
    pose proof WF1 as (_ & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
    assert (IN' : In sc' (as_sec a)) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_app_iff; left; exact Hsc').
    destruct (WS3 sc' IN') as (Q1 & Q2 & Q3 & Q4 & _). unfold app_mem in Q2. rewrite kLowAppEnd_val, kHighMemBeg_val in Q2.
    assert (U1 : bv_unsigned (Z_to_bv 64 (sc_map_beg sc')) = sc_map_beg sc') by (apply u64_small; clear -Q2 Q3 Q4 ACR; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 (sc_map_size sc')) = sc_map_size sc') by (apply u64_small; clear -Q2 Q3 Q4 ACR; lia).
    split; [apply In_keep; [exact S1| |]; unfold went, kwz, elo, ehi; cbn [fst snd]; rewrite ?U1, ?U2; clear -D' Q4; lia| apply eager_rw_keep_u; [exact Q4| clear -D'; lia| exact S2]].
  - apply eager_rw_keep_u; [change kPageSize with 4096; lia| change kPageSize with 4096; clear -DT; lia| exact (ak_thread _ _ _ K2)].
  - apply eager_rw_keep_u; [lia| clear -DD; lia| exact (ak_depot_nodes _ _ _ K2)].
  - destruct (ak_store _ _ _ K2) as [I1 I2]. split; [apply inside_keep; [lia| clear -DS; lia| exact I1]| eapply clear_ofp_pieces; [exact I2| exact noacc_pieces_u]].
  - intros b Hb. destruct (ak_node_blocks _ _ _ K2 b Hb) as [N1 N2]. pose proof Hb as Hb0. rewrite Enb in Hb.
    pose proof (DB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as D'. unfold kDepotNodeBlockBytes in D'.
    pose proof (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb0 eq_refl))) as (B1 & B2 & _).
    unfold app_mem in B1. rewrite kLowAppEnd_val, kHighMemBeg_val in B1. unfold kDepotNodeBlockBytes in *.
    assert (UB : bv_unsigned (Z_to_bv 64 b) = b) by (apply u64_small; clear -B1 B2 ACR; lia).
    split; [apply In_keep; [exact N1| |]; unfold went, kwz, elo, ehi; cbn [fst snd]; rewrite ?UB, ?U20; clear -D'; lia| apply eager_rw_keep_u; [lia| clear -D'; lia| exact N2]].
  - intros b Hb. destruct (ak_store_blocks _ _ _ K2 b Hb) as [I1 I2]. rewrite Esb in Hb.
    pose proof (DB b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as D'. unfold kStoreBlockBytes in D' |- *.
    split; [apply inside_keep; [lia| clear -D'; lia| exact I1]| eapply clear_ofp_pieces; [exact I2| exact noacc_pieces_u]].
  - exact (ak_blocks_sep _ _ _ K2).
  - intros e' He'. destruct (lazy_pieces_u e' He') as (e & He & R1 & R2).
    destruct (ak_lazy _ _ _ K2 e He) as [X|[X|[X|[X|X]]]].
    + left. lia.
    + right; left. lia.
    + right; right; left. destruct X as (b & Hb & X1 & X2). exists b. split; [exact Hb| lia].
    + right; right; right; left. lia.
    + right; right; right; right. destruct X as (X0 & X1 & X2 & X3). split; [lia|]. split; [lia|]. split.
      * intros c Hc Hm. destruct (X2 c Hc Hm); lia.
      * intros c Hc Hm. destruct (X3 c Hc Hm); lia.
  - exact (ak_store_sep _ _ _ K2).
Qed.
End AKU.

(* [comment removed for export] *)
Lemma eager_uncovered : forall mo x n y,
  eager_rw mo x n -> x <= y < x + n -> covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) y = false.
Proof.
  cstat. intros mo x n y (_ & C1 & C2) Hy. rewrite covered_app. apply Bool.orb_false_iff. split.
  - unfold covered. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (e & He & IV).
    unfold in_iv, in_rng, B, S in IV. apply andb_true_iff in IV as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    pose proof (C1 e He ltac:(lia)) as D. unfold elo, ehi in D. lia.
  - unfold covered. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (e & He & IV).
    unfold in_iv, in_rng, B, S in IV. apply andb_true_iff in IV as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    pose proof (C2 e He) as D. unfold elo, ehi in D. lia.
Qed.

(* [comment removed for export] *)
Theorem ev_munmap : forall R R' mo mo1 Pq Dq,
  ATOKu R R' (sA a2 s) A L mo -> AKern E0 a mo -> AWf E0 Pq Dq a ->
  magree mo mo1 -> KIA (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s) + L) mo1 ->
     (forall eff, munmap_CHK A L mo1 eff <> CheckUnmodeled)
  /\ (exists eff mo', munmap_CHK A L mo1 eff = CheckOk mo' [] /\ node_refusal (NMunmap A L) mo1 (eff_ret eff) = false)
  /\ (forall eff mo', munmap_CHK A L mo1 eff = CheckOk mo' [] -> node_refusal (NMunmap A L) mo1 (eff_ret eff) = false ->
        mm_answer mo1 eff mo' []
        /\ eff = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] []
        /\ mo' = m_unmap mo1 A L
        /\ ATOKc R R' (sA a2 s) mo' /\ AKern E0 a2 mo').
Proof.
  intros R R' mo mo1 Pq Dq TOK K WF Hag KIA1.
  pose proof (ATOKu_magree _ _ _ _ _ _ _ TOK Hag KIA1) as TOK1.
  destruct TOK1 as ((LI1 & MI1 & HH1) & [O0 O1] & EV1 & LIM1 & KV1 & ER1 & [P0 PS1]).
  pose proof KV1 as (KR & (fog & PM & FG1 & FG2) & KW & KWF & KNA & KT).
  pose proof (magree_vmmaps _ _ Hag) as Fvm. pose proof (magree_lazy _ _ Hag) as Flz.
  assert (K1 : AKern E0 a mo1) by (eapply AKern_frame; [exact Fvm| exact Flz| exact K]).
  pose proof (sc_geom Pq Dq WF) as (M1 & M2 & M3 & M5 & M6 & M7). unfold app_mem in M2. rewrite kLowAppEnd_val, kHighMemBeg_val in M2.
  pose proof alloc_ceiling_range as ACR.
  assert (HE : A + L < 2^64) by lia.
  assert (INw : In (went A L) (vm_maps (m_vmmaps mo1))).
  { apply (Permutation_in _ (Permutation_sym PM)). rewrite !in_app_iff. right; right; right. left. reflexivity. }
  assert (MH : map_has (vm_maps (m_vmmaps mo1)) (Z_to_bv 64 A) (Z_to_bv 64 L) = true).
  { unfold map_has. apply existsb_exists. exists (went A L). split; [exact INw|]. unfold went, kwz. cbn [fst snd].
    unfold bv_eqb. rewrite !Z.eqb_refl. reflexivity. }
  assert (TS : A + L <= TASK_SIZE) by (unfold TASK_SIZE; lia).
  pose proof (chk_munmap_nu A L mo1 M1 M5 ltac:(lia) HL TS MH) as NU.
  pose proof (chk_munmap_grant A L mo1 M1 M5 ltac:(lia) HL TS MH) as GR.
  pose proof (chk_munmap_inv A L mo1 M1 M5 ltac:(lia) HL TS MH) as INV.
  split; [exact NU|]. split; [eexists; eexists; split; [exact GR| reflexivity]|].
  intros eff mo' HC _. destruct (INV eff mo' [] HC) as (_ & -> & ->).
  split; [eapply check_munmap_only; exact HC|]. split; [reflexivity|]. split; [reflexivity|].
  pose proof (check_munmap_only _ _ _ _ _ _ HC) as MMA.
  assert (DJ : forall e, In e (map_remove (vm_maps (m_vmmaps mo1)) (Z_to_bv 64 A)) -> ehi e <= A \/ A + L <= elo e).
  { intros e He. apply map_remove_In in He as [He NE].
    destruct (In_nth_error _ _ He) as (i & Hi). destruct (In_nth_error _ _ INw) as (j & Hj).
    destruct (Nat.eq_dec i j) as [->|NEQ].
    - exfalso. rewrite Hj in Hi. injection Hi as <-. apply NE. reflexivity.
    - pose proof (proj1 KW i j _ _ Hi Hj NEQ) as D. unfold elo, ehi, went, kwz in D |- *. cbn [fst snd] in D.
      rewrite !u64_small in D by lia. lia. }
  assert (EG : eager_used (m_unmap mo1 A L) <= eager_used mo1 - L).
  { apply unmap_eager_exact; [exact KWF| lia| exact HL| exact HE| exact INw| | exact DJ].
    intros y Hy. exact (eager_uncovered mo1 A L y ER1 Hy). }
  change (munmap_post A L mo1) with (m_unmap mo1 A L).
  split.
  - (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split]]]].
    + split; [| split; [eapply mm_answer_minvA; [exact MMA| exact MI1]| rewrite (mm_answer_halted _ _ _ _ MMA); exact HH1]].
      destruct LI1 as [Q1 Q2 Q3 Q4 Q5]. constructor.
      * rewrite (unmap_mat mo1 A L) by lia. apply List.NoDup_filter. exact Q1.
      * rewrite (unmap_mat mo1 A L) by lia. apply Forall_forall. intros p Hp. apply filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) Q2 p Hp).
      * exact Q3.
      * lia.
      * rewrite unmap_limit. lia.
    + split; [exact O0|]. unfold OSL. rewrite unmap_limit. lia.
    + exact EV1.
    + rewrite unmap_limit. exact LIM1.
    + unfold KVM. unfold sA, aps_set_alloc. cbn [aps_alloc].
      rewrite unmap_reserved, unmap_maps, (unmap_noaccess mo1 A L). split; [exact KR|]. split; [| split; [| split; [| split]]].
      * exists fog. split; [| split; [exact FG1| exact FG2]].
        destruct (in_split _ _ INw) as (l1 & l2 & EQ). rewrite EQ in PM, KW |- *.
        assert (KEEP : forall e, In e (l1 ++ l2) -> negb (bv_eqb (fst e) (Z_to_bv 64 A)) = true).
        { intros e He. apply Bool.negb_true_iff. apply PropExec.bv_eqb_neq. intros EQe.
          assert (e = went A L) as ->.
          { apply (mwf_base_unique _ _ _ KW); [apply in_app_iff; apply in_app_iff in He; destruct He; [left; assumption| right; right; assumption]| apply in_elt| ].
            unfold elo. rewrite EQe. reflexivity. }
          apply in_app_iff in He.
          destruct He as [He|He]; destruct (In_nth_error _ _ He) as (i & Hi).
          - pose proof (nth_lt _ _ _ Hi) as LT.
            pose proof (proj1 KW i (length l1) (went A L) (went A L) ltac:(rewrite nth_error_app1 by exact LT; exact Hi)
                          ltac:(rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity) ltac:(lia)) as D.
            pose proof (w_ext Pq Dq WF) as [W1 W2]. rewrite W1 in D. rewrite W2 in D. clear -D HL. lia.
          - pose proof (proj1 KW (length l1 + Datatypes.S i)%nat (length l1) (went A L) (went A L)
                          ltac:(rewrite nth_error_app2 by lia; replace (length l1 + Datatypes.S i - length l1)%nat with (Datatypes.S i) by lia; exact Hi)
                          ltac:(rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity) ltac:(lia)) as D.
            pose proof (w_ext Pq Dq WF) as [W1 W2]. rewrite W1 in D. rewrite W2 in D. clear -D HL. lia. }
        assert (F1 : List.filter (fun p : word * word => negb (bv_eqb (fst p) (Z_to_bv 64 A))) l1 = l1).
        { apply forallb_filter_id. apply forallb_forall. intros e He. apply KEEP. apply in_app_iff. left. exact He. }
        assert (F2 : List.filter (fun p : word * word => negb (bv_eqb (fst p) (Z_to_bv 64 A))) l2 = l2).
        { apply forallb_filter_id. apply forallb_forall. intros e He. apply KEEP. apply in_app_iff. right. exact He. }
        unfold map_remove. rewrite List.filter_app. cbn [List.filter]. rewrite F1.
        replace (negb (bv_eqb (fst (went A L)) (Z_to_bv 64 A))) with false by (unfold went, kwz; cbn [fst]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity).
        rewrite F2.
        assert (PM' : Permutation (l1 ++ went A L :: l2) ((L0 ++ fog ++ amaps a2) ++ [went A L])).
        { rewrite <- (app_assoc L0 (fog ++ amaps a2) [went A L]). rewrite <- (app_assoc fog (amaps a2) [went A L]). exact PM. }
        pose proof (Permutation_app_inv _ _ _ _ _ PM') as PM''. rewrite app_nil_r in PM''. exact PM''.
      * apply mwf_filter. exact KW.
      * apply unmap_wf; try assumption; lia.
      * intros e' He'. destruct (maps_subtract_incl _ A (A + L) e' (proj1 (proj2 KWF)) ltac:(lia) He') as (e & He & R1 & R2 & R3).
        pose proof (maps_subtract_pos _ A (A + L) e' (proj1 (proj2 KWF)) ltac:(lia) ltac:(intros e0 He0; exact (proj1 (KNA e0 He0))) He') as Pe'.
        split; [exact Pe'|].
        destruct (KNA e He) as (Pe & m & Hm & Q1 & Q2 & Q3).
        exists m. split; [| split; [lia| split; [lia| exact (shband_clear_sub e e' Q3 R1 R2)]]]. apply In_map_remove; [exact Hm|]. intros EQm.
        assert (m = went A L) as -> by (apply (mwf_base_unique _ _ _ KW Hm INw); unfold elo; rewrite EQm; reflexivity).
        pose proof (w_ext Pq Dq WF) as [W1 W2]. unfold ehi, elo in *. unfold went, kwz in W1, W2, Q1, Q2. cbn [fst snd] in *.
        rewrite !u64_small in Q1, Q2 by lia. lia.
      * unfold m_unmap, munmap_post, with_mmap_destroyed. mproj. cbn. exact KT.
    + split; [exact P0|]. eapply PSL_remove; [apply unmap_reserved| apply unmap_maps| unfold m_unmap, munmap_post, with_mmap_destroyed; mproj; cbn; reflexivity| exact PS1].
  - (* [comment removed for export] *)
    eapply (AKern_unmap mo1 (m_unmap mo1 A L) Pq Dq K1 WF KW KWF INw).
    + rewrite unmap_maps. reflexivity.
    + apply unmap_noaccess.
    + apply unmap_lazy; lia.
Qed.
End Drop.

End Ev3.
End RC__1.
