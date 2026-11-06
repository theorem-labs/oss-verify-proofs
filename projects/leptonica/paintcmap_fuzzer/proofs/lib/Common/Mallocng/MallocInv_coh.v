(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition meta_usage (A : astate) (sc : Z) (ma : Z) : Z :=
  match a_meta A ma with
  | Some mt => match mt_role mt with
               | RGroup _ _ => if mt_sc mt =? sc then mt_cnt mt else 0
               | _ => 0
               end
  | None => 0
  end.

Fixpoint sumk (f : Z -> Z) (n : nat) : Z :=
  match n with O => 0 | S n' => sumk f n' + f (Z.of_nat n') end.

Definition area_usage (A : astate) (sc pg : Z) : Z :=
  sumk (fun k => meta_usage A sc (meta_addr pg k)) 101.

Definition usage_of (A : astate) (sc : Z) : Z :=
  fold_right (fun pg acc => area_usage A sc pg + acc) 0 (a_areas A).

Lemma sumk_ext : forall f g n, (forall k, 0 <= k < Z.of_nat n -> f k = g k) -> sumk f n = sumk g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; [reflexivity|].
  cbn [sumk]. rewrite IH by (intros k Hk; apply H; llia). rewrite H by llia. reflexivity.
Qed.

Lemma sumk_nonneg : forall f n, (forall k, 0 <= k < Z.of_nat n -> 0 <= f k) -> 0 <= sumk f n.
Proof.
  intros f n. induction n as [|n IH]; intros H; [cbn; llia|].
  cbn [sumk]. assert (0 <= f (Z.of_nat n)) by (apply H; llia). specialize (IH ltac:(intros k Hk; apply H; llia)). llia.
Qed.

Lemma usage_of_nil : forall A sc, a_areas A = [] -> usage_of A sc = 0.
Proof. intros A sc E. unfold usage_of. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma usage_of_ext : forall A A' sc,
  a_areas A' = a_areas A -> (forall ma, meta_usage A' sc ma = meta_usage A sc ma) ->
  usage_of A' sc = usage_of A sc.
Proof.
  intros A A' sc Ea Em. unfold usage_of. rewrite Ea.
  generalize (a_areas A) as l. induction l as [|pg l IH]; [reflexivity|]. cbn [fold_right].
  rewrite IH. f_equal. unfold area_usage. apply sumk_ext. intros k Hk. apply Em.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record Coh (A : astate) (m : word -> option byte) (h : VmMaps) : Prop := {
  coh_cov : forall a : word, m a <> None -> 0x1000 <= bv_unsigned a < alloc_ceiling ->
            ~ (IMG_LO <= bv_unsigned a < IMG_HI) -> mcov (vm_maps h) (bv_unsigned a) 1;
  coh_nodead : forall ma mt, a_meta A ma = Some mt -> mt_role mt <> RDead;
  coh_usage : forall sc, 0 <= sc < 48 -> a_ctx A (KUsage sc) = usage_of A sc;
  coh_avail : forall ma mt, a_meta A ma = Some mt -> mt_role mt = RAvail ->
              exists k, 101 - a_ctx A KAmc <= k < 101 /\ ma = meta_addr (last (a_areas A) 0) k
}.

Lemma coh_frame : forall A m m' h, Coh A m h ->
  (forall a : word, 0x1000 <= bv_unsigned a < alloc_ceiling -> ~ (IMG_LO <= bv_unsigned a < IMG_HI) ->
                    m' a <> None -> m a <> None) ->
  Coh A m' h.
Proof.
  intros A m m' h [C1 C2 C3 C4] Hnew. constructor; [| exact C2 | exact C3 | exact C4].
  intros a Ha Hr Hi. apply C1; [| exact Hr | exact Hi]. exact (Hnew a Hr Hi Ha).
Qed.

Lemma coh_agree : forall A m m' h, Coh A m h ->
  (forall a : word, bv_unsigned a < alloc_ceiling -> m' a = m a) -> Coh A m' h.
Proof.
  intros A m m' h HC Hag. apply (coh_frame A m m' h HC). intros a Hr _ Hm'. rewrite <- Hag; [exact Hm' | llia].
Qed.

Lemma coh_init : forall m h, (forall a : word, 0x1000 <= bv_unsigned a < alloc_ceiling ->
                                ~ (IMG_LO <= bv_unsigned a < IMG_HI) -> m a = None) ->
  Coh A0 m h.
Proof.
  intros m h Hm. constructor.
  - intros a Ha Hr Hi. exfalso. apply Ha. apply Hm; assumption.
  - intros ma mt H. discriminate H.
  - intros sc Hsc. reflexivity.
  - intros ma mt H. discriminate H.
Qed.

(* [comment removed for export] *)
Lemma reserved_top_RSEGS : reserved_top (segments_reserved ml_segs) = IMG_HI.
Proof. exact mlo_reserved_top. Qed.

Lemma VMok_init : forall h,
  vm_maps h = [] -> vm_noaccess h = [] -> vm_reserved h = segments_reserved ml_segs ->
  vm_start_brk h = vm_brk h -> valid_brk ml_segs (vm_brk h) -> alloc_top h = alloc_ceiling ->
  VMok A0 h.
Proof.
  intros h Hm Hn Hr Hsb (Hlo & Hhi & Hal) Htop. rewrite reserved_top_RSEGS in Hlo, Hhi. unfold page_size in Hal. unfold brk_aslr_max in Hhi.
  pose proof layout_nums.
  constructor; cbn; rewrite ?Hm, ?Hn, ?Hsb.
  - intros ma mt aib slots H0. discriminate H0.
  - left. reflexivity.
  - unfold A0, ctx0. cbn. intros H0. lia.
  - exact Hr.
  - unfold page_aligned. lia.
  - exact I.
  - intros b sz [].
  - intros b sz [].
  - intros pg [].
  - intros pg [].
  - intros b sz [].
  - split; [reflexivity | cbn; lia].
  - exact Htop.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dom_mcov : forall A h x, WF A -> VMok A h -> dom A x -> mcov (vm_maps h) x 1.
Proof.
  intros A h x HW HV [(pg & Hpg & Hx) | [(ma & mt & aib & slots & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx)]].
  - destruct (proj1 (vm_areas_cov A h HV pg Hpg)) as (b & sz & Hin & H1 & H2). exists b, sz. split; [exact Hin | llia].
  - destruct (vm_grp A h HV ma mt aib slots Hma Hr Hml) as [Hin _].
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hce & Hpg).
    destruct (Hpg Hml) as [_ (R1 & R2 & R3 & R4)]. pose proof layout_nums.
    exists (Z_to_bv 64 (mt_mem mt)), (Z_to_bv 64 (grp_map_len mt)). split; [exact Hin|].
    unfold grp_map_len in *. rewrite !u_lit by llia. llia.
  - destruct (proj1 (vm_pages_cov A h HV pg Hpg)) as (b & sz & Hin & H1 & H2). exists b, sz. split; [exact Hin | llia].
Qed.

(* [comment removed for export] *)
Lemma coh_mem : forall A m m' h, WF A -> VMok A h -> Coh A m h ->
  (forall a : word, m' a <> None -> 0x1000 <= bv_unsigned a < alloc_ceiling ->
     ~ (IMG_LO <= bv_unsigned a < IMG_HI) -> m a <> None \/ dom A (bv_unsigned a)) ->
  Coh A m' h.
Proof.
  intros A m m' h HW HV [C1 C2 C3 C4] Hm. constructor; [| exact C2 | exact C3 | exact C4].
  intros a Ha Hr Hi. destruct (Hm a Ha Hr Hi) as [Hm0 | Hd].
  - exact (C1 a Hm0 Hr Hi).
  - exact (dom_mcov A h _ HW HV Hd).
Qed.

(* [comment removed for export] *)
Lemma coh_restate : forall A A' m h, Coh A m h ->
  a_areas A' = a_areas A -> a_ctx A' KAmc = a_ctx A KAmc ->
  (forall sc, 0 <= sc < 48 -> a_ctx A' (KUsage sc) = a_ctx A (KUsage sc)) ->
  (forall x mt', a_meta A' x = Some mt' -> exists mt, a_meta A x = Some mt /\
      (mt_role mt' = RDead -> mt_role mt = RDead) /\ (mt_role mt' = RAvail -> mt_role mt = RAvail)) ->
  (forall sc x, 0 <= sc < 48 -> meta_usage A' sc x = meta_usage A sc x) ->
  Coh A' m h.
Proof.
  intros A A' m h [C1 C2 C3 C4] Ea Ec Eu Hm Hu. constructor.
  - exact C1.
  - intros ma mt' Hma' Hd. destruct (Hm ma mt' Hma') as (mt & Hma & H1 & _). exact (C2 ma mt Hma (H1 Hd)).
  - intros sc Hsc. rewrite (Eu sc Hsc), (C3 sc Hsc). symmetry. apply usage_of_ext; [exact Ea | intros x; apply Hu; exact Hsc].
  - intros ma mt' Hma' Hav. destruct (Hm ma mt' Hma') as (mt & Hma & _ & H2).
    rewrite Ea, Ec. exact (C4 ma mt Hma (H2 Hav)).
Qed.

End WithLayout.
