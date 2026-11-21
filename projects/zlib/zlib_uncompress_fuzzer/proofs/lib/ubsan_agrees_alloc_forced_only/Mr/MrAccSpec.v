(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require AsanCeil.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition mapped (mo : Model) : Z :=
  live_bytes (vm_maps (m_vmmaps mo)) + Z.of_nat (length (m_vm_materialized mo)) * page_size.

Lemma backing_le_mapped : forall mo, vm_backing_used mo <= mapped mo.
Proof.
  intro mo. unfold vm_backing_used, mapped, vm_backed_maps.
  pose proof (live_bytes_maps_subtract_all_le (m_vm_lazy mo)
                (maps_subtract_all (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)))) as H1.
  pose proof (live_bytes_maps_subtract_all_le (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))) as H2.
  lia.
Qed.

Definition small (l : list (word * word)) : Prop := Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) l.

Definition accs (C U : Z) (mo : Model) : Prop :=
  AsanCeil.init_sp_ok (m_vmmaps mo) /\
  small (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) /\
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= C /\
  mapped mo <= U /\
  vm_wf (m_vmmaps mo).

Lemma accs_mono : forall C U C' U' mo, accs C U mo -> C <= C' -> U <= U' -> accs C' U' mo.
Proof. intros C U C' U' mo (H1 & H2 & H3 & H4 & H5) HC HU. unfold accs. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|exact H5]. Qed.

Lemma accs_intro : forall C U dC dU m m',
  accs C U m ->
  vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m) ->
  vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m) ->
  (length (m_vm_materialized m') <= length (m_vm_materialized m))%nat ->
  small (vm_maps (m_vmmaps m')) ->
  Z.of_nat (length (vm_maps (m_vmmaps m'))) <= Z.of_nat (length (vm_maps (m_vmmaps m))) + dC ->
  live_bytes (vm_maps (m_vmmaps m')) <= live_bytes (vm_maps (m_vmmaps m)) + dU ->
  vm_wf (m_vmmaps m') ->
  accs (C + dC) (U + dU) m'.
Proof.
  intros C U dC dU m m' (H1 & H2 & H3 & H4 & H5) Hres Hsp Hmat Hsm Hlen Hlb Hwf.
  unfold accs, small in *. rewrite Hres.
  apply Forall_app in H2 as [H2a H2b].
  rewrite length_app in *.
  split; [|split; [|split; [|split]]].
  - unfold AsanCeil.init_sp_ok in *. rewrite Hsp. exact H1.
  - apply Forall_app. split; assumption.
  - lia.
  - unfold mapped in *. unfold page_size in *. lia.
  - exact Hwf.
Qed.

Lemma u64' : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. exact u64. Qed.

Lemma small_iv_subtract : forall a sz lo hi,
  bv_unsigned sz <= 2 ^ 30 -> small (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hsz. unfold iv_subtract, small.
  pose proof (word_range a) as Ha. pose proof (word_range sz) as Hs.
  apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64 by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
    apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
    rewrite u64 by lia. lia.
Qed.

Lemma small_maps_subtract : forall l lo hi, small l -> small (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] r IH]; intros lo hi H; [constructor|].
  inversion H as [|? ? Hhd Htl]; subst. cbn [maps_subtract].
  apply Forall_app. split; [apply small_iv_subtract; exact Hhd | apply IH; exact Htl].
Qed.

Lemma small_filter : forall f l, small l -> small (List.filter f l).
Proof. intros f l H. unfold small in *. rewrite Forall_forall in *. intros x Hx. apply filter_In in Hx as [Hx _]. auto. Qed.

Lemma length_iv_subtract : forall a sz lo hi, lo <= hi ->
  (length (iv_subtract a sz lo hi) <= 1 + (if owns_b (a, sz) lo then 1 else 0))%nat.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract, owns_b. cbn [fst snd]. rewrite length_app.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; cbn [length]; try lia.
  apply Z.ltb_lt in E1, E2.
  assert (Hle : (bv_unsigned a <=? lo) = true) by (apply Z.leb_le; lia).
  assert (Hlt : (lo <? bv_unsigned a + bv_unsigned sz) = true) by (apply Z.ltb_lt; lia).
  rewrite Hle, Hlt. cbn. lia.
Qed.

Lemma length_maps_subtract : forall l lo hi, lo <= hi ->
  (length (maps_subtract l lo hi) <= length l + owners l lo)%nat.
Proof.
  induction l as [|[a sz] r IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract owners length]. rewrite length_app.
  pose proof (length_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma length_maps_subtract_wf : forall l lo hi, maps_wf l -> lo <= hi -> lo mod page_size = 0 ->
  (length (maps_subtract l lo hi) <= length l + 1)%nat.
Proof.
  intros l lo hi [_ Hun] Hlh Hal. pose proof (length_maps_subtract l lo hi Hlh). specialize (Hun lo Hal). lia.
Qed.

Lemma live_bytes_filter_le : forall f l, live_bytes (List.filter f l) <= live_bytes l.
Proof.
  intros f l. induction l as [|[a sz] r IH]; [cbn; lia|].
  cbn [List.filter]. pose proof (word_range sz). destruct (f (a, sz)); cbn [live_bytes]; lia.
Qed.

Lemma length_filter_le : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros A f l. induction l as [|x r IH]; [cbn; lia|]. cbn [List.filter]. destruct (f x); cbn [length]; lia. Qed.

Lemma mat_vmmaps : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mat_mmap_backing : forall flags a n m, m_vm_materialized (with_mmap_backing flags a n m) = m_vm_materialized m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mat_forget_range : forall lo hi m,
  (length (m_vm_materialized (vm_forget_range lo hi m)) <= length (m_vm_materialized m))%nat.
Proof. intros. unfold vm_forget_range. change (m_vm_materialized (with_vm_backing ?l ?p m)) with p. apply length_filter_le. Qed.
Lemma mat_mmap_destroyed : forall a n h m,
  (length (m_vm_materialized (with_mmap_destroyed a n h m)) <= length (m_vm_materialized m))%nat.
Proof. intros. unfold with_mmap_destroyed. etransitivity; [apply mat_forget_range|]. rewrite mat_vmmaps. lia. Qed.
Lemma mat_mmap_replacement : forall flags a n m,
  (length (m_vm_materialized (with_mmap_replacement flags a n m)) <= length (m_vm_materialized m))%nat.
Proof. intros. unfold with_mmap_replacement. rewrite mat_mmap_backing. apply mat_forget_range. Qed.
Lemma mat_forget_ranges : forall rs m,
  (length (m_vm_materialized (forget_vm_ranges rs m)) <= length (m_vm_materialized m))%nat.
Proof.
  induction rs as [|[a n] r IH]; intro m; [cbn; lia|].
  cbn [forget_vm_ranges]. etransitivity; [apply IH|]. apply mat_forget_range.
Qed.

(* a brk GROW now records the whole pages Linux installs, [PAGE_ALIGN(old),
   PAGE_ALIGN(req)) (Mmap.brk_grants / brk_page_range), up to one page more than req - old. Hence the size
   premise keeps a page of room (2^30 - 4096) and the byte budget grows by at most req - old + 4096. *)
Lemma pru_bounds_a2 : forall z, 0 <= z -> z <= page_round_up_Z z <= z + 4095.
Proof. intros z Hz. unfold page_round_up_Z. change page_size with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma accs_brk : forall req eff m m' evs C U,
  check_brk req eff m = CheckOk m' evs ->
  (bv_unsigned req = 0 \/ bv_unsigned (vm_brk (m_vmmaps m)) <= bv_unsigned req) ->
  bv_unsigned req - bv_unsigned (vm_brk (m_vmmaps m)) <= 2 ^ 30 - 4096 ->
  accs C U m ->
  accs (C + 1) (U + (Z.max 0 (bv_unsigned req - bv_unsigned (vm_brk (m_vmmaps m))) + 4096)) m'.
Proof.
  intros req eff m m' evs C U H Hreq Hsz Hacc.
  pose proof (check_brk_preserves _ _ _ _ _ H (proj2 (proj2 (proj2 (proj2 Hacc))))) as Hwf.
  destruct eff as [ret ws zs us cs ci].
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct ci as [|? ?]; [|discriminate].
  destruct (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (vm_brk (m_vmmaps m)))
            && listNN_eqb us (brk_unmaps ret (vm_brk (m_vmmaps m)))) eqn:E; [|discriminate].
  injection H as <- <-.
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
  set (b := vm_brk (m_vmmaps m)) in *.
  pose proof (word_range req) as Hrr. pose proof (word_range b) as Hbr. pose proof (word_range ret) as Hretr.
  assert (Hret : ret = b \/ (ret = req /\ bv_unsigned b <= bv_unsigned req)).
  { unfold brk_r_ok in E. fold b in E.
    destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m)))) eqn:E1.
    - left. apply bv_eqb_eq in E. exact E.
    - destruct (bv_unsigned req <? bv_unsigned b) eqn:E2.
      + apply Z.ltb_lt in E2. apply orb_false_iff in E1 as [E1 _].
        apply w_is0_false in E1. lia.
      + apply Z.ltb_ge in E2. apply andb_true_iff in E as [E _].
        apply orb_true_iff in E as [E|E]; apply bv_eqb_eq in E; [right; split; [exact E|lia] | left; exact E]. }
  rewrite vmm_brk_next in Hwf.
  eapply (accs_intro C U 1 _ m); [exact Hacc | | | | | | | rewrite vmm_brk_next; exact Hwf].
  - rewrite vmm_brk_next. reflexivity.
  - rewrite vmm_brk_next. reflexivity.
  - unfold with_brk_next. etransitivity; [apply mat_forget_ranges|]. rewrite mat_vmmaps. lia.
  - rewrite vmm_brk_next. cbn [brk_model_next vm_maps]. unfold brk_maps_next. fold b.
    destruct Hacc as (_ & Hsm & _). apply Forall_app in Hsm as [_ Hsm].
    destruct Hret as [-> | [-> Hle]].
    + rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. exact Hsm.
    + replace (bv_unsigned req <? bv_unsigned b) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      unfold brk_grants. destruct (brk_is_grow req req b) eqn:G; [|exact Hsm].
      pose proof (pru_bounds_a2 (bv_unsigned b) ltac:(lia)). pose proof (pru_bounds_a2 (bv_unsigned req) ltac:(lia)).
      unfold brk_page_range.
      destruct (page_round_up_Z (bv_unsigned b) <? page_round_up_Z (bv_unsigned req))%Z eqn:L; [|exact Hsm].
      apply Z.ltb_lt in L.
      constructor; [|exact Hsm]. cbn [snd]. rewrite u64' by lia. lia.
  - rewrite vmm_brk_next. cbn [brk_model_next vm_maps]. unfold brk_maps_next. fold b.
    destruct Hret as [-> | [-> Hle]].
    + rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. cbn [app]. lia.
    + replace (bv_unsigned req <? bv_unsigned b) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      unfold brk_grants. destruct (brk_is_grow req req b); [unfold brk_page_range; destruct (_ <? _)%Z|];
        cbn [app length]; lia.
  - rewrite vmm_brk_next. cbn [brk_model_next vm_maps]. unfold brk_maps_next. fold b.
    destruct Hret as [-> | [-> Hle]].
    + rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. cbn [app]. lia.
    + replace (bv_unsigned req <? bv_unsigned b) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      unfold brk_grants. destruct (brk_is_grow req req b); cbn [app live_bytes]; [|lia].
      pose proof (pru_bounds_a2 (bv_unsigned b) ltac:(lia)). pose proof (pru_bounds_a2 (bv_unsigned req) ltac:(lia)).
      unfold brk_page_range.
      destruct (page_round_up_Z (bv_unsigned b) <? page_round_up_Z (bv_unsigned req))%Z eqn:L; cbn [app live_bytes];
        [|lia].
      apply Z.ltb_lt in L. rewrite u64' by lia. lia.
Qed.

(* accs_munmap moved to the end of this file (it now uses accs_destroyed and chk_walk). *)

(* accs_mprotect moved to the end of this file ('s check_mprotect has the vDSO
   gate; the proof walks it with chk_walk). *)

Lemma page_round_up_le : forall z, 0 <= z -> z <= page_round_up_Z z <= z + 4095.
Proof. intros z Hz. unfold page_round_up_Z. change page_size with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma accs_cons : forall flags a nZ noacc m C U dU,
  accs C U m -> 0 <= nZ <= 2 ^ 30 -> nZ <= dU ->
  let m' := with_mmap_backing flags a (Z_to_bv 64 nZ)
              (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m)) noacc
                              (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                              (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m) in
  vm_wf (m_vmmaps m') -> accs (C + 2) (U + dU) m'.
Proof.
  intros flags a nZ noacc m C U dU Hacc HnZ HdU m' Hwf.
  assert (Hv : m_vmmaps m' = mkVmMapsFull (vm_reserved (m_vmmaps m)) ((a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m)) noacc
                              (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                              (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))).
  { unfold m'. rewrite vmm_mmap_backing, vmm_vmmaps. reflexivity. }
  apply (accs_mono (C + 1) (U + nZ)); [|lia|lia].
  eapply (accs_intro C U 1 nZ m); [exact Hacc | | | | | | | exact Hwf]; try (rewrite Hv; cbn [vm_reserved vm_init_sp vm_maps]).
  - reflexivity.
  - reflexivity.
  - unfold m'. rewrite mat_mmap_backing, mat_vmmaps. lia.
  - destruct Hacc as (_ & Hsm & _). apply Forall_app in Hsm as [_ Hsm].
    constructor; [|exact Hsm]. cbn [snd]. rewrite u64 by lia. lia.
  - cbn [length]. lia.
  - cbn [live_bytes]. rewrite u64 by lia. lia.
Qed.

Lemma accs_destroyed : forall addr n m C U,
  accs C U m -> bv_unsigned addr mod page_size = 0 ->
  let m' := with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m in
  vm_wf (m_vmmaps m') -> accs (C + 2) U m'.
Proof.
  intros addr n m C U Hacc Hal m' Hwf.
  assert (Hv : m_vmmaps m' = mmap_fixed_destroyed_next (m_vmmaps m) addr n).
  { unfold m'. rewrite vmm_mmap_destroyed. reflexivity. }
  pose proof (word_range n) as Hn.
  apply (accs_mono (C + 1) (U + 0)); [|lia|lia].
  eapply (accs_intro C U 1 0 m); [exact Hacc | | | | | | | exact Hwf];
    try (rewrite Hv; cbn [mmap_fixed_destroyed_next vm_reserved vm_init_sp vm_maps]).
  - reflexivity.
  - reflexivity.
  - apply mat_mmap_destroyed.
  - destruct Hacc as (_ & Hsm & _). apply Forall_app in Hsm as [_ Hsm]. apply small_maps_subtract. exact Hsm.
  - destruct Hacc as (_ & _ & _ & _ & Hw).
    pose proof (length_maps_subtract_wf (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hw ltac:(lia) Hal). lia.
  - pose proof (live_bytes_maps_subtract_le (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ltac:(lia)). lia.
Qed.

Lemma accs_repl_same : forall flags addr n h' m C U,
  accs C U m ->
  vm_reserved h' = vm_reserved (m_vmmaps m) -> vm_init_sp h' = vm_init_sp (m_vmmaps m) -> vm_maps h' = vm_maps (m_vmmaps m) ->
  let m' := with_mmap_replacement flags addr n (with_vmmaps h' m) in
  vm_wf (m_vmmaps m') -> accs (C + 2) U m'.
Proof.
  intros flags addr n h' m C U Hacc Hr Hs Hm m' Hwf.
  assert (Hv : m_vmmaps m' = h'). { unfold m'. rewrite vmm_mmap_replacement, vmm_vmmaps. reflexivity. }
  apply (accs_mono (C + 0) (U + 0)); [|lia|lia].
  eapply (accs_intro C U 0 0 m); [exact Hacc | | | | | | | exact Hwf]; try rewrite Hv.
  - exact Hr.
  - exact Hs.
  - unfold m'. etransitivity; [apply mat_mmap_replacement|]. rewrite mat_vmmaps. lia.
  - rewrite Hm. destruct Hacc as (_ & Hsm & _). apply Forall_app in Hsm as [_ Hsm]. exact Hsm.
  - rewrite Hm. lia.
  - rewrite Hm. lia.
Qed.

Lemma accs_span : forall flags addr nZ h' m C U dU,
  accs C U m -> 0 <= nZ <= 2 ^ 30 -> nZ <= dU -> bv_unsigned addr mod page_size = 0 ->
  vm_reserved h' = vm_reserved (m_vmmaps m) -> vm_init_sp h' = vm_init_sp (m_vmmaps m) ->
  vm_maps h' = (addr, Z_to_bv 64 nZ) :: maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr)
                                           (bv_unsigned addr + bv_unsigned (Z_to_bv 64 nZ)) ->
  let m' := with_mmap_replacement flags addr (Z_to_bv 64 nZ) (with_vmmaps h' m) in
  vm_wf (m_vmmaps m') -> accs (C + 2) (U + dU) m'.
Proof.
  intros flags addr nZ h' m C U dU Hacc HnZ HdU Hal Hr Hs Hm m' Hwf.
  assert (Hv : m_vmmaps m' = h'). { unfold m'. rewrite vmm_mmap_replacement, vmm_vmmaps. reflexivity. }
  apply (accs_mono (C + 2) (U + nZ)); [|lia|lia].
  eapply (accs_intro C U 2 nZ m); [exact Hacc | | | | | | | exact Hwf]; try rewrite Hv.
  - exact Hr.
  - exact Hs.
  - unfold m'. etransitivity; [apply mat_mmap_replacement|]. rewrite mat_vmmaps. lia.
  - rewrite Hm. destruct Hacc as (_ & Hsm & _). apply Forall_app in Hsm as [_ Hsm].
    constructor; [cbn [snd]; rewrite u64 by lia; lia | apply small_maps_subtract; exact Hsm].
  - rewrite Hm. cbn [length]. destruct Hacc as (_ & _ & _ & _ & Hw). rewrite u64 by lia.
    pose proof (length_maps_subtract_wf (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + nZ) Hw ltac:(lia) Hal). lia.
  - rewrite Hm. cbn [live_bytes]. rewrite !u64 by lia.
    pose proof (live_bytes_maps_subtract_le (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + nZ) ltac:(lia)). lia.
Qed.

(* accs_mmap re-walked over 's check_mmap. The tree is new (the placement
   decline gate, linux_place_is, the MAP_FIXED overflow arm, the fd arm), but its LEAVES are the old ones: the model
   unchanged (CheckOk m), a fresh entry (accs_cons), the range destroyed (accs_destroyed), replaced in place
   (accs_repl_same) or spanned (accs_span). So the walk keeps every branch condition (mm_walk) and each leaf is
   closed by the leaf lemma whose shape it has; the statement is unchanged. *)
Ltac mm_walk H :=
  repeat match type of H with
  | CheckOk _ _ = CheckOk _ _ => injection H as <- <-
  | CheckReject = CheckOk _ _ => discriminate H
  | CheckUnmodeled = CheckOk _ _ => discriminate H
  | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_model in H; subst
  | check_mmap_fixed_overflow _ _ _ _ = CheckOk _ _ => unfold check_mmap_fixed_overflow in H
  | context [match ?l with [] => _ | _ :: _ => _ end] => destruct l
  | context [match ?o with Some _ => _ | None => _ end] => destruct o
  | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
  end.

Lemma accs_mmap : forall addr len prot flags fd off eff m m' evs C U,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  bv_unsigned len <= 2 ^ 30 - 4096 ->
  accs C U m ->
  accs (C + 2) (U + (bv_unsigned len + 4096)) m'.
Proof.
  intros addr len prot flags fd off eff m m' evs C U H Hlen Hacc.
  pose proof (check_mmap_preserves _ _ _ _ _ _ _ _ _ _ H (proj2 (proj2 (proj2 (proj2 Hacc))))) as Hwf.
  assert (Hsame : accs (C + 2) (U + (bv_unsigned len + 4096)) m).
  { pose proof (word_range len). apply (accs_mono C U); [exact Hacc|lia|lia]. }
  destruct eff as [ret ws zs us cs ci].
  unfold check_mmap in H. cbv zeta in H.
  pose proof (word_range len) as Hlenr.
  pose proof (page_round_up_le (bv_unsigned len) ltac:(lia)) as Hru.
  set (nZ := page_round_up_Z (bv_unsigned len)) in *.
  assert (HnZ : 0 <= nZ <= 2 ^ 30) by lia.
  assert (HdU : nZ <= bv_unsigned len + 4096) by lia.
  mm_walk H.
  all: try exact Hsame.
  all: try exact (accs_cons _ _ nZ _ m C U _ Hacc HnZ HdU Hwf).
  all: try (match goal with Ea : negb (bv_unsigned ?a mod page_size =? 0) = false |- _ =>
              apply negb_false_iff, Z.eqb_eq in Ea end).
  all: try (apply (accs_mono (C + 2) U); [exact (accs_destroyed addr (Z_to_bv 64 nZ) m C U Hacc ltac:(assumption) Hwf)
                                         | lia | lia]).
  all: try (apply (accs_mono (C + 2) U); [eapply (accs_repl_same _ addr (Z_to_bv 64 nZ) _ m C U Hacc);
                                          [..|exact Hwf]; reflexivity | lia | lia]).
  all: try (eapply (accs_span _ addr nZ _ m C U _ Hacc HnZ HdU ltac:(assumption)); [..|exact Hwf]; reflexivity).
Qed.

Ltac chk_walk H :=
  repeat match type of H with
  | CheckOk _ _ = CheckOk _ _ => injection H as <- <-
  | CheckReject = CheckOk _ _ => discriminate H
  | CheckUnmodeled = CheckOk _ _ => discriminate H
  | check_ret_only _ _ _ _ = CheckOk _ _ => apply check_ret_only_model in H; subst
  | context [match ?l with [] => _ | _ :: _ => _ end] => destruct l
  | context [if ?b then _ else _] => destruct b
  end.
Ltac lim_leaf :=
  rewrite ?vmm_mmap_backing, ?vmm_mmap_replacement, ?vmm_mmap_destroyed, ?vmm_vmmaps, ?vmm_fixed_rw_next,
          ?vmm_mprotect_next, ?vmm_brk_next; reflexivity.

Lemma lim_mmap : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap in H. cbv zeta in H. mm_walk H; lim_leaf.
Qed.

Lemma lim_munmap : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap in H. cbv zeta in H. chk_walk H; lim_leaf.
Qed.

Lemma lim_mprotect : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect in H. cbv zeta in H. chk_walk H; lim_leaf.
Qed.

Lemma lim_brk : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> vm_limit (m_vmmaps m') = vm_limit (m_vmmaps m).
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H. chk_walk H; lim_leaf.
Qed.

Lemma brk0_query_chk : forall eff m m' evs,
  check_brk (Z_to_bv 64 0) eff m = CheckOk m' evs ->
  eff_ret eff = vm_brk (m_vmmaps m) /\ m_vmmaps m' = m_vmmaps m /\ m_vm_materialized m' = m_vm_materialized m
  /\ m_vm_lazy m' = m_vm_lazy m.
Proof.
  intros [ret ws zs us cs ci] m m' evs H. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok m (Z_to_bv 64 0) ret && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  injection H as <- <-.
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
  unfold brk_r_ok in E. change (w_is0 (Z_to_bv 64 0)) with true in E. cbn [orb] in E. apply bv_eqb_eq in E. subst ret.
  cbn [eff_ret]. split; [reflexivity|].
  assert (Hun : brk_unmaps (vm_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) = []).
  { unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl. destruct (0 <? _); reflexivity. }
  unfold with_brk_next. cbv zeta. rewrite Hun. cbn [forget_vm_ranges].
  split; [|split; reflexivity].
  rewrite vmm_vmmaps. unfold brk_model_next, brk_maps_next. rewrite Hun. cbn [maps_subtract_ranges fold_left].
  rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
  destruct (m_vmmaps m); reflexivity.
Qed.

(* munmap now removes the RANGE (Mmap.mmap_fixed_destroyed_next, a maps_subtract that can
   split an entry), in its exact arm and in its new partial arm, and both arms may answer ENOMEM. So the entry count
   may grow, as in accs_destroyed (C + 2); the bytes never grow. *)
Lemma accs_munmap : forall addr len eff m m' evs C U,
  check_munmap addr len eff m = CheckOk m' evs -> accs C U m -> accs (C + 2) U m'.
Proof.
  intros addr len eff m m' evs C U H Hacc.
  pose proof (check_munmap_preserves _ _ _ _ _ _ H (proj2 (proj2 (proj2 (proj2 Hacc))))) as Hwf.
  destruct eff as [ret ws zs us cs ci].
  unfold check_munmap in H. cbv zeta in H.
  destruct (negb (bv_unsigned addr mod page_size =? 0) || w_is0 len)%bool eqn:Hal.
  { chk_walk H. eapply accs_mono; [exact Hacc | lia | lia]. }
  apply orb_false_iff in Hal as [Hal _]. apply negb_false_iff, Z.eqb_eq in Hal.
  chk_walk H; try (eapply accs_mono; [exact Hacc | lia | lia]).
  all: apply accs_destroyed; [exact Hacc | exact Hal | exact Hwf].
Qed.

(* mprotect changes vm_noaccess only (never vm_maps' entries or bytes); every leaf of
   's check_mprotect (EINVAL / ENOMEM / the vDSO gate / the modeled arm) keeps the count and the bytes. *)
Lemma accs_mprotect : forall addr len prot eff m m' evs C U,
  check_mprotect addr len prot eff m = CheckOk m' evs -> accs C U m -> accs C U m'.
Proof.
  intros addr len prot eff m m' evs C U H Hacc.
  pose proof (check_mprotect_preserves _ _ _ _ _ _ _ H (proj2 (proj2 (proj2 (proj2 Hacc))))) as Hwf.
  destruct eff as [ret ws zs us cs ci].
  unfold check_mprotect in H. cbv zeta in H.
  chk_walk H; try exact Hacc.
  all: replace C with (C + 0) by lia; replace U with (U + 0) by lia;
    eapply (accs_intro C U 0 0 m); [exact Hacc | | | | | | | exact Hwf];
    try (rewrite vmm_mprotect_next; cbn [vm_reserved vm_init_sp vm_maps]).
  all: try reflexivity.
  all: try (unfold mprotect_model_next; rewrite mat_vmmaps; lia).
  all: try (destruct Hacc as (_ & Hsm & _); apply Forall_app in Hsm as [_ Hsm]; exact Hsm).
  all: lia.
Qed.

(* a SAFE munmap (Lib/Nodes' munmap_safe_b: an exact entry, or a range free of the
   ledger) never splits an entry, so it costs no entry: accs C U, not C + 2. Only the partial arm (munmap_cut_ok)
   can split, and safety excludes it. A splitting entry is one that strictly straddles both ends of the range. *)
Definition straddles (lo hi : Z) (p : word * word) : bool :=
  (bv_unsigned (fst p) <? lo) && (hi <? bv_unsigned (fst p) + bv_unsigned (snd p)).

Lemma length_iv_subtract_s : forall a sz lo hi,
  (length (iv_subtract a sz lo hi) <= (if straddles lo hi (a, sz) then 2 else 1))%nat.
Proof.
  intros a sz lo hi. unfold iv_subtract, straddles. cbn [fst snd]. rewrite length_app.
  destruct (bv_unsigned a <? lo); destruct (hi <? bv_unsigned a + bv_unsigned sz); cbn; lia.
Qed.

Lemma length_maps_subtract_ns : forall l lo hi,
  (forall p, In p l -> straddles lo hi p = false) -> (length (maps_subtract l lo hi) <= length l)%nat.
Proof.
  induction l as [|[a sz] r IH]; intros lo hi H; [cbn; lia|].
  cbn [maps_subtract length]. rewrite length_app.
  pose proof (length_iv_subtract_s a sz lo hi) as L. rewrite (H (a, sz) (or_introl eq_refl)) in L.
  specialize (IH lo hi (fun p Hp => H p (or_intror Hp))). lia.
Qed.

Lemma accs_destroyed_ns : forall addr n m C U,
  accs C U m ->
  (forall p, In p (vm_maps (m_vmmaps m)) -> straddles (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) p = false) ->
  let m' := with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m in
  vm_wf (m_vmmaps m') -> accs C U m'.
Proof.
  intros addr n m C U Hacc Hns m' Hwf.
  assert (Hv : m_vmmaps m' = mmap_fixed_destroyed_next (m_vmmaps m) addr n).
  { unfold m'. rewrite vmm_mmap_destroyed. reflexivity. }
  pose proof (word_range n) as Hn.
  apply (accs_mono (C + 0) (U + 0)); [|lia|lia].
  eapply (accs_intro C U 0 0 m); [exact Hacc | | | | | | | exact Hwf];
    try (rewrite Hv; cbn [mmap_fixed_destroyed_next vm_reserved vm_init_sp vm_maps]).
  - reflexivity.
  - reflexivity.
  - apply mat_mmap_destroyed.
  - destruct Hacc as (_ & Hsm & _). apply Forall_app in Hsm as [_ Hsm]. apply small_maps_subtract. exact Hsm.
  - pose proof (length_maps_subtract_ns (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hns).
    lia.
  - pose proof (live_bytes_maps_subtract_le (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) ltac:(lia)). lia.
Qed.

Lemma owners_ge1 : forall l p x, In p l -> owns_b p x = true -> (1 <= owners l x)%nat.
Proof.
  induction l as [|e r IH]; intros p x Hin Ho; [destruct Hin|]. cbn [owners].
  destruct Hin as [<-|Hin]; [rewrite Ho; lia|]. specialize (IH p x Hin Ho). lia.
Qed.

Lemma owners_two : forall l p q x, In p l -> In q l -> p <> q ->
  owns_b p x = true -> owns_b q x = true -> (2 <= owners l x)%nat.
Proof.
  induction l as [|e r IH]; intros p q x Hp Hq Hpq Hop Hoq; [destruct Hp|]. cbn [owners].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - congruence.
  - rewrite Hop. pose proof (owners_ge1 r q x Hq Hoq). lia.
  - rewrite Hoq. pose proof (owners_ge1 r p x Hp Hop). lia.
  - specialize (IH p q x Hp Hq Hpq Hop Hoq). destruct (owns_b e x); lia.
Qed.

(* The premise is Lib/Nodes' munmap_safe_b over the model's ledger, unfolded (so this text needs no Lib import). *)
Lemma accs_munmap_safe : forall addr len eff m m' evs C U,
  (if (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len)%bool then true
   else if (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z then true
   else (map_has (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
         || munmap_free_ok (m_vmmaps m) addr (page_round_up_Z (bv_unsigned len)))%bool) = true ->
  check_munmap addr len eff m = CheckOk m' evs -> accs C U m -> accs C U m'.
Proof.
  intros addr len eff m m' evs C U Hs H Hacc.
  pose proof (check_munmap_preserves _ _ _ _ _ _ H (proj2 (proj2 (proj2 (proj2 Hacc))))) as Hwf.
  destruct eff as [ret ws zs us cs ci].
  unfold check_munmap in H. cbv zeta in H.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0) || w_is0 len)%bool eqn:Hal.
  (* destruct ... eqn rewrites AND reduces H and Hs to the taken branch (probe p12). *)
  { apply check_ret_only_model in H. subst. exact Hacc. }
  apply orb_false_iff in Hal as [Hal _]. apply negb_false_iff, Z.eqb_eq in Hal.
  destruct (TASK_SIZE <? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z eqn:Ht.
  { apply check_ret_only_model in H. subst. exact Hacc. }
  set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) in *.
  destruct (map_has (vm_maps (m_vmmaps m)) addr n) eqn:Hm.
  - (* No entry straddles the range: it would own the range's first page together with the exact entry. *)
    assert (NS : forall p, In p (vm_maps (m_vmmaps m)) ->
                 straddles (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) p = false).
    2:{ chk_walk H; try exact Hacc.
        all: apply accs_destroyed_ns; [exact Hacc | exact NS | exact Hwf]. }
    intros [pa ps] Hin. unfold straddles. cbn [fst snd].
    destruct (bv_unsigned pa <? bv_unsigned addr) eqn:E1; [|reflexivity].
    destruct (bv_unsigned addr + bv_unsigned n <? bv_unsigned pa + bv_unsigned ps) eqn:E2; [|reflexivity].
    exfalso. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    unfold map_has in Hm. apply existsb_exists in Hm as [[qa qs] [Hq Hqe]]. cbn [fst snd] in Hqe.
    apply andb_prop in Hqe as [Hqa Hqs]. apply bv_eqb_eq in Hqa. apply bv_eqb_eq in Hqs. subst qa qs.
    destruct Hacc as (_ & _ & _ & _ & [Hnz Hun]).
    pose proof (proj1 (Forall_forall _ _) Hnz (addr, n) Hq) as Hn0. cbn [snd] in Hn0.
    pose proof (word_range n) as Hnr.
    pose proof (owners_two (vm_maps (m_vmmaps m)) (pa, ps) (addr, n) (bv_unsigned addr) Hin Hq
                  ltac:(intros Eq; injection Eq as Ea _; subst pa; lia)
                  ltac:(unfold owns_b; cbn [fst snd]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia)
                  ltac:(unfold owns_b; cbn [fst snd]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia))
      as H2.
    specialize (Hun (bv_unsigned addr) Hal). lia.
  - cbn [orb] in Hs. rewrite Hs in H. cbn iota in H. apply check_ret_only_model in H. subst. exact Hacc.
Qed.
