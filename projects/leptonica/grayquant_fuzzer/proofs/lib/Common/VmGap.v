(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the vDSO; the THP flag of the mmap placement; Linux's mmap placement). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import AsanCeil PropExec AgentLib AllocRefusal VmLedger.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Abbreviation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
Fixpoint find_ovl (l : list (word * word)) (lo n : Z) : option (word * word) :=
  match l with
  | [] => None
  | (b, s) :: r => if (u b <? lo + n) && (lo <? u b + u s) then Some (b, s) else find_ovl r lo n
  end.

Lemma find_ovl_none : forall l lo n, find_ovl l lo n = None ->
  forall b s, In (b, s) l -> u b + u s <= lo \/ lo + n <= u b.
Proof.
  induction l as [|[b0 s0] r IH]; intros lo n H b s Hin; [contradiction|].
  cbn in H. destruct ((u b0 <? lo + n) && (lo <? u b0 + u s0)) eqn:E; [discriminate|].
  destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. apply andb_false_iff in E as [E | E]; apply Z.ltb_ge in E; lia.
  - exact (IH lo n H b s Hin).
Qed.

Lemma find_ovl_some : forall l lo n b s, find_ovl l lo n = Some (b, s) ->
  In (b, s) l /\ u b < lo + n /\ lo < u b + u s.
Proof.
  induction l as [|[b0 s0] r IH]; intros lo n b s H; [discriminate|].
  cbn in H. destruct ((u b0 <? lo + n) && (lo <? u b0 + u s0)) eqn:E.
  - injection H as <- <-. apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
    split; [left; reflexivity | lia].
  - destruct (IH lo n b s H) as (Hin & H1 & H2). split; [right; exact Hin | lia].
Qed.

Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a s] r IH]; intros l2; cbn; [reflexivity | rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a s] r IH]; cbn; [lia | pose proof (u64_range s); lia]. Qed.

Lemma round_up_4096 : forall x, 0 <= x ->
  x <= (x + 4095) / 4096 * 4096 <= x + 4095 /\ ((x + 4095) / 4096 * 4096) mod 4096 = 0.
Proof.
  intros x Hx. pose proof (Z_div_mod_eq_full (x + 4095) 4096) as E.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as B.
  split; [lia | apply Z_mod_mult].
Qed.

(* [comment removed for export] *)
Lemma first_fit : forall (k : nat) (l : list (word * word)) (lo n : Z),
  length l = k -> 0 < n -> 0 <= lo -> lo mod 4096 = 0 ->
  exists a, lo <= a /\ a mod 4096 = 0 /\
            a <= lo + live_bytes l + Z.of_nat (length l) * (n + 4095) /\
            forall b s, In (b, s) l -> u b + u s <= a \/ a + n <= u b.
Proof.
  induction k as [|k IH]; intros l lo n Hlen Hn Hlo Hal.
  - destruct l; [|discriminate]. exists lo. cbn. split; [lia|]. split; [exact Hal|]. split; [lia|]. intros b s [].
  - destruct (find_ovl l lo n) as [[b s]|] eqn:Ef.
    + destruct (find_ovl_some l lo n b s Ef) as (Hin & H1 & H2).
      destruct (in_split (b, s) l Hin) as (l1 & l2 & ->).
      pose proof (u64_range b) as Hb. pose proof (u64_range s) as Hs.
      set (lo' := (u b + u s + 4095) / 4096 * 4096).
      destruct (round_up_4096 (u b + u s) ltac:(lia)) as [[R1 R2] R3]. fold lo' in R1, R2, R3.
      destruct (IH (l1 ++ l2) lo' n) as (a & A1 & A2 & A3 & A4);
        [rewrite length_app in *; cbn in Hlen; lia | exact Hn | lia | exact R3 |].
      exists a. split; [lia|]. split; [exact A2|]. split.
      * rewrite live_bytes_app' in *. cbn [live_bytes]. rewrite !length_app in *. cbn [length].
        rewrite !Nat2Z.inj_add in *. rewrite Nat2Z.inj_succ. nia.
      * intros b' s' Hin'. apply in_app_or in Hin'. destruct Hin' as [Hi | [Heq | Hi]].
        -- apply A4. apply in_or_app. left. exact Hi.
        -- injection Heq as <- <-. left. lia.
        -- apply A4. apply in_or_app. right. exact Hi.
    + exists lo. split; [lia|]. split; [exact Hal|]. split.
      * pose proof (live_bytes_nonneg l). nia.
      * exact (find_ovl_none l lo n Ef).
Qed.

Lemma region_free_of_disjoint : forall maps (a n : word),
  (forall b s, In (b, s) maps -> u b + u s <= u a \/ u a + u n <= u b) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[b s] r IH]; intros a n H; [reflexivity|].
  cbn [region_free]. apply andb_true_intro. split.
  - apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
    destruct (H b s ltac:(left; reflexivity)) as [X | X]; [left | right]; apply Z.ltb_ge; lia.
  - apply IH. intros b' s' Hin. apply H. right. exact Hin.
Qed.

(* [comment removed for export] *)
Theorem gap_exists_na : forall (thp : bool) (hint : word) (h : VmMaps) (n lo : Z),
  0 < n -> n mod 4096 = 0 ->
  task_unmapped_base <= lo -> lo mod 4096 = 0 ->
  (forall b s, In (b, s) (vm_reserved h) -> u b + u s <= lo) ->
  lo + vm_live_bytes h + Z.of_nat (length (vm_maps h)) * (n + 4095) + n <= alloc_top h ->
  exists a, grant_ok_na_vm thp hint h a n = true.
Proof.
  intros thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom.
  assert (Hlo0 : 0 < lo) by (unfold task_unmapped_base in Hlo; lia).
  destruct (first_fit (length (vm_maps h)) (vm_maps h) lo n eq_refl Hn ltac:(lia) Hloal) as (g & A1 & A2 & A3 & A4).
  unfold vm_live_bytes in Hroom.
  pose proof (alloc_top_lt_errno h) as Htop. unfold stack_max_size in Htop.
  assert (Hg : 0 < g /\ g + n <= alloc_top h) by lia.
  assert (Hug : u (Z_to_bv 64 g) = g) by (apply u64_lit; lia).
  assert (Hun : u (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  assert (Hpg : n mod page_size = 0) by (unfold page_size; exact Hnal).
  assert (Hfit : gap_fits (vm_reserved h ++ vm_maps h) task_unmapped_base (alloc_top h) n g).
  { unfold gap_fits. split; [unfold page_size; exact A2|]. split; [lia|]. split; [lia|].
    apply region_free_of_disjoint. intros b s Hin. rewrite Hug, Hun.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - left. pose proof (Hres b s Hin). lia.
    - exact (A4 b s Hin). }
  destruct (linux_place_exists h thp hint n Hn Hpg (ex_intro _ g (or_intror Hfit))) as [aZ Hpl].
  assert (Hav : vm_place_available h thp hint n = true).
  { unfold vm_place_available. destruct (linux_place_b_spec h thp hint n Hn Hpg) as [Hs _].
    rewrite (proj2 (Hs aZ) Hpl). reflexivity. }
  exact (proj1 (vm_place_available_na_iff thp hint h n Hn Hpg) Hav).
Qed.

(** the same, when the reserved ledger also holds entries above [lo]
    (the launch's vDSO/vvar pair at 08b1429): they are counted like mappings. *)
Theorem gap_exists_na_rx : forall (thp : bool) (hint : word) (h : VmMaps) (n lo : Z) (rx : list (word * word)),
  0 < n -> n mod 4096 = 0 ->
  task_unmapped_base <= lo -> lo mod 4096 = 0 ->
  (forall b s, In (b, s) (vm_reserved h) -> u b + u s <= lo \/ In (b, s) rx) ->
  lo + live_bytes rx + vm_live_bytes h + Z.of_nat (length rx + length (vm_maps h)) * (n + 4095) + n <= alloc_top h ->
  exists a, grant_ok_na_vm thp hint h a n = true.
Proof.
  intros thp hint h n lo rx Hn Hnal Hlo Hloal Hres Hroom.
  assert (Hlo0 : 0 < lo) by (unfold task_unmapped_base in Hlo; lia).
  destruct (first_fit (length (rx ++ vm_maps h)) (rx ++ vm_maps h) lo n eq_refl Hn ltac:(lia) Hloal) as (g & A1 & A2 & A3 & A4).
  rewrite live_bytes_app', length_app in A3.
  unfold vm_live_bytes in Hroom.
  pose proof (alloc_top_lt_errno h) as Htop. unfold stack_max_size in Htop.
  assert (Hg : 0 < g /\ g + n <= alloc_top h) by lia.
  assert (Hug : u (Z_to_bv 64 g) = g) by (apply u64_lit; lia).
  assert (Hun : u (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  assert (Hpg : n mod page_size = 0) by (unfold page_size; exact Hnal).
  assert (Hfit : gap_fits (vm_reserved h ++ vm_maps h) task_unmapped_base (alloc_top h) n g).
  { unfold gap_fits. split; [unfold page_size; exact A2|]. split; [lia|]. split; [lia|].
    apply region_free_of_disjoint. intros b s Hin. rewrite Hug, Hun.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - destruct (Hres b s Hin) as [X | X]; [left; lia | exact (A4 b s (in_or_app _ _ _ (or_introl X)))].
    - exact (A4 b s (in_or_app _ _ _ (or_intror Hin))). }
  destruct (linux_place_exists h thp hint n Hn Hpg (ex_intro _ g (or_intror Hfit))) as [aZ Hpl].
  assert (Hav : vm_place_available h thp hint n = true).
  { unfold vm_place_available. destruct (linux_place_b_spec h thp hint n Hn Hpg) as [Hs _].
    rewrite (proj2 (Hs aZ) Hpl). reflexivity. }
  exact (proj1 (vm_place_available_na_iff thp hint h n Hn Hpg) Hav).
Qed.

(* [comment removed for export] *)
Theorem gap_exists : forall (thp : bool) (hint : word) (h : VmMaps) (n lo : Z),
  0 < n -> n mod 4096 = 0 ->
  task_unmapped_base <= lo -> lo mod 4096 = 0 ->
  (forall b s, In (b, s) (vm_reserved h) -> u b + u s <= lo) ->
  lo + vm_live_bytes h + Z.of_nat (length (vm_maps h)) * (n + 4095) + n <= alloc_top h ->
  vm_backed_bytes h + n <= vm_limit h ->
  exists a, grant_ok_vm thp hint h a n = true.
Proof.
  intros thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom Hbud.
  destruct (gap_exists_na thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom) as [a Ha].
  exists a. unfold grant_ok_vm. unfold grant_ok_na_vm in Ha. rewrite Ha.
  rewrite (proj2 (Z.leb_le _ _) Hbud). reflexivity.
Qed.

(* [comment removed for export] *)
Corollary not_refusable_na : forall (thp : bool) (hint : word) (h : VmMaps) (n lo : Z),
  0 < n -> n mod 4096 = 0 -> task_unmapped_base <= lo -> lo mod 4096 = 0 ->
  (forall b s, In (b, s) (vm_reserved h) -> u b + u s <= lo) ->
  lo + vm_live_bytes h + Z.of_nat (length (vm_maps h)) * (n + 4095) + n <= alloc_top h ->
  mmap_na_refusable_vm thp hint h n = false.
Proof.
  intros thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom.
  apply (mmap_na_refusable_vm_false_iff thp hint h n Hn ltac:(unfold page_size; exact Hnal)).
  exact (gap_exists_na thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom).
Qed.

Corollary not_refusable : forall (thp : bool) (hint : word) (h : VmMaps) (n lo : Z),
  0 < n -> n mod 4096 = 0 -> task_unmapped_base <= lo -> lo mod 4096 = 0 ->
  (forall b s, In (b, s) (vm_reserved h) -> u b + u s <= lo) ->
  lo + vm_live_bytes h + Z.of_nat (length (vm_maps h)) * (n + 4095) + n <= alloc_top h ->
  vm_backed_bytes h + n <= vm_limit h ->
  mmap_refusable_vm thp hint h n = false.
Proof.
  intros thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom Hbud.
  apply (mmap_refusable_vm_false_iff thp hint h n Hn ltac:(unfold page_size; exact Hnal)).
  exact (gap_exists thp hint h n lo Hn Hnal Hlo Hloal Hres Hroom Hbud).
Qed.
