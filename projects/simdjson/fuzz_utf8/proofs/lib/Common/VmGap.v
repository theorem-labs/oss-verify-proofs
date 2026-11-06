(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_up_Z_spec : forall x,
  x <= page_round_up_Z x < x + page_size /\ page_round_up_Z x mod page_size = 0.
Proof.
  intros x. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)) as Hmb.
  split; [lia |]. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_le_aligned : forall x B,
  x <= B -> B mod page_size = 0 -> page_round_up_Z x <= B.
Proof.
  intros x B Hx HB. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)) as Hmb.
  pose proof (Z.div_mod B 4096 ltac:(lia)) as HBd.
  rewrite HB in HBd.
  assert ((x + 4096 - 1) / 4096 <= B / 4096) by lia.
  lia.
Qed.

(* [comment removed for export] *)
Lemma max_below : forall (l : list Z) (B x0 : Z),
  In x0 l -> x0 <= B ->
  exists m, In m l /\ m <= B /\ forall y, In y l -> y <= B -> y <= m.
Proof.
  induction l as [|z l IH]; intros B x0 Hin Hle; [contradiction |].
  assert (Hcase : (exists m, In m l /\ m <= B /\ forall y, In y l -> y <= B -> y <= m)
                  \/ (forall y, In y l -> y <= B -> False)).
  { destruct (List.Exists_dec (fun y => y <= B) l (fun y => Z_le_dec y B)) as [Hex | Hno].
    - left. apply List.Exists_exists in Hex as (y & Hy & HyB). exact (IH B y Hy HyB).
    - right. intros y Hy HyB. apply Hno. apply List.Exists_exists. exists y. split; assumption. }
  destruct Hcase as [(m & Hm & HmB & Hmax) | Hnone].
  - destruct (Z_le_dec z B) as [HzB | HzB].
    + destruct (Z_le_dec z m) as [Hzm | Hzm].
      * exists m. split; [right; exact Hm |]. split; [exact HmB |].
        intros y [<- | Hy] HyB; [exact Hzm | exact (Hmax y Hy HyB)].
      * exists z. split; [left; reflexivity |]. split; [exact HzB |].
        intros y [<- | Hy] HyB; [lia |]. pose proof (Hmax y Hy HyB). lia.
    + exists m. split; [right; exact Hm |]. split; [exact HmB |].
      intros y [<- | Hy] HyB; [lia | exact (Hmax y Hy HyB)].
  - destruct Hin as [-> | Hin]; [| exfalso; exact (Hnone x0 Hin Hle)].
    exists x0. split; [left; reflexivity |]. split; [exact Hle |].
    intros y [<- | Hy] HyB; [lia | exfalso; exact (Hnone y Hy HyB)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_intro : forall maps lo n,
  (forall b sz, In (b, sz) maps -> iv_overlap lo n b sz = false) ->
  region_free maps lo n = true.
Proof.
  induction maps as [|[b sz] r IH]; intros lo n H; [reflexivity |].
  cbn [region_free]. rewrite (H b sz (or_introl eq_refl)). cbn [negb andb].
  apply IH. intros b' sz' Hin. apply H. right. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_base_candidate_values (h : VmMaps) : list Z :=
  page_size
  :: map (fun iv => page_round_up_Z (bv_unsigned (fst iv) + bv_unsigned (snd iv)))
         (vm_reserved h ++ vm_maps h).

Lemma vm_base_candidates_values : forall h,
  vm_base_candidates h = map (Z_to_bv 64) (vm_base_candidate_values h).
Proof.
  intros h. unfold vm_base_candidates, vm_base_candidate_values.
  cbn [map]. rewrite map_map. reflexivity.
Qed.

Lemma candidate_value_mod : forall h v,
  In v (vm_base_candidate_values h) -> v mod page_size = 0.
Proof.
  intros h v Hin. destruct Hin as [<- | Hin].
  - reflexivity.
  - apply in_map_iff in Hin as (iv & <- & _). apply page_round_up_Z_spec.
Qed.

(* [comment removed for export] *)
Theorem vm_gap_available_complete' : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ a Hok.
  pose proof Hok as Hok0. unfold vm_base_ok in Hok.
  apply andb_true_iff in Hok as [Hok Hfree].
  apply andb_true_iff in Hok as [Hok Htop].
  apply andb_true_iff in Hok as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  set (ua := bv_unsigned a) in *.
  set (n := Z_to_bv 64 nZ) in *.
  pose proof (bv_unsigned_in_range 64 a) as Hua. fold ua in Hua.
  unfold bv_modulus in Hua.
  (* [comment removed for export] *)
  assert (H4096 : page_size <= ua).
  { unfold page_size in *. pose proof (Z.div_mod ua 4096 ltac:(lia)). rewrite Halign in H. lia. }
  destruct (max_below (vm_base_candidate_values h) ua page_size (or_introl eq_refl) H4096)
    as (m & Hm_in & Hm_le & Hm_max).
  assert (Hm_pos : page_size <= m) by (apply Hm_max; [left; reflexivity | exact H4096]).
  assert (Hm_mod : m mod page_size = 0) by (exact (candidate_value_mod h m Hm_in)).
  assert (Hm_u : bv_unsigned (Z_to_bv 64 m) = m).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus, page_size in *. lia. }
  (* [comment removed for export] *)
  assert (Hm_ok : vm_base_ok h nZ (Z_to_bv 64 m) = true).
  { unfold vm_base_ok. rewrite Hm_u. fold n.
    rewrite (proj2 (Z.eqb_eq _ _) Hm_mod).
    rewrite (proj2 (Z.ltb_lt 0 m)) by (unfold page_size in Hm_pos; lia).
    rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb].
    apply region_free_intro. intros b sz Hin.
    pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hab.
    unfold iv_overlap in *. rewrite Hm_u. fold ua in Hab.
    pose proof (bv_unsigned_in_range 64 n) as Hn.
    destruct (Z_le_dec (bv_unsigned b + bv_unsigned sz) ua) as [Hend | Hend].
    - (* [comment removed for export] *)
      assert (Hc : page_round_up_Z (bv_unsigned b + bv_unsigned sz) <= m).
      { apply Hm_max.
        - right. apply in_map_iff. exists (b, sz). split; [reflexivity | exact Hin].
        - apply page_round_up_Z_le_aligned; [exact Hend | exact Halign]. }
      pose proof (page_round_up_Z_spec (bv_unsigned b + bv_unsigned sz)) as [Hr _].
      apply andb_false_iff. left. apply Z.ltb_ge. lia.
    - (* [comment removed for export] *)
      apply andb_false_iff in Hab.
      apply andb_false_iff. right. apply Z.ltb_ge.
      destruct Hab as [Hab | Hab]; [apply Z.ltb_ge in Hab; lia | apply Z.ltb_ge in Hab; lia]. }
  (* [comment removed for export] *)
  unfold vm_gap_available, vm_find_base.
  destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) as [c|] eqn:Hfind; [reflexivity |].
  exfalso.
  assert (Hin : In (Z_to_bv 64 m) (vm_base_candidates h)).
  { rewrite vm_base_candidates_values. apply in_map. exact Hm_in. }
  pose proof (List.find_none _ _ Hfind (Z_to_bv 64 m) Hin) as Hc. cbn beta in Hc.
  rewrite Hm_ok in Hc. discriminate Hc.
Qed.

(* [comment removed for export] *)
Theorem vm_gap_available_complete : forall h nZ a,
  (0 < nZ)%Z -> vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof. intros h nZ a _ H. exact (vm_gap_available_complete' h nZ a H). Qed.

(* [comment removed for export] *)
Lemma vm_base_ok_intro : forall h nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  vm_base_ok h nZ a = true.
Proof.
  intros h nZ a H1 H2 H3 H4. unfold vm_base_ok.
  rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_reserve_refusable_false : forall m nZ a,
  (0 < nZ)%Z -> vm_base_ok (m_vmmaps m) nZ a = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m nZ a Hn H. unfold mmap_reserve_refusable.
  rewrite (vm_gap_available_complete _ _ _ Hn H). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_grant_refusable_false : forall flags m nZ a,
  (0 < nZ)%Z -> vm_base_ok (m_vmmaps m) nZ a = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a Hn H Hb. unfold mmap_grant_refusable.
  rewrite Hb, (vm_gap_available_complete _ _ _ Hn H). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof. reflexivity. Qed.

Lemma mmap_reserve_errnos_nil : forall m nZ a,
  (0 < nZ)%Z -> vm_base_ok (m_vmmaps m) nZ a = true ->
  mmap_errnos_when (mmap_reserve_refusable m nZ) = [].
Proof. intros m nZ a Hn H. rewrite (mmap_reserve_refusable_false m nZ a Hn H). reflexivity. Qed.

Lemma mmap_grant_errnos_nil : forall flags m nZ a,
  (0 < nZ)%Z -> vm_base_ok (m_vmmaps m) nZ a = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_errnos_when (mmap_grant_refusable flags m nZ) = [].
Proof. intros flags m nZ a Hn H Hb. rewrite (mmap_grant_refusable_false flags m nZ a Hn H Hb). reflexivity. Qed.
