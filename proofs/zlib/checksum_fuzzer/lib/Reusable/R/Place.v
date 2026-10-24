(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable.Z Require Import Placement MmapComplete.
Import ListNotations.
Local Open Scope Z_scope.
Lemma mmap_errnos_when_ok : forall b, errnos_ok (mmap_errnos_when b) = true.
Proof. destruct b; reflexivity. Qed.
Lemma mprotect_errnos_when_ok : forall b, errnos_ok (mprotect_errnos_when b) = true.
Proof. destruct b; reflexivity. Qed.
Lemma vm_find_base_complete : forall h nZ g,
  vm_base_ok h nZ g = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ g Hok.
  destruct (vm_base_ok_sound h nZ g Hok) as (HgAl & HgPos & Hghi & Hgfree).
  set (maps := vm_reserved h ++ vm_maps h) in *.
  set (G := bv_unsigned g) in *.
  set (N := bv_unsigned (Z_to_bv 64 nZ)) in *.
  pose proof (bv_unsigned_in_range 64 g) as HGr. fold G in HGr.
  assert (Hmod : bv_modulus 64 = two_pow_64) by reflexivity.
  assert (Hfloor : page_size <= G).
  { unfold page_size in *.
    pose proof (Z.div_mod G 4096 ltac:(lia)) as Hdm. nia. }
  set (cZ := page_size
             :: map (fun iv : word * word =>
                       page_round_up_Z (bv_unsigned (fst iv) + bv_unsigned (snd iv))) maps).
  set (cs := List.filter (fun c => c <=? G) cZ).
  set (b0 := fold_left Z.max cs page_size).
  assert (Hcs : forall x, In x cs <-> In x cZ /\ (x <=? G) = true)
    by (intro x; unfold cs; exact (filter_In _ x _)).
  assert (Hlo : page_size <= b0) by (unfold b0; apply vm_base_fold_max_ge_seed).
  assert (Hhi : b0 <= G).
  { unfold b0. apply vm_base_fold_max_le; [exact Hfloor|]. intros x Hx.
    apply Hcs in Hx. apply Z.leb_le. exact (proj2 Hx). }
  assert (Hin : In b0 cZ).
  { destruct (vm_base_fold_max_in_or_seed cs page_size) as [E|E].
    - fold b0 in E. rewrite E. left. reflexivity.
    - apply Hcs in E. exact (proj1 E). }
  assert (Hb0W : bv_unsigned (Z_to_bv 64 b0) = b0).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus in *.
    unfold page_size in Hlo. lia. }
  assert (Hb0Al : b0 mod page_size = 0).
  { destruct Hin as [E|E]; [rewrite <- E; reflexivity|].
    apply in_map_iff in E. destruct E as (iv & E & _). rewrite <- E. apply vm_base_round_aligned. }
  assert (Hb0free : region_free maps (Z_to_bv 64 b0) (Z_to_bv 64 nZ) = true).
  { apply region_free_intro. intros b s Hbs.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hbs) as Hno.
    unfold iv_overlap in Hno |- *. fold G N in Hno. fold N. rewrite Hb0W.
    destruct (Z.le_gt_cases (bv_unsigned b + bv_unsigned s) G) as [Hend|Hend].
    -
      assert (Hc : In (page_round_up_Z (bv_unsigned b + bv_unsigned s)) cs).
      { apply Hcs. split.
        - right. apply in_map_iff. exists (b, s). split; [reflexivity | exact Hbs].
        - apply Z.leb_le. apply vm_base_round_le; [exact Hend | exact HgAl]. }
      pose proof (vm_base_fold_max_ge_in cs page_size _ Hc) as Hge. fold b0 in Hge.
      pose proof (vm_base_round_ge (bv_unsigned b + bv_unsigned s)) as Hr.
      apply andb_false_iff. left. apply Z.ltb_ge. lia.
    -
      apply andb_false_iff in Hno. destruct Hno as [Hno|Hno]; apply Z.ltb_ge in Hno; [lia|].
      apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  assert (Hc : In (Z_to_bv 64 b0) (vm_base_candidates h)).
  { unfold vm_base_candidates. fold maps. destruct Hin as [E|E].
    - left. rewrite E. reflexivity.
    - right. apply in_map_iff in E. destruct E as (iv & E & Hiv).
      apply in_map_iff. exists iv. split; [rewrite <- E; reflexivity | exact Hiv]. }
  assert (Hb0ok : vm_base_ok h nZ (Z_to_bv 64 b0) = true).
  { unfold vm_base_ok. fold maps. rewrite Hb0W, Hb0free.
    rewrite (proj2 (Z.eqb_eq _ _) Hb0Al).
    assert (Hpos : 0 < b0) by (unfold page_size in Hlo; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hpos).
    assert (Htop : b0 + nZ <= alloc_top h) by lia.
    rewrite (proj2 (Z.leb_le _ _) Htop). reflexivity. }
  destruct (vm_base_find_of_In _ _ _ Hc Hb0ok) as [a Ha].
  unfold vm_gap_available, vm_find_base. rewrite Ha. reflexivity.
Qed.