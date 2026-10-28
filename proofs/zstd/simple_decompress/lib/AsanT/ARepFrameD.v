(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ACanary AModelFacts ARep ALayout AHeapP ARepKit ARepFrame AFrameD.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section FramesD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.

Ltac xcell := eapply cells_frameD; [eassumption | exact MU | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)

Lemma arep_rt_frameD : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) (rt_hulls L) -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma arelro_frameD : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)

Lemma ashadow_avail_frameD : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frameD; [exact Z1 | exact MU | exact D1] | eapply azero_frameD; [exact Z2 | exact MU | exact D2]].
Qed.

Lemma arep_rt2_frameD : arep_rt2 m -> disjoint_from W 0x16192c 1 -> disjoint_from W 0x1618b8 8 -> disjoint_from W 0xc9160 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
Lemma arep_rt3_frameD : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
Lemma ainstance_frameD : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma aregion_cells_frameD : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  destruct RC as (A1 & A2 & A3 & A4 & A5).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frameD; [exact A3 | exact MU | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frameD; [exact A5 | exact MU | intros _; exact De].
Qed.

(* [comment removed for export] *)
Lemma afreearray_frameD : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  destruct FA as (A1 & A2 & A3).
  split; [| split].
  - eapply u32arr_frameD; [exact A1 | exact MU |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A2 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact A3 | exact MU | intros _; exact DS].
Qed.

(* [comment removed for export] *)
Lemma acache_cells_frameD : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frameD; [exact A1 | exact MU |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frameD; [exact A2 | exact MU |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)

Lemma aslot_busy_frameD : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frameD; [exact LC | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frameD; [exact J | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frameD; [exact HDR | exact MU |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frameD; [exact UJ | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frameD; [exact SB | exact MU | intros _; exact D].
Qed.

(* [comment removed for export] *)
Lemma aslots_updateD : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as (EB & D & WFB). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + destruct (WFB b eq_refl) as (C1' & K1 & FIT1).
      eapply aslot_busy_frameD; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frameD; [exact SL | exact MU | intros _; exact D].
  - eapply junk_frameD; [exact UND | exact MU | exact DU].
Qed.

(* [comment removed for export] *)
Lemma aslot_shadow_updateD : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells bsegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frameD; [exact SL | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frameD; [exact UND | exact MU | exact DU].
Qed.
End FramesD.
End CANSEC1.
