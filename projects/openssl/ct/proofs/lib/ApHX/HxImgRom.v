(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec Mem.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie AxFetchFast AxFetchFast2.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxImg.
From OSSVerify.Proofs.openssl.ct.lib.ApHX Require Import HxFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Img.
Variable segs : list Segment.

Lemma dimage_export_rom (rho : valuation) (m : word -> option byte) (lo size al : int) (wr : bool) (i : nat) (dl : int) (d : nat)
    (sg : Segment) (c : string) :
  region_export segs m rho (to_Z lo) (RG (Some lo) size al wr (DImage i dl) d IEmpty) ->
  nth_error segs i = Some sg -> seg_bytes sg = [c] -> seg_readable sg = true ->
  to_Z lo = Z.of_N (seg_base sg) + to_Z dl ->
  (forall a, to_Z lo <= a < to_Z lo + to_Z size -> find_segment segs a 1 = Some sg) ->
  2 * (to_Z dl + to_Z size) <= to_Z (PrimString.length c) -> to_Z dl + to_Z size < 2 ^ 59 ->
  img_valid c dl (Z.to_nat (to_Z size)) = true -> to_Z size mod 8 = 0 -> to_Z lo + to_Z size < 2 ^ 63 ->
  forall a, to_Z lo <= a < to_Z lo + to_Z size -> mrd segs m (wa a) = seg_rom segs (wa a).
Proof.
  intros HE Hn Hc Hrd Elo Hseg Hlen H59 Hval Hs8 Htop a Ha.
  pose proof (to_Z_bounded dl) as Bdl. pose proof (to_Z_bounded size) as Bsz. pose proof (to_Z_bounded lo) as Blo.
  set (k := a - to_Z lo). assert (Hk : 0 <= k < to_Z size) by lia.
  destruct (HE k ltac:(cbn [rg_size]; lia)) as (b & Eb & Kb & _). replace (to_Z lo + k) with a in Eb by lia. rewrite Eb.
  (* [comment removed for export] *)
  assert (Exk : to_Z (dl + of_Z k)%uint63 = to_Z dl + k).
  { rewrite add_spec, of_Z_spec. rewrite (Z.mod_small k) by (rewrite wB_eq; unfold two63; lia). apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
  destruct (img_valid_spec c (Z.to_nat (to_Z size)) dl (dl + of_Z k)%uint63 Hval ltac:(rewrite Z2Nat.id by lia; lia) ltac:(rewrite Exk, Z2Nat.id by lia; lia)) as [v Hv].
  assert (Hib : img_byte segs i (dl + of_Z k)%uint63 = Some v) by (unfold img_byte; rewrite Hn, Hc; exact Hv).
  destruct (img_byte_spec segs i sg c _ v Hn Hc Hib ltac:(rewrite Exk; lia) ltac:(rewrite Exk; lia)) as [Hsb Hv256].
  rewrite Exk in Hsb.
  assert (Hwa : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  assert (Hoff : Z.to_N (a - Z.of_N (seg_base sg)) = Z.to_N (to_Z dl + k)) by (f_equal; lia).
  assert (Hrom : seg_rom segs (wa a) = Some (Z_to_bv 8 (to_Z v))).
  { unfold seg_rom, memory_read. rewrite Hwa. change (Z.of_N 1) with 1. rewrite (Hseg a ltac:(lia)), Hrd.
    rewrite Hoff. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hsb. reflexivity. }
  rewrite Hrom. f_equal.
  (* [comment removed for export] *)
  unfold rg_kb, rd_cell in Kb. cbn [rg_d rg_cells rg_dflt] in Kb. rewrite iget_empty in Kb. cbn [dflt_cell] in Kb. unfold img_cell in Kb.
  pose proof (Z.div_mod k 8 ltac:(lia)) as Ek8. pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as Hk8.
  set (x0 := (dl + (of_Z (k / 8) << 3))%uint63) in Kb.
  assert (Ex0 : to_Z x0 = to_Z dl + 8 * (k / 8)).
  { unfold x0. rewrite add_spec, lsl_spec, of_Z_spec. change (2 ^ to_Z 3%uint63) with 8.
    assert (0 <= k / 8) by (apply Z.div_pos; lia). assert (k / 8 <= k) by (apply Z.div_le_upper_bound; lia).
    rewrite (Z.mod_small (k / 8)) by (rewrite wB_eq; unfold two63; lia). rewrite (Z.mod_small (k / 8 * 8)) by (rewrite wB_eq; unfold two63; lia).
    rewrite Z.mod_small by (rewrite wB_eq; unfold two63; lia). lia. }
  (* [comment removed for export] *)
  assert (HBj : forall j : Z, 0 <= j < 8 -> exists bj, img_byte segs i (x0 + of_Z j)%uint63 = Some bj /\ to_Z bj < 256).
  { intros j Hj.
    assert (Exj : to_Z (x0 + of_Z j)%uint63 = to_Z dl + 8 * (k / 8) + j).
    { rewrite add_spec, Ex0, of_Z_spec. rewrite (Z.mod_small j) by (rewrite wB_eq; unfold two63; lia). apply Z.mod_small. rewrite wB_eq. unfold two63. lia. }
    assert (Hin : to_Z dl <= to_Z (x0 + of_Z j)%uint63 < to_Z dl + Z.of_nat (Z.to_nat (to_Z size))).
    { rewrite Exj, Z2Nat.id by lia. Z.div_mod_to_equations. lia. }
    destruct (img_valid_spec c (Z.to_nat (to_Z size)) dl (x0 + of_Z j)%uint63 Hval ltac:(rewrite Z2Nat.id by lia; lia) Hin) as [bj Hbj].
    exists bj. split; [unfold img_byte; rewrite Hn, Hc; exact Hbj | exact (hbyte_lt _ _ _ Hbj)]. }
  destruct (HBj 0 ltac:(lia)) as (b0 & E0 & L0). change (of_Z 0) with 0%uint63 in E0. rewrite uadd_0_r in E0.
  destruct (HBj 1 ltac:(lia)) as (b1 & E1 & L1). destruct (HBj 2 ltac:(lia)) as (b2 & E2 & L2). destruct (HBj 3 ltac:(lia)) as (b3 & E3 & L3).
  destruct (HBj 4 ltac:(lia)) as (b4 & E4 & L4). destruct (HBj 5 ltac:(lia)) as (b5 & E5 & L5). destruct (HBj 6 ltac:(lia)) as (b6 & E6 & L6).
  destruct (HBj 7 ltac:(lia)) as (b7 & E7 & L7).
  change (of_Z 1) with 1%uint63 in E1. change (of_Z 2) with 2%uint63 in E2. change (of_Z 3) with 3%uint63 in E3. change (of_Z 4) with 4%uint63 in E4.
  change (of_Z 5) with 5%uint63 in E5. change (of_Z 6) with 6%uint63 in E6. change (of_Z 7) with 7%uint63 in E7.
  rewrite E0, E1, E2, E3, E4, E5, E6, E7 in Kb. fold (asm8 b0 b1 b2 b3 b4 b5 b6 b7) in Kb.
  cbn [cell_kb] in Kb. change (to_Z 255%uint63) with 255 in Kb. rewrite testbit_255 in Kb by lia. cbn [kb_ok] in Kb.
  rewrite wZ_asm8 in Kb by assumption.
  pose proof (to_Z_bounded b0). pose proof (to_Z_bounded b1). pose proof (to_Z_bounded b2). pose proof (to_Z_bounded b3).
  pose proof (to_Z_bounded b4). pose proof (to_Z_bounded b5). pose proof (to_Z_bounded b6). pose proof (to_Z_bounded b7).
  rewrite byteZ_sum8 in Kb by lia.
  (* [comment removed for export] *)
  assert (Exj : (dl + of_Z k)%uint63 = (x0 + of_Z (k mod 8))%uint63).
  { apply to_Z_inj. rewrite Exk. rewrite add_spec, Ex0, of_Z_spec. rewrite (Z.mod_small (k mod 8)) by (rewrite wB_eq; unfold two63; lia).
    rewrite Z.mod_small by (rewrite wB_eq; unfold two63; lia). lia. }
  rewrite Exj in Hib.
  apply bv_eq. rewrite Kb, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; pose proof (to_Z_bounded v); lia).
  assert (C : k mod 8 = 0 \/ k mod 8 = 1 \/ k mod 8 = 2 \/ k mod 8 = 3 \/ k mod 8 = 4 \/ k mod 8 = 5 \/ k mod 8 = 6 \/ k mod 8 = 7) by lia.
  destruct C as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; rewrite C in Hib |- *; simpl (nth _ _ _);
    [change (of_Z 0) with 0%uint63 in Hib; rewrite uadd_0_r in Hib | change (of_Z 1) with 1%uint63 in Hib | change (of_Z 2) with 2%uint63 in Hib
    | change (of_Z 3) with 3%uint63 in Hib | change (of_Z 4) with 4%uint63 in Hib | change (of_Z 5) with 5%uint63 in Hib
    | change (of_Z 6) with 6%uint63 in Hib | change (of_Z 7) with 7%uint63 in Hib ]; congruence.
Qed.

End Img.
