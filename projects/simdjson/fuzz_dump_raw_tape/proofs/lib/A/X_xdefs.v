(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx FX_Exit I_iodefs X_aexdefs D_aex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record gdesc := mkGD { gd_beg : Z; gd_size : Z; gd_srz : Z; gd_name : Z; gd_mod : Z; gd_dyn : Z; gd_loc : Z; gd_odr : Z }.

Definition gd_cells (g : gdesc) : list cell :=
  [C8 (Z_to_bv 64 (gd_beg g)); C8 (Z_to_bv 64 (gd_size g)); C8 (Z_to_bv 64 (gd_srz g)); C8 (Z_to_bv 64 (gd_name g));
   C8 (Z_to_bv 64 (gd_mod g)); C8 (Z_to_bv 64 (gd_dyn g)); C8 (Z_to_bv 64 (gd_loc g)); C8 (Z_to_bv 64 (gd_odr g))].

Fixpoint gds_at (m : mem) (a : Z) (gs : list gdesc) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => ro_cells asegs m a (gd_cells g) /\ gds_at m (a + 64) gs'
  end.

Definition ODR_NONE : Z := 0xffffffffffffffff.

Definition asan_gds : list gdesc := [
  mkGD 0x23500 0xd 0x20 0x2088c 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23520 0x3 0x20 0x14f83 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23540 0x3 0x20 0x13cdb 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23560 0x4 0x20 0x11611 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235a0 0x4 0x20 0x172df 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235c0 0x11 0x40 0x21c6e 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23600 0x1a 0x40 0x11618 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23640 0x9 0x20 0x1b59f 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23660 0x9 0x20 0x21c76 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23680 0x2 0x20 0x1fc87 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236a0 0x12 0x40 0x1dc66 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236e0 0x7 0x20 0x1ad60 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0x6 0x20 0x1d33a 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23720 0x6 0x20 0x11e59 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0x7 0x20 0x11e61 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x25 0x60 0x18f6a 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237c0 0x20 0x40 0x1b5a7 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23800 0x12 0x40 0x14f8a 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23840 0x29 0x60 0x143f9 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0x17 0x40 0x13ce2 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x25 0x60 0x17ccd 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0x29 0x60 0x10b98 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x8 0x20 0x18f72 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239c0 0xf 0x20 0x1846a 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x3 0x20 0x10ba0 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a00 0x3 0x20 0x13cea 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x3 0x20 0x11620 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a40 0x3 0x20 0x126eb 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a60 0x3 0x20 0x14401 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a80 0x3 0x20 0x1fc8f 0x23aa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x240a0 0x100 0x140 0x22b45 0x2bb80 0x0 0x0 0x69e660;
  mkGD 0x241e0 0xdd8 0x1140 0x1b5dc 0x2bb80 0x0 0x0 0x69e661;
  mkGD 0x25320 0xb8 0xe0 0x21c7e 0x2bb80 0x0 0x0 0x69e662;
  mkGD 0x25400 0x28b0 0x32e0 0x17cd5 0x2bb80 0x0 0x0 0x69e663;
  mkGD 0x286e0 0x9 0x20 0x1fc8f 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28700 0x300 0x3c0 0x22b7a 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28ac0 0x25 0x60 0x11e69 0x2bb80 0x0 0x0 0x69e666;
  mkGD 0x28b40 0x30 0x60 0x172e6 0x2bb80 0x0 0x0 0x69e669;
  mkGD 0x28be0 0xc 0x20 0x18ffe 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28c00 0x30 0x60 0x1d342 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28ca0 0x20 0x40 0x1ad68 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28ce0 0x100 0x140 0x20893 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28e20 0x100 0x140 0x17385 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b820 0xa0 0xc0 0x1fd11 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2bb60 0x1 0x20 0x1fd3b 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x15d5e0 0x40 0x60 0x1b5ff 0x2bb80 0x0 0x0 0x69e664;
  mkGD 0x15d640 0x18 0x40 0x126f3 0x2bb80 0x0 0x0 0x69e665;
  mkGD 0x15d6a0 0x60 0x80 0x1fc97 0x2bb80 0x0 0x0 0x69e667;
  mkGD 0x15d720 0x18 0x40 0x14409 0x2bb80 0x0 0x0 0x69e668;
  mkGD 0x69e4c0 0x30 0x60 0x1588d 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e520 0x8 0x20 0x14f92 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e540 0x8 0x20 0x1c811 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e560 0x8 0x20 0x22519 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e580 0x10 0x20 0x17326 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e5a0 0x8 0x20 0x13cf2 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e5c0 0x8 0x20 0x12723 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e5e0 0x30 0x60 0x1fcd0 0x2bb80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x69e640 0x8 0x20 0x1d34a 0x2bb80 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 58%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc6a0%Z (only parsing).  Notation XS1_HI := 0x7fffd770%Z (only parsing).
Notation XS2_LO := 0x80023abc%Z (only parsing).  Notation XS2_HI := 0x800250ee%Z (only parsing).
Notation XS3_LO := 0x800cbc98%Z (only parsing).  Notation XS3_HI := 0x800cbccc%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x69e660 <=? o) && (o <? 0x69e66b)).

Definition gd_okb (g : gdesc) : bool :=
  (0 <=? gd_beg g) && (gd_beg g mod 8 =? 0) && (8 <=? gd_srz g) && (gd_srz g mod 8 =? 0)
  && (gd_beg g + gd_srz g <=? SEGTOP_A) && (gd_srz g / 8 <? 0x10000)
  && in_scratchb (SHB + gd_beg g / 8) (gd_srz g / 8) && odr_okb (gd_odr g)
  && (0 <=? gd_size g) && (gd_size g <? 2^64) && (0 <=? gd_name g) && (gd_name g <? 2^64) && (0 <=? gd_mod g) && (gd_mod g <? 2^64)
  && (0 <=? gd_dyn g) && (gd_dyn g <? 2^64) && (0 <=? gd_loc g) && (gd_loc g <? 2^64).

Lemma asan_gds_ok : Forall (fun g => gd_okb g = true) asan_gds.
Proof.
  assert (H : forallb gd_okb asan_gds = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Forall_forall. exact H.
Qed.

Lemma gd_okb_spec : forall g, gd_okb g = true ->
  0 <= gd_beg g /\ gd_beg g mod 8 = 0 /\ 8 <= gd_srz g /\ gd_srz g mod 8 = 0 /\ gd_beg g + gd_srz g <= SEGTOP_A
  /\ gd_srz g / 8 < 0x10000
  /\ ((XS1_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS1_HI)
      \/ (XS2_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS2_HI)
      \/ (XS3_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS3_HI))
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x69e660 \/ gd_odr g = 0x69e661 \/ gd_odr g = 0x69e662 \/ gd_odr g = 0x69e663 \/ gd_odr g = 0x69e664 \/ gd_odr g = 0x69e665 \/ gd_odr g = 0x69e666 \/ gd_odr g = 0x69e667 \/ gd_odr g = 0x69e668 \/ gd_odr g = 0x69e669 \/ gd_odr g = 0x69e66a)
  /\ 0 <= gd_size g < 2^64 /\ 0 <= gd_name g < 2^64 /\ 0 <= gd_mod g < 2^64 /\ 0 <= gd_dyn g < 2^64 /\ 0 <= gd_loc g < 2^64.
Proof.
  intros g H. unfold gd_okb, in_scratchb, odr_okb in H.
  repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
                       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  repeat split; try assumption; lia.
Qed.

Definition XENV_CORE_FPA : list (Z * Z) :=
  [(0x69ffc0, 0x69ffc4); (0x6c02d8, 0x6c02dc); (0x6c02f8, 0x6c0300);
   (0x6c0870, 0x6c0878); (0x1676e0, 0x1676e8); (0x1677d0, 0x1677d8); (0x1677d8, 0x168788); (0x1687d0, 0x1687d1);
   (0x69e660, 0x69e661); (0x69e661, 0x69e66b);
   (0x167540, 0x167548); (0x167550, 0x167560)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x69ffc0 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells asegs m 0x6c02d8 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x6c02f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells asegs m 0x6c0870 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x1676e0 [C8 (Z_to_bv 64 0x1675f8)]
  /\ rw_cells asegs m 0x1677d0 [C8 (Z_to_bv 64 0x1676e8)]
  /\ stdin_file m /\ rw_cells asegs m 0x1678c0 [C8 (Z_to_bv 64 0x1677d8)]
  /\ gds_at m 0x1678f0 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0x168780 [C8 v])
  /\ rw_cells asegs m 0x1687d0 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells asegs m 0x69e660 [C1 o1] /\ rw_cells asegs m 0x69e661 [C1 o2] /\ rw_cells asegs m 0x69e662 [C1 o3] /\ rw_cells asegs m 0x69e663 [C1 o4] /\ rw_cells asegs m 0x69e664 [C1 o5] /\ rw_cells asegs m 0x69e665 [C1 o6] /\ rw_cells asegs m 0x69e666 [C1 o7] /\ rw_cells asegs m 0x69e667 [C1 o8] /\ rw_cells asegs m 0x69e668 [C1 o9] /\ rw_cells asegs m 0x69e669 [C1 o10] /\ rw_cells asegs m 0x69e66a [C1 o11])
  /\ el_xdataA m.

Definition XENVA (m : mem) : Prop := XENV_coreA m /\ aexA m.

Lemma in_XENV_CORE_FPA : forall lo hi x, In (lo, hi) XENV_CORE_FPA -> lo <= x < hi -> in_ranges XENV_CORE_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma in_ranges_app_l : forall l1 l2 x, in_ranges l1 x -> in_ranges (l1 ++ l2) x.
Proof. intros l1 l2 x (lo & hi & H1 & H2). exists lo, hi. split; [apply in_app_iff; left; exact H1| exact H2]. Qed.
Lemma in_ranges_app_r : forall l1 l2 x, in_ranges l2 x -> in_ranges (l1 ++ l2) x.
Proof. intros l1 l2 x (lo & hi & H1 & H2). exists lo, hi. split; [apply in_app_iff; right; exact H1| exact H2]. Qed.
Lemma in_ranges_app_inv : forall l1 l2 x, in_ranges (l1 ++ l2) x -> in_ranges l1 x \/ in_ranges l2 x.
Proof.
  intros l1 l2 x (lo & hi & H1 & H2). apply in_app_iff in H1. destruct H1 as [H1|H1]; [left| right]; exists lo, hi; (split; [exact H1| exact H2]).
Qed.

Lemma gds_at_agree : forall gs m m' a, gds_at m a gs ->
  agree_on (fun x => a <= x < a + 64 * Z.of_nat (length gs)) m m' -> gds_at m' a gs.
Proof.
  induction gs as [|g gs IH]; intros m m' a H AG; [exact I|]. destruct H as [H1 H2]. split.
  - apply (ro_cells_agree asegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
  - apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Lemma XENV_coreA_loc : fp_local XENV_CORE_FPA XENV_coreA.
Proof.
  intros m m' (TID & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & XD) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_CORE_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_CORE_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x69ffc0 0x69ffc4); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6c02d8 0x6c02dc); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6c02f8 0x6c0300); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x6c0870 0x6c0878); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x1676e0 0x1676e8); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x1677d0 0x1677d8); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x1677d8 0x168788); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x1677d8 0x168788); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x1677d8 0x168788); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x1677d8 0x168788); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x1687d0 0x1687d1); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split; cycle 1.
  { destruct XD as [X1 X2]. split; [apply (R 0x167540 (0x167540 + 8)); [cbn; tauto| lia| cbn; lia| exact X1]
                                  | apply (R 0x167550 (0x167550 + 16)); [cbn; tauto| lia| cbn; lia| exact X2]]. }
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
  split; [apply (R 0x69e660 0x69e661); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  split; [apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC10]|].
  apply (R 0x69e661 0x69e66b); [cbn; tauto| lia| cbn; lia| exact OC11].
Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof.
  intros m m' [CORE AEXP] AG. split.
  - apply (XENV_coreA_loc m m' CORE). intros a Ha. apply AG. apply in_ranges_app_l. exact Ha.
  - apply (aexA_agree m m'); [| exact AEXP]. intros a Ha. apply AG. apply in_ranges_app_r. exact Ha.
Qed.

Lemma aex_core_sep : forall x, in_ranges AEX_FPA x -> ~ in_ranges XENV_CORE_FPA x.
Proof.
  intros x Hx (lo & hi & Hin & Hlh). apply in_AEX_FPA_iff in Hx. unfold AEX, AEX_A0, TR_LATCH, AEF_INCB in Hx. cbn in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Definition XENV_lawsA : xenv_laws XENVA XENV_FPA.
Proof.
  refine {| xl_loc := XENV_locA; xl_core := XENV_coreA; xl_core_fp := XENV_CORE_FPA; xl_split := _;
            xl_core_loc := XENV_coreA_loc; xl_core_sep := aex_core_sep; xl_aex_in := _; xl_core_in := _; xl_libc := _; xl_xdata := _ |}.
  - intros m. unfold XENVA. tauto.
  - intros x Hx. apply in_ranges_app_r. exact Hx.
  - intros x Hx. apply in_ranges_app_l. exact Hx.
  - intros m (TID & EXL & LIBC & _). exact LIBC.
  - intros m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XD). exact XD.
Defined.

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). unfold XENV_FPA, XENV_CORE_FPA, AEX_FPA, AEX, AEX_A0, TR_LATCH, AEF_INCB in Hin. cbn in Hin.
  split; [| split; [| split]].
  - apply client_static_intro.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold IO_FPA. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
  - unfold LIB_FP. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

Definition xit_rt (m : mem) : Prop :=
  ro_cells asegs m 0x15d030 [C8 (Z_to_bv 64 0xb24d0); C8 (Z_to_bv 64 0x586d4)]
  /\ ro_cells asegs m 0x163bd8 [C8 (Z_to_bv 64 0x15d040); C8 (Z_to_bv 64 0x15d030)]
  /\ ro_cells asegs m 0x162de0 [C8 (Z_to_bv 64 0x14423c); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells asegs m 0x164c18 [C8 d])
  /\ ro_cells asegs m 0x163ad8 [C8 (Z_to_bv 64 0x1678f0); C8 (Z_to_bv 64 0x168770)]
  /\ ro_cells asegs m 0x162df0 [C8 (Z_to_bv 64 0x1fb8e0)]
  /\ ro_cells asegs m 0x162e00 [C8 (Z_to_bv 64 0x1fd968); C8 (Z_to_bv 64 0x169638); C8 (Z_to_bv 64 0x16be38);
                               C8 (Z_to_bv 64 0x16cb28); C8 (Z_to_bv 64 0x16cb30); C8 (Z_to_bv 64 0x16cb20);
                               C8 (Z_to_bv 64 0x164e18)]
  /\ ro_cells asegs m 0x169650 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x1696f0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x16be38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x16cb18 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x16b69c [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x1fd9e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells asegs m 0x164e18 [C8 (Z_to_bv 64 0x1558ac)]
  /\ ro_cells asegs m 0x1fdce0 [C1 (Z_to_bv 8 0)]
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
