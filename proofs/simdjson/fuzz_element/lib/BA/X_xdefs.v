(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_Exit I_iodefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import X_aexdefs D_aex.
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
  mkGD 0x23700 0x7 0x20 0x1dd39 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23720 0xd 0x20 0x20999 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0x3 0x20 0x15002 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x3 0x20 0x13d5a 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23780 0x5 0x20 0x11619 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0x14 0x40 0x1735e 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237e0 0x4 0x20 0x21d7b 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23800 0x2 0x20 0x11620 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23820 0x2 0x20 0x1b66b 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23860 0x4 0x20 0x1fd94 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0x11 0x40 0x1dd3e 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238c0 0x1a 0x40 0x1ae2c 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23900 0x9 0x20 0x1d40d 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23920 0x9 0x20 0x11e69 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0x2 0x20 0x11e71 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23960 0x12 0x40 0x19008 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x7 0x20 0x1b673 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239c0 0x6 0x20 0x15009 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x6 0x20 0x14478 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a00 0x7 0x20 0x13d61 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x25 0x60 0x17d4c 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a80 0x20 0x40 0x10ba0 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ac0 0x12 0x40 0x19010 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x29 0x60 0x184e9 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b60 0x17 0x40 0x10ba8 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ba0 0x25 0x60 0x13d69 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c00 0x29 0x60 0x11628 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c60 0x8 0x20 0x12745 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c80 0xf 0x20 0x14480 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ca0 0x3 0x20 0x1fd9c 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23cc0 0x3 0x20 0x19018 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ce0 0x3 0x20 0x1d415 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d00 0x3 0x20 0x1ae34 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0x3 0x20 0x19020 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0x3 0x20 0x11630 0x23d60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24360 0x12 0x40 0x1dd39 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243a0 0x38 0x60 0x20999 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24400 0x43 0x80 0x22c9b 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24480 0x9d 0xc0 0x15002 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24540 0x51 0x80 0x13d5a 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245c0 0x2d 0x60 0x1ee42 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24620 0x49 0x80 0x19bd9 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246a0 0x49 0x80 0x1be59 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24720 0x49 0x80 0x11619 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247a0 0x2d 0x60 0x1735e 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24800 0x49 0x80 0x21d7b 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24880 0x29 0x60 0x11620 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248e0 0x1d 0x40 0x1b66b 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24920 0x15 0x40 0x21d83 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24960 0x60 0x80 0x1fd94 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x249e0 0x37 0x60 0x1dd3e 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a40 0xac 0xe0 0x1ae2c 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b20 0x43 0x80 0x1d40d 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ba0 0x61 0xa0 0x11e69 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24c40 0x5f 0x80 0x11e71 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24cc0 0x48 0x80 0x19008 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24d40 0x22 0x60 0x1b673 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24da0 0x33 0x60 0x15009 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24e00 0x33 0x60 0x14478 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24e60 0x6c 0xa0 0x13d61 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24f00 0x4d 0x80 0x17d4c 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24f80 0x61 0xa0 0x10ba0 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25020 0xcf 0x100 0x19010 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25120 0x84 0xc0 0x184e9 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x251e0 0xb1 0xe0 0x10ba8 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x252c0 0x3f 0x60 0x13d69 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25320 0x41 0x80 0x11628 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x253a0 0x4e 0x80 0x12745 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25420 0x100 0x140 0x22ca2 0x2cf00 0x0 0x0 0x6a6461;
  mkGD 0x25560 0xdd8 0x1140 0x1b6a8 0x2cf00 0x0 0x0 0x6a6462;
  mkGD 0x266a0 0xb8 0xe0 0x21d8b 0x2cf00 0x0 0x0 0x6a6463;
  mkGD 0x26780 0x28b0 0x32e0 0x17d54 0x2cf00 0x0 0x0 0x6a6464;
  mkGD 0x29a60 0x9 0x20 0x1fd9c 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x29a80 0x300 0x3c0 0x22cd7 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x29e40 0x25 0x60 0x11e79 0x2cf00 0x0 0x0 0x6a6467;
  mkGD 0x29ec0 0x30 0x60 0x17365 0x2cf00 0x0 0x0 0x6a646a;
  mkGD 0x29f60 0xc 0x20 0x19018 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x29f80 0x30 0x60 0x1d415 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2a020 0x20 0x40 0x1ae34 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2a060 0x100 0x140 0x209a0 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2a1a0 0x100 0x140 0x17404 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cba0 0xa0 0xc0 0x1fe1e 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cee0 0x1 0x20 0x1fe48 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x164760 0x210 0x2a0 0x1a31e 0x2cf00 0x0 0x0 0x6a6460;
  mkGD 0x164a00 0x40 0x60 0x1b6cb 0x2cf00 0x0 0x0 0x6a6465;
  mkGD 0x164a60 0x18 0x40 0x1274d 0x2cf00 0x0 0x0 0x6a6466;
  mkGD 0x164ac0 0x60 0x80 0x1fda4 0x2cf00 0x0 0x0 0x6a6468;
  mkGD 0x164b40 0x18 0x40 0x14488 0x2cf00 0x0 0x0 0x6a6469;
  mkGD 0x6a62c0 0x30 0x60 0x1590c 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a6320 0x8 0x20 0x15011 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a6340 0x8 0x20 0x1c8e4 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a6360 0x8 0x20 0x22626 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a6380 0x10 0x20 0x173a5 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a63a0 0x8 0x20 0x13d71 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a63c0 0x8 0x20 0x1277d 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a63e0 0x30 0x60 0x1fddd 0x2cf00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6a6440 0x8 0x20 0x1d41d 0x2cf00 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 97%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc6e0%Z (only parsing).  Notation XS1_HI := 0x7fffd9e0%Z (only parsing).
Notation XS2_LO := 0x800248ec%Z (only parsing).  Notation XS2_HI := 0x80027eb2%Z (only parsing).
Notation XS3_LO := 0x800ccc58%Z (only parsing).  Notation XS3_HI := 0x800ccc8c%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x6a6460 <=? o) && (o <? 0x6a646b)).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6a6460 \/ gd_odr g = 0x6a6461 \/ gd_odr g = 0x6a6462 \/ gd_odr g = 0x6a6463 \/ gd_odr g = 0x6a6464 \/ gd_odr g = 0x6a6465 \/ gd_odr g = 0x6a6466 \/ gd_odr g = 0x6a6467 \/ gd_odr g = 0x6a6468 \/ gd_odr g = 0x6a6469 \/ gd_odr g = 0x6a646a)
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
  [(0x6a7dc0, 0x6a7dc4); (0x6c80d8, 0x6c80dc); (0x6c80f8, 0x6c8100);
   (0x6c8670, 0x6c8678); (0x16eb20, 0x16eb28); (0x16ec10, 0x16ec18); (0x16ec18, 0x170588); (0x1705d0, 0x1705d1);
   (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b);
   (0x16e978, 0x16e988); (0x16e990, 0x16e9a0)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x6a7dc0 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells asegs m 0x6c80d8 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x6c80f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells asegs m 0x6c8670 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x16eb20 [C8 (Z_to_bv 64 0x16ea38)]
  /\ rw_cells asegs m 0x16ec10 [C8 (Z_to_bv 64 0x16eb28)]
  /\ stdin_file m /\ rw_cells asegs m 0x16ed00 [C8 (Z_to_bv 64 0x16ec18)]
  /\ gds_at m 0x16ed30 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0x170580 [C8 v])
  /\ rw_cells asegs m 0x1705d0 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells asegs m 0x6a6460 [C1 o1] /\ rw_cells asegs m 0x6a6461 [C1 o2] /\ rw_cells asegs m 0x6a6462 [C1 o3] /\ rw_cells asegs m 0x6a6463 [C1 o4] /\ rw_cells asegs m 0x6a6464 [C1 o5] /\ rw_cells asegs m 0x6a6465 [C1 o6] /\ rw_cells asegs m 0x6a6466 [C1 o7] /\ rw_cells asegs m 0x6a6467 [C1 o8] /\ rw_cells asegs m 0x6a6468 [C1 o9] /\ rw_cells asegs m 0x6a6469 [C1 o10] /\ rw_cells asegs m 0x6a646a [C1 o11])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x6a7dc0 0x6a7dc4); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6c80d8 0x6c80dc); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6c80f8 0x6c8100); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x6c8670 0x6c8678); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x16eb20 0x16eb28); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x16ec10 0x16ec18); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x16ec18 0x170588); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x16ec18 0x170588); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x16ec18 0x170588); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x16ec18 0x170588); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x1705d0 0x1705d1); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split; cycle 1.
  { destruct XD as [X1 X2]. split; [apply (R 0x16e978 (0x16e978 + 16)); [cbn; tauto| lia| cbn; lia| exact X1]
                                  | apply (R 0x16e990 (0x16e990 + 16)); [cbn; tauto| lia| cbn; lia| exact X2]]. }
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
  split; [apply (R 0x6a6460 0x6a6461); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  split; [apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC10]|].
  apply (R 0x6a6461 0x6a646b); [cbn; tauto| lia| cbn; lia| exact OC11].
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
  ro_cells asegs m 0x164170 [C8 (Z_to_bv 64 0xb9304); C8 (Z_to_bv 64 0x5a4e0)]
  /\ ro_cells asegs m 0x16b008 [C8 (Z_to_bv 64 0x164180); C8 (Z_to_bv 64 0x164170)]
  /\ ro_cells asegs m 0x16a200 [C8 (Z_to_bv 64 0x14b2b8); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells asegs m 0x16c048 [C8 d])
  /\ ro_cells asegs m 0x16af20 [C8 (Z_to_bv 64 0x16ed30); C8 (Z_to_bv 64 0x170570)]
  /\ ro_cells asegs m 0x16a210 [C8 (Z_to_bv 64 0x2036e0)]
  /\ ro_cells asegs m 0x16a220 [C8 (Z_to_bv 64 0x205768); C8 (Z_to_bv 64 0x171438); C8 (Z_to_bv 64 0x173c38);
                               C8 (Z_to_bv 64 0x174928); C8 (Z_to_bv 64 0x174930); C8 (Z_to_bv 64 0x174920);
                               C8 (Z_to_bv 64 0x16c250)]
  /\ ro_cells asegs m 0x171450 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x1714f0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x173c38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x174918 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x17349c [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x2057e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells asegs m 0x16c250 [C8 (Z_to_bv 64 0x15c928)]
  /\ ro_cells asegs m 0x205ae0 [C1 (Z_to_bv 8 0)]
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
