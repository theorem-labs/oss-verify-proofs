(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  mkGD 0x22da0 0x11 0x40 0x20250 0x22de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e20 0x20 0x40 0x1d687 0x22f00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e60 0xa 0x20 0x1c25f 0x22f00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e80 0xe 0x20 0x20250 0x22f00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ea0 0x12 0x40 0x1e7b8 0x22f00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ee0 0xe 0x20 0x10af5 0x22f00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f40 0x16 0x40 0x1d687 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f80 0xa 0x20 0x11d4c 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fa0 0x18 0x40 0x20250 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fe0 0x18 0x40 0x22421 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23020 0x10 0x20 0x13b80 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0x25 0x60 0x1e7b8 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0xb 0x20 0x1a858 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0xf 0x20 0x1b7fd 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230e0 0xf 0x20 0x22428 0x23100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23140 0xe 0x20 0x1d687 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0xa 0x20 0x19d9e 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23180 0x10 0x20 0x1cd41 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231a0 0x1d 0x40 0x20250 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231e0 0x11 0x40 0x22421 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23220 0x12 0x40 0x20269 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23260 0x18 0x40 0x160ee 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232a0 0x27 0x60 0x1e7b8 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23300 0x10 0x20 0x20284 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23320 0x12 0x40 0x19683 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23360 0x13 0x40 0x1b815 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233a0 0x2f 0x60 0x114fc 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23400 0xc 0x20 0x16ff0 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23420 0x18 0x40 0x2161b 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23460 0x30 0x60 0x11503 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234c0 0x34 0x60 0x1b091 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23520 0x35 0x60 0x21623 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23580 0x25 0x60 0x1f75f 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0xb 0x20 0x19db1 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23600 0x8 0x20 0x14d5c 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23620 0x1c 0x40 0x1d68c 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23660 0x13 0x40 0x16ff7 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236a0 0x11 0x40 0x1a86c 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236e0 0x10 0x20 0x19dc5 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0x1f 0x40 0x1cd5a 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0xf 0x20 0x11d5f 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0xf 0x20 0x11d67 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23780 0x10 0x20 0x13bb0 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0xc 0x20 0x2029d 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237c0 0xc 0x20 0x22440 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237e0 0x13 0x40 0x178cc 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23820 0xd 0x20 0x1efe4 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23840 0xd 0x20 0x1f767 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23860 0xf 0x20 0x10b0c 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0xc 0x20 0x1b099 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0xc 0x20 0x1150b 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238c0 0xf 0x20 0x18b39 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x11 0x40 0x11d6f 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23920 0xa 0x20 0x125cc 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0x11 0x40 0x18087 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23980 0xa 0x20 0x1effa 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0xf 0x20 0x1e0c4 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239c0 0xf 0x20 0x14d6d 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x16 0x40 0x11520 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0xb 0x20 0x1b0ae 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a80 0x10 0x20 0x20250 0x23bc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23aa0 0xe 0x20 0x1cd62 0x23bc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ac0 0x1b 0x40 0x178cc 0x23bc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x84 0xc0 0x18b6d 0x23bc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c00 0x12 0x40 0x13b80 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c40 0xc 0x20 0x16801 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c60 0xd 0x20 0x1e7b8 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c80 0x25 0x60 0x19683 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ce0 0xf 0x20 0x1b0c2 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d00 0x13 0x40 0x1b815 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0xf 0x20 0x202b2 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d60 0x11 0x40 0x114fc 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23da0 0x17 0x40 0x16ff0 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23de0 0x25 0x60 0x2161b 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e40 0x2f 0x60 0x11503 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ea0 0x2e 0x60 0x1b091 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f00 0x1f 0x40 0x21623 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f40 0x33 0x60 0x1f75f 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23fa0 0x38 0x60 0x1d68c 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24000 0x3a 0x60 0x1a86c 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24060 0x4d 0x80 0x1cd5a 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x240e0 0x10 0x20 0x178d4 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24100 0x16 0x40 0x11d5f 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24140 0xf 0x20 0x1e7bf 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24160 0x13 0x40 0x11d67 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241a0 0x10 0x20 0x1d694 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241c0 0x10 0x20 0x1a874 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241e0 0x11 0x40 0x17013 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24220 0xf 0x20 0x202ca 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24240 0x1d 0x40 0x14d85 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24280 0xb 0x20 0x11528 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x242a0 0xe 0x20 0x18b75 0x242c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24300 0x11 0x40 0x1d687 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24340 0x16 0x40 0x1e7d7 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24380 0x14 0x40 0x1e0dc 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243c0 0x25 0x60 0x1a88d 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24460 0x13 0x40 0x21e3d 0x244e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244a0 0x8 0x20 0x20c72 0x244e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244c0 0x10 0x20 0x1cd79 0x244e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24520 0x11 0x40 0x1d687 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24560 0x11 0x40 0x14dd8 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245a0 0xc 0x20 0x20250 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245c0 0x17 0x40 0x22421 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24600 0x20 0x40 0x14df2 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24640 0x18 0x40 0x13b80 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24680 0x17 0x40 0x2161b 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246c0 0x17 0x40 0x202d2 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24700 0x27 0x60 0x1a86c 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247a0 0xd 0x20 0x22421 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247c0 0x11 0x40 0x114fc 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24800 0x19 0x40 0x178ed 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24840 0x23 0x60 0x1cd5a 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248a0 0x12 0x40 0x11d5f 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248e0 0xe 0x20 0x11d67 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24900 0xf 0x20 0x18b7d 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24920 0xf 0x20 0x1b10d 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24940 0x10 0x20 0x14df9 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24960 0x16 0x40 0x14265 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x249a0 0x54 0x80 0x13bb0 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a20 0xe 0x20 0x178cc 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a40 0x12 0x40 0x10b0c 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a80 0x19 0x40 0x18b39 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd1840 0x4 0x20 0x18068 0x22de0 0x0 0x0 0x6098c0;
  mkGD 0xd1860 0x8 0x20 0x18078 0x22de0 0x0 0x0 0x6098c1;
  mkGD 0xd1880 0x8 0x20 0x18b27 0x23a40 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd18a0 0x8 0x20 0x20257 0x23a40 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 126%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc5b4%Z (only parsing).  Notation XS1_HI := 0x7fffc958%Z (only parsing).
Notation XS2_LO := 0x80012308%Z (only parsing).  Notation XS2_HI := 0x80012770%Z (only parsing).
Notation XS3_LO := 0x80012770%Z (only parsing).  Notation XS3_HI := 0x80012770%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x6098c2) || (o =? 0x6098c0) || (o =? 0x6098c1).

(* [comment removed for export] *)
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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6098c2 \/ gd_odr g = 0x6098c0 \/ gd_odr g = 0x6098c1)
  /\ 0 <= gd_size g < 2^64 /\ 0 <= gd_name g < 2^64 /\ 0 <= gd_mod g < 2^64 /\ 0 <= gd_dyn g < 2^64 /\ 0 <= gd_loc g < 2^64.
Proof.
  intros g H. unfold gd_okb, in_scratchb, odr_okb in H.
  repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
                       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition XENV_FPA : list (Z * Z) :=
  [(0x60a360, 0x60a364); (0x62a458, 0x62a480); (0x62a578, 0x62a580); (0x62a678, 0x62a67c); (0x62a698, 0x62a6a0);
   (0x62ab00, 0x62ab08); (0xd19f0, 0xd19f8); (0xd1ae0, 0xd1ae8); (0xd1ae8, 0xd3b88); (0xd3bd0, 0xd3bd1);
   (0x6098c2, 0x6098c3); (0x6098c0, 0x6098c2); (0x62a480, 0x62a488); (0x62a580, 0x62a588); (0x609890, 0x609891)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x60a360 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x62a578 [C8 (Z_to_bv 64 0x7cb0c)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x62a678 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x62a698 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x62ab00 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd19f0 [C8 (Z_to_bv 64 0xd1908)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd1ae0 [C8 (Z_to_bv 64 0xd19f8)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xd1bd0 [C8 (Z_to_bv 64 0xd1ae8)]                           (* [comment removed for export] *)
  /\ gds_at m 0xd1c00 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xd3b80 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd3bd0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x6098c2 [C1 o1] /\ rw_cells asegs m 0x6098c0 [C1 o2]
                              /\ rw_cells asegs m 0x6098c1 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x62a458 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x62a470 0 0xb9a70))
  /\ (if ph then rw_cells asegs m 0x62a480 [C8 (Z_to_bv 64 0xb9a70)] /\ rw_cells asegs m 0x62a580 [C8 (Z_to_bv 64 0x8d4d4)]
      else (exists j1 : word, rw_cells asegs m 0x62a480 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x62a580 [C8 j2])
           /\ rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 0)]).

Definition XENVA_ph (ph : bool) (m : mem) : Prop := XENVC m /\ atxA ph m.
Definition XENVA : mem -> Prop := XENVA_ph false.
Definition XENVA1 : mem -> Prop := XENVA_ph true.
Definition XENVA1x (m : mem) : Prop := XENVA1 m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].

Lemma XENVA1x_of : forall m, XENVA1 m -> rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENVA1x m.
Proof. intros m H1 H2. exact (conj H1 H2). Qed.

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma gds_at_agree : forall gs m m' a, gds_at m a gs ->
  agree_on (fun x => a <= x < a + 64 * Z.of_nat (length gs)) m m' -> gds_at m' a gs.
Proof.
  induction gs as [|g gs IH]; intros m m' a H AG; [exact I|]. destruct H as [H1 H2]. split.
  - apply (ro_cells_agree asegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
  - apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Local Ltac DJ := intros xd Hxd Hrd; apply in_REG_CELLS in Hrd; lia.

Lemma XENVC_loc' : forall m m', XENVC m ->
  (forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) -> XENVC m'.
Proof.
  intros m m' (TID & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> (forall x, lo <= x < hi -> ~ in_ranges REG_CELLS x) -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin HD H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. pose proof (rw_cells_bound asegs m _ _ H). apply AG; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| apply HD; lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x60a360 0x60a364); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x62a578 0x62a580); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x62a678 0x62a67c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x62a698 0x62a6a0); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x62ab00 0x62ab08); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xd19f0 0xd19f8); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xd1ae0 0xd1ae8); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xd1ae8 0xd3b88); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xd1ae8 0xd3b88); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xd1ae8 0xd3b88); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xd1ae8 0xd3b88); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xd3bd0 0xd3bd1); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x6098c2 0x6098c3); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x6098c0 0x6098c2); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x6098c0 0x6098c2); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
Qed.


Lemma XENVC_loc : fp_local XENV_FPA XENVC.
Proof. intros m m' H AG. apply (XENVC_loc' m m' H). intros a Ha _. exact (AG a Ha). Qed.

Lemma atxA_loc : forall ph, fp_local XENV_FPA (atxA ph).
Proof.
  intros ph m m' ((p1 & p2 & ATX) & PH) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
  split; [exists p1, p2; apply (R 0x62a458 0x62a480); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x62a480 0x62a488); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x62a580 0x62a588); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x62a480 0x62a488); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x62a580 0x62a588); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x609890 0x609891); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
Qed.

Lemma XENV_locA_ph : forall ph, fp_local XENV_FPA (XENVA_ph ph).
Proof. intros ph m m' [HC HA] AG. split; [exact (XENVC_loc m m' HC AG)| exact (atxA_loc ph m m' HA AG)]. Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof. exact (XENV_locA_ph false). Qed.

Lemma XENV_locA1 : fp_local XENV_FPA XENVA1.
Proof. exact (XENV_locA_ph true). Qed.

Lemma REG_fpA : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FPA x.
Proof.
  intros x Hx. apply in_REG_CELLS in Hx.
  destruct Hx as [H|[H|[H|H]]];
    [apply (in_XENV_FPA 0x609890 0x609891)| apply (in_XENV_FPA 0x62a458 0x62a480)| apply (in_XENV_FPA 0x62a480 0x62a488)| apply (in_XENV_FPA 0x62a580 0x62a588)];
    first [cbn; tauto| lia].
Qed.

Lemma XENVA_reg_out : forall m, XENVA m -> reg_pre m.
Proof.
  intros m (HC & (p1 & p2 & ATX) & (j1 & PF) & (j2 & PA) & PL).
  destruct HC as (TID & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & _).
  exists p1, p2, cdt, thr, sec, tm1, j1, j2. cbn [ph_slot] in ATX.
  split; [exact ATX|]. split; [exact PF|]. split; [exact PA|]. split; [exact LIBC| exact PL].
Qed.

Lemma XENVA_reg_in : forall m m', XENVA m ->
  (forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
  reg_post m' -> XENVA1 m'.
Proof.
  intros m m' [HC _] AG (p1 & p2 & ATX & PF & PA & PL). split.
  - exact (XENVC_loc' m m' HC AG).
  - split; [exists p1, p2; exact ATX|]. cbn. split; [exact PF| exact PA].
Qed.

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn in Hin.
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
  ro_cells asegs m 0xc9de0 [C8 (Z_to_bv 64 0x8db74); C8 (Z_to_bv 64 0x3bf48)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcdf28 [C8 (Z_to_bv 64 0xc9df0); C8 (Z_to_bv 64 0xc9de0)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcd1f0 [C8 (Z_to_bv 64 0xb99a8); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xcef80 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcdea0 [C8 (Z_to_bv 64 0xd1c00); C8 (Z_to_bv 64 0xd3b80)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcd200 [C8 (Z_to_bv 64 0x166ce0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcd210 [C8 (Z_to_bv 64 0x168d68); C8 (Z_to_bv 64 0xd4a38); C8 (Z_to_bv 64 0xd7238);
                               C8 (Z_to_bv 64 0xd7f28); C8 (Z_to_bv 64 0xd7f30); C8 (Z_to_bv 64 0xd7f20);
                               C8 (Z_to_bv 64 0xcf100)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd4a50 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd4af0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd7238 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd7f18 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd6a9c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x168de0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcf100 [C8 (Z_to_bv 64 0xc395c)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1690e0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
