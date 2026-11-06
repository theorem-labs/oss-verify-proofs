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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
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
  mkGD 0x22c80 0x11 0x40 0x20159 0x22cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d00 0x17 0x40 0x1808f 0x22da0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d40 0xb 0x20 0x10af5 0x22da0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d60 0x11 0x40 0x10b09 0x22da0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22de0 0x24 0x60 0x1965f 0x22f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e40 0xd 0x20 0x11501 0x22f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e60 0x19 0x40 0x22306 0x22f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ea0 0xd 0x20 0x1d5b4 0x22f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ec0 0x25 0x60 0x11517 0x22f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f20 0xe 0x20 0x21d0b 0x22f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f80 0x24 0x60 0x214cf 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fe0 0xc 0x20 0x1151f 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23000 0x18 0x40 0x1e014 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0xc 0x20 0x19666 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23060 0x25 0x60 0x142bd 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0xd 0x20 0x1e01c 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23120 0x15 0x40 0x1d5ca 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0xb 0x20 0x1568a 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23180 0x25 0x60 0x17011 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231e0 0xc 0x20 0x1569e 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23240 0x16 0x40 0x1d5ca 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23280 0xa 0x20 0x11d84 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232a0 0x18 0x40 0x20159 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232e0 0x18 0x40 0x2230e 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23320 0x10 0x20 0x13bc4 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23340 0x25 0x60 0x1e72a 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233a0 0xb 0x20 0x1a830 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233c0 0xf 0x20 0x22315 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233e0 0x13 0x40 0x1b7bc 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23420 0xb 0x20 0x13bcb 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23440 0x11 0x40 0x11534 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23480 0x11 0x40 0x17011 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234c0 0xc 0x20 0x1153b 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234e0 0xb 0x20 0x1d5cf 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23500 0xe 0x20 0x1b050 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23520 0x11 0x40 0x214d7 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23560 0x16 0x40 0x12604 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235a0 0x17 0x40 0x1f666 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0x1f 0x40 0x1d5e3 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23620 0x2a 0x60 0x1a844 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23680 0x1b 0x40 0x1ccd5 0x236c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0xe 0x20 0x1d5ca 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23720 0xa 0x20 0x19d8f 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0x10 0x20 0x1ccdd 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x1d 0x40 0x20159 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0x11 0x40 0x2230e 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237e0 0x27 0x60 0x1e72a 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23840 0x10 0x20 0x20172 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23860 0x12 0x40 0x1965f 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0x13 0x40 0x1b7bc 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x2f 0x60 0x11534 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0xc 0x20 0x17011 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23960 0x18 0x40 0x214cf 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x30 0x60 0x11550 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a00 0x34 0x60 0x1b050 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a60 0x35 0x60 0x214d7 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ac0 0x9 0x20 0x1d5eb 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ae0 0x25 0x60 0x1f666 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b40 0xb 0x20 0x19da2 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b60 0x10 0x20 0x13c08 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b80 0xc 0x20 0x2018b 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ba0 0xd 0x20 0x1ef03 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23bc0 0xc 0x20 0x1b058 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23be0 0x11 0x40 0x11d97 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c20 0xa 0x20 0x1ef19 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c40 0xf 0x20 0x14dbc 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c60 0x16 0x40 0x11558 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ca0 0xb 0x20 0x1b06d 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d00 0x10 0x20 0x20159 0x23e40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0xe 0x20 0x1ccf6 0x23e40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0x1b 0x40 0x178ed 0x23e40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d80 0x84 0xc0 0x18b41 0x23e40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e80 0x25 0x60 0x1965f 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ee0 0xf 0x20 0x1b081 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f00 0x13 0x40 0x1b7bc 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f40 0xf 0x20 0x201a0 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f60 0x11 0x40 0x11534 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23fa0 0x17 0x40 0x17011 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23fe0 0x25 0x60 0x214cf 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24040 0x2f 0x60 0x11550 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x240a0 0x2e 0x60 0x1b050 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24100 0x1f 0x40 0x214d7 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24140 0x33 0x60 0x1f666 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241a0 0x38 0x60 0x1d5e3 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24200 0x3a 0x60 0x1a844 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24260 0x4d 0x80 0x1ccd5 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x242e0 0x16 0x40 0x11db1 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24320 0xf 0x20 0x1e731 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24340 0x11 0x40 0x17018 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24380 0xf 0x20 0x201b8 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243a0 0x1d 0x40 0x14dd4 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243e0 0xb 0x20 0x11560 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24400 0xe 0x20 0x18b49 0x24420 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24460 0x11 0x40 0x1d5ca 0x24580 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244a0 0x16 0x40 0x1e749 0x24580 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244e0 0x14 0x40 0x1e032 0x24580 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24520 0x25 0x60 0x1a84c 0x24580 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245c0 0x13 0x40 0x21d22 0x24640 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24600 0x8 0x20 0x20b40 0x24640 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24620 0x10 0x20 0x1cd0d 0x24640 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24680 0xd 0x20 0x2230e 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246a0 0x11 0x40 0x11534 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246e0 0x19 0x40 0x178f5 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24720 0x23 0x60 0x1ccd5 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24780 0x12 0x40 0x11db1 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247c0 0xe 0x20 0x11db9 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247e0 0xf 0x20 0x18b51 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24800 0xf 0x20 0x1b0cc 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24820 0x10 0x20 0x14dfa 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24840 0x16 0x40 0x142c5 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24880 0x54 0x80 0x13c08 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24900 0xe 0x20 0x178ed 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24920 0x12 0x40 0x10b11 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24960 0x19 0x40 0x18b59 0x249a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x249e0 0x11 0x40 0x1d5ca 0x24b60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a20 0x12 0x40 0x18097 0x24b60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a60 0x10 0x20 0x20159 0x24b60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a80 0x14 0x40 0x2230e 0x24b60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ac0 0x25 0x60 0x14e02 0x24b60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b20 0x13 0x40 0x17020 0x24b60 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd0400 0x4 0x20 0x18070 0x22cc0 0x0 0x0 0x608400;
  mkGD 0xd0420 0x8 0x20 0x18080 0x22cc0 0x0 0x0 0x608401;
  mkGD 0xd0440 0x8 0x20 0x18b03 0x23cc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd0460 0x8 0x20 0x20160 0x23cc0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 124%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc590%Z (only parsing).  Notation XS1_HI := 0x7fffc96c%Z (only parsing).
Notation XS2_LO := 0x80012080%Z (only parsing).  Notation XS2_HI := 0x800124d8%Z (only parsing).
Notation XS3_LO := 0x800124d8%Z (only parsing).  Notation XS3_HI := 0x800124d8%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x608402) || (o =? 0x608400) || (o =? 0x608401).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x608402 \/ gd_odr g = 0x608400 \/ gd_odr g = 0x608401)
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
  [(0x608ea0, 0x608ea4); (0x628f98, 0x628fc0); (0x6290b8, 0x6290c0); (0x6291b8, 0x6291bc); (0x6291d8, 0x6291e0);
   (0x629640, 0x629648); (0xd05b0, 0xd05b8); (0xd06a0, 0xd06a8); (0xd06a8, 0xd26c8); (0xd2710, 0xd2711);
   (0x608402, 0x608403); (0x608400, 0x608402); (0x628fc0, 0x628fc8); (0x6290c0, 0x6290c8); (0x6083d0, 0x6083d1)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x608ea0 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x6290b8 [C8 (Z_to_bv 64 0x7c9f0)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x6291b8 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x6291d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x629640 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd05b0 [C8 (Z_to_bv 64 0xd04c8)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd06a0 [C8 (Z_to_bv 64 0xd05b8)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xd0790 [C8 (Z_to_bv 64 0xd06a8)]                           (* [comment removed for export] *)
  /\ gds_at m 0xd07c0 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xd26c0 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd2710 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x608402 [C1 o1] /\ rw_cells asegs m 0x608400 [C1 o2]
                              /\ rw_cells asegs m 0x608401 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x628f98 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x628fb0 0 0xb864c))
  /\ (if ph then rw_cells asegs m 0x628fc0 [C8 (Z_to_bv 64 0xb864c)] /\ rw_cells asegs m 0x6290c0 [C8 (Z_to_bv 64 0x8d3b8)]
      else (exists j1 : word, rw_cells asegs m 0x628fc0 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x6290c0 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x608ea0 0x608ea4); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6290b8 0x6290c0); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x6291b8 0x6291bc); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6291d8 0x6291e0); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x629640 0x629648); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xd05b0 0xd05b8); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xd06a0 0xd06a8); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xd06a8 0xd26c8); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xd06a8 0xd26c8); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xd06a8 0xd26c8); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xd06a8 0xd26c8); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xd2710 0xd2711); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x608402 0x608403); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x608400 0x608402); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x608400 0x608402); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x628f98 0x628fc0); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x628fc0 0x628fc8); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x6290c0 0x6290c8); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x628fc0 0x628fc8); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x6290c0 0x6290c8); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x6083d0 0x6083d1); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x6083d0 0x6083d1)| apply (in_XENV_FPA 0x628f98 0x628fc0)| apply (in_XENV_FPA 0x628fc0 0x628fc8)| apply (in_XENV_FPA 0x6290c0 0x6290c8)];
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
  ro_cells asegs m 0xc89b8 [C8 (Z_to_bv 64 0x8d9a4); C8 (Z_to_bv 64 0x3bfc8)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xccb00 [C8 (Z_to_bv 64 0xc89c8); C8 (Z_to_bv 64 0xc89b8)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcbdc8 [C8 (Z_to_bv 64 0xb8584); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xcdb40 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcca78 [C8 (Z_to_bv 64 0xd07c0); C8 (Z_to_bv 64 0xd26c0)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcbdd8 [C8 (Z_to_bv 64 0x165820)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcbde8 [C8 (Z_to_bv 64 0x1678a8); C8 (Z_to_bv 64 0xd3578); C8 (Z_to_bv 64 0xd5d78);
                               C8 (Z_to_bv 64 0xd6a68); C8 (Z_to_bv 64 0xd6a70); C8 (Z_to_bv 64 0xd6a60);
                               C8 (Z_to_bv 64 0xcdcc0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd3590 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd3630 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd5d78 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd6a58 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd55dc [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x167920 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcdcc0 [C8 (Z_to_bv 64 0xc2538)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x167c20 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
