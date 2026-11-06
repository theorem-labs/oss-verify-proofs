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
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
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
  mkGD 0x22cc0 0x11 0x40 0x20184 0x22d00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d40 0x17 0x40 0x180a4 0x22de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d80 0xb 0x20 0x10af5 0x22de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22da0 0x11 0x40 0x10b09 0x22de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e20 0x24 0x60 0x19674 0x22f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e80 0xd 0x20 0x11501 0x22f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ea0 0x19 0x40 0x22331 0x22f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ee0 0xd 0x20 0x1d5c9 0x22f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f00 0x25 0x60 0x11517 0x22f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f60 0xe 0x20 0x21d36 0x22f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fc0 0x24 0x60 0x214fa 0x23120 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23020 0xc 0x20 0x1151f 0x23120 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0x18 0x40 0x1e029 0x23120 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23080 0xc 0x20 0x1967b 0x23120 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0x25 0x60 0x142d2 0x23120 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23100 0xd 0x20 0x1e031 0x23120 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0x15 0x40 0x1d5df 0x23240 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231a0 0xb 0x20 0x1569f 0x23240 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231c0 0x25 0x60 0x17026 0x23240 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23220 0xc 0x20 0x156b3 0x23240 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23280 0x16 0x40 0x1d5df 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232c0 0xa 0x20 0x11d99 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232e0 0x18 0x40 0x20184 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23320 0x18 0x40 0x22339 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23360 0x10 0x20 0x13bd9 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23380 0x25 0x60 0x1e73f 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233e0 0xb 0x20 0x1a845 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23400 0xf 0x20 0x22340 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23420 0x13 0x40 0x1b7d1 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23460 0xb 0x20 0x13be0 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23480 0x11 0x40 0x11534 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234c0 0x11 0x40 0x17026 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23500 0xc 0x20 0x1153b 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23520 0xb 0x20 0x1d5e4 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23540 0xe 0x20 0x1b065 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23560 0x11 0x40 0x21502 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235a0 0x16 0x40 0x12619 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0x17 0x40 0x1f67b 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23620 0x1f 0x40 0x1d5f8 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23660 0x2a 0x60 0x1a859 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236c0 0x1b 0x40 0x1ccea 0x23700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0xe 0x20 0x1d5df 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0xa 0x20 0x19da4 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23780 0x10 0x20 0x1ccf2 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0x1d 0x40 0x20184 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237e0 0x11 0x40 0x22339 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23820 0x27 0x60 0x1e73f 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0x10 0x20 0x2019d 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0x12 0x40 0x19674 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x13 0x40 0x1b7d1 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23920 0x2f 0x60 0x11534 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23980 0xc 0x20 0x17026 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x18 0x40 0x214fa 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x30 0x60 0x11550 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a40 0x34 0x60 0x1b065 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23aa0 0x35 0x60 0x21502 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x9 0x20 0x1d600 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b20 0x25 0x60 0x1f67b 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b80 0xb 0x20 0x19db7 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ba0 0x10 0x20 0x13c1d 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23bc0 0xc 0x20 0x201b6 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23be0 0xc 0x20 0x22358 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c00 0x13 0x40 0x17902 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c40 0xd 0x20 0x1ef18 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c60 0xd 0x20 0x1f69b 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c80 0xf 0x20 0x10b11 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ca0 0xc 0x20 0x1b06d 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23cc0 0xc 0x20 0x11558 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ce0 0xf 0x20 0x18b2a 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d00 0x11 0x40 0x11dac 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0xa 0x20 0x1ef2e 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d60 0xf 0x20 0x14dd1 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d80 0x16 0x40 0x1156d 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23dc0 0xb 0x20 0x1b082 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e20 0x10 0x20 0x20184 0x23f60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e40 0xe 0x20 0x1cd0b 0x23f60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e60 0x1b 0x40 0x17902 0x23f60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ea0 0x84 0xc0 0x18b5e 0x23f60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23fa0 0x25 0x60 0x19674 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24000 0xf 0x20 0x1b096 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24020 0x13 0x40 0x1b7d1 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24060 0xf 0x20 0x201cb 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24080 0x11 0x40 0x11534 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x240c0 0x17 0x40 0x17026 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24100 0x25 0x60 0x214fa 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24160 0x2f 0x60 0x11550 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241c0 0x2e 0x60 0x1b065 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24220 0x1f 0x40 0x21502 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24260 0x33 0x60 0x1f67b 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x242c0 0x38 0x60 0x1d5f8 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24320 0x3a 0x60 0x1a859 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24380 0x4d 0x80 0x1ccea 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24400 0x16 0x40 0x11dc6 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24440 0xf 0x20 0x1e746 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24460 0x11 0x40 0x1702d 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244a0 0xf 0x20 0x201e3 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244c0 0x1d 0x40 0x14de9 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24500 0xb 0x20 0x11575 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24520 0xe 0x20 0x18b66 0x24540 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24580 0x11 0x40 0x1d5df 0x246a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245c0 0x16 0x40 0x1e75e 0x246a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24600 0x14 0x40 0x1e047 0x246a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24640 0x25 0x60 0x1a861 0x246a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246e0 0x13 0x40 0x21d4d 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24720 0x8 0x20 0x20b6b 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24740 0x10 0x20 0x1cd22 0x24760 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247a0 0xd 0x20 0x22339 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247c0 0x11 0x40 0x11534 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24800 0x19 0x40 0x1790a 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24840 0x23 0x60 0x1ccea 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248a0 0x12 0x40 0x11dc6 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248e0 0xe 0x20 0x11dce 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24900 0xf 0x20 0x18b6e 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24920 0xf 0x20 0x1b0e1 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24940 0x10 0x20 0x14e0f 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24960 0x16 0x40 0x142da 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x249a0 0x54 0x80 0x13c1d 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a20 0xe 0x20 0x17902 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a40 0x12 0x40 0x10b11 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a80 0x19 0x40 0x18b2a 0x24ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b00 0x11 0x40 0x1d5df 0x24c80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b40 0x12 0x40 0x180ac 0x24c80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b80 0x10 0x20 0x20184 0x24c80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ba0 0x14 0x40 0x22339 0x24c80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24be0 0x25 0x60 0x14e17 0x24c80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24c40 0x13 0x40 0x17035 0x24c80 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd0de0 0x4 0x20 0x18085 0x22d00 0x0 0x0 0x608f80;
  mkGD 0xd0e00 0x8 0x20 0x18095 0x22d00 0x0 0x0 0x608f81;
  mkGD 0xd0e20 0x8 0x20 0x18b18 0x23de0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd0e40 0x8 0x20 0x2018b 0x23de0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 130%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc598%Z (only parsing).  Notation XS1_HI := 0x7fffc990%Z (only parsing).
Notation XS2_LO := 0x800121bc%Z (only parsing).  Notation XS2_HI := 0x80012644%Z (only parsing).
Notation XS3_LO := 0x80012644%Z (only parsing).  Notation XS3_HI := 0x80012644%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x608f82) || (o =? 0x608f80) || (o =? 0x608f81).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x608f82 \/ gd_odr g = 0x608f80 \/ gd_odr g = 0x608f81)
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
  [(0x609a20, 0x609a24); (0x629b18, 0x629b40); (0x629c38, 0x629c40); (0x629d38, 0x629d3c); (0x629d58, 0x629d60);
   (0x62a1c0, 0x62a1c8); (0xd0f90, 0xd0f98); (0xd1080, 0xd1088); (0xd1088, 0xd3248); (0xd3290, 0xd3291);
   (0x608f82, 0x608f83); (0x608f80, 0x608f82); (0x629b40, 0x629b48); (0x629c40, 0x629c48); (0x608f50, 0x608f51)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x609a20 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x629c38 [C8 (Z_to_bv 64 0x7cb78)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x629d38 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x629d58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x62a1c0 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd0f90 [C8 (Z_to_bv 64 0xd0ea8)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd1080 [C8 (Z_to_bv 64 0xd0f98)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xd1170 [C8 (Z_to_bv 64 0xd1088)]                           (* [comment removed for export] *)
  /\ gds_at m 0xd11a0 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xd3240 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd3290 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x608f82 [C1 o1] /\ rw_cells asegs m 0x608f80 [C1 o2]
                              /\ rw_cells asegs m 0x608f81 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x629b18 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x629b30 0 0xb9024))
  /\ (if ph then rw_cells asegs m 0x629b40 [C8 (Z_to_bv 64 0xb9024)] /\ rw_cells asegs m 0x629c40 [C8 (Z_to_bv 64 0x8d540)]
      else (exists j1 : word, rw_cells asegs m 0x629b40 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x629c40 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x609a20 0x609a24); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x629c38 0x629c40); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x629d38 0x629d3c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x629d58 0x629d60); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x62a1c0 0x62a1c8); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xd0f90 0xd0f98); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xd1080 0xd1088); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xd1088 0xd3248); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xd1088 0xd3248); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xd1088 0xd3248); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xd1088 0xd3248); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xd3290 0xd3291); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x608f82 0x608f83); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x608f80 0x608f82); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x608f80 0x608f82); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x629b18 0x629b40); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x629b40 0x629b48); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x629c40 0x629c48); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x629b40 0x629b48); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x629c40 0x629c48); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x608f50 0x608f51); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x608f50 0x608f51)| apply (in_XENV_FPA 0x629b18 0x629b40)| apply (in_XENV_FPA 0x629b40 0x629b48)| apply (in_XENV_FPA 0x629c40 0x629c48)];
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
  ro_cells asegs m 0xc9390 [C8 (Z_to_bv 64 0x8db2c); C8 (Z_to_bv 64 0x3c150)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcd4d8 [C8 (Z_to_bv 64 0xc93a0); C8 (Z_to_bv 64 0xc9390)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcc7a0 [C8 (Z_to_bv 64 0xb8f5c); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xce520 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcd450 [C8 (Z_to_bv 64 0xd11a0); C8 (Z_to_bv 64 0xd3220)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcc7b0 [C8 (Z_to_bv 64 0x1663a0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcc7c0 [C8 (Z_to_bv 64 0x168428); C8 (Z_to_bv 64 0xd40f8); C8 (Z_to_bv 64 0xd68f8);
                               C8 (Z_to_bv 64 0xd75e8); C8 (Z_to_bv 64 0xd75f0); C8 (Z_to_bv 64 0xd75e0);
                               C8 (Z_to_bv 64 0xce6a0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd4110 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd41b0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd68f8 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd75d8 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd615c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1684a0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xce6a0 [C8 (Z_to_bv 64 0xc2f10)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1687a0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
