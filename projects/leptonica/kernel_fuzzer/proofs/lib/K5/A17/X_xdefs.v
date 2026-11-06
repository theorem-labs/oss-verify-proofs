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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
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
  mkGD 0x22ba0 0x11 0x40 0x2004b 0x22be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c20 0xe 0x20 0x1d4ef 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c40 0xa 0x20 0x19c9c 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c60 0x10 0x20 0x1cc10 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c80 0x1d 0x40 0x2004b 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22cc0 0x27 0x60 0x1e606 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d20 0x10 0x20 0x20064 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d40 0x12 0x40 0x19559 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d80 0x13 0x40 0x1b6ce 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22dc0 0x2f 0x60 0x114e5 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e20 0xc 0x20 0x16f18 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e40 0x18 0x40 0x21413 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e80 0x30 0x60 0x114ec 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ee0 0x34 0x60 0x1af62 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f40 0x35 0x60 0x2141b 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fa0 0x25 0x60 0x1f570 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23000 0xb 0x20 0x19caf 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23020 0x10 0x20 0x13b57 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0xc 0x20 0x2007d 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23060 0xd 0x20 0x1edf5 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23080 0xc 0x20 0x1af6a 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0x11 0x40 0x11d20 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230e0 0xa 0x20 0x1ee0b 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23100 0xf 0x20 0x14d0a 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23120 0x16 0x40 0x114f4 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0xb 0x20 0x1af7f 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23240 0x11 0x40 0x1d4ef 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23280 0xc 0x20 0x17f7a 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232a0 0x10 0x20 0x2004b 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232c0 0x25 0x60 0x2224f 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23320 0xe 0x20 0x1cc29 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23340 0x1b 0x40 0x177d8 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23380 0x84 0xc0 0x18a1e 0x23440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23480 0x25 0x60 0x19559 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234e0 0xf 0x20 0x1af93 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23500 0x13 0x40 0x1b6ce 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23540 0xf 0x20 0x20092 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23560 0x11 0x40 0x114e5 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235a0 0x17 0x40 0x16f18 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0x25 0x60 0x21413 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23640 0x2f 0x60 0x114ec 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236a0 0x2e 0x60 0x1af62 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0x1f 0x40 0x2141b 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0x33 0x60 0x1f570 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0x38 0x60 0x1d4f4 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23800 0x3a 0x60 0x1a73d 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23860 0x4d 0x80 0x1cc40 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x16 0x40 0x11d3a 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23920 0xf 0x20 0x1e60d 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0x11 0x40 0x16f1f 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23980 0xf 0x20 0x200aa 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x1d 0x40 0x14d22 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0xb 0x20 0x114fc 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a00 0xe 0x20 0x18a26 0x23a20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a60 0x11 0x40 0x1d4ef 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23aa0 0x16 0x40 0x1e625 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ae0 0x14 0x40 0x1df2a 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b20 0x25 0x60 0x1a745 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23bc0 0x13 0x40 0x21c4f 0x23c40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c00 0x8 0x20 0x20a32 0x23c40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c20 0x10 0x20 0x1cc48 0x23c40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c80 0xd 0x20 0x2224f 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ca0 0x11 0x40 0x114e5 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ce0 0x19 0x40 0x177e0 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0x23 0x60 0x1cc40 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d80 0x12 0x40 0x11d3a 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23dc0 0xe 0x20 0x11d42 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23de0 0xf 0x20 0x18a2e 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e00 0xf 0x20 0x1afde 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e20 0x10 0x20 0x14d48 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e40 0x16 0x40 0x14213 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e80 0x54 0x80 0x13b57 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f00 0xe 0x20 0x177d8 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f20 0x12 0x40 0x10af5 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f60 0x19 0x40 0x18a36 0x23fa0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23fe0 0x12 0x40 0x1d4ef 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24020 0xd 0x20 0x1e62d 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24040 0x13 0x40 0x2004b 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24080 0x30 0x60 0x2224f 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x240e0 0xd 0x20 0x14d50 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24100 0x13 0x40 0x13b9e 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24140 0x25 0x60 0x1e606 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241a0 0xe 0x20 0x1d4fc 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x241c0 0x19 0x40 0x21413 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24200 0x19 0x40 0x114ec 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24240 0x10 0x20 0x1af62 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24260 0x11 0x40 0x21423 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x242a0 0x10 0x20 0x1a74d 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x242c0 0x11 0x40 0x1a73d 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24300 0x13 0x40 0x21c57 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24340 0x11 0x40 0x1cc40 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24380 0x10 0x20 0x16736 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243a0 0x14 0x40 0x18a3e 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243e0 0xe 0x20 0x1e625 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24400 0x11 0x40 0x1a745 0x24440 0x0 0x0 0xffffffffffffffff;
  mkGD 0xce660 0x4 0x20 0x17f5b 0x22be0 0x0 0x0 0x606040;
  mkGD 0xce680 0x8 0x20 0x17f6b 0x22be0 0x0 0x0 0x606041;
  mkGD 0xce6a0 0x8 0x20 0x189e0 0x23180 0x0 0x0 0xffffffffffffffff;
  mkGD 0xce6c0 0x8 0x20 0x20052 0x23180 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 99%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc574%Z (only parsing).  Notation XS1_HI := 0x7fffc888%Z (only parsing).
Notation XS2_LO := 0x80011ccc%Z (only parsing).  Notation XS2_HI := 0x8001205c%Z (only parsing).
Notation XS3_LO := 0x8001205c%Z (only parsing).  Notation XS3_HI := 0x8001205c%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x606042) || (o =? 0x606040) || (o =? 0x606041).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x606042 \/ gd_odr g = 0x606040 \/ gd_odr g = 0x606041)
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
  [(0x606ae0, 0x606ae4); (0x626bd8, 0x626c00); (0x626cf8, 0x626d00); (0x626df8, 0x626dfc); (0x626e18, 0x626e20);
   (0x627280, 0x627288); (0xce810, 0xce818); (0xce900, 0xce908); (0xce908, 0xd0308); (0xd0350, 0xd0351);
   (0x606042, 0x606043); (0x606040, 0x606042); (0x626c00, 0x626c08); (0x626d00, 0x626d08); (0x606010, 0x606011)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x606ae0 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x626cf8 [C8 (Z_to_bv 64 0x7bff8)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x626df8 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x626e18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x627280 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xce810 [C8 (Z_to_bv 64 0xce728)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xce900 [C8 (Z_to_bv 64 0xce818)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xce9f0 [C8 (Z_to_bv 64 0xce908)]                           (* [comment removed for export] *)
  /\ gds_at m 0xcea20 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xd0300 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd0350 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x606042 [C1 o1] /\ rw_cells asegs m 0x606040 [C1 o2]
                              /\ rw_cells asegs m 0x606041 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x626bd8 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x626bf0 0 0xb68ac))
  /\ (if ph then rw_cells asegs m 0x626c00 [C8 (Z_to_bv 64 0xb68ac)] /\ rw_cells asegs m 0x626d00 [C8 (Z_to_bv 64 0x8c9c0)]
      else (exists j1 : word, rw_cells asegs m 0x626c00 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x626d00 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x606ae0 0x606ae4); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x626cf8 0x626d00); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x626df8 0x626dfc); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x626e18 0x626e20); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x627280 0x627288); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xce810 0xce818); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xce900 0xce908); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xce908 0xd0308); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xce908 0xd0308); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xce908 0xd0308); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xce908 0xd0308); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xd0350 0xd0351); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x606042 0x606043); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x606040 0x606042); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x606040 0x606042); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x626bd8 0x626c00); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x626c00 0x626c08); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x626d00 0x626d08); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x626c00 0x626c08); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x626d00 0x626d08); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x606010 0x606011); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x606010 0x606011)| apply (in_XENV_FPA 0x626bd8 0x626c00)| apply (in_XENV_FPA 0x626c00 0x626c08)| apply (in_XENV_FPA 0x626d00 0x626d08)];
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
  ro_cells asegs m 0xc6c18 [C8 (Z_to_bv 64 0x8cfac); C8 (Z_to_bv 64 0x3b5d0)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcad60 [C8 (Z_to_bv 64 0xc6c28); C8 (Z_to_bv 64 0xc6c18)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xca028 [C8 (Z_to_bv 64 0xb67e4); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xcbda0 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcacd8 [C8 (Z_to_bv 64 0xcea20); C8 (Z_to_bv 64 0xd02e0)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xca038 [C8 (Z_to_bv 64 0x163460)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xca048 [C8 (Z_to_bv 64 0x1654e8); C8 (Z_to_bv 64 0xd11b8); C8 (Z_to_bv 64 0xd39b8);
                               C8 (Z_to_bv 64 0xd46a8); C8 (Z_to_bv 64 0xd46b0); C8 (Z_to_bv 64 0xd46a0);
                               C8 (Z_to_bv 64 0xcbf20)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd11d0 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd1270 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd39b8 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd4698 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd321c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x165560 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcbf20 [C8 (Z_to_bv 64 0xc0798)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x165860 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
