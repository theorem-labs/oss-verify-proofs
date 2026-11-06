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
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.B22 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
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
  mkGD 0x22ac0 0x11 0x40 0x1ffc7 0x22b00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b40 0xe 0x20 0x1d482 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b60 0xa 0x20 0x19c59 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b80 0x10 0x20 0x1cba3 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ba0 0x1d 0x40 0x1ffc7 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22be0 0x11 0x40 0x2215d 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c20 0x27 0x60 0x1e582 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c80 0x10 0x20 0x1ffe0 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ca0 0x12 0x40 0x1953e 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ce0 0x13 0x40 0x1b68a 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d20 0x2f 0x60 0x114e5 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d80 0xc 0x20 0x16f1f 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22da0 0x18 0x40 0x21357 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22de0 0x30 0x60 0x114ec 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e40 0x34 0x60 0x1af1e 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ea0 0x35 0x60 0x2135f 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f00 0x25 0x60 0x1f4d6 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f60 0xb 0x20 0x19c6c 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f80 0x10 0x20 0x13b74 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fa0 0xc 0x20 0x1fff9 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fc0 0xc 0x20 0x22164 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fe0 0x13 0x40 0x177df 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23020 0xd 0x20 0x1ed5b 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0xd 0x20 0x1f4de 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23060 0xf 0x20 0x10af5 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23080 0xc 0x20 0x1af26 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0xc 0x20 0x114f4 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0xf 0x20 0x189f4 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230e0 0x11 0x40 0x11d35 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23120 0xa 0x20 0x1ed71 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23140 0xf 0x20 0x14d20 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0x16 0x40 0x11509 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231a0 0xb 0x20 0x1af3b 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231c0 0xf 0x20 0x1a6fa 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231e0 0xe 0x20 0x125a2 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23240 0x10 0x20 0x1ffc7 0x23380 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23260 0xe 0x20 0x1cbbc 0x23380 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23280 0x1b 0x40 0x177df 0x23380 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232c0 0x84 0xc0 0x18a28 0x23380 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233c0 0x25 0x60 0x1953e 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23420 0xf 0x20 0x1af4f 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23440 0x13 0x40 0x1b68a 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23480 0xf 0x20 0x2000e 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234a0 0x11 0x40 0x114e5 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234e0 0x17 0x40 0x16f1f 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23520 0x25 0x60 0x21357 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23580 0x2f 0x60 0x114ec 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0x2e 0x60 0x1af1e 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23640 0x1f 0x40 0x2135f 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23680 0x33 0x60 0x1f4d6 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236e0 0x38 0x60 0x1d487 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0x3a 0x60 0x1a712 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0x4d 0x80 0x1cbd3 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23820 0x16 0x40 0x11d4f 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23860 0xf 0x20 0x1e589 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0x11 0x40 0x16f26 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238c0 0xf 0x20 0x20026 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x1d 0x40 0x14d38 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23920 0xb 0x20 0x11511 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0xe 0x20 0x18a30 0x23960 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x11 0x40 0x1d482 0x23ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x16 0x40 0x1e5a1 0x23ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x14 0x40 0x1dea6 0x23ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a60 0x25 0x60 0x1a71a 0x23ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x13 0x40 0x21b79 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b40 0x8 0x20 0x209ae 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b60 0x10 0x20 0x1cbdb 0x23b80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23bc0 0xd 0x20 0x2215d 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23be0 0x11 0x40 0x114e5 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c20 0x19 0x40 0x177e7 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c60 0x23 0x60 0x1cbd3 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23cc0 0x12 0x40 0x11d4f 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d00 0xe 0x20 0x11d57 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0xf 0x20 0x18a38 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0xf 0x20 0x1af9a 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d60 0x10 0x20 0x14d5e 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d80 0x16 0x40 0x14229 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23dc0 0x54 0x80 0x13b74 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e40 0xe 0x20 0x177df 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e60 0x12 0x40 0x10af5 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ea0 0x19 0x40 0x189f4 0x23ee0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xcd780 0x4 0x20 0x17f72 0x22b00 0x0 0x0 0x604dc0;
  mkGD 0xcd7a0 0x8 0x20 0x17f82 0x22b00 0x0 0x0 0x604dc1;
  mkGD 0xcd7c0 0x8 0x20 0x189e2 0x23200 0x0 0x0 0xffffffffffffffff;
  mkGD 0xcd7e0 0x8 0x20 0x1ffce 0x23200 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 85%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc558%Z (only parsing).  Notation XS1_HI := 0x7fffc7dc%Z (only parsing).
Notation XS2_LO := 0x80011af0%Z (only parsing).  Notation XS2_HI := 0x80011e10%Z (only parsing).
Notation XS3_LO := 0x80011e10%Z (only parsing).  Notation XS3_HI := 0x80011e10%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x604dc2) || (o =? 0x604dc0) || (o =? 0x604dc1).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x604dc2 \/ gd_odr g = 0x604dc0 \/ gd_odr g = 0x604dc1)
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
  [(0x605860, 0x605864); (0x625958, 0x625980); (0x625a78, 0x625a80); (0x625b78, 0x625b7c); (0x625b98, 0x625ba0);
   (0x626000, 0x626008); (0xcd930, 0xcd938); (0xcda20, 0xcda28); (0xcda28, 0xcf088); (0xcf0d0, 0xcf0d1);
   (0x604dc2, 0x604dc3); (0x604dc0, 0x604dc2); (0x625980, 0x625988); (0x625a80, 0x625a88); (0x604d90, 0x604d91)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x605860 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x625a78 [C8 (Z_to_bv 64 0x7b9ec)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x625b78 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x625b98 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x626000 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcd930 [C8 (Z_to_bv 64 0xcd848)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcda20 [C8 (Z_to_bv 64 0xcd938)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xcdb10 [C8 (Z_to_bv 64 0xcda28)]                           (* [comment removed for export] *)
  /\ gds_at m 0xcdb40 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xcf080 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcf0d0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x604dc2 [C1 o1] /\ rw_cells asegs m 0x604dc0 [C1 o2]
                              /\ rw_cells asegs m 0x604dc1 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x625958 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x625970 0 0xb59c4))
  /\ (if ph then rw_cells asegs m 0x625980 [C8 (Z_to_bv 64 0xb59c4)] /\ rw_cells asegs m 0x625a80 [C8 (Z_to_bv 64 0x8c3b4)]
      else (exists j1 : word, rw_cells asegs m 0x625980 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x625a80 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x605860 0x605864); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x625a78 0x625a80); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x625b78 0x625b7c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x625b98 0x625ba0); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x626000 0x626008); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xcd930 0xcd938); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xcda20 0xcda28); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xcda28 0xcf088); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xcda28 0xcf088); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xcda28 0xcf088); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xcda28 0xcf088); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xcf0d0 0xcf0d1); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x604dc2 0x604dc3); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x604dc0 0x604dc2); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x604dc0 0x604dc2); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x625958 0x625980); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x625980 0x625988); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x625a80 0x625a88); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x625980 0x625988); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x625a80 0x625a88); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x604d90 0x604d91); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x604d90 0x604d91)| apply (in_XENV_FPA 0x625958 0x625980)| apply (in_XENV_FPA 0x625980 0x625988)| apply (in_XENV_FPA 0x625a80 0x625a88)];
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
  ro_cells asegs m 0xc5d30 [C8 (Z_to_bv 64 0x8c930); C8 (Z_to_bv 64 0x3afc4)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9e78 [C8 (Z_to_bv 64 0xc5d40); C8 (Z_to_bv 64 0xc5d30)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9140 [C8 (Z_to_bv 64 0xb58fc); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xcaec0 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9df0 [C8 (Z_to_bv 64 0xcdb40); C8 (Z_to_bv 64 0xcf080)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9150 [C8 (Z_to_bv 64 0x1621e0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9160 [C8 (Z_to_bv 64 0x164268); C8 (Z_to_bv 64 0xcff38); C8 (Z_to_bv 64 0xd2738);
                               C8 (Z_to_bv 64 0xd3428); C8 (Z_to_bv 64 0xd3430); C8 (Z_to_bv 64 0xd3420);
                               C8 (Z_to_bv 64 0xcb040)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcff50 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcfff0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd2738 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd3418 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd1f9c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1642e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcb040 [C8 (Z_to_bv 64 0xbf8b0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1645e0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
