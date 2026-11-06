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
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import Layout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
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
  mkGD 0x22ae0 0x11 0x40 0x1ffe5 0x22b20 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b60 0xe 0x20 0x1d4a0 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b80 0xa 0x20 0x19c71 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ba0 0x10 0x20 0x1cbc1 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22bc0 0x1d 0x40 0x1ffe5 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c00 0x27 0x60 0x1e5a0 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c60 0x10 0x20 0x1fffe 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c80 0x12 0x40 0x19556 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22cc0 0x13 0x40 0x1b68a 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d00 0x2f 0x60 0x114fe 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d60 0xc 0x20 0x16f30 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d80 0x18 0x40 0x21375 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22dc0 0x30 0x60 0x11505 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e20 0x34 0x60 0x1af1e 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e80 0x35 0x60 0x2137d 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ee0 0x25 0x60 0x1f4f4 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f40 0xb 0x20 0x19c84 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f60 0x10 0x20 0x13b85 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f80 0xc 0x20 0x20017 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fa0 0xc 0x20 0x2217b 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fc0 0x13 0x40 0x177f0 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23000 0xd 0x20 0x1ed79 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23020 0xd 0x20 0x1f4fc 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0xf 0x20 0x10b0e 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23060 0xc 0x20 0x1af26 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23080 0xc 0x20 0x1150d 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0xf 0x20 0x18a0c 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0x11 0x40 0x11d4e 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23100 0xa 0x20 0x1ed8f 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23120 0xe 0x20 0x17f92 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23140 0xf 0x20 0x14d31 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0x16 0x40 0x11522 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231a0 0xb 0x20 0x1af3b 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23200 0x10 0x20 0x1ffe5 0x23340 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23220 0xe 0x20 0x1cbda 0x23340 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23240 0x1b 0x40 0x177f0 0x23340 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23280 0x84 0xc0 0x18a40 0x23340 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23380 0x25 0x60 0x19556 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233e0 0xf 0x20 0x1af4f 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23400 0x13 0x40 0x1b68a 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23440 0xf 0x20 0x2002c 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23460 0x11 0x40 0x114fe 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234a0 0x17 0x40 0x16f30 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234e0 0x25 0x60 0x21375 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23540 0x2f 0x60 0x11505 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235a0 0x2e 0x60 0x1af1e 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23600 0x1f 0x40 0x2137d 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23640 0x33 0x60 0x1f4f4 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x236a0 0x38 0x60 0x1d4a5 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0x3a 0x60 0x1a712 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x4d 0x80 0x1cbf1 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237e0 0x16 0x40 0x11d68 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23820 0xf 0x20 0x1e5a7 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23840 0x11 0x40 0x16f37 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0xf 0x20 0x20044 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0x1d 0x40 0x14d49 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0xb 0x20 0x1152a 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23900 0xe 0x20 0x18a48 0x23920 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23960 0x11 0x40 0x1d4a0 0x23a80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0x16 0x40 0x1e5bf 0x23a80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x14 0x40 0x1dec4 0x23a80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x25 0x60 0x1a71a 0x23a80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ac0 0x13 0x40 0x21b97 0x23b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x8 0x20 0x209cc 0x23b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b20 0x10 0x20 0x1cbf9 0x23b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b80 0x10 0x20 0x11d70 0x23be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ba0 0x15 0x40 0x1c0d4 0x23be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c20 0xd 0x20 0x221a7 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c40 0x11 0x40 0x114fe 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c80 0x19 0x40 0x177f8 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23cc0 0x23 0x60 0x1cbf1 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0x12 0x40 0x11d68 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d60 0xe 0x20 0x11d70 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d80 0xf 0x20 0x18a50 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23da0 0xf 0x20 0x1af9a 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23dc0 0x10 0x20 0x14d6f 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23de0 0x16 0x40 0x1423a 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23e20 0x54 0x80 0x13b85 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ea0 0xe 0x20 0x177f0 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ec0 0x12 0x40 0x10b0e 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23f00 0x19 0x40 0x18a0c 0x23f40 0x0 0x0 0xffffffffffffffff;
  mkGD 0xcd720 0x4 0x20 0x17f73 0x22b20 0x0 0x0 0x604d80;
  mkGD 0xcd740 0x8 0x20 0x17f83 0x22b20 0x0 0x0 0x604d81;
  mkGD 0xcd760 0x8 0x20 0x189fa 0x231c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xcd780 0x8 0x20 0x1ffec 0x231c0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 85%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc55c%Z (only parsing).  Notation XS1_HI := 0x7fffc7e8%Z (only parsing).
Notation XS2_LO := 0x80011ae4%Z (only parsing).  Notation XS2_HI := 0x80011e04%Z (only parsing).
Notation XS3_LO := 0x80011e04%Z (only parsing).  Notation XS3_HI := 0x80011e04%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x604d82) || (o =? 0x604d80) || (o =? 0x604d81).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x604d82 \/ gd_odr g = 0x604d80 \/ gd_odr g = 0x604d81)
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
  [(0x605820, 0x605824); (0x625918, 0x625940); (0x625a38, 0x625a40); (0x625b38, 0x625b3c); (0x625b58, 0x625b60);
   (0x625fc0, 0x625fc8); (0xcd8d0, 0xcd8d8); (0xcd9c0, 0xcd9c8); (0xcd9c8, 0xcf048); (0xcf090, 0xcf091);
   (0x604d82, 0x604d83); (0x604d80, 0x604d82); (0x625940, 0x625948); (0x625a40, 0x625a48); (0x604d50, 0x604d51)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x605820 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x625a38 [C8 (Z_to_bv 64 0x7ba58)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x625b38 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x625b58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x625fc0 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcd8d0 [C8 (Z_to_bv 64 0xcd7e8)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcd9c0 [C8 (Z_to_bv 64 0xcd8d8)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xcdab0 [C8 (Z_to_bv 64 0xcd9c8)]                           (* [comment removed for export] *)
  /\ gds_at m 0xcdae0 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xcf040 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcf090 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x604d82 [C1 o1] /\ rw_cells asegs m 0x604d80 [C1 o2]
                              /\ rw_cells asegs m 0x604d81 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x625918 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x625930 0 0xb595c))
  /\ (if ph then rw_cells asegs m 0x625940 [C8 (Z_to_bv 64 0xb595c)] /\ rw_cells asegs m 0x625a40 [C8 (Z_to_bv 64 0x8c420)]
      else (exists j1 : word, rw_cells asegs m 0x625940 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x625a40 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x605820 0x605824); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x625a38 0x625a40); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x625b38 0x625b3c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x625b58 0x625b60); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x625fc0 0x625fc8); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xcd8d0 0xcd8d8); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xcd9c0 0xcd9c8); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xcd9c8 0xcf048); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xcd9c8 0xcf048); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xcd9c8 0xcf048); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xcd9c8 0xcf048); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xcf090 0xcf091); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x604d82 0x604d83); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x604d80 0x604d82); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x604d80 0x604d82); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x625918 0x625940); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x625940 0x625948); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x625a40 0x625a48); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x625940 0x625948); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x625a40 0x625a48); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x604d50 0x604d51); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x604d50 0x604d51)| apply (in_XENV_FPA 0x625918 0x625940)| apply (in_XENV_FPA 0x625940 0x625948)| apply (in_XENV_FPA 0x625a40 0x625a48)];
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
  ro_cells asegs m 0xc5cc8 [C8 (Z_to_bv 64 0x8c9a8); C8 (Z_to_bv 64 0x3b030)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9e10 [C8 (Z_to_bv 64 0xc5cd8); C8 (Z_to_bv 64 0xc5cc8)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc90d8 [C8 (Z_to_bv 64 0xb5894); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xcae60 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9d88 [C8 (Z_to_bv 64 0xcdae0); C8 (Z_to_bv 64 0xcf020)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc90e8 [C8 (Z_to_bv 64 0x1621a0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc90f8 [C8 (Z_to_bv 64 0x164228); C8 (Z_to_bv 64 0xcfef8); C8 (Z_to_bv 64 0xd26f8);
                               C8 (Z_to_bv 64 0xd33e8); C8 (Z_to_bv 64 0xd33f0); C8 (Z_to_bv 64 0xd33e0);
                               C8 (Z_to_bv 64 0xcafe0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcff10 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcffb0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd26f8 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd33d8 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd1f5c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1642a0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcafe0 [C8 (Z_to_bv 64 0xbf848)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x1645a0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
