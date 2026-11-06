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
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
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
  mkGD 0x22a80 0x11 0x40 0x1ff9c 0x22ac0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b00 0xe 0x20 0x1d46d 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b20 0xa 0x20 0x19c44 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b40 0x10 0x20 0x1cb8e 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22b60 0x1d 0x40 0x1ff9c 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ba0 0x11 0x40 0x22132 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22be0 0x27 0x60 0x1e56d 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c40 0x10 0x20 0x1ffb5 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22c60 0x12 0x40 0x19529 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ca0 0x13 0x40 0x1b675 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ce0 0x2f 0x60 0x114e5 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d40 0xc 0x20 0x16f0a 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22d60 0x18 0x40 0x2132c 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22da0 0x30 0x60 0x114ec 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e00 0x34 0x60 0x1af09 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22e60 0x35 0x60 0x21334 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22ec0 0x25 0x60 0x1f4c1 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f20 0xb 0x20 0x19c57 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f40 0x10 0x20 0x13b5f 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f60 0xc 0x20 0x1ffce 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22f80 0xd 0x20 0x1ed46 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fa0 0xc 0x20 0x1af11 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x22fc0 0x11 0x40 0x11d20 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23000 0xa 0x20 0x1ed5c 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23020 0xf 0x20 0x14d0b 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23040 0x16 0x40 0x114f4 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23080 0xb 0x20 0x1af26 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0xf 0x20 0x1a6e5 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0xe 0x20 0x1258d 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23120 0x10 0x20 0x1ff9c 0x23260 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23140 0xe 0x20 0x1cba7 0x23260 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0x1b 0x40 0x177ca 0x23260 0x0 0x0 0xffffffffffffffff;
  mkGD 0x231a0 0x84 0xc0 0x18a0b 0x23260 0x0 0x0 0xffffffffffffffff;
  mkGD 0x232a0 0x25 0x60 0x19529 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23300 0xf 0x20 0x1af3a 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23320 0x13 0x40 0x1b675 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23360 0xf 0x20 0x1ffe3 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23380 0x11 0x40 0x114e5 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x233c0 0x17 0x40 0x16f0a 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23400 0x25 0x60 0x2132c 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23460 0x2f 0x60 0x114ec 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x234c0 0x2e 0x60 0x1af09 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23520 0x1f 0x40 0x21334 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23560 0x33 0x60 0x1f4c1 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235c0 0x38 0x60 0x1d472 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23620 0x3a 0x60 0x1a6fd 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23680 0x4d 0x80 0x1cbbe 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23700 0x16 0x40 0x11d3a 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23740 0xf 0x20 0x1e574 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x11 0x40 0x16f11 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237a0 0xf 0x20 0x1fffb 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x237c0 0x1d 0x40 0x14d23 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23800 0xb 0x20 0x114fc 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23820 0xe 0x20 0x18a13 0x23840 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23880 0x11 0x40 0x1d46d 0x239a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238c0 0x16 0x40 0x1e58c 0x239a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23900 0x14 0x40 0x1de91 0x239a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23940 0x25 0x60 0x1a705 0x239a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x13 0x40 0x21b4e 0x23a60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x8 0x20 0x20983 0x23a60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a40 0x10 0x20 0x1cbc6 0x23a60 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23aa0 0xd 0x20 0x22132 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ac0 0x11 0x40 0x114e5 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x19 0x40 0x177d2 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b40 0x23 0x60 0x1cbbe 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ba0 0x12 0x40 0x11d3a 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23be0 0xe 0x20 0x11d42 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c00 0xf 0x20 0x18a1b 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c20 0xf 0x20 0x1af85 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c40 0x10 0x20 0x14d49 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c60 0x16 0x40 0x14214 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ca0 0x54 0x80 0x13b5f 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0xe 0x20 0x177ca 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0x12 0x40 0x10af5 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d80 0x19 0x40 0x18a23 0x23dc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xcce80 0x4 0x20 0x17f5d 0x22ac0 0x0 0x0 0x604340;
  mkGD 0xccea0 0x8 0x20 0x17f6d 0x22ac0 0x0 0x0 0x604341;
  mkGD 0xccec0 0x8 0x20 0x189cd 0x230e0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xccee0 0x8 0x20 0x1ffa3 0x230e0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 79%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc550%Z (only parsing).  Notation XS1_HI := 0x7fffc7b8%Z (only parsing).
Notation XS2_LO := 0x800119d0%Z (only parsing).  Notation XS2_HI := 0x80011cc0%Z (only parsing).
Notation XS3_LO := 0x80011cc0%Z (only parsing).  Notation XS3_HI := 0x80011cc0%Z (only parsing).  (* [comment removed for export] *)

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x604342) || (o =? 0x604340) || (o =? 0x604341).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x604342 \/ gd_odr g = 0x604340 \/ gd_odr g = 0x604341)
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
  [(0x604de0, 0x604de4); (0x624ed8, 0x624f00); (0x624ff8, 0x625000); (0x6250f8, 0x6250fc); (0x625118, 0x625120);
   (0x625580, 0x625588); (0xcd030, 0xcd038); (0xcd120, 0xcd128); (0xcd128, 0xce608); (0xce650, 0xce651);
   (0x604342, 0x604343); (0x604340, 0x604342); (0x624f00, 0x624f08); (0x625000, 0x625008); (0x604310, 0x604311)].

(* [comment removed for export] *)
Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x604de0 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x624ff8 [C8 (Z_to_bv 64 0x7b83c)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x6250f8 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x625118 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x625580 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcd030 [C8 (Z_to_bv 64 0xccf48)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcd120 [C8 (Z_to_bv 64 0xcd038)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xcd210 [C8 (Z_to_bv 64 0xcd128)]                           (* [comment removed for export] *)
  /\ gds_at m 0xcd240 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xce600 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xce650 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x604342 [C1 o1] /\ rw_cells asegs m 0x604340 [C1 o2]
                              /\ rw_cells asegs m 0x604341 [C1 o3]).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x624ed8 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x624ef0 0 0xb50c8))
  /\ (if ph then rw_cells asegs m 0x624f00 [C8 (Z_to_bv 64 0xb50c8)] /\ rw_cells asegs m 0x625000 [C8 (Z_to_bv 64 0x8c204)]
      else (exists j1 : word, rw_cells asegs m 0x624f00 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x625000 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x604de0 0x604de4); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x624ff8 0x625000); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x6250f8 0x6250fc); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x625118 0x625120); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x625580 0x625588); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xcd030 0xcd038); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xcd120 0xcd128); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xcd128 0xce608); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xcd128 0xce608); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xcd128 0xce608); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xcd128 0xce608); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xce650 0xce651); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x604342 0x604343); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x604340 0x604342); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x604340 0x604342); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x624ed8 0x624f00); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x624f00 0x624f08); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x625000 0x625008); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x624f00 0x624f08); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x625000 0x625008); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x604310 0x604311); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x604310 0x604311)| apply (in_XENV_FPA 0x624ed8 0x624f00)| apply (in_XENV_FPA 0x624f00 0x624f08)| apply (in_XENV_FPA 0x625000 0x625008)];
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
  ro_cells asegs m 0xc5438 [C8 (Z_to_bv 64 0x8c780); C8 (Z_to_bv 64 0x3ae14)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9580 [C8 (Z_to_bv 64 0xc5448); C8 (Z_to_bv 64 0xc5438)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc8848 [C8 (Z_to_bv 64 0xb5000); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xca5c0 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc94f8 [C8 (Z_to_bv 64 0xcd240); C8 (Z_to_bv 64 0xce600)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc8858 [C8 (Z_to_bv 64 0x161760)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc8868 [C8 (Z_to_bv 64 0x1637e8); C8 (Z_to_bv 64 0xcf4b8); C8 (Z_to_bv 64 0xd1cb8);
                               C8 (Z_to_bv 64 0xd29a8); C8 (Z_to_bv 64 0xd29b0); C8 (Z_to_bv 64 0xd29a0);
                               C8 (Z_to_bv 64 0xca740)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xcf4d0 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xcf570 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd1cb8 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xd2998 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xd151c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x163860 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xca740 [C8 (Z_to_bv 64 0xbefb4)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x163b60 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
