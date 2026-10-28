(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx FX_Exit I_iodefs X_aexdefs D_aex Imp_ios_defsA.
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
  | g :: gs' => ro_cells bsegs m a (gd_cells g) /\ gds_at m (a + 64) gs'
  end.

Definition ODR_NONE : Z := 0xffffffffffffffff.

Definition asan_gds : list gdesc := [
  mkGD 0x23980 0x7 0x20 0x1dd50 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239a0 0xd 0x20 0x1aea4 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239c0 0x3 0x20 0x1a2ee 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x239e0 0x3 0x20 0x1be42 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a00 0x5 0x20 0x173e0 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a20 0x5 0x20 0x1507c 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a40 0x6 0x20 0x19b92 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23a60 0x4 0x20 0x21562 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23c80 0x11 0x40 0x173e8 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23cc0 0x8 0x20 0x1a2f6 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ce0 0xa 0x20 0x1d424 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d00 0x10 0x20 0x19b9a 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d20 0x6 0x20 0x1e789 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d40 0x8 0x20 0x1f666 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23d60 0xf 0x20 0x127b2 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24380 0x12 0x40 0x1dd50 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243c0 0x38 0x60 0x20b3a 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24420 0x43 0x80 0x22fa8 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244a0 0x9d 0xc0 0x15084 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24560 0x51 0x80 0x13daa 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245e0 0x2d 0x60 0x1ee8a 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24640 0x49 0x80 0x19ba2 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246c0 0x49 0x80 0x1be4a 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24740 0x49 0x80 0x1168b 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247c0 0x2d 0x60 0x173f0 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24820 0x49 0x80 0x21f0f 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248a0 0x29 0x60 0x11692 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24900 0x1d 0x40 0x1b6f9 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24940 0x15 0x40 0x21f17 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24980 0x60 0x80 0x1febd 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a00 0x37 0x60 0x1dd55 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a60 0xac 0xe0 0x1aeac 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b40 0x43 0x80 0x1d42c 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24bc0 0x61 0xa0 0x11edb 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24c60 0x5f 0x80 0x11ee3 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ce0 0x48 0x80 0x19000 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24d60 0x22 0x60 0x1b701 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24dc0 0x33 0x60 0x1508b 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24e20 0x33 0x60 0x144c8 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24e80 0x6c 0xa0 0x13db1 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24f20 0x4d 0x80 0x17dde 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24fa0 0x61 0xa0 0x10beb 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25040 0xcf 0x100 0x19008 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25140 0x84 0xc0 0x18565 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25200 0xb1 0xe0 0x10bf3 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x252e0 0x3f 0x60 0x13db9 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25340 0x41 0x80 0x1169a 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x253c0 0x4e 0x80 0x127ba 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25440 0x100 0x140 0x22faf 0x2fca0 0x0 0x0 0x6bc241;
  mkGD 0x25580 0xdd8 0x1140 0x1b709 0x2fca0 0x0 0x0 0x6bc242;
  mkGD 0x266c0 0xb8 0xe0 0x21f1f 0x2fca0 0x0 0x0 0x6bc243;
  mkGD 0x267a0 0x28b0 0x32e0 0x17de6 0x2fca0 0x0 0x0 0x6bc244;
  mkGD 0x29a80 0x9 0x20 0x19010 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x29aa0 0x25 0x60 0x11f30 0x2fca0 0x0 0x0 0x6bc247;
  mkGD 0x29b20 0x30 0x60 0x173f7 0x2fca0 0x0 0x0 0x6bc24a;
  mkGD 0x29c80 0x26b0 0x3060 0x19ba9 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cce0 0xc 0x20 0x19018 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cd00 0x30 0x60 0x116a2 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cda0 0x20 0x40 0x23003 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cde0 0x100 0x140 0x20b41 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cf20 0x100 0x140 0x17496 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2f920 0xa0 0xc0 0x1ff3f 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2fc60 0x1 0x20 0x1ff69 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2fc80 0x1 0x20 0x1f6c6 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x179de0 0x210 0x2a0 0x1a396 0x2fca0 0x0 0x0 0x6bc240;
  mkGD 0x17a080 0x40 0x60 0x1b72c 0x2fca0 0x0 0x0 0x6bc245;
  mkGD 0x17a0e0 0x18 0x40 0x127c2 0x2fca0 0x0 0x0 0x6bc246;
  mkGD 0x17a140 0x60 0x80 0x1fec5 0x2fca0 0x0 0x0 0x6bc248;
  mkGD 0x17a1c0 0x18 0x40 0x144d0 0x2fca0 0x0 0x0 0x6bc249;
  mkGD 0x184680 0x300 0x3c0 0x22fe4 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc000 0x18 0x40 0x1504a 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc040 0x8 0x20 0x19b4d 0x23d80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc060 0x30 0x60 0x1598e 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc0c0 0x8 0x20 0x15093 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc0e0 0x1 0x20 0x11eeb 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc100 0x8 0x20 0x1f66e 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc120 0x8 0x20 0x1c8d5 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc140 0x8 0x20 0x22897 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc160 0x10 0x20 0x17437 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc180 0x8 0x20 0x13dc1 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc1a0 0x8 0x20 0x127f2 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc1c0 0x30 0x60 0x1fefe 0x2fca0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6bc220 0x8 0x20 0x1d434 0x2fca0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 83%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc730%Z (only parsing).  Notation XS1_HI := 0x7fffdf94%Z (only parsing).
Notation XS2_LO := 0x800273bc%Z (only parsing).  Notation XS2_HI := 0x80028c56%Z (only parsing).
Notation XS3_LO := 0x800cf800%Z (only parsing).  Notation XS3_HI := 0x800cf848%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x6bc240 <=? o) && (o <? 0x6bc24b)).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6bc240 \/ gd_odr g = 0x6bc241 \/ gd_odr g = 0x6bc242 \/ gd_odr g = 0x6bc243 \/ gd_odr g = 0x6bc244 \/ gd_odr g = 0x6bc245 \/ gd_odr g = 0x6bc246 \/ gd_odr g = 0x6bc247 \/ gd_odr g = 0x6bc248 \/ gd_odr g = 0x6bc249 \/ gd_odr g = 0x6bc24a)
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
  [(0x6be340, 0x6be344); (0x6de658, 0x6de65c); (0x6de678, 0x6de680);
   (0x6debe8, 0x6debf8); (0x184bd8, 0x184be0); (0x184db8, 0x184dc0); (0x184be0, 0x184cd0); (0x184dc0, 0x1862c8); (0x186310, 0x186311);
   (0x6bc240, 0x6bc241); (0x6bc241, 0x6bc24b);
   (0x184668, 0x184670); (0x184a48, 0x184a58);
   (0x6bc488, 0x6bcc28)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0x6be340 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells bsegs m 0x6de658 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0x6de678 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells bsegs m 0x6debe8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x184bd8 [C8 (Z_to_bv 64 0x184af0)]
  /\ rw_cells bsegs m 0x184db8 [C8 (Z_to_bv 64 0x184cd0)]
  /\ stdin_file m /\ rw_cells bsegs m 0x184cc8 [C8 (Z_to_bv 64 0x184be0)]
  /\ gds_at m 0x184df0 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x1862c0 [C8 v])
  /\ rw_cells bsegs m 0x186310 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells bsegs m 0x6bc240 [C1 o1] /\ rw_cells bsegs m 0x6bc241 [C1 o2] /\ rw_cells bsegs m 0x6bc242 [C1 o3] /\ rw_cells bsegs m 0x6bc243 [C1 o4] /\ rw_cells bsegs m 0x6bc244 [C1 o5] /\ rw_cells bsegs m 0x6bc245 [C1 o6] /\ rw_cells bsegs m 0x6bc246 [C1 o7] /\ rw_cells bsegs m 0x6bc247 [C1 o8] /\ rw_cells bsegs m 0x6bc248 [C1 o9] /\ rw_cells bsegs m 0x6bc249 [C1 o10] /\ rw_cells bsegs m 0x6bc24a [C1 o11])
  /\ el_xdataA m
  /\ ios_block m.

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
  - apply (ro_cells_agree bsegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
  - apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Lemma XENV_coreA_loc : fp_local XENV_CORE_FPA XENV_coreA.
Proof.
  intros m m' (TID & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & XD & IOB) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_CORE_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_CORE_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x6be340 0x6be344); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6de658 0x6de65c); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6de678 0x6de680); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x6debe8 0x6debf8); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x184bd8 0x184be0); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x184db8 0x184dc0); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x184be0 0x184cd0); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x184be0 0x184cd0); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x184dc0 0x1862c8); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x184dc0 0x1862c8); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x186310 0x186311); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split; cycle 1.
  { split. { destruct XD as [X1 X2]. split; [apply (R 0x184668 (0x184668 + 8)); [cbn; tauto| lia| cbn; lia| exact X1]
                                  | apply (R 0x184a48 (0x184a48 + 16)); [cbn; tauto| lia| cbn; lia| exact X2]]. }
    apply (R 0x6bc488 0x6bcc28); [cbn; tauto| unfold IOS; lia| unfold IOS; rewrite ios_cells_size; cbn; lia| exact IOB]. }
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
  split; [apply (R 0x6bc240 0x6bc241); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  split; [apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC10]|].
  apply (R 0x6bc241 0x6bc24b); [cbn; tauto| lia| cbn; lia| exact OC11].
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
  - intros m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XD & _). exact XD.
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
  ro_cells bsegs m 0x1799e0 [C8 (Z_to_bv 64 0xbff10); C8 (Z_to_bv 64 0x5dcf4)]
  /\ ro_cells bsegs m 0x180ce8 [C8 (Z_to_bv 64 0x1799f0); C8 (Z_to_bv 64 0x1799e0)]
  /\ ro_cells bsegs m 0x17fe98 [C8 (Z_to_bv 64 0x160574); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells bsegs m 0x181d40 [C8 d])
  /\ ro_cells bsegs m 0x180bb0 [C8 (Z_to_bv 64 0x184df0); C8 (Z_to_bv 64 0x1862b0)]
  /\ ro_cells bsegs m 0x17fea8 [C8 (Z_to_bv 64 0x219420)]
  /\ ro_cells bsegs m 0x17feb8 [C8 (Z_to_bv 64 0x21b4a8); C8 (Z_to_bv 64 0x187178); C8 (Z_to_bv 64 0x189978);
                               C8 (Z_to_bv 64 0x18a668); C8 (Z_to_bv 64 0x18a670); C8 (Z_to_bv 64 0x18a660);
                               C8 (Z_to_bv 64 0x181f40)]
  /\ ro_cells bsegs m 0x187190 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x187230 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bsegs m 0x189978 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0x18a658 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x1891dc [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x21b520 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells bsegs m 0x181f40 [C8 (Z_to_bv 64 0x1721b4)]
  /\ ro_cells bsegs m 0x21b820 [C1 (Z_to_bv 8 0)]
  /\ stk bsegs m XS1_LO XS1_HI /\ stk bsegs m XS2_LO XS2_HI /\ stk bsegs m XS3_LO XS3_HI.
