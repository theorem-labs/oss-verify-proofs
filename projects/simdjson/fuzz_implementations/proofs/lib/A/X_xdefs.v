(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx FX_Exit I_iodefs X_aexdefs D_aex Imp_ios_defsA.
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
  mkGD 0x23880 0x7 0x20 0x1dec2 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0xd 0x20 0x20ba3 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238c0 0x6 0x20 0x1be6d 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238e0 0x4 0x20 0x11677 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b00 0x11 0x40 0x173ca 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b40 0x8 0x20 0x21fdd 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b60 0xa 0x20 0x1167e 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23b80 0x10 0x20 0x1b6f7 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ba0 0x6 0x20 0x21fe5 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23bc0 0x8 0x20 0x1ff9e 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23be0 0xf 0x20 0x1dec7 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24200 0x12 0x40 0x1dec2 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24240 0x38 0x60 0x20ba3 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x242a0 0x43 0x80 0x22ee6 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24320 0x9d 0xc0 0x15058 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x243e0 0x51 0x80 0x13d86 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24460 0x2d 0x60 0x1eff4 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x244c0 0x49 0x80 0x19c40 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24540 0x49 0x80 0x1be6d 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x245c0 0x49 0x80 0x11677 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24640 0x2d 0x60 0x173ca 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x246a0 0x49 0x80 0x21fdd 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24720 0x29 0x60 0x1167e 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24780 0x1d 0x40 0x1b6f7 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x247c0 0x15 0x40 0x21fe5 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24800 0x60 0x80 0x1ff9e 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24880 0x37 0x60 0x1dec7 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x248e0 0xac 0xe0 0x1aeb8 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x249c0 0x43 0x80 0x1d596 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24a40 0x61 0xa0 0x11ebf 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ae0 0x5f 0x80 0x11ec7 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24b60 0x48 0x80 0x190b6 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24be0 0x22 0x60 0x1b72c 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24c40 0x33 0x60 0x1505f 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ca0 0x33 0x60 0x144a4 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24d00 0x6c 0xa0 0x13d8d 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24da0 0x4d 0x80 0x17db8 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24e20 0x61 0xa0 0x10bfe 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24ec0 0xcf 0x100 0x190be 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x24fc0 0x84 0xc0 0x1853f 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25080 0xb1 0xe0 0x10c06 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25160 0x3f 0x60 0x13d95 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x251c0 0x41 0x80 0x11686 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x25240 0x4e 0x80 0x12796 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x252c0 0x100 0x140 0x22eed 0x2fec0 0x0 0x0 0x6adf81;
  mkGD 0x25400 0xdd8 0x1140 0x1b734 0x2fec0 0x0 0x0 0x6adf82;
  mkGD 0x26540 0xb8 0xe0 0x21fed 0x2fec0 0x0 0x0 0x6adf83;
  mkGD 0x26620 0x28b0 0x32e0 0x17dc0 0x2fec0 0x0 0x0 0x6adf84;
  mkGD 0x29900 0x9 0x20 0x1ffa6 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x29920 0x300 0x3c0 0x22f22 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x29ce0 0x25 0x60 0x11f14 0x2fec0 0x0 0x0 0x6adf87;
  mkGD 0x29d60 0x30 0x60 0x173d1 0x2fec0 0x0 0x0 0x6adf8a;
  mkGD 0x29ec0 0x26b0 0x3060 0x19c47 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cf20 0xc 0x20 0x190c6 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cf40 0x30 0x60 0x1d59e 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2cfe0 0x20 0x40 0x1aec0 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2d020 0x100 0x140 0x20baa 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2d160 0x100 0x140 0x17470 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2fb60 0xa0 0xc0 0x20028 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2fea0 0x1 0x20 0x20052 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x16c060 0x210 0x2a0 0x1a3aa 0x2fec0 0x0 0x0 0x6adf80;
  mkGD 0x16c300 0x40 0x60 0x1b757 0x2fec0 0x0 0x0 0x6adf85;
  mkGD 0x16c360 0x18 0x40 0x1279e 0x2fec0 0x0 0x0 0x6adf86;
  mkGD 0x16c3c0 0x60 0x80 0x1ffae 0x2fec0 0x0 0x0 0x6adf88;
  mkGD 0x16c440 0x18 0x40 0x144ac 0x2fec0 0x0 0x0 0x6adf89;
  mkGD 0x6add40 0x18 0x40 0x15026 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6add80 0x8 0x20 0x19bfb 0x23c00 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6adda0 0x30 0x60 0x15978 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6ade00 0x8 0x20 0x15067 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6ade20 0x1 0x20 0x11ecf 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6ade40 0x8 0x20 0x1f7d0 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6ade60 0x8 0x20 0x1c970 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6ade80 0x8 0x20 0x22888 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6adea0 0x10 0x20 0x17411 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6adec0 0x8 0x20 0x13d9d 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6adee0 0x8 0x20 0x127ce 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6adf00 0x30 0x60 0x1ffe7 0x2fec0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6adf60 0x8 0x20 0x1d5a6 0x2fec0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 78%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc710%Z (only parsing).  Notation XS1_HI := 0x7fffdfd8%Z (only parsing).
Notation XS2_LO := 0x8002580c%Z (only parsing).  Notation XS2_HI := 0x80027000%Z (only parsing).
Notation XS3_LO := 0x800cdba8%Z (only parsing).  Notation XS3_HI := 0x800cdbf0%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x6adf80 <=? o) && (o <? 0x6adf8b)).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6adf80 \/ gd_odr g = 0x6adf81 \/ gd_odr g = 0x6adf82 \/ gd_odr g = 0x6adf83 \/ gd_odr g = 0x6adf84 \/ gd_odr g = 0x6adf85 \/ gd_odr g = 0x6adf86 \/ gd_odr g = 0x6adf87 \/ gd_odr g = 0x6adf88 \/ gd_odr g = 0x6adf89 \/ gd_odr g = 0x6adf8a)
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
  [(0x6b0080, 0x6b0084); (0x6d0398, 0x6d039c); (0x6d03b8, 0x6d03c0);
   (0x6d0928, 0x6d0938); (0x176a70, 0x176a78); (0x176c50, 0x176c58); (0x176a78, 0x176b68); (0x176c58, 0x178008); (0x178050, 0x178051);
   (0x6adf80, 0x6adf81); (0x6adf81, 0x6adf8b);
   (0x1768d0, 0x1768d8); (0x1768e0, 0x1768f0);
   (0x6ae1c8, 0x6ae968)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x6b0080 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells asegs m 0x6d0398 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x6d03b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells asegs m 0x6d0928 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x176a70 [C8 (Z_to_bv 64 0x176988)]
  /\ rw_cells asegs m 0x176c50 [C8 (Z_to_bv 64 0x176b68)]
  /\ stdin_file m /\ rw_cells asegs m 0x176b60 [C8 (Z_to_bv 64 0x176a78)]
  /\ gds_at m 0x176c80 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0x178000 [C8 v])
  /\ rw_cells asegs m 0x178050 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells asegs m 0x6adf80 [C1 o1] /\ rw_cells asegs m 0x6adf81 [C1 o2] /\ rw_cells asegs m 0x6adf82 [C1 o3] /\ rw_cells asegs m 0x6adf83 [C1 o4] /\ rw_cells asegs m 0x6adf84 [C1 o5] /\ rw_cells asegs m 0x6adf85 [C1 o6] /\ rw_cells asegs m 0x6adf86 [C1 o7] /\ rw_cells asegs m 0x6adf87 [C1 o8] /\ rw_cells asegs m 0x6adf88 [C1 o9] /\ rw_cells asegs m 0x6adf89 [C1 o10] /\ rw_cells asegs m 0x6adf8a [C1 o11])
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
  - apply (ro_cells_agree asegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
  - apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Lemma XENV_coreA_loc : fp_local XENV_CORE_FPA XENV_coreA.
Proof.
  intros m m' (TID & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & XD & IOB) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_CORE_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_CORE_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x6b0080 0x6b0084); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6d0398 0x6d039c); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6d03b8 0x6d03c0); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x6d0928 0x6d0938); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x176a70 0x176a78); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x176c50 0x176c58); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x176a78 0x176b68); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x176a78 0x176b68); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x176c58 0x178008); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x176c58 0x178008); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x178050 0x178051); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  split; cycle 1.
  { split. { destruct XD as [X1 X2]. split; [apply (R 0x1768d0 (0x1768d0 + 8)); [cbn; tauto| lia| cbn; lia| exact X1]
                                  | apply (R 0x1768e0 (0x1768e0 + 16)); [cbn; tauto| lia| cbn; lia| exact X2]]. }
    apply (R 0x6ae1c8 0x6ae968); [cbn; tauto| unfold IOS; lia| unfold IOS; rewrite ios_cells_size; cbn; lia| exact IOB]. }
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
  split; [apply (R 0x6adf80 0x6adf81); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  split; [apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC10]|].
  apply (R 0x6adf81 0x6adf8b); [cbn; tauto| lia| cbn; lia| exact OC11].
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
  ro_cells asegs m 0x16bc60 [C8 (Z_to_bv 64 0xbdf28); C8 (Z_to_bv 64 0x5db40)]
  /\ ro_cells asegs m 0x172f68 [C8 (Z_to_bv 64 0x16bc70); C8 (Z_to_bv 64 0x16bc60)]
  /\ ro_cells asegs m 0x172118 [C8 (Z_to_bv 64 0x1528c4); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells asegs m 0x173fa8 [C8 d])
  /\ ro_cells asegs m 0x172e30 [C8 (Z_to_bv 64 0x176c80); C8 (Z_to_bv 64 0x178000)]
  /\ ro_cells asegs m 0x172128 [C8 (Z_to_bv 64 0x20b160)]
  /\ ro_cells asegs m 0x172138 [C8 (Z_to_bv 64 0x20d1e8); C8 (Z_to_bv 64 0x178eb8); C8 (Z_to_bv 64 0x17b6b8);
                               C8 (Z_to_bv 64 0x17c3a8); C8 (Z_to_bv 64 0x17c3b0); C8 (Z_to_bv 64 0x17c3a0);
                               C8 (Z_to_bv 64 0x1741a8)]
  /\ ro_cells asegs m 0x178ed0 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x178f70 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x17b6b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x17c398 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x17af1c [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x20d260 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells asegs m 0x1741a8 [C8 (Z_to_bv 64 0x1644d4)]
  /\ ro_cells asegs m 0x20d560 [C1 (Z_to_bv 8 0)]
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
