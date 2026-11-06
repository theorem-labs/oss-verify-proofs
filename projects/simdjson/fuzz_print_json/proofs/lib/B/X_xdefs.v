(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_aexdefs D_aex.
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
  mkGD 0x235a0 0xd 0x20 0x1d238 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235c0 0x3 0x20 0x1732e 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x235e0 0x3 0x20 0x1a177 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23600 0x5 0x20 0x1bc83 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23620 0x5 0x20 0x17336 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23640 0x6 0x20 0x14fd1 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23660 0x4 0x20 0x16adb 0x2389c 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23ea0 0x100 0x140 0x22bc3 0x2e700 0x0 0x0 0x6b2660;
  mkGD 0x23fe0 0xdd8 0x1140 0x1b54a 0x2e700 0x0 0x0 0x6b2661;
  mkGD 0x25120 0xb8 0xe0 0x21bc4 0x2e700 0x0 0x0 0x6b2662;
  mkGD 0x25200 0x28b0 0x32e0 0x17d25 0x2e700 0x0 0x0 0x6b2663;
  mkGD 0x284e0 0x9 0x20 0x18f18 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28500 0x25 0x60 0x11eb4 0x2e700 0x0 0x0 0x6b2666;
  mkGD 0x28580 0x30 0x60 0x1733e 0x2e700 0x0 0x0 0x6b2669;
  mkGD 0x286e0 0x26b0 0x3060 0x19a32 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b740 0xc 0x20 0x18f20 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b760 0x30 0x60 0x1167b 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b800 0x20 0x40 0x22c17 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b840 0x100 0x140 0x207fe 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b980 0x100 0x140 0x173dd 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2e380 0xa0 0xc0 0x1fc70 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2e6c0 0x1 0x20 0x1fc9a 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2e6e0 0x1 0x20 0x1f42d 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x171720 0x40 0x60 0x1b56d 0x2e700 0x0 0x0 0x6b2664;
  mkGD 0x171780 0x18 0x40 0x12736 0x2e700 0x0 0x0 0x6b2665;
  mkGD 0x1717e0 0x60 0x80 0x1fbf6 0x2e700 0x0 0x0 0x6b2667;
  mkGD 0x171860 0x18 0x40 0x14457 0x2e700 0x0 0x0 0x6b2668;
  mkGD 0x17b6a0 0x300 0x3c0 0x22bf8 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b24c0 0x30 0x60 0x158d4 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b2520 0x8 0x20 0x14fd9 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b2540 0x8 0x20 0x1c70f 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b2560 0x8 0x20 0x224e4 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b2580 0x10 0x20 0x1737e 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b25a0 0x8 0x20 0x13d50 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b25c0 0x8 0x20 0x12766 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b25e0 0x30 0x60 0x1fc2f 0x2e700 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6b2640 0x8 0x20 0x1d240 0x2e700 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 37%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc6b4%Z (only parsing).  Notation XS1_HI := 0x7fffdce0%Z (only parsing).
Notation XS2_LO := 0x800262e4%Z (only parsing).  Notation XS2_HI := 0x800278ea%Z (only parsing).
Notation XS3_LO := 0x800ce498%Z (only parsing).  Notation XS3_HI := 0x800ce4cc%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x6b2660 <=? o) && (o <? 0x6b266a)).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6b2660 \/ gd_odr g = 0x6b2661 \/ gd_odr g = 0x6b2662 \/ gd_odr g = 0x6b2663 \/ gd_odr g = 0x6b2664 \/ gd_odr g = 0x6b2665 \/ gd_odr g = 0x6b2666 \/ gd_odr g = 0x6b2667 \/ gd_odr g = 0x6b2668 \/ gd_odr g = 0x6b2669)
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
  [(0x6b3fc0, 0x6b3fc4); (0x6d42d8, 0x6d42dc); (0x6d42f8, 0x6d4300);
   (0x6d4870, 0x6d4878); (0x17bbf8, 0x17bc00); (0x17bce8, 0x17bcf0); (0x17bcf0, 0x17c788); (0x17c7d0, 0x17c7d1);
   (0x6b2660, 0x6b2661); (0x6b2661, 0x6b266a)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0x6b3fc0 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells bsegs m 0x6d42d8 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0x6d42f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells bsegs m 0x6d4870 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x17bbf8 [C8 (Z_to_bv 64 0x17bb10)]
  /\ rw_cells bsegs m 0x17bce8 [C8 (Z_to_bv 64 0x17bc00)]
  /\ stdin_file m /\ rw_cells bsegs m 0x17bdd8 [C8 (Z_to_bv 64 0x17bcf0)]
  /\ gds_at m 0x17be10 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x17c780 [C8 v])
  /\ rw_cells bsegs m 0x17c7d0 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : byte, rw_cells bsegs m 0x6b2660 [C1 o1] /\ rw_cells bsegs m 0x6b2661 [C1 o2] /\ rw_cells bsegs m 0x6b2662 [C1 o3] /\ rw_cells bsegs m 0x6b2663 [C1 o4] /\ rw_cells bsegs m 0x6b2664 [C1 o5] /\ rw_cells bsegs m 0x6b2665 [C1 o6] /\ rw_cells bsegs m 0x6b2666 [C1 o7] /\ rw_cells bsegs m 0x6b2667 [C1 o8] /\ rw_cells bsegs m 0x6b2668 [C1 o9] /\ rw_cells bsegs m 0x6b2669 [C1 o10]).

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
  intros m m' (TID & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_CORE_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_CORE_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x6b3fc0 0x6b3fc4); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x6d42d8 0x6d42dc); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6d42f8 0x6d4300); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x6d4870 0x6d4878); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x17bbf8 0x17bc00); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x17bce8 0x17bcf0); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x17bcf0 0x17c788); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x17bcf0 0x17c788); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x17bcf0 0x17c788); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x17bcf0 0x17c788); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x17c7d0 0x17c7d1); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10.
  split; [apply (R 0x6b2660 0x6b2661); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  apply (R 0x6b2661 0x6b266a); [cbn; tauto| lia| cbn; lia| exact OC10].
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
            xl_core_loc := XENV_coreA_loc; xl_core_sep := aex_core_sep; xl_aex_in := _; xl_core_in := _; xl_libc := _ |}.
  - intros m. unfold XENVA. tauto.
  - intros x Hx. apply in_ranges_app_r. exact Hx.
  - intros x Hx. apply in_ranges_app_l. exact Hx.
  - intros m (TID & EXL & LIBC & _). exact LIBC.
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
  ro_cells bsegs m 0x171180 [C8 (Z_to_bv 64 0xba438); C8 (Z_to_bv 64 0x5af9c)]
  /\ ro_cells bsegs m 0x177d10 [C8 (Z_to_bv 64 0x171190); C8 (Z_to_bv 64 0x171180)]
  /\ ro_cells bsegs m 0x176f20 [C8 (Z_to_bv 64 0x158304); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells bsegs m 0x178d60 [C8 d])
  /\ ro_cells bsegs m 0x177c18 [C8 (Z_to_bv 64 0x17be10); C8 (Z_to_bv 64 0x17c750)]
  /\ ro_cells bsegs m 0x176f30 [C8 (Z_to_bv 64 0x20f8e0)]
  /\ ro_cells bsegs m 0x176f40 [C8 (Z_to_bv 64 0x211968); C8 (Z_to_bv 64 0x17d638); C8 (Z_to_bv 64 0x17fe38);
                               C8 (Z_to_bv 64 0x180b28); C8 (Z_to_bv 64 0x180b30); C8 (Z_to_bv 64 0x180b20);
                               C8 (Z_to_bv 64 0x178f60)]
  /\ ro_cells bsegs m 0x17d650 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x17d6f0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bsegs m 0x17fe38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0x180b18 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x17f69c [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x2119e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells bsegs m 0x178f60 [C8 (Z_to_bv 64 0x169974)]
  /\ ro_cells bsegs m 0x211ce0 [C1 (Z_to_bv 8 0)]
  /\ stk bsegs m XS1_LO XS1_HI /\ stk bsegs m XS2_LO XS2_HI /\ stk bsegs m XS3_LO XS3_HI.
