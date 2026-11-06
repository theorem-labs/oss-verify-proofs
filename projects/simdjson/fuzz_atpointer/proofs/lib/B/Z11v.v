(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Z81 D_defs D_kit Z82 D_clx Z8u Zbv Z11k D_aex.
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
  mkGD 0x23060 0x7 0x20 0x18c5b 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23080 0xd 0x20 0x1a9ca 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230a0 0x5 0x20 0x168d1 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0x14 0x40 0x1e83e 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23100 0x4 0x20 0x14e37 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23120 0x2 0x20 0x10b68 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23140 0x2 0x20 0x1f007 0x23160 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23760 0x100 0x140 0x226c3 0x2aea0 0x0 0x0 0x6530e0;
  mkGD 0x238a0 0xdd8 0x1140 0x1b1ce 0x2aea0 0x0 0x0 0x6530e1;
  mkGD 0x249e0 0xb8 0xe0 0x21796 0x2aea0 0x0 0x0 0x6530e2;
  mkGD 0x24ac0 0x28b0 0x32e0 0x17a6c 0x2aea0 0x0 0x0 0x6530e3;
  mkGD 0x27da0 0x9 0x20 0x18c63 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x27dc0 0x25 0x60 0x11dc0 0x2aea0 0x0 0x0 0x6530e6;
  mkGD 0x27e40 0x30 0x60 0x170d7 0x2aea0 0x0 0x0 0x6530e9;
  mkGD 0x27ee0 0xc 0x20 0x18c6b 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x27f00 0x30 0x60 0x11591 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x27fa0 0x20 0x40 0x22717 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x27fe0 0x100 0x140 0x203fb 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28120 0x100 0x140 0x17176 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2ab20 0xa0 0xc0 0x1f880 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2ae60 0x1 0x20 0x1f8aa 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2ae80 0x1 0x20 0x1f00f 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x1146e0 0x40 0x60 0x1b1f1 0x2aea0 0x0 0x0 0x6530e4;
  mkGD 0x114740 0x18 0x40 0x12638 0x2aea0 0x0 0x0 0x6530e5;
  mkGD 0x1147a0 0x60 0x80 0x1f806 0x2aea0 0x0 0x0 0x6530e7;
  mkGD 0x114820 0x18 0x40 0x14306 0x2aea0 0x0 0x0 0x6530e8;
  mkGD 0x11c1e0 0x300 0x3c0 0x226f8 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x652f40 0x30 0x60 0x1572a 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x652fa0 0x8 0x20 0x14e3f 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x652fc0 0x8 0x20 0x1c351 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x652fe0 0x8 0x20 0x2204e 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x653000 0x10 0x20 0x17117 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x653020 0x8 0x20 0x13c11 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x653040 0x8 0x20 0x12668 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x653060 0x30 0x60 0x1f83f 0x2aea0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x6530c0 0x8 0x20 0x1ce5d 0x2aea0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 36%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc60c%Z (only parsing).  Notation XS1_HI := 0x7fffd5d4%Z (only parsing).
Notation XS2_LO := 0x8001a8dc%Z (only parsing).  Notation XS2_HI := 0x8001ba3c%Z (only parsing).
Notation XS3_LO := 0x800c25e8%Z (only parsing).  Notation XS3_HI := 0x800c261c%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x6530e0 <=? o) && (o <? 0x6530ea)).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x6530e0 \/ gd_odr g = 0x6530e1 \/ gd_odr g = 0x6530e2 \/ gd_odr g = 0x6530e3 \/ gd_odr g = 0x6530e4 \/ gd_odr g = 0x6530e5 \/ gd_odr g = 0x6530e6 \/ gd_odr g = 0x6530e7 \/ gd_odr g = 0x6530e8 \/ gd_odr g = 0x6530e9)
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
  [(0x653b88, 0x653b8c); (0x673ea0, 0x673ea4); (0x673ec0, 0x673ec8);
   (0x674328, 0x674330); (0x11c6d0, 0x11c6d8); (0x11c7c0, 0x11c7c8); (0x11c7c8, 0x11d208); (0x11d250, 0x11d251);
   (0x6530e0, 0x6530e1); (0x6530e1, 0x6530ea)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0x653b88 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells bsegs m 0x673ea0 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0x673ec0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells bsegs m 0x674328 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x11c6d0 [C8 (Z_to_bv 64 0x11c5e8)]
  /\ rw_cells bsegs m 0x11c7c0 [C8 (Z_to_bv 64 0x11c6d8)]
  /\ stdin_file m /\ rw_cells bsegs m 0x11c8b0 [C8 (Z_to_bv 64 0x11c7c8)]
  /\ gds_at m 0x11c8e0 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x11d200 [C8 v])
  /\ rw_cells bsegs m 0x11d250 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : byte, rw_cells bsegs m 0x6530e0 [C1 o1] /\ rw_cells bsegs m 0x6530e1 [C1 o2] /\ rw_cells bsegs m 0x6530e2 [C1 o3] /\ rw_cells bsegs m 0x6530e3 [C1 o4] /\ rw_cells bsegs m 0x6530e4 [C1 o5] /\ rw_cells bsegs m 0x6530e5 [C1 o6] /\ rw_cells bsegs m 0x6530e6 [C1 o7] /\ rw_cells bsegs m 0x6530e7 [C1 o8] /\ rw_cells bsegs m 0x6530e8 [C1 o9] /\ rw_cells bsegs m 0x6530e9 [C1 o10]).

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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x653b88 0x653b8c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x673ea0 0x673ea4); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x673ec0 0x673ec8); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x674328 0x674330); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x11c6d0 0x11c6d8); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x11c7c0 0x11c7c8); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x11c7c8 0x11d208); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x11c7c8 0x11d208); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x11c7c8 0x11d208); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x11c7c8 0x11d208); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x11d250 0x11d251); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10.
  split; [apply (R 0x6530e0 0x6530e1); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  apply (R 0x6530e1 0x6530ea); [cbn; tauto| lia| cbn; lia| exact OC10].
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
  ro_cells bsegs m 0x1142d8 [C8 (Z_to_bv 64 0x9b158); C8 (Z_to_bv 64 0x44880)]
  /\ ro_cells bsegs m 0x1188e0 [C8 (Z_to_bv 64 0x1142e8); C8 (Z_to_bv 64 0x1142d8)]
  /\ ro_cells bsegs m 0x117b30 [C8 (Z_to_bv 64 0xff588); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells bsegs m 0x119920 [C8 d])
  /\ ro_cells bsegs m 0x118820 [C8 (Z_to_bv 64 0x11c8e0); C8 (Z_to_bv 64 0x11d1e0)]
  /\ ro_cells bsegs m 0x117b40 [C8 (Z_to_bv 64 0x1b0360)]
  /\ ro_cells bsegs m 0x117b50 [C8 (Z_to_bv 64 0x1b23e8); C8 (Z_to_bv 64 0x11e0b8); C8 (Z_to_bv 64 0x1208b8);
                               C8 (Z_to_bv 64 0x1215a8); C8 (Z_to_bv 64 0x1215b0); C8 (Z_to_bv 64 0x1215a0);
                               C8 (Z_to_bv 64 0x119aa8)]
  /\ ro_cells bsegs m 0x11e0d0 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x11e170 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bsegs m 0x1208b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0x121598 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x12011c [C1 (Z_to_bv 8 1)]
  /\ ro_cells bsegs m 0x1b2460 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells bsegs m 0x119aa8 [C8 (Z_to_bv 64 0x10dd6c)]
  /\ ro_cells bsegs m 0x1b2760 [C1 (Z_to_bv 8 0)]
  /\ stk bsegs m XS1_LO XS1_HI /\ stk bsegs m XS2_LO XS2_HI /\ stk bsegs m XS3_LO XS3_HI.
