(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_aexdefs D_aex.
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
  mkGD 0x230a0 0x7 0x20 0x1d83e 0x232a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230c0 0xd 0x20 0x2043d 0x232a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x230e0 0x5 0x20 0x11596 0x232a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23100 0x14 0x40 0x170b2 0x232a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23140 0x4 0x20 0x21831 0x232a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x23160 0x100 0x140 0x20444 0x232a0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x238a0 0x100 0x140 0x226e1 0x2b4c0 0x0 0x0 0x647da0;
  mkGD 0x239e0 0x100 0x140 0x17a4e 0x2b4c0 0x0 0x0 0x647da1;
  mkGD 0x23b20 0xdd8 0x1140 0x1b204 0x2b4c0 0x0 0x0 0x647da2;
  mkGD 0x24c60 0xb8 0xe0 0x21839 0x2b4c0 0x0 0x0 0x647da3;
  mkGD 0x24d40 0x28b0 0x32e0 0x17a7b 0x2b4c0 0x0 0x0 0x647da4;
  mkGD 0x28020 0x9 0x20 0x1f840 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28040 0x300 0x3c0 0x22716 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28400 0x25 0x60 0x11dc4 0x2b4c0 0x0 0x0 0x647da7;
  mkGD 0x28480 0x30 0x60 0x170b9 0x2b4c0 0x0 0x0 0x647daa;
  mkGD 0x28520 0xc 0x20 0x18cee 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28540 0x30 0x60 0x1cf43 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x285e0 0x20 0x40 0x1a9d3 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28620 0x100 0x140 0x20496 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x28760 0x100 0x140 0x17158 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b160 0xa0 0xc0 0x1f8c2 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x2b4a0 0x1 0x20 0x1f8ec 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x109780 0x40 0x60 0x1b227 0x2b4c0 0x0 0x0 0x647da5;
  mkGD 0x1097e0 0x18 0x40 0x1263c 0x2b4c0 0x0 0x0 0x647da6;
  mkGD 0x109840 0x60 0x80 0x1f848 0x2b4c0 0x0 0x0 0x647da8;
  mkGD 0x1098c0 0x18 0x40 0x142f1 0x2b4c0 0x0 0x0 0x647da9;
  mkGD 0x647c00 0x30 0x60 0x1570d 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647c60 0x8 0x20 0x14e22 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647c80 0x8 0x20 0x1c3ff 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647ca0 0x8 0x20 0x2206c 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647cc0 0x10 0x20 0x170f9 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647ce0 0x8 0x20 0x13bfc 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647d00 0x8 0x20 0x1266c 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647d20 0x30 0x60 0x1f881 0x2b4c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x647d80 0x8 0x20 0x1cf4b 0x2b4c0 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 35%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc614%Z (only parsing).  Notation XS1_HI := 0x7fffd698%Z (only parsing).
Notation XS2_LO := 0x800192f0%Z (only parsing).  Notation XS2_HI := 0x8001a3d2%Z (only parsing).
Notation XS3_LO := 0x800c0f80%Z (only parsing).  Notation XS3_HI := 0x800c0fb4%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((0x647da0 <=? o) && (o <? 0x647dab)).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x647da0 \/ gd_odr g = 0x647da1 \/ gd_odr g = 0x647da2 \/ gd_odr g = 0x647da3 \/ gd_odr g = 0x647da4 \/ gd_odr g = 0x647da5 \/ gd_odr g = 0x647da6 \/ gd_odr g = 0x647da7 \/ gd_odr g = 0x647da8 \/ gd_odr g = 0x647da9 \/ gd_odr g = 0x647daa)
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
  [(0x648848, 0x64884c); (0x668b60, 0x668b64); (0x668b80, 0x668b88);
   (0x668fe8, 0x668ff0); (0x1113c0, 0x1113c8); (0x1114b0, 0x1114b8); (0x1114b8, 0x111ec8); (0x111f10, 0x111f11);
   (0x647da0, 0x647da1); (0x647da1, 0x647dab)].
Definition XENV_FPA : list (Z * Z) := XENV_CORE_FPA ++ AEX_FPA.

Definition XENV_coreA (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x648848 [C4 (Z_to_bv 64 tid)])
  /\ rw_cells asegs m 0x668b60 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x668b80 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells asegs m 0x668fe8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x1113c0 [C8 (Z_to_bv 64 0x1112d8)]
  /\ rw_cells asegs m 0x1114b0 [C8 (Z_to_bv 64 0x1113c8)]
  /\ stdin_file m /\ rw_cells asegs m 0x1115a0 [C8 (Z_to_bv 64 0x1114b8)]
  /\ gds_at m 0x1115d0 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0x111ec0 [C8 v])
  /\ rw_cells asegs m 0x111f10 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells asegs m 0x647da0 [C1 o1] /\ rw_cells asegs m 0x647da1 [C1 o2] /\ rw_cells asegs m 0x647da2 [C1 o3] /\ rw_cells asegs m 0x647da3 [C1 o4] /\ rw_cells asegs m 0x647da4 [C1 o5] /\ rw_cells asegs m 0x647da5 [C1 o6] /\ rw_cells asegs m 0x647da6 [C1 o7] /\ rw_cells asegs m 0x647da7 [C1 o8] /\ rw_cells asegs m 0x647da8 [C1 o9] /\ rw_cells asegs m 0x647da9 [C1 o10] /\ rw_cells asegs m 0x647daa [C1 o11]).

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
  intros m m' (TID & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_CORE_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells asegs m A cs -> rw_cells asegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_CORE_FPA lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x648848 0x64884c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x668b60 0x668b64); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x668b80 0x668b88); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0x668fe8 0x668ff0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x1113c0 0x1113c8); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x1114b0 0x1114b8); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x1114b8 0x111ec8); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x1114b8 0x111ec8); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; apply AG; apply (in_XENV_CORE_FPA 0x1114b8 0x111ec8); [cbn; tauto|];
          rewrite asan_gds_length in Ha; cbn in Ha; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x1114b8 0x111ec8); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x111f10 0x111f11); [cbn; tauto| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
  split; [apply (R 0x647da0 0x647da1); [cbn; tauto| lia| cbn; lia| exact OC1]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC2]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC3]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC4]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC5]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC6]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC7]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC8]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC9]|].
  split; [apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC10]|].
  apply (R 0x647da1 0x647dab); [cbn; tauto| lia| cbn; lia| exact OC11].
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
  ro_cells asegs m 0x109378 [C8 (Z_to_bv 64 0x9beec); C8 (Z_to_bv 64 0x44764)]
  /\ ro_cells asegs m 0x10d998 [C8 (Z_to_bv 64 0x109388); C8 (Z_to_bv 64 0x109378)]
  /\ ro_cells asegs m 0x10cbd0 [C8 (Z_to_bv 64 0xf4628); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells asegs m 0x10e9d8 [C8 d])
  /\ ro_cells asegs m 0x10d8d8 [C8 (Z_to_bv 64 0x1115d0); C8 (Z_to_bv 64 0x111e90)]
  /\ ro_cells asegs m 0x10cbe0 [C8 (Z_to_bv 64 0x1a5020)]
  /\ ro_cells asegs m 0x10cbf0 [C8 (Z_to_bv 64 0x1a70a8); C8 (Z_to_bv 64 0x112d78); C8 (Z_to_bv 64 0x115578);
                               C8 (Z_to_bv 64 0x116268); C8 (Z_to_bv 64 0x116270); C8 (Z_to_bv 64 0x116260);
                               C8 (Z_to_bv 64 0x10eb60)]
  /\ ro_cells asegs m 0x112d90 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0x112e30 [C8 (Z_to_bv 64 0)]
  /\ ro_cells asegs m 0x115578 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x116258 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x114ddc [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x1a7120 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells asegs m 0x10eb60 [C8 (Z_to_bv 64 0x102e0c)]
  /\ ro_cells asegs m 0x1a7420 [C1 (Z_to_bv 8 0)]
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
