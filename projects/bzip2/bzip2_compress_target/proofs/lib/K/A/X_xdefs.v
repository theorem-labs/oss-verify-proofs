(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.FX_Exit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  | g :: gs' => ro_cells bsegs m a (gd_cells g) /\ gds_at m (a + 64) gs'
  end.

Definition ODR_NONE : Z := 0xffffffffffffffff.

Definition asan_gds : list gdesc := [
  mkGD 0x20f60 0xd 0x20 0x1c1c0 0x20f03 0x0 0x0 0xffffffffffffffff;
  mkGD 0x20f80 0x17 0x40 0x1f9a4 0x20f03 0x0 0x0 0xffffffffffffffff;
  mkGD 0x20fc0 0x20 0x40 0x1e90b 0x20f03 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21000 0x19d 0x200 0x1c1c0 0x21820 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21200 0x421 0x540 0x1e90b 0x21820 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21740 0x12 0x40 0x20688 0x21820 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21780 0x37 0x60 0x13776 0x21820 0x0 0x0 0xffffffffffffffff;
  mkGD 0x217e0 0x13 0x40 0x1d164 0x21820 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21880 0x3e 0x60 0x1c1c0 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x218e0 0x24 0x60 0x1e90b 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21940 0x40 0x60 0x20688 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x219a0 0x3b 0x60 0x148e7 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21a00 0x29 0x60 0x13776 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21a60 0x4 0x20 0x1d164 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21a80 0x1a 0x40 0x1a5db 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21ac0 0xf 0x20 0x11400 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21ae0 0x12 0x40 0x1678a 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21b20 0xa 0x20 0x1f9c4 0x21b40 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21b80 0x26 0x60 0x1c1c0 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21be0 0x36 0x60 0x1e90b 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21c40 0x1c 0x40 0x20688 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21c80 0x17 0x40 0x148e7 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21cc0 0x18 0x40 0x13776 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21d00 0x22 0x60 0x1d164 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21d60 0x22 0x60 0x188b6 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21dc0 0x30 0x60 0x1a5db 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21e20 0x2c 0x60 0x11400 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21f60 0x14 0x40 0x1c1c0 0x21fc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21fa0 0x7 0x20 0x1e90b 0x21fc0 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd13e0 0x400 0x500 0x123db 0x2184d 0x0 0x0 0x608bc0;
  mkGD 0xd18e0 0x38 0x60 0x15077 0x21e80 0x0 0x0 0xffffffffffffffff;
  mkGD 0xd1940 0x800 0xa00 0x18e77 0x21ff2 0x0 0x0 0x608bc1 ].

Lemma asan_gds_length : length asan_gds = 32%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc1ec%Z (only parsing).  Notation XS1_HI := 0x7fffc3f8%Z (only parsing).
Notation XS2_LO := 0x8001227c%Z (only parsing).  Notation XS2_HI := 0x800125cc%Z (only parsing).
Notation XS3_LO := 0x800b9178%Z (only parsing).  Notation XS3_HI := 0x800b917c%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x608bc0) || (o =? 0x608bc1) || (o =? 0x608bc2).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x608bc0 \/ gd_odr g = 0x608bc1 \/ gd_odr g = 0x608bc2)
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
  [(0x609430, 0x609434); (0x629528, 0x629550); (0x629648, 0x629650); (0x629748, 0x62974c); (0x629768, 0x629770);
   (0x629bd0, 0x629bd8); (0xd2450, 0xd2458); (0xd2630, 0xd2638); (0xd2458, 0xd2548); (0xd2660, 0xd2e88); (0xd2ed0, 0xd2ed1);
   (0x608bc0, 0x608bc1); (0x608bc1, 0x608bc3); (0x629550, 0x629558); (0x629650, 0x629658); (0x608b90, 0x608b91)].

Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0x609430 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  /\ rw_cells bsegs m 0x629648 [C8 (Z_to_bv 64 0x708c4)]                                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x629748 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x629bd0 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd2450 [C8 (Z_to_bv 64 0xd2368)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd2630 [C8 (Z_to_bv 64 0xd2548)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells bsegs m 0xd2540 [C8 (Z_to_bv 64 0xd2458)]                           (* [comment removed for export] *)
  /\ gds_at m 0xd2660 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0xd2e80 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd2ed0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells bsegs m 0x608bc0 [C1 o1] /\ rw_cells bsegs m 0x608bc1 [C1 o2]
                              /\ rw_cells bsegs m 0x608bc2 [C1 o3]).                         (* [comment removed for export] *)

Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells bsegs m 0x629528 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x629540 0 0xbc6d8))
  /\ (if ph then rw_cells bsegs m 0x629550 [C8 (Z_to_bv 64 0xbc6d8)] /\ rw_cells bsegs m 0x629650 [C8 (Z_to_bv 64 0x8128c)]
      else (exists j1 : word, rw_cells bsegs m 0x629550 [C8 j1]) /\ (exists j2 : word, rw_cells bsegs m 0x629650 [C8 j2])
           /\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 0)]).

Definition XENVA_ph (ph : bool) (m : mem) : Prop := XENVC m /\ atxA ph m.
Definition XENVA : mem -> Prop := XENVA_ph false.
Definition XENVA1 : mem -> Prop := XENVA_ph true.
Definition XENVA1x (m : mem) : Prop := XENVA1 m /\ rw_cells bsegs m TR_INIT [C1 (Z_to_bv 8 0)].

Lemma XENVA1x_of : forall m, XENVA1 m -> rw_cells bsegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENVA1x m.
Proof. intros m H1 H2. exact (conj H1 H2). Qed.

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma gds_at_agree : forall gs m m' a, gds_at m a gs ->
  agree_on (fun x => a <= x < a + 64 * Z.of_nat (length gs)) m m' -> gds_at m' a gs.
Proof.
  induction gs as [|g gs IH]; intros m m' a H AG; [exact I|]. destruct H as [H1 H2]. split.
  - apply (ro_cells_agree bsegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
    cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
  - apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Local Ltac DJ := intros xd Hxd Hrd; apply in_REG_CELLS in Hrd; lia.

Lemma XENVC_loc' : forall m m', XENVC m ->
  (forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) -> XENVC m'.
Proof.
  intros m m' (TID & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> (forall x, lo <= x < hi -> ~ in_ranges REG_CELLS x) -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin HD H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. pose proof (rw_cells_bound bsegs m _ _ H). apply AG; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| apply HD; lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x609430 0x609434); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x629648 0x629650); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x629748 0x62974c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x629768 0x629770); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x629bd0 0x629bd8); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xd2450 0xd2458); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xd2630 0xd2638); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xd2458 0xd2548); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xd2458 0xd2548); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xd2660 0xd2e88); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xd2660 0xd2e88); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xd2ed0 0xd2ed1); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x608bc0 0x608bc1); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x608bc1 0x608bc3); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x608bc1 0x608bc3); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
Qed.


Lemma XENVC_loc : fp_local XENV_FPA XENVC.
Proof. intros m m' H AG. apply (XENVC_loc' m m' H). intros a Ha _. exact (AG a Ha). Qed.

Lemma atxA_loc : forall ph, fp_local XENV_FPA (atxA ph).
Proof.
  intros ph m m' ((p1 & p2 & ATX) & PH) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
  split; [exists p1, p2; apply (R 0x629528 0x629550); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x629550 0x629558); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x629650 0x629658); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x629550 0x629558); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x629650 0x629658); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x608b90 0x608b91); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x608b90 0x608b91)| apply (in_XENV_FPA 0x629528 0x629550)| apply (in_XENV_FPA 0x629550 0x629558)| apply (in_XENV_FPA 0x629650 0x629658)];
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells bsegs m 0xcc8c0 [C8 (Z_to_bv 64 0x81638); C8 (Z_to_bv 64 0x31788)]     (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcdb00 [C8 (Z_to_bv 64 0xcc8d0); C8 (Z_to_bv 64 0xcc8c0)]  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcce08 [C8 (Z_to_bv 64 0xbc610); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells bsegs m 0xceb40 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcdac0 [C8 (Z_to_bv 64 0xd2660); C8 (Z_to_bv 64 0xd2e60)]  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcce18 [C8 (Z_to_bv 64 0x165fe0)]                           (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcce28 [C8 (Z_to_bv 64 0x168068); C8 (Z_to_bv 64 0xd3d38); C8 (Z_to_bv 64 0xd6538);
                               C8 (Z_to_bv 64 0xd7228); C8 (Z_to_bv 64 0xd7230); C8 (Z_to_bv 64 0xd7220);
                               C8 (Z_to_bv 64 0xcecb0)]                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xd3d50 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd3df0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xd6538 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd7218 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xd5d9c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x1680e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells bsegs m 0xcecb0 [C8 (Z_to_bv 64 0xc6568)]                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x1683e0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk bsegs m XS1_LO XS1_HI /\ stk bsegs m XS2_LO XS2_HI /\ stk bsegs m XS3_LO XS3_HI.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs X_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  mkGD 0x20f20 0xd 0x20 0x1c1c0 0x21040 0x0 0x0 0xffffffffffffffff;
  mkGD 0x20f40 0x41 0x80 0x1e90b 0x21040 0x0 0x0 0xffffffffffffffff;
  mkGD 0x20fc0 0x17 0x40 0x1f9a4 0x21040 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21000 0x20 0x40 0x20688 0x21040 0x0 0x0 0xffffffffffffffff;
  mkGD 0x210a0 0x19d 0x200 0x1c1c0 0x218c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x212a0 0x421 0x540 0x1e90b 0x218c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x217e0 0x12 0x40 0x20688 0x218c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21820 0x37 0x60 0x13776 0x218c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21880 0x13 0x40 0x1d164 0x218c0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21920 0x3e 0x60 0x1c1c0 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21980 0x24 0x60 0x1e90b 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x219e0 0x40 0x60 0x20688 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21a40 0x3b 0x60 0x148e7 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21aa0 0x29 0x60 0x13776 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21b00 0x4 0x20 0x1d164 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21b20 0x1a 0x40 0x1a5db 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21b60 0xf 0x20 0x11400 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21b80 0x12 0x40 0x1678a 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21bc0 0xa 0x20 0x1f9c4 0x21be0 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21c20 0x26 0x60 0x1c1c0 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21c80 0x36 0x60 0x1e90b 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21ce0 0x1c 0x40 0x20688 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21d20 0x17 0x40 0x148e7 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21d60 0x18 0x40 0x13776 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21da0 0x22 0x60 0x1d164 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21e00 0x22 0x60 0x188b6 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21e60 0x30 0x60 0x1a5db 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21ec0 0x2c 0x60 0x11400 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x21f20 0x38 0x60 0x15077 0x21f80 0x0 0x0 0xffffffffffffffff;
  mkGD 0x220a0 0x14 0x40 0x1c1c0 0x22100 0x0 0x0 0xffffffffffffffff;
  mkGD 0x220e0 0x7 0x20 0x1e90b 0x22100 0x0 0x0 0xffffffffffffffff;
  mkGD 0xc4000 0x400 0x500 0x123db 0x218ed 0x0 0x0 0x5fb7c0;
  mkGD 0xc4500 0x800 0xa00 0x18e77 0x21fb1 0x0 0x0 0x5fb7c1 ].

Lemma asan_gds_length : length asan_gds = 33%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Notation XS1_LO := 0x7fffc1e4%Z (only parsing).  Notation XS1_HI := 0x7fffc420%Z (only parsing).
Notation XS2_LO := 0x80010800%Z (only parsing).  Notation XS2_HI := 0x80010b4c%Z (only parsing).
Notation XS3_LO := 0x800b76f8%Z (only parsing).  Notation XS3_HI := 0x800b76fc%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
  ((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || (o =? 0x5fb7c0) || (o =? 0x5fb7c1) || (o =? 0x5fb7c2).

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
  /\ (gd_odr g = ODR_NONE \/ gd_odr g = 0x5fb7c0 \/ gd_odr g = 0x5fb7c1 \/ gd_odr g = 0x5fb7c2)
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
  [(0x5fc030, 0x5fc034); (0x61c128, 0x61c150); (0x61c248, 0x61c250); (0x61c348, 0x61c34c); (0x61c368, 0x61c370);
   (0x61c7d0, 0x61c7d8); (0xc5010, 0xc5018); (0xc51f0, 0xc51f8); (0xc5018, 0xc5108); (0xc5220, 0xc5a88); (0xc5ad0, 0xc5ad1);
   (0x5fb7c0, 0x5fb7c1); (0x5fb7c1, 0x5fb7c3); (0x61c150, 0x61c158); (0x61c250, 0x61c258); (0x5fb790, 0x5fb791)].

Definition XENVC (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x5fc030 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  /\ rw_cells asegs m 0x61c248 [C8 (Z_to_bv 64 0x70e78)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x61c348 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells asegs m 0x61c7d0 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0xc5010 [C8 (Z_to_bv 64 0xc4f28)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xc51f0 [C8 (Z_to_bv 64 0xc5108)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells asegs m 0xc5100 [C8 (Z_to_bv 64 0xc5018)]                           (* [comment removed for export] *)
  /\ gds_at m 0xc5220 asan_gds                                                                     (* [comment removed for export] *)
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xc5a80 [C8 v])                    (* [comment removed for export] *)
  /\ rw_cells asegs m 0xc5ad0 [C1 (Z_to_bv 8 0)]                                                  (* [comment removed for export] *)
  /\ (exists o1 o2 o3 : byte, rw_cells asegs m 0x5fb7c0 [C1 o1] /\ rw_cells asegs m 0x5fb7c1 [C1 o2]
                              /\ rw_cells asegs m 0x5fb7c2 [C1 o3]).                         (* [comment removed for export] *)

Definition atxA (ph : bool) (m : mem) : Prop :=
  (exists p1 p2 : list byte, rw_cells asegs m 0x61c128 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x61c140 0 0xaf2f8))
  /\ (if ph then rw_cells asegs m 0x61c150 [C8 (Z_to_bv 64 0xaf2f8)] /\ rw_cells asegs m 0x61c250 [C8 (Z_to_bv 64 0x81840)]
      else (exists j1 : word, rw_cells asegs m 0x61c150 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x61c250 [C8 j2])
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
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x5fc030 0x5fc034); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0x61c248 0x61c250); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0x61c348 0x61c34c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x61c368 0x61c370); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
  split; [apply (R 0x61c7d0 0x61c7d8); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0xc5010 0xc5018); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0xc51f0 0xc51f8); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xc5018 0xc5108); [cbn; tauto| DJ| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xc5018 0xc5108); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
  split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
          apply AG; [apply (in_XENV_FPA 0xc5220 0xc5a88); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xc5220 0xc5a88); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
  split; [apply (R 0xc5ad0 0xc5ad1); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
  destruct ODR as (o1 & o2 & o3 & C1 & C2 & C3). exists o1, o2, o3. split; [| split].
  - apply (R 0x5fb7c0 0x5fb7c1); [cbn; tauto| DJ| lia| cbn; lia| exact C1].
  - apply (R 0x5fb7c1 0x5fb7c3); [cbn; tauto| DJ| lia| cbn; lia| exact C2].
  - apply (R 0x5fb7c1 0x5fb7c3); [cbn; tauto| DJ| lia| cbn; lia| exact C3].
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
  split; [exists p1, p2; apply (R 0x61c128 0x61c150); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
          unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
  destruct ph.
  - destruct PH as [PF PA]. split; [apply (R 0x61c150 0x61c158); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x61c250 0x61c258); [cbn; tauto| lia| cbn; lia| exact PA]].
  - destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
    + exists j1. apply (R 0x61c150 0x61c158); [cbn; tauto| lia| cbn; lia| exact PF].
    + exists j2. apply (R 0x61c250 0x61c258); [cbn; tauto| lia| cbn; lia| exact PA].
    + apply (R 0x5fb790 0x5fb791); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
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
    [apply (in_XENV_FPA 0x5fb790 0x5fb791)| apply (in_XENV_FPA 0x61c128 0x61c150)| apply (in_XENV_FPA 0x61c150 0x61c158)| apply (in_XENV_FPA 0x61c250 0x61c258)];
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells asegs m 0xbf4e0 [C8 (Z_to_bv 64 0x81bf4); C8 (Z_to_bv 64 0x318a0)]     (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc0720 [C8 (Z_to_bv 64 0xbf4f0); C8 (Z_to_bv 64 0xbf4e0)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xbfa28 [C8 (Z_to_bv 64 0xaf230); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells asegs m 0xc1760 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc06e0 [C8 (Z_to_bv 64 0xc5220); C8 (Z_to_bv 64 0xc5a60)]  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xbfa38 [C8 (Z_to_bv 64 0x158be0)]                           (* [comment removed for export] *)
  /\ ro_cells asegs m 0xbfa48 [C8 (Z_to_bv 64 0x15ac68); C8 (Z_to_bv 64 0xc6938); C8 (Z_to_bv 64 0xc9138);
                               C8 (Z_to_bv 64 0xc9e28); C8 (Z_to_bv 64 0xc9e30); C8 (Z_to_bv 64 0xc9e20);
                               C8 (Z_to_bv 64 0xc18d0)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc6950 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xc69f0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc9138 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xc9e18 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc899c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells asegs m 0x15ace0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xc18d0 [C8 (Z_to_bv 64 0xb9188)]                            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x15afe0 [C1 (Z_to_bv 8 0)]                                  (* [comment removed for export] *)
  /\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
