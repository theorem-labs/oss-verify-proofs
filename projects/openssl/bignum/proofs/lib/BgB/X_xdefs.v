(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Mem.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GDESC_LO : Z := 0x5e3680.
Definition GDESC_HI : Z := 0x69c380.

Definition gdesc_pristine (m : mem) : Prop := forall a, GDESC_LO <= a < GDESC_HI -> mrd bgbsegs m (wa a) = seg_rom bgbsegs (wa a).

Definition AEF_CALLX : Z := 0x553c88.
Definition AEF_GUARDX : Z := 0x1edf58.

Definition XENV_FPA : list (Z * Z) :=
  [(0xbd6d48, 0xbd6d4c); (0xbf6e40, 0xbf6e70); (0xbf6f60, 0xbf6f70); (0xbf7060, 0xbf7064); (0xbf7080, 0xbf7088);
   (0xbf74e8, 0xbf74f0); (0x5e3470, 0x5e3478); (0x5e3650, 0x5e3658); (0x5e3478, 0x5e3568); (0x5e3680, 0x69c388); (0x69c3d0, 0x69c3d1);
   (0xbd2091, 0xbd2095)].

Definition XENVT (n : Z) (f1 a1v : word) (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bgbsegs m 0xbd6d48 [C4 (Z_to_bv 64 tid)])
  /\ (exists (p1 p2 : list byte),
        rw_cells bgbsegs m 0xbf6e40 [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); CB 4 p2;
                                   C8 (Z_to_bv 64 0xbf6e58); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x553c88); C8 f1])
  /\ rw_cells bgbsegs m 0xbf6f60 [C8 (Z_to_bv 64 0x1dd520); C8 a1v]
  /\ rw_cells bgbsegs m 0xbf7060 [C4 (Z_to_bv 64 0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bgbsegs m 0xbf7080 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells bgbsegs m 0xbf74e8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bgbsegs m 0x5e3470 [C8 (Z_to_bv 64 0x5e3388)]
  /\ rw_cells bgbsegs m 0x5e3650 [C8 (Z_to_bv 64 0x5e3568)]
  /\ stdin_file m /\ rw_cells bgbsegs m 0x5e3560 [C8 (Z_to_bv 64 0x5e3478)]
  /\ gdesc_pristine m
  /\ rw_cells bgbsegs m 0x69c380 [C8 (Z_to_bv 64 1)]
  /\ rw_cells bgbsegs m 0x69c3d0 [C1 (Z_to_bv 8 0)].

Definition incb0 (m : mem) : Prop := exists p : list byte, rw_cells bgbsegs m 0xbd2091 [CB 3 p; C1 (Z_to_bv 8 0)].

Definition XENVA (m : mem) : Prop := (exists f1 a1v : word, XENVT 1 f1 a1v m) /\ incb0 m.

Definition XENVA1 (m : mem) : Prop := XENVT 2 (Z_to_bv 64 AEF_CALLX) (Z_to_bv 64 AEF_GUARDX) m.

Definition XENVX (m : mem) : Prop :=
  exists (n : Z) (f1 a1v : word), XENVT n f1 a1v m /\ (n = 1 \/ (n = 2 /\ f1 = Z_to_bv 64 AEF_CALLX /\ a1v = Z_to_bv 64 AEF_GUARDX)) /\ incb0 m.

Lemma XENVA_X : forall m, XENVA m -> XENVX m.
Proof. intros m ((f1 & a1v & H) & I0). exists 1, f1, a1v. split; [exact H|]. split; [left; reflexivity| exact I0]. Qed.
Lemma XENVA1_X : forall m, XENVA1 m /\ incb0 m -> XENVX m.
Proof. intros m (H & I0). exists 2, (Z_to_bv 64 AEF_CALLX), (Z_to_bv 64 AEF_GUARDX). split; [exact H|]. split; [right; repeat split| exact I0]. Qed.

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma gdesc_pristine_agree : forall (m m' : mem), gdesc_pristine m -> agree_on (fun x => GDESC_LO <= x < GDESC_HI) m m' -> gdesc_pristine m'.
Proof.
  intros m m' H AG a Ha. unfold mrd. rewrite (AG (wa a)); [exact (H a Ha)|].
  rewrite wa_unsigned by (unfold GDESC_LO, GDESC_HI in Ha; lia). exact Ha.
Qed.

Definition XENV_FPA1 : list (Z * Z) :=
  [(0xbd6d48, 0xbd6d4c); (0xbf6e40, 0xbf6e70); (0xbf6f60, 0xbf6f70); (0xbf7060, 0xbf7064); (0xbf7080, 0xbf7088);
   (0xbf74e8, 0xbf74f0); (0x5e3470, 0x5e3478); (0x5e3650, 0x5e3658); (0x5e3478, 0x5e3568); (0x5e3680, 0x69c388); (0x69c3d0, 0x69c3d1)].
Lemma in_XENV_FPA1 : forall lo hi x, In (lo, hi) XENV_FPA1 -> lo <= x < hi -> in_ranges XENV_FPA1 x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma XENV_FPA1_sub : forall x, in_ranges XENV_FPA1 x -> in_ranges XENV_FPA x.
Proof. intros x (lo & hi & Hin & Hx). exists lo, hi. split; [| exact Hx]. unfold XENV_FPA1 in Hin. unfold XENV_FPA. cbn [In] in *. tauto. Qed.

Lemma XENVT_locA1 : forall n f1 a1v, fp_local XENV_FPA1 (XENVT n f1 a1v).
Proof.
  intros n f1 a1v m m' (TID & ATX & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA1 -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bgbsegs m A cs -> rw_cells bgbsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bgbsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA1 lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xbd6d48 0xbd6d4c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [destruct ATX as (p1 & p2 & C); exists p1, p2; apply (R 0xbf6e40 0xbf6e70); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xbf6f60 0xbf6f70); [cbn; tauto| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0xbf7060 0xbf7064); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbf7080 0xbf7088); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbf74e8 0xbf74f0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5e3470 0x5e3478); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5e3650 0x5e3658); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5e3478 0x5e3568); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5e3478 0x5e3568); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gdesc_pristine_agree m m' GDS); intros a Ha; apply AG; apply (in_XENV_FPA1 0x5e3680 0x69c388); [cbn; tauto|];
          unfold GDESC_LO, GDESC_HI in Ha; lia|].
  split; [apply (R 0x5e3680 0x69c388); [cbn; tauto| lia| cbn; lia| exact FLG]|].
  apply (R 0x69c3d0 0x69c3d1); [cbn; tauto| lia| cbn; lia| exact CPL].
Qed.

Lemma XENVT_locA : forall n f1 a1v, fp_local XENV_FPA (XENVT n f1 a1v).
Proof.
  intros n f1 a1v m m' H AG. apply (XENVT_locA1 n f1 a1v m m' H). intros a Ha. apply AG. exact (XENV_FPA1_sub _ Ha).
Qed.

Definition XENV_FPB : list (Z * Z) :=
  [(0xbd6d48, 0xbd6d4c); (0xbf7060, 0xbf7064); (0xbf7080, 0xbf7088);
   (0xbf74e8, 0xbf74f0); (0x5e3470, 0x5e3478); (0x5e3650, 0x5e3658); (0x5e3478, 0x5e3568); (0x5e3680, 0x69c388); (0x69c3d0, 0x69c3d1)].

Lemma XENVT_retab : forall n f1 a1v n' f1' a1v' (m m' : mem), XENVT n f1 a1v m ->
  (forall a : word, in_ranges XENV_FPB (bv_unsigned a) -> m' a = m a) ->
  (exists (p1 p2 : list byte),
      rw_cells bgbsegs m' 0xbf6e40 [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n'); CB 4 p2;
                                   C8 (Z_to_bv 64 0xbf6e58); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x553c88); C8 f1']) ->
  rw_cells bgbsegs m' 0xbf6f60 [C8 (Z_to_bv 64 0x1dd520); C8 a1v'] ->
  XENVT n' f1' a1v' m'.
Proof.
  intros n f1 a1v n' f1' a1v' m m' (TID & ATX & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL) AG ATX' ATA'.
  assert (INB : forall lo hi x, In (lo, hi) XENV_FPB -> lo <= x < hi -> in_ranges XENV_FPB x) by (intros lo hi x H1 H2; exists lo, hi; split; assumption).
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPB -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bgbsegs m A cs -> rw_cells bgbsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bgbsegs m m' _ _ H).
    intros a Ha. apply AG. apply (INB lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xbd6d48 0xbd6d4c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [exact ATX'|].
  split; [exact ATA'|].
  split; [apply (R 0xbf7060 0xbf7064); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbf7080 0xbf7088); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbf74e8 0xbf74f0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5e3470 0x5e3478); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5e3650 0x5e3658); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5e3478 0x5e3568); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5e3478 0x5e3568); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gdesc_pristine_agree m m' GDS); intros a Ha; apply AG; apply (INB 0x5e3680 0x69c388); [cbn; tauto|];
          unfold GDESC_LO, GDESC_HI in Ha; lia|].
  split; [apply (R 0x5e3680 0x69c388); [cbn; tauto| lia| cbn; lia| exact FLG]|].
  apply (R 0x69c3d0 0x69c3d1); [cbn; tauto| lia| cbn; lia| exact CPL].
Qed.

Lemma incb0_locA : fp_local XENV_FPA incb0.
Proof.
  intros m m' (p & C) AG. exists p. apply (rw_cells_agree_nw bgbsegs m m' _ _ C).
  intros a Ha. apply AG. apply (in_XENV_FPA 0xbd2091 0xbd2095); [cbn; tauto|].
  destruct C as [[Hw _] _]. cbn in Hw. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof.
  intros m m' ((f1 & a1v & H) & I0) AG. split; [exists f1, a1v; exact (XENVT_locA 1 f1 a1v m m' H AG)| exact (incb0_locA m m' I0 AG)].
Qed.
Lemma XENV1_locA : fp_local XENV_FPA XENVA1.
Proof. exact (XENVT_locA 2 _ _). Qed.
Lemma XENV1_locA1 : fp_local XENV_FPA1 XENVA1.
Proof. exact (XENVT_locA1 2 _ _). Qed.

Definition XENVA2 (m : mem) : Prop := XENVA1 m /\ incb0 m.
Lemma XENV2_locA : fp_local XENV_FPA XENVA2.
Proof. intros m m' (H & I0) AG. split; [exact (XENV1_locA m m' H AG)| exact (incb0_locA m m' I0 AG)]. Qed.

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn in Hin.
  split; [| split; [| split]].
  - apply client_static_intro.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, g_read_stage.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
  - unfold IO_FPA. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
  - unfold LIB_FP. cbn.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.
Lemma XENV1_imgA : forall x, in_ranges XENV_FPA1 x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof. intros x Hx. exact (XENV_imgA x (XENV_FPA1_sub x Hx)). Qed.

Lemma INCB_offA : forall x, 0xbd2091 <= x < 0xbd2095 -> outside IO_FPA x /\ outside XENV_FPA1 x.
Proof.
  intros x Hx. split.
  - unfold IO_FPA. cbn. repeat (split; [lia|]). exact I.
  - unfold XENV_FPA1. cbn. repeat (split; [lia|]). exact I.
Qed.
Lemma ATXW_offA : forall x, in_ranges [(0xbf6e48, 0xbf6e4c); (0xbf6e68, 0xbf6e70); (0xbf6f68, 0xbf6f70)] x -> outside IO_FPA x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn [In] in Hin. unfold IO_FPA. cbn.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat (split; [lia|]); exact I|]). destruct Hin.
Qed.

Definition XSH_LO : Z := 0x7fffa000.
Definition XSH_HI : Z := 0x80177200.

Definition xit_rt (m : mem) : Prop :=
  ro_cells bgbsegs m 0x567640 [C8 (Z_to_bv 64 0x1eee38); C8 (Z_to_bv 64 0x194a70); C8 (Z_to_bv 64 0x1ee3b4)]
  /\ ro_cells bgbsegs m 0x5deeb8 [C8 (Z_to_bv 64 0x567658); C8 (Z_to_bv 64 0x567640)]
  /\ ro_cells bgbsegs m 0x5dcee8 [C8 (Z_to_bv 64 0x553bc0); C8 (Z_to_bv 64 0)]
  /\ (exists d : word, ro_cells bgbsegs m 0x5dff20 [C8 d])
  /\ ro_cells bgbsegs m 0x69d250 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bgbsegs m 0x69d2f0 [C8 (Z_to_bv 64 0)]
  /\ ro_cells bgbsegs m 0x69fa38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells bgbsegs m 0x6a0718 [C1 (Z_to_bv 8 1)]
  /\ ro_cells bgbsegs m 0x69f29c [C1 (Z_to_bv 8 1)]
  /\ ro_cells bgbsegs m 0x7315e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ ro_cells bgbsegs m 0x5e0150 [C8 (Z_to_bv 64 0x55f6f8)]
  /\ ro_cells bgbsegs m 0x7318e0 [C1 (Z_to_bv 8 0)]
  /\ stk bgbsegs m XSH_LO XSH_HI.
