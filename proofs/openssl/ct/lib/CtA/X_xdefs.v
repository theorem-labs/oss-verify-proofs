(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GDESC_LO : Z := 0x5af720.
Definition GDESC_HI : Z := 0x66e960.
(* [comment removed for export] *)
Definition gdesc_pristine (m : mem) : Prop := forall a, GDESC_LO <= a < GDESC_HI -> mrd ctasegs m (wa a) = seg_rom ctasegs (wa a).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AEF_CALLX : Z := 0x51fbd8.           (* [comment removed for export] *)
Definition AEF_GUARDX : Z := 0x1f4074.          (* [comment removed for export] *)

Definition XENV_FPA : list (Z * Z) :=
  [(0xba9348, 0xba934c); (0xbc9440, 0xbc9470); (0xbc9560, 0xbc9570); (0xbc9660, 0xbc9664); (0xbc9680, 0xbc9688);
   (0xbc9ae8, 0xbc9af0); (0x5af510, 0x5af518); (0x5af6f0, 0x5af6f8); (0x5af518, 0x5af608); (0x5af720, 0x66e988); (0x66e9d0, 0x66e9d1);
   (0xba4691, 0xba4695)].       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition XENVT (n : Z) (f1 a1v : word) (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells ctasegs m 0xba9348 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ (exists (p1 p2 : list byte),                                                                 (* [comment removed for export] *)
        rw_cells ctasegs m 0xbc9440 [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); CB 4 p2;  (* [comment removed for export] *)
                                   C8 (Z_to_bv 64 0xbc9458); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x51fbd8); C8 f1])  (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0xbc9560 [C8 (Z_to_bv 64 0x1e363c); C8 a1v]                                  (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0xbc9660 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells ctasegs m 0xbc9680 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0xbc9ae8 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0x5af510 [C8 (Z_to_bv 64 0x5af428)]                                           (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0x5af6f0 [C8 (Z_to_bv 64 0x5af608)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells ctasegs m 0x5af600 [C8 (Z_to_bv 64 0x5af518)]                           (* [comment removed for export] *)
  /\ gdesc_pristine m                                                                             (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0x66e980 [C8 (Z_to_bv 64 1)]                                                (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0x66e9d0 [C1 (Z_to_bv 8 0)].                                                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition incb0 (m : mem) : Prop := exists p : list byte, rw_cells ctasegs m 0xba4691 [CB 3 p; C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition XENVA (m : mem) : Prop := (exists f1 a1v : word, XENVT 1 f1 a1v m) /\ incb0 m.
(* [comment removed for export] *)
Definition XENVA1 (m : mem) : Prop := XENVT 2 (Z_to_bv 64 AEF_CALLX) (Z_to_bv 64 AEF_GUARDX) m.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition XENV_FPA1 : list (Z * Z) :=
  [(0xba9348, 0xba934c); (0xbc9440, 0xbc9470); (0xbc9560, 0xbc9570); (0xbc9660, 0xbc9664); (0xbc9680, 0xbc9688);
   (0xbc9ae8, 0xbc9af0); (0x5af510, 0x5af518); (0x5af6f0, 0x5af6f8); (0x5af518, 0x5af608); (0x5af720, 0x66e988); (0x66e9d0, 0x66e9d1)].
Lemma in_XENV_FPA1 : forall lo hi x, In (lo, hi) XENV_FPA1 -> lo <= x < hi -> in_ranges XENV_FPA1 x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma XENV_FPA1_sub : forall x, in_ranges XENV_FPA1 x -> in_ranges XENV_FPA x.
Proof. intros x (lo & hi & Hin & Hx). exists lo, hi. split; [| exact Hx]. unfold XENV_FPA1 in Hin. unfold XENV_FPA. cbn [In] in *. tauto. Qed.

Lemma XENVT_locA1 : forall n f1 a1v, fp_local XENV_FPA1 (XENVT n f1 a1v).
Proof.
  intros n f1 a1v m m' (TID & ATX & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA1 -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells ctasegs m A cs -> rw_cells ctasegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw ctasegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA1 lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xba9348 0xba934c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [destruct ATX as (p1 & p2 & C); exists p1, p2; apply (R 0xbc9440 0xbc9470); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xbc9560 0xbc9570); [cbn; tauto| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0xbc9660 0xbc9664); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbc9680 0xbc9688); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbc9ae8 0xbc9af0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5af510 0x5af518); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5af6f0 0x5af6f8); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5af518 0x5af608); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5af518 0x5af608); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gdesc_pristine_agree m m' GDS); intros a Ha; apply AG; apply (in_XENV_FPA1 0x5af720 0x66e988); [cbn; tauto|];
          unfold GDESC_LO, GDESC_HI in Ha; lia|].
  split; [apply (R 0x5af720 0x66e988); [cbn; tauto| lia| cbn; lia| exact FLG]|].
  apply (R 0x66e9d0 0x66e9d1); [cbn; tauto| lia| cbn; lia| exact CPL].
Qed.

Lemma XENVT_locA : forall n f1 a1v, fp_local XENV_FPA (XENVT n f1 a1v).
Proof.
  intros n f1 a1v m m' H AG. apply (XENVT_locA1 n f1 a1v m m' H). intros a Ha. apply AG. exact (XENV_FPA1_sub _ Ha).
Qed.

(* [comment removed for export] *)
Definition XENV_FPB : list (Z * Z) :=
  [(0xba9348, 0xba934c); (0xbc9660, 0xbc9664); (0xbc9680, 0xbc9688);
   (0xbc9ae8, 0xbc9af0); (0x5af510, 0x5af518); (0x5af6f0, 0x5af6f8); (0x5af518, 0x5af608); (0x5af720, 0x66e988); (0x66e9d0, 0x66e9d1)].

Lemma XENVT_retab : forall n f1 a1v n' f1' a1v' (m m' : mem), XENVT n f1 a1v m ->
  (forall a : word, in_ranges XENV_FPB (bv_unsigned a) -> m' a = m a) ->
  (exists (p1 p2 : list byte),
      rw_cells ctasegs m' 0xbc9440 [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n'); CB 4 p2;
                                   C8 (Z_to_bv 64 0xbc9458); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x51fbd8); C8 f1']) ->
  rw_cells ctasegs m' 0xbc9560 [C8 (Z_to_bv 64 0x1e363c); C8 a1v'] ->
  XENVT n' f1' a1v' m'.
Proof.
  intros n f1 a1v n' f1' a1v' m m' (TID & ATX & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL) AG ATX' ATA'.
  assert (INB : forall lo hi x, In (lo, hi) XENV_FPB -> lo <= x < hi -> in_ranges XENV_FPB x) by (intros lo hi x H1 H2; exists lo, hi; split; assumption).
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPB -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells ctasegs m A cs -> rw_cells ctasegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw ctasegs m m' _ _ H).
    intros a Ha. apply AG. apply (INB lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xba9348 0xba934c); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [exact ATX'|].
  split; [exact ATA'|].
  split; [apply (R 0xbc9660 0xbc9664); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbc9680 0xbc9688); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbc9ae8 0xbc9af0); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5af510 0x5af518); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5af6f0 0x5af6f8); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5af518 0x5af608); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5af518 0x5af608); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gdesc_pristine_agree m m' GDS); intros a Ha; apply AG; apply (INB 0x5af720 0x66e988); [cbn; tauto|];
          unfold GDESC_LO, GDESC_HI in Ha; lia|].
  split; [apply (R 0x5af720 0x66e988); [cbn; tauto| lia| cbn; lia| exact FLG]|].
  apply (R 0x66e9d0 0x66e9d1); [cbn; tauto| lia| cbn; lia| exact CPL].
Qed.

Lemma incb0_locA : fp_local XENV_FPA incb0.
Proof.
  intros m m' (p & C) AG. exists p. apply (rw_cells_agree_nw ctasegs m m' _ _ C).
  intros a Ha. apply AG. apply (in_XENV_FPA 0xba4691 0xba4695); [cbn; tauto|].
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma INCB_offA : forall x, 0xba4691 <= x < 0xba4695 -> outside IO_FPA x /\ outside XENV_FPA1 x.
Proof.
  intros x Hx. split.
  - unfold IO_FPA. cbn. repeat (split; [lia|]). exact I.
  - unfold XENV_FPA1. cbn. repeat (split; [lia|]). exact I.
Qed.
Lemma ATXW_offA : forall x, in_ranges [(0xbc9448, 0xbc944c); (0xbc9468, 0xbc9470); (0xbc9568, 0xbc9570)] x -> outside IO_FPA x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn [In] in Hin. unfold IO_FPA. cbn.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat (split; [lia|]); exact I|]). destruct Hin.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition XSH_LO : Z := 0x7fffa000.      (* [comment removed for export] *)
Definition XSH_HI : Z := 0x80171600.      (* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells ctasegs m 0x533428 [C8 (Z_to_bv 64 0x1f43d0); C8 (Z_to_bv 64 0x19ab8c); C8 (Z_to_bv 64 0x1f4400)]   (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5ab210 [C8 (Z_to_bv 64 0x533440); C8 (Z_to_bv 64 0x533428)]  (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5a9208 [C8 (Z_to_bv 64 0x51fb10); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells ctasegs m 0x5ac280 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x66f850 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0x66f8f0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x672038 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x672d18 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x67189c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x703be0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                 (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5ac4b0 [C8 (Z_to_bv 64 0x52b4e0)]                           (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x703ee0 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
  /\ stk ctasegs m XSH_LO XSH_HI.                                                     (* [comment removed for export] *)
