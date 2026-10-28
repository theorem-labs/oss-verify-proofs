(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Mem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx FX_Exit I_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GDESC_LO : Z := 0x5e7460.
Definition GDESC_HI : Z := 0x6a0320.
(* [comment removed for export] *)
Definition gdesc_pristine (m : mem) : Prop := forall a, GDESC_LO <= a < GDESC_HI -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AEF_CALLX : Z := 0x557954.           (* [comment removed for export] *)
Definition AEF_GUARDX : Z := 0x1ee2e0.          (* [comment removed for export] *)

Definition XENV_FPA : list (Z * Z) :=
  [(0xbdada8, 0xbdadac); (0xbfaea0, 0xbfaed0); (0xbfafc0, 0xbfafd0); (0xbfb0c0, 0xbfb0c4); (0xbfb0e0, 0xbfb0e8);
   (0xbfb548, 0xbfb550); (0x5e7250, 0x5e7258); (0x5e7430, 0x5e7438); (0x5e7258, 0x5e7348); (0x5e7460, 0x6a0348); (0x6a0390, 0x6a0391);
   (0xbd6051, 0xbd6055)].       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition XENVT (n : Z) (f1 a1v : word) (m : mem) : Prop :=
  (exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0xbdada8 [C4 (Z_to_bv 64 tid)])        (* [comment removed for export] *)
  /\ (exists (p1 p2 : list byte),                                                                 (* [comment removed for export] *)
        rw_cells bsegs m 0xbfaea0 [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); CB 4 p2;  (* [comment removed for export] *)
                                   C8 (Z_to_bv 64 0xbfaeb8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x557954); C8 f1])  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbfafc0 [C8 (Z_to_bv 64 0x1dd8a8); C8 a1v]                                  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbfb0c0 [C4 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ (exists (cdt thr sec : byte) (tm1 : word),
        rw_cells bsegs m 0xbfb0e0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xbfb548 [C8 (Z_to_bv 64 0)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5e7250 [C8 (Z_to_bv 64 0x5e7168)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x5e7430 [C8 (Z_to_bv 64 0x5e7348)]                                           (* [comment removed for export] *)
  /\ stdin_file m /\ rw_cells bsegs m 0x5e7340 [C8 (Z_to_bv 64 0x5e7258)]                           (* [comment removed for export] *)
  /\ gdesc_pristine m                                                                             (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x6a0340 [C8 (Z_to_bv 64 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x6a0390 [C1 (Z_to_bv 8 0)].                                                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition incb0 (m : mem) : Prop := exists p : list byte, rw_cells bsegs m 0xbd6051 [CB 3 p; C1 (Z_to_bv 8 0)].

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
  [(0xbdada8, 0xbdadac); (0xbfaea0, 0xbfaed0); (0xbfafc0, 0xbfafd0); (0xbfb0c0, 0xbfb0c4); (0xbfb0e0, 0xbfb0e8);
   (0xbfb548, 0xbfb550); (0x5e7250, 0x5e7258); (0x5e7430, 0x5e7438); (0x5e7258, 0x5e7348); (0x5e7460, 0x6a0348); (0x6a0390, 0x6a0391)].
Lemma in_XENV_FPA1 : forall lo hi x, In (lo, hi) XENV_FPA1 -> lo <= x < hi -> in_ranges XENV_FPA1 x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.
Lemma XENV_FPA1_sub : forall x, in_ranges XENV_FPA1 x -> in_ranges XENV_FPA x.
Proof. intros x (lo & hi & Hin & Hx). exists lo, hi. split; [| exact Hx]. unfold XENV_FPA1 in Hin. unfold XENV_FPA. cbn [In] in *. tauto. Qed.

Lemma XENVT_locA1 : forall n f1 a1v, fp_local XENV_FPA1 (XENVT n f1 a1v).
Proof.
  intros n f1 a1v m m' (TID & ATX & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL) AG.
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA1 -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (in_XENV_FPA1 lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xbdada8 0xbdadac); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [destruct ATX as (p1 & p2 & C); exists p1, p2; apply (R 0xbfaea0 0xbfaed0); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0xbfafc0 0xbfafd0); [cbn; tauto| lia| cbn; lia| exact ATA]|].
  split; [apply (R 0xbfb0c0 0xbfb0c4); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbfb0e0 0xbfb0e8); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbfb548 0xbfb550); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5e7250 0x5e7258); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5e7430 0x5e7438); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5e7258 0x5e7348); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5e7258 0x5e7348); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gdesc_pristine_agree m m' GDS); intros a Ha; apply AG; apply (in_XENV_FPA1 0x5e7460 0x6a0348); [cbn; tauto|];
          unfold GDESC_LO, GDESC_HI in Ha; lia|].
  split; [apply (R 0x5e7460 0x6a0348); [cbn; tauto| lia| cbn; lia| exact FLG]|].
  apply (R 0x6a0390 0x6a0391); [cbn; tauto| lia| cbn; lia| exact CPL].
Qed.

Lemma XENVT_locA : forall n f1 a1v, fp_local XENV_FPA (XENVT n f1 a1v).
Proof.
  intros n f1 a1v m m' H AG. apply (XENVT_locA1 n f1 a1v m m' H). intros a Ha. apply AG. exact (XENV_FPA1_sub _ Ha).
Qed.

(* [comment removed for export] *)
Definition XENV_FPB : list (Z * Z) :=
  [(0xbdada8, 0xbdadac); (0xbfb0c0, 0xbfb0c4); (0xbfb0e0, 0xbfb0e8);
   (0xbfb548, 0xbfb550); (0x5e7250, 0x5e7258); (0x5e7430, 0x5e7438); (0x5e7258, 0x5e7348); (0x5e7460, 0x6a0348); (0x6a0390, 0x6a0391)].

Lemma XENVT_retab : forall n f1 a1v n' f1' a1v' (m m' : mem), XENVT n f1 a1v m ->
  (forall a : word, in_ranges XENV_FPB (bv_unsigned a) -> m' a = m a) ->
  (exists (p1 p2 : list byte),
      rw_cells bsegs m' 0xbfaea0 [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 n'); CB 4 p2;
                                   C8 (Z_to_bv 64 0xbfaeb8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x557954); C8 f1']) ->
  rw_cells bsegs m' 0xbfafc0 [C8 (Z_to_bv 64 0x1dd8a8); C8 a1v'] ->
  XENVT n' f1' a1v' m'.
Proof.
  intros n f1 a1v n' f1' a1v' m m' (TID & ATX & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL) AG ATX' ATA'.
  assert (INB : forall lo hi x, In (lo, hi) XENV_FPB -> lo <= x < hi -> in_ranges XENV_FPB x) by (intros lo hi x H1 H2; exists lo, hi; split; assumption).
  assert (R : forall lo hi cs A, In (lo, hi) XENV_FPB -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
            rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
  { intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
    intros a Ha. apply AG. apply (INB lo hi); [exact Hin| lia]. }
  split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0xbdada8 0xbdadac); [cbn; tauto| lia| cbn; lia| exact C]]|].
  split; [exact ATX'|].
  split; [exact ATA'|].
  split; [apply (R 0xbfb0c0 0xbfb0c4); [cbn; tauto| lia| cbn; lia| exact EXL]|].
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0xbfb0e0 0xbfb0e8); [cbn; tauto| lia| cbn; lia| exact C]|].
  split; [apply (R 0xbfb548 0xbfb550); [cbn; tauto| lia| cbn; lia| exact OFL]|].
  split; [apply (R 0x5e7250 0x5e7258); [cbn; tauto| lia| cbn; lia| exact SEU]|].
  split; [apply (R 0x5e7430 0x5e7438); [cbn; tauto| lia| cbn; lia| exact SOU]|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x5e7258 0x5e7348); [cbn; tauto| lia| | exact C];
          destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
  split; [apply (R 0x5e7258 0x5e7348); [cbn; tauto| lia| cbn; lia| exact SINU]|].
  split; [apply (gdesc_pristine_agree m m' GDS); intros a Ha; apply AG; apply (INB 0x5e7460 0x6a0348); [cbn; tauto|];
          unfold GDESC_LO, GDESC_HI in Ha; lia|].
  split; [apply (R 0x5e7460 0x6a0348); [cbn; tauto| lia| cbn; lia| exact FLG]|].
  apply (R 0x6a0390 0x6a0391); [cbn; tauto| lia| cbn; lia| exact CPL].
Qed.

Lemma incb0_locA : fp_local XENV_FPA incb0.
Proof.
  intros m m' (p & C) AG. exists p. apply (rw_cells_agree_nw bsegs m m' _ _ C).
  intros a Ha. apply AG. apply (in_XENV_FPA 0xbd6051 0xbd6055); [cbn; tauto|].
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
Lemma INCB_offA : forall x, 0xbd6051 <= x < 0xbd6055 -> outside IO_FPA x /\ outside XENV_FPA1 x.
Proof.
  intros x Hx. split.
  - unfold IO_FPA. cbn. repeat (split; [lia|]). exact I.
  - unfold XENV_FPA1. cbn. repeat (split; [lia|]). exact I.
Qed.
Lemma ATXW_offA : forall x, in_ranges [(0xbfaea8, 0xbfaeac); (0xbfaec8, 0xbfaed0); (0xbfafc8, 0xbfafd0)] x -> outside IO_FPA x.
Proof.
  intros x (lo & hi & Hin & Hx). cbn [In] in Hin. unfold IO_FPA. cbn.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; repeat (split; [lia|]); exact I|]). destruct Hin.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition XSH_LO : Z := 0x7fffa000.      (* [comment removed for export] *)
Definition XSH_HI : Z := 0x80177a00.      (* [comment removed for export] *)

Definition xit_rt (m : mem) : Prop :=
  ro_cells bsegs m 0x56b3f0 [C8 (Z_to_bv 64 0x1ee8d4); C8 (Z_to_bv 64 0x194a98); C8 (Z_to_bv 64 0x20c324)]   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5e2c70 [C8 (Z_to_bv 64 0x56b408); C8 (Z_to_bv 64 0x56b3f0)]  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5e0ca8 [C8 (Z_to_bv 64 0x55788c); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
  /\ (exists d : word, ro_cells bsegs m 0x5e3ce0 [C8 d])                            (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x6a1210 [C4 (Z_to_bv 64 1)]                                  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x6a12b0 [C8 (Z_to_bv 64 0)]                                  (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x6a39f8 [C8 (Z_to_bv 64 0x7fff8000)]                         (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x6a46d8 [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x6a325c [C1 (Z_to_bv 8 1)]                                   (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x7355a0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                 (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x5e3f18 [C8 (Z_to_bv 64 0x5634a4)]                           (* [comment removed for export] *)
  /\ ro_cells bsegs m 0x7358a0 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
  /\ stk bsegs m XSH_LO XSH_HI.                                                     (* [comment removed for export] *)
