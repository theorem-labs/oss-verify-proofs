(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SIF.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Section Stmt.
Variable SEGS : list Segment.
(* [comment removed for export] *)
Variable RR : shape_rel SEGS.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable XA : nat -> list expr -> acs -> option (acs * acs).
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : expr.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Variable FXOK : GPS.FX -> Prop.
(* [comment removed for export] *)
Variable HOLES : nat -> env -> Fs.Fs -> TSet.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).
#[local] Notation cfg := (GPS.cfgF SEGS).

(* [comment removed for export] *)
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E fx R M model T,
    CSOK E cs R M model -> FXOK fx -> pre cs = true -> node cs = Some cs' ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc cs') M' model') T) ->
    RR (cfg fx R (pc cs) M model) T.

Definition always (cs : acs) : bool := true.

(* [comment removed for export] *)
Definition node1_stmtN (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E fx R M model (T : TSet),
    T [] ->
    CSOK E cs R M model -> FXOK fx -> pre cs = true -> node cs = Some cs' ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc cs') M' model') T) ->
    RR (cfg fx R (pc cs) M model) T.
Lemma node1_stmt_N : forall pre node, node1_stmt pre node -> node1_stmtN pre node.
Proof. intros pre node H cs cs' E fx R M model T _ HC HF Hp Hn Hk. exact (H cs cs' E fx R M model T HC HF Hp Hn Hk). Qed.

(* [comment removed for export] *)
Definition sys_stmt (y : snode) : Prop := node1_stmt (is_ecall_at SEGS) (node_sys A nx0 y).

(* [comment removed for export] *)
Definition brk2_stmt : Prop :=
  forall cs csa csb E fx R M model TA TB,
    CSOK E cs R M model -> FXOK fx -> is_ecall_at SEGS cs = true -> node_brk2 A LIMIT ISP cs = Some (csa, csb) -> t_eq TA TB ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csa R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csa) M' model') TA) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csb) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) (t_alt2 TA TB).

(* [comment removed for export] *)
Definition brk2x_stmt : Prop :=
  forall cs csa csb E fx R M model T,
    CSOK E cs R M model -> FXOK fx -> is_ecall_at SEGS cs = true -> node_brk2x A LIMIT ISP cs = Some (csa, csb) -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csa R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csa) M' model') T) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csb) M' model') T) ->
    RR (cfg fx R (pc cs) M model) T.

(* [comment removed for export] *)
Definition exit_stmt : Prop :=
  forall cs code E fx R M model,
    CSOK E cs R M model -> FXOK fx -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    RR (cfg fx R (pc cs) M model) (t_exit (Z_to_bv 64 code) (m_fs model)).

(* [comment removed for export] *)
Definition mm2_stmt (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E fx R M model TB,
    CSOK E cs R M model -> FXOK fx -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csb) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) TB.

(* [comment removed for export] *)
Definition mm3_stmt (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall cs csa csb cscs E fx R M model TB,
    CSOK E cs R M model -> FXOK fx -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csb) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) TB.

(* [comment removed for export] *)
Definition mmw_stmt (node : acs -> option (acs * option acs * acs)) : Prop :=
  forall cs csr csl csh E fx R M model TB,
    CSOK E cs R M model -> FXOK fx -> is_ecall_at SEGS cs = true -> node cs = Some (csr, csl, csh) ->
    (forall csl' E' fx' R' M' model', csl = Some csl' ->
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csl' R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csl') M' model') TB) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csh R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csh) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) TB.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ext_stmt : Prop := forall id args, node1_stmtN always (XN id args).

(* [comment removed for export] *)
Definition emit_stmt : Prop :=
  forall id args cs fd ps cs' E fx R M model T,
    CSOK E cs R M model -> FXOK fx -> XE id args cs = Some (fd, ps, cs') -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc cs') M' model') T) ->
    RR (cfg fx R (pc cs) M model) (t_emit (GPS.Wp E fd ps) T).

(* [comment removed for export] *)
Definition ext2_stmt : Prop :=
  forall id args cs csa csb E fx R M model T,
    CSOK E cs R M model -> FXOK fx -> XB id args cs = Some (csa, csb) -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csa R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csa) M' model') T) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csb) M' model') T) ->
    RR (cfg fx R (pc cs) M model) T.

(* [comment removed for export] *)
Definition alt2_stmt : Prop :=
  forall id args cs csa csb E fx R M model Ta Tb,
    CSOK E cs R M model -> FXOK fx -> XA id args cs = Some (csa, csb) -> Ta [] -> Tb [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csa R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csa) M' model') Ta) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> FXOK fx' ->
        m_fs model' = m_fs model ->
        RR (cfg fx' R' (pc csb) M' model') Tb) ->
    RR (cfg fx R (pc cs) M model) (t_alt2 Ta Tb).

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  forall h ch, HS h = Some ch ->
  forall E fx R M model, CSOK E ch R M model -> FXOK fx ->
    RR (cfg fx R (pc ch) M model) (HOLES h E (m_fs model)).

(* [comment removed for export] *)
Section Here.
Variable fx : GPS.FX.

Definition node1_here (pre : acs -> bool) (node : acs -> option acs) : Prop :=
  forall cs cs' E R M model T,
    CSOK E cs R M model -> pre cs = true -> node cs = Some cs' ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc cs') M' model') T) ->
    RR (cfg fx R (pc cs) M model) T.

Definition sys_here (y : snode) : Prop := node1_here (is_ecall_at SEGS) (node_sys A nx0 y).

Definition brk2_here : Prop :=
  forall cs csa csb E R M model TA TB,
    CSOK E cs R M model -> is_ecall_at SEGS cs = true -> node_brk2 A LIMIT ISP cs = Some (csa, csb) -> t_eq TA TB ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csa R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csa) M' model') TA) ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csb) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) (t_alt2 TA TB).

Definition brk2x_here : Prop :=
  forall cs csa csb E R M model T,
    CSOK E cs R M model -> is_ecall_at SEGS cs = true -> node_brk2x A LIMIT ISP cs = Some (csa, csb) -> T [] ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csa R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csa) M' model') T) ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csb) M' model') T) ->
    RR (cfg fx R (pc cs) M model) T.

Definition exit_here : Prop :=
  forall cs code E R M model,
    CSOK E cs R M model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
    RR (cfg fx R (pc cs) M model) (t_exit (Z_to_bv 64 code) (m_fs model)).

Definition mm2_here (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E R M model TB,
    CSOK E cs R M model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csb) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) TB.

Definition mm3_here (node : acs -> option (acs * acs * list acs)) : Prop :=
  forall cs csa csb cscs E R M model TB,
    CSOK E cs R M model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csb R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csb) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) TB.
End Here.

Lemma node1_pack : forall pre node, (forall fx, node1_here fx pre node) -> node1_stmt pre node.
Proof.
  intros pre node H cs cs' E fx R M model T HC HF Hp Hn HK.
  apply (H fx cs cs' E R M model T HC Hp Hn).
  intros E' R' M' model' Hag HC' Hfs. exact (HK E' fx R' M' model' Hag HC' HF Hfs).
Qed.
Lemma sys_pack : forall y, (forall fx, sys_here fx y) -> sys_stmt y.
Proof. intros y H. apply node1_pack. exact H. Qed.
Lemma brk2_pack : (forall fx, brk2_here fx) -> brk2_stmt.
Proof.
  intros H cs csa csb E fx R M model TA TB HC HF Hec Hn Heq HKA HKB.
  apply (H fx cs csa csb E R M model TA TB HC Hec Hn Heq).
  - intros E' R' M' model' Hag HC' Hfs. exact (HKA E' fx R' M' model' Hag HC' HF Hfs).
  - intros E' R' M' model' Hag HC' Hfs. exact (HKB E' fx R' M' model' Hag HC' HF Hfs).
Qed.
Lemma brk2x_pack : (forall fx, brk2x_here fx) -> brk2x_stmt.
Proof.
  intros H cs csa csb E fx R M model T HC HF Hec Hn HT HKA HKB.
  apply (H fx cs csa csb E R M model T HC Hec Hn HT).
  - intros E' R' M' model' Hag HC' Hfs. exact (HKA E' fx R' M' model' Hag HC' HF Hfs).
  - intros E' R' M' model' Hag HC' Hfs. exact (HKB E' fx R' M' model' Hag HC' HF Hfs).
Qed.
Lemma exit_pack : (forall fx, exit_here fx) -> exit_stmt.
Proof. intros H cs code E fx R M model HC HF Hec Hn. exact (H fx cs code E R M model HC Hec Hn). Qed.
Definition mmw_here (fx : GPS.FX) (node : acs -> option (acs * option acs * acs)) : Prop :=
  forall cs csr csl csh E R M model TB,
    CSOK E cs R M model -> is_ecall_at SEGS cs = true -> node cs = Some (csr, csl, csh) ->
    (forall csl' E' R' M' model', csl = Some csl' ->
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csl' R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csl') M' model') TB) ->
    (forall E' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csh R' M' model' -> m_fs model' = m_fs model ->
        RR (cfg fx R' (pc csh) M' model') TB) ->
    RR (cfg fx R (pc cs) M model) TB.
Lemma mmw_pack : forall node, (forall fx, mmw_here fx node) -> mmw_stmt node.
Proof.
  intros node H cs csr csl csh E fx R M model TB HC HF Hec Hn HKL HKH.
  apply (H fx cs csr csl csh E R M model TB HC Hec Hn).
  - intros csl' E' R' M' model' Hl Hag HC' Hfs. exact (HKL csl' E' fx R' M' model' Hl Hag HC' HF Hfs).
  - intros E' R' M' model' Hag HC' Hfs. exact (HKH E' fx R' M' model' Hag HC' HF Hfs).
Qed.

Lemma mm2_pack : forall node, (forall fx, mm2_here fx node) -> mm2_stmt node.
Proof.
  intros node H cs csa csb E fx R M model TB HC HF Hec Hn HKB.
  apply (H fx cs csa csb E R M model TB HC Hec Hn).
  intros E' R' M' model' Hag HC' Hfs. exact (HKB E' fx R' M' model' Hag HC' HF Hfs).
Qed.
Lemma mm3_pack : forall node, (forall fx, mm3_here fx node) -> mm3_stmt node.
Proof.
  intros node H cs csa csb cscs E fx R M model TB HC HF Hec Hn HKB.
  apply (H fx cs csa csb cscs E R M model TB HC Hec Hn).
  intros E' R' M' model' Hag HC' Hfs. exact (HKB E' fx R' M' model' Hag HC' HF Hfs).
Qed.

End Stmt.
End SIF.
