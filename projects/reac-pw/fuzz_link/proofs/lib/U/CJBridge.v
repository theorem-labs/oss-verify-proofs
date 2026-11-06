From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma msteps_bridge : forall segs ms ms',
  CJ.Lib.Exec.msteps segs ms ms' -> lib.Lib.Exec.msteps segs ms ms'.
Proof.
  intros segs ms ms' H. induction H as [ms|ms ms1 ms2 H1 _ IH].
  - apply lib.Lib.Exec.msteps_refl.
  - eapply lib.Lib.Exec.msteps_cons; [exact H1 | exact IH].
Qed.

Lemma evt_bridge : forall segs (Q Q' : machine_state -> Prop) ms,
  (forall ms', Q ms' -> Q' ms') -> CJ.Lib.Exec.evt segs Q ms -> lib.Lib.Exec.evt segs Q' ms.
Proof.
  intros segs Q Q' ms HQ [ms' [H HQ1]]. exists ms'. split; [exact (msteps_bridge segs ms ms' H) | exact (HQ ms' HQ1)].
Qed.

Lemma MS_eq : forall R F pc fc rv m ro,
  CJ.Lib.MState.MS R F pc fc rv m ro = lib.Lib.MState.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.

Lemma mkR_eq : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                      x27 x28 x29 x30 x31,
  CJ.Lib.Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                   x27 x28 x29 x30 x31
  = lib.Lib.Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                      x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

Lemma ret_pc_eq : forall ra, CJ.Lib.MState.ret_pc ra = lib.Lib.MState.ret_pc ra.
Proof. reflexivity. Qed.

Lemma frm0_iff : forall fc, CJ.Lib.FP.frm0 fc <-> lib.Lib.FP.frm0 fc.
Proof. intros fc. split; intros H; exact H. Qed.

Lemma bytes_at_iff : forall segs m a bs, CJ.Lib.Mem.bytes_at segs m a bs <-> lib.Lib.Mem.bytes_at segs m a bs.
Proof. intros segs m a bs. split; intros H; exact H. Qed.

Lemma stk_iff : forall segs m lo hi, CJ.Lib.Frame.stk segs m lo hi <-> lib.Lib.Frame.stk segs m lo hi.
Proof. intros segs m lo hi. split; intros H; exact H. Qed.

Lemma munch_iff : forall W m m', CJ.Lib.Frame.munch W m m' <-> lib.Lib.Frame.munch W m m'.
Proof. intros W m m'. split; intros H; exact H. Qed.

Lemma wmono_iff : forall segs m m', CJ.Lib.Frame.wmono segs m m' <-> lib.Lib.Frame.wmono segs m m'.
Proof. intros segs m m'. split; intros H; exact H. Qed.

Definition cell_to (c : lib.Lib.Cells.cell) : CJ.Lib.Cells.cell :=
  match c with
  | lib.Lib.Cells.C8 v => CJ.Lib.Cells.C8 v
  | lib.Lib.Cells.C4 v => CJ.Lib.Cells.C4 v
  | lib.Lib.Cells.C2 v => CJ.Lib.Cells.C2 v
  | lib.Lib.Cells.C1 b => CJ.Lib.Cells.C1 b
  | lib.Lib.Cells.CB n bs => CJ.Lib.Cells.CB n bs
  end.

Lemma cells_wf_to : forall cs, CJ.Lib.Cells.cells_wf (map cell_to cs) <-> lib.Lib.Cells.cells_wf cs.
Proof.
  induction cs as [|c cs IH]; cbn; [tauto|].
  destruct c; cbn; rewrite IH; tauto.
Qed.

Lemma cells_bytes_to : forall cs, CJ.Lib.Cells.cells_bytes (map cell_to cs) = lib.Lib.Cells.cells_bytes cs.
Proof. induction cs as [|c cs IH]; cbn; [reflexivity|]. rewrite IH. destruct c; reflexivity. Qed.

Lemma cells_size_to : forall cs, CJ.Lib.Cells.cells_size (map cell_to cs) = lib.Lib.Cells.cells_size cs.
Proof. induction cs as [|c cs IH]; cbn; [reflexivity|]. rewrite IH. destruct c; reflexivity. Qed.

Lemma rw_cells_iff : forall segs m A cs,
  CJ.Lib.Step.rw_cells segs m A (map cell_to cs) <-> lib.Lib.Step.rw_cells segs m A cs.
Proof.
  intros segs m A cs. unfold CJ.Lib.Step.rw_cells, lib.Lib.Step.rw_cells, CJ.Lib.Cells.cells_at, lib.Lib.Cells.cells_at.
  rewrite cells_wf_to, cells_bytes_to, cells_size_to. split; intros H; exact H.
Qed.

Lemma mem_inv_to_cj : forall segs m,
  lib.Lib.Mem.mem_inv segs m -> MemNorm.task_mem segs m -> CJ.Lib.Mem.mem_inv segs m.
Proof.
  intros segs m H T a b E. destruct (T a b E) as [S|S]; [left|right]; split; try exact S; exact (H a b E).
Qed.

Lemma mem_inv_of_cj : forall segs m,
  CJ.Lib.Mem.mem_inv segs m -> lib.Lib.Mem.mem_inv segs m /\ MemNorm.task_mem segs m.
Proof.
  intros segs m H. split.
  - intros a b E. destruct (H a b E) as [[R _]|[R _]]; exact R.
  - intros a b E. destruct (H a b E) as [[_ S]|[_ S]]; [left|right]; exact S.
Qed.
