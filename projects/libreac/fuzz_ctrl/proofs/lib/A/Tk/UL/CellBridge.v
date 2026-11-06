(* The cell / write-set bridge between the lib.Lib engine and this (lib.A.Tk.UL) engine.
   lib.A.Tk.UL.Cells.cell and lib.Lib.Cells.cell are two distinct inductives with the same five
   constructors and the same csize / cbytes / cell_wf bodies, and lib.A.Tk.UL.Frame.outside is a
   second copy of lib.Lib.Frame.outside, so a statement over one copy is not convertible with the
   same statement over the other -- although every other word of those statements (bytes_at,
   cells_at, wr_at, wmono, MS, mkR, seg_rom, mstep) has the same body in the two copies and needs
   no lemma. ul_cell_lib / lib_cell_ul translate constructor by constructor; csize, cbytes,
   cell_wf, cells_size, cells_bytes, cells_wf, cells_at, ro_cells, rw_cells, outside and munch
   transfer by induction. Everything is stated for an arbitrary [segs], and the file depends only on
   lib.Lib.Cells / Step / Frame and this engine's Cells / Step / Frame, so image-A and image-B
   segment files can both use it (image B has its own UL engine: lib/B/Tk/UL).
   SOURCE: this file is a Theorem Labs lane's lib/B/Tk/UL/CellBridge.v 7761521b3b52 (the blob this tree had at release c5e779efe8c) at
   a working branch 7cfcf43257e, with the module paths changed from lib.B.Tk.UL to
   lib.A.Tk.UL; the names, the statements and the scripts are a Theorem Labs lane's, unchanged.
   Provenance: route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane ("A4: what would lift the
   refusal"). Image A = fuzz_ctrl.asan, libreac v1.9.0 (pau-libreac-v190), sha256
   aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d; measured against this image
   only. rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Cells Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Cells Step Frame.
Import ListNotations.
Open Scope Z_scope.

Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module UC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.
Module US := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Step.
Module UF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.

(* ---- the two translations ---- *)
Definition ul_cell_lib (c : UC.cell) : LC.cell :=
  match c with
  | UC.C8 v => LC.C8 v | UC.C4 v => LC.C4 v | UC.C2 v => LC.C2 v
  | UC.C1 b => LC.C1 b | UC.CB n bs => LC.CB n bs
  end.

Definition lib_cell_ul (c : LC.cell) : UC.cell :=
  match c with
  | LC.C8 v => UC.C8 v | LC.C4 v => UC.C4 v | LC.C2 v => UC.C2 v
  | LC.C1 b => UC.C1 b | LC.CB n bs => UC.CB n bs
  end.

Lemma ul_cell_lib_ul : forall c, lib_cell_ul (ul_cell_lib c) = c.
Proof. intros [v|v|v|b|n bs]; reflexivity. Qed.
Lemma lib_cell_ul_lib : forall c, ul_cell_lib (lib_cell_ul c) = c.
Proof. intros [v|v|v|b|n bs]; reflexivity. Qed.

(* ---- UL -> lib.Lib ---- *)
Lemma csize_ul_cell_lib : forall c, LC.csize (ul_cell_lib c) = UC.csize c.
Proof. intros [v|v|v|b|n bs]; reflexivity. Qed.
Lemma cbytes_ul_cell_lib : forall c, LC.cbytes (ul_cell_lib c) = UC.cbytes c.
Proof. intros [v|v|v|b|n bs]; reflexivity. Qed.
Lemma cell_wf_ul_cell_lib : forall c, UC.cell_wf c -> LC.cell_wf (ul_cell_lib c).
Proof. intros [v|v|v|b|n bs] H; exact H. Qed.

Lemma cells_size_ul_cell_lib : forall cs, LC.cells_size (map ul_cell_lib cs) = UC.cells_size cs.
Proof.
  induction cs as [|c cs IH]; [reflexivity|].
  cbn [map LC.cells_size UC.cells_size]. rewrite csize_ul_cell_lib, IH. reflexivity.
Qed.

Lemma cells_bytes_ul_cell_lib : forall cs, LC.cells_bytes (map ul_cell_lib cs) = UC.cells_bytes cs.
Proof.
  induction cs as [|c cs IH]; [reflexivity|].
  cbn [map LC.cells_bytes UC.cells_bytes]. rewrite cbytes_ul_cell_lib, IH. reflexivity.
Qed.

Lemma cells_wf_ul_cell_lib : forall cs, UC.cells_wf cs -> LC.cells_wf (map ul_cell_lib cs).
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|].
  destruct H as [H1 H2]. split; [apply cell_wf_ul_cell_lib, H1 | apply IH, H2].
Qed.

Lemma cells_at_ul_lib : forall segs m A cs,
  UC.cells_at segs m A cs -> LC.cells_at segs m A (map ul_cell_lib cs).
Proof.
  intros segs m A cs [Hwf Hb]. split; [apply cells_wf_ul_cell_lib, Hwf|].
  rewrite cells_bytes_ul_cell_lib. exact Hb.
Qed.

Lemma ro_cells_ul_lib : forall segs m A cs,
  US.ro_cells segs m A cs -> LS.ro_cells segs m A (map ul_cell_lib cs).
Proof. intros segs m A cs H. apply cells_at_ul_lib, H. Qed.

Lemma rw_cells_ul_lib : forall segs m A cs,
  US.rw_cells segs m A cs -> LS.rw_cells segs m A (map ul_cell_lib cs).
Proof.
  intros segs m A cs [Hat Hw]. split; [apply cells_at_ul_lib, Hat|].
  rewrite cells_size_ul_cell_lib. exact Hw.
Qed.

(* ---- lib.Lib -> UL ---- *)
Lemma csize_lib_cell_ul : forall c, UC.csize (lib_cell_ul c) = LC.csize c.
Proof. intros [v|v|v|b|n bs]; reflexivity. Qed.
Lemma cbytes_lib_cell_ul : forall c, UC.cbytes (lib_cell_ul c) = LC.cbytes c.
Proof. intros [v|v|v|b|n bs]; reflexivity. Qed.
Lemma cell_wf_lib_cell_ul : forall c, LC.cell_wf c -> UC.cell_wf (lib_cell_ul c).
Proof. intros [v|v|v|b|n bs] H; exact H. Qed.

Lemma cells_size_lib_cell_ul : forall cs, UC.cells_size (map lib_cell_ul cs) = LC.cells_size cs.
Proof.
  induction cs as [|c cs IH]; [reflexivity|].
  cbn [map LC.cells_size UC.cells_size]. rewrite csize_lib_cell_ul, IH. reflexivity.
Qed.

Lemma cells_bytes_lib_cell_ul : forall cs, UC.cells_bytes (map lib_cell_ul cs) = LC.cells_bytes cs.
Proof.
  induction cs as [|c cs IH]; [reflexivity|].
  cbn [map LC.cells_bytes UC.cells_bytes]. rewrite cbytes_lib_cell_ul, IH. reflexivity.
Qed.

Lemma cells_wf_lib_cell_ul : forall cs, LC.cells_wf cs -> UC.cells_wf (map lib_cell_ul cs).
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|].
  destruct H as [H1 H2]. split; [apply cell_wf_lib_cell_ul, H1 | apply IH, H2].
Qed.

Lemma cells_at_lib_ul : forall segs m A cs,
  LC.cells_at segs m A cs -> UC.cells_at segs m A (map lib_cell_ul cs).
Proof.
  intros segs m A cs [Hwf Hb]. split; [apply cells_wf_lib_cell_ul, Hwf|].
  rewrite cells_bytes_lib_cell_ul. exact Hb.
Qed.

Lemma ro_cells_lib_ul : forall segs m A cs,
  LS.ro_cells segs m A cs -> US.ro_cells segs m A (map lib_cell_ul cs).
Proof. intros segs m A cs H. apply cells_at_lib_ul, H. Qed.

Lemma rw_cells_lib_ul : forall segs m A cs,
  LS.rw_cells segs m A cs -> US.rw_cells segs m A (map lib_cell_ul cs).
Proof.
  intros segs m A cs [Hat Hw]. split; [apply cells_at_lib_ul, Hat|].
  rewrite cells_size_lib_cell_ul. exact Hw.
Qed.

(* ---- the write set: outside / munch (two copies of the same fixpoint) ----
   wmono is stated through the semantics' own wview, so it is the same statement in both copies and
   needs no lemma. *)
Lemma outside_ul_lib : forall (W : list (Z * Z)) (x : Z), UF.outside W x -> LF.outside W x.
Proof.
  induction W as [|p W IH]; intros x H; [exact I|].
  destruct p as [lo hi]. cbn [UF.outside] in H. destruct H as [H1 H2].
  cbn [LF.outside]. split; [exact H1 | apply IH; exact H2].
Qed.

Lemma outside_lib_ul : forall (W : list (Z * Z)) (x : Z), LF.outside W x -> UF.outside W x.
Proof.
  induction W as [|p W IH]; intros x H; [exact I|].
  destruct p as [lo hi]. cbn [LF.outside] in H. destruct H as [H1 H2].
  cbn [UF.outside]. split; [exact H1 | apply IH; exact H2].
Qed.

Lemma munch_ul_lib : forall (W : list (Z * Z)) m m', UF.munch W m m' -> LF.munch W m m'.
Proof. intros W m m' H x Hx. apply H. apply outside_lib_ul. exact Hx. Qed.

Lemma munch_lib_ul : forall (W : list (Z * Z)) m m', LF.munch W m m' -> UF.munch W m m'.
Proof. intros W m m' H x Hx. apply H. apply outside_ul_lib. exact Hx. Qed.
