(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint mk_wcells (szs : list nat) (ws : list word) : list cell :=
  match szs, ws with
  | 8%nat :: s, w :: r => C8 w :: mk_wcells s r
  | 4%nat :: s, w :: r => C4 w :: mk_wcells s r
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition h5_sizes : list nat :=
  [8;4;4;4;4; 8;8;8;8;8;8;8; 4;4; 8;8; 4;4;4;4; 8; 4;4;4;4; 8;8;8;8;8;8;8;8;8; 4;4;4;4; 8;8;8; 8;8; 4]%nat.
Definition h5_cells (ws : list word) : list cell := mk_wcells h5_sizes ws.

Definition H5_headerSize : nat := 0.          Definition H5_format : nat := 1.
Definition H5_forceIgnoreChecksum : nat := 2. Definition H5_validateChecksum : nat := 3.
Definition H5_litPtr : nat := 5.
Definition H5_customAlloc : nat := 6.         Definition H5_customFree : nat := 7.        Definition H5_customOpaque : nat := 8.
Definition H5_litSize : nat := 9.             Definition H5_rleSize : nat := 10.          Definition H5_staticSize : nat := 11.
Definition H5_isFrameDecompression : nat := 12.
Definition H5_ddictLocal : nat := 14.         Definition H5_ddict : nat := 15.            Definition H5_dictID : nat := 16.
Definition H5_ddictIsCold : nat := 17.        Definition H5_dictUses : nat := 18.         Definition H5_ddictSet : nat := 20.
Definition H5_refMultipleDDicts : nat := 21.  Definition H5_disableHufAsm : nat := 22.    Definition H5_maxBlockSizeParam : nat := 23.
Definition H5_streamStage : nat := 24.        Definition H5_inBuff : nat := 25.
Definition H5_litBuffer : nat := 41.          Definition H5_litBufferEnd : nat := 42.     Definition H5_litBufferLocation : nat := 43.

Definition wnth (ws : list word) (i : nat) : word := nth i ws (Z_to_bv 64 0).
Fixpoint wupd (ws : list word) (i : nat) (v : word) : list word :=
  match ws, i with
  | [], _ => []
  | _ :: r, O => v :: r
  | w :: r, S i' => w :: wupd r i' v
  end.

Lemma h5_cells_size : forall ws, length ws = 44%nat -> cells_size (h5_cells ws) = 276%nat.
Proof.
  intros ws L. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [reflexivity| discriminate L].
Qed.

(* [comment removed for export] *)
Ltac h5_open_rec ws L n :=
  lazymatch n with
  | O => destruct ws; [| discriminate L]
  | S ?n' => let r := fresh "wr" in destruct ws as [|? r]; [discriminate L|]; h5_open_rec r L n'
  end.
Ltac h5_open ws L :=
  h5_open_rec ws L 44%nat; clear L;
  cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth wupd nth
                       H5_headerSize H5_format H5_forceIgnoreChecksum H5_validateChecksum H5_litPtr H5_customAlloc H5_customFree
                       H5_customOpaque H5_litSize H5_rleSize H5_staticSize H5_isFrameDecompression H5_ddictLocal H5_ddict H5_dictID
                       H5_ddictIsCold H5_dictUses H5_ddictSet H5_refMultipleDDicts H5_disableHufAsm H5_maxBlockSizeParam H5_streamStage
                       H5_inBuff H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in *.

Section Rep.
Variable segs : list Segment.
Notation fmem := (word -> option byte).

Definition dctx_ptrs (m : fmem) (DCTX : Z) (llt mlt oft huf : word) : Prop :=
  rw_cells segs m DCTX [C8 llt; C8 mlt; C8 oft; C8 huf].
Definition dctx_h1 (m : fmem) (DCTX : Z) (pde pfx vst dend expd : word) : Prop :=
  rw_cells segs m (DCTX + 29888) [C8 pde; C8 pfx; C8 vst; C8 dend; C8 expd].
Definition dctx_fp (m : fmem) (DCTX : Z) (fp : list cell) : Prop :=
  rw_cells segs m (DCTX + 29928) fp /\ cells_size fp = 48%nat.
Definition dctx_h3 (m : fmem) (DCTX : Z) (pcs dsz bt stg le fe : word) : Prop :=
  rw_cells segs m (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe].
Definition dctx_xs (m : fmem) (DCTX : Z) (xs : list cell) : Prop :=
  rw_cells segs m (DCTX + 30008) xs /\ cells_size xs = 88%nat.
Definition dctx_h5 (m : fmem) (DCTX : Z) (ws : list word) : Prop :=
  rw_cells segs m (DCTX + 30096) (h5_cells ws) /\ length ws = 44%nat.
Definition dctx_tx (m : fmem) (DCTX : Z) (jhb : list byte) (ovd dcb dce trace : word) : Prop :=
  rw_cells segs m (DCTX + 95940) [CB 20 jhb; C8 ovd; C8 dcb; C8 dce; C8 trace].
(* [comment removed for export] *)
Definition dctx_owned (m : fmem) (DCTX : Z) : Prop :=
  stk segs m (DCTX + 32) (DCTX + 29888) /\ stk segs m (DCTX + 30372) (DCTX + 95940).
End Rep.
