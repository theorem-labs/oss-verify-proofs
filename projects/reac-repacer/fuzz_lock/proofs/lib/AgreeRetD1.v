(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/Reusable/YO06.v (SPECX) for a return value of the fuzz target of 0 or -1, the trace both builds walk in the agreement step *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/Reusable/YO06.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.AgreeRetD1.
   SPECX_q ret is YO06.v SPECX with the driver leaf chosen on the payload of the input file: the kit's leaf_shapeX where
   ret is 0 on that payload, Prog/FrameRetD2.v leaf_shapeX_r where it is -1. The agreement step takes any shape LS, so
   the frame's rewrite LIBK LS pl fs K = K (LL (ret pl) fs []) is not at hand; on a payload where ret is 0 the kit's
   arms walk the kit's leaf_shapeX unchanged. U/Prog/AgreeRetD2.v states the same trace for the UBSan build. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK15 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import FrameRet FrameRetD2.
Import ListNotations.
Local Open Scope Z_scope.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
(* the driver leaf on the payload of data: the kit's leaf_shapeX where ret is 0 there, leaf_shapeX_r where it is not *)
Definition leaf_shapeX_q (ret : list byte -> Z) (data : list byte) (fs : Fs) : dleaf * astate -> TSet :=
  if ret (payload data) =? 0 then leaf_shapeX data fs else leaf_shapeX_r data fs.
Definition SPECX_loaded_q (ret : list byte -> Z) (data : list byte) (fs : Fs) : TSet :=
  tset (driver_tree data) (leaf_shapeX_q ret data fs).
Definition SPECX_args_q (ret : list byte -> Z) (argv : list (list byte)) (fs : Fs) : TSet :=
  match argv with
  | [_; p] =>
    match classify_open p fs with
    | OpenFails => diag (msg_cannot_open p) fs
    | OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_dir p fs)
    | OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (SPECX_loaded_q ret data fs)
    end
  | _ => diag (msg_usage (nth 0 argv [])) fs
  end.
Definition SPECX_q (ret : list byte -> Z) (inp : ProcInput) : TSet := SPECX_args_q ret (in_argv inp) (in_fs inp).

Lemma do_jinvX_q : forall ret data fs, jinv (leaf_shapeX_q ret data fs) (driver_tree data).
Proof.
  intros ret data fs. unfold leaf_shapeX_q.
  destruct (ret (payload data) =? 0); [exact (do_jinvX_proved data fs) | exact (do_jinvX_r_proved data fs)].
Qed.

(* the shape under which the kit's leaf_shapeX on data is leaf_shapeX_q (the read loop takes the kit's leaf_shapeX) *)
Definition shape_q (ret : list byte -> Z) (data : list byte) : lib_shape :=
  if ret (payload data) =? 0 then LS else shape_at (fun fs0 => run_shape_r (LS:=LS) (payload data) (calls data) fs0).

Lemma leaf_shapeX_q_at : forall ret data fs r,
  t_eq (leaf_shapeX_q ret data fs r) (leaf_shapeX (LS:=shape_q ret data) data fs r).
Proof.
  intros ret data fs r. unfold leaf_shapeX_q, shape_q.
  destruct (ret (payload data) =? 0); [apply t_eq_refl | apply leaf_shapeX_r_at].
Qed.
End q.
