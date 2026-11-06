(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/U/Reusable/YO06.v, which re-exports lib/Reusable/YO06.v (the Copyright line and the SPDX line), and lib/U/ZTraceSpec.v for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/U/Reusable/YO06.v (= lib/Reusable/YO06.v) and lib/U/ZTraceSpec.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.FrameRetD2. *)
From Stdlib Require Import ZArith List Bool Lia String Ascii FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK15 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import TraceHalting AllocSlots AllocRoom ZTraceSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
(* YO06.v leaf_shapeX, with run_shape_r *)
Definition leaf_shapeX_r (data : list byte) (fs : Fs) (r : dleaf * astate) : TSet :=
match fst r with
| DL_run _ _ _ => run_shape_r (payload data) (calls data) fs
| _ => leaf_shape data fs r
end.
Definition SPECX_loaded_r (data : list byte) (fs : Fs) : TSet :=
tset (driver_tree data) (leaf_shapeX_r data fs).
Definition SPECX_args_r (argv : list (list byte)) (fs : Fs) : TSet :=
match argv with
| [_; p] =>
match classify_open p fs with
| OpenFails => diag (msg_cannot_open p) fs
| OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_dir p fs)
| OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (SPECX_loaded_r data fs)
end
| _ => diag (msg_usage (nth 0 argv [])) fs
end.
Definition SPECX_r (inp : ProcInput) : TSet := SPECX_args_r (in_argv inp) (in_fs inp).

(* YO06.v do_jinvX_proved, for leaf_shapeX_r; the same script *)
Theorem do_jinvX_r_proved : forall data fs, jinv (leaf_shapeX_r data fs) (driver_tree data).
Proof.
intros data fs. unfold driver_tree, driver_m.
pose proof wf_init as HW.
jwalk.
all: apply jinv_mbind;
[ eapply jinv_malloc_nonesome;
[ eassumption
| unfold payload_len, HDR_MIN, config_len, dlen in *; bool_hyps; lia
| intros; cbv beta iota; cbn [tset ret fst snd leaf_shapeX_r leaf_shape]; apply t_eq_refl
| intros; cbv beta iota; cbn [tset ret fst snd leaf_shapeX_r leaf_shape]; apply t_eq_refl ]
| intros ? [?|] ? ?; cbv beta iota; exact I ].
Qed.

(* where every call on pl returns 0, run_shape_r is the kit's run_shape *)
Lemma run_shape_r_of_0 : forall pl, (forall fs K, LIBK pl fs K = K (LL 0 fs [])) ->
  forall k fs, run_shape_r pl k fs = run_shape pl k fs.
Proof. intros pl H [|k] fs; [reflexivity|]. cbn [run_shape_r run_shape]. rewrite !H. reflexivity. Qed.

Lemma leaf_shapeX_r_of_0 : forall data, (forall fs K, LIBK (payload data) fs K = K (LL 0 fs [])) ->
  forall fs r, leaf_shapeX_r data fs r = leaf_shapeX data fs r.
Proof.
intros data H fs [dl a]. destruct dl; cbn [leaf_shapeX_r leaf_shapeX fst]; try reflexivity.
apply run_shape_r_of_0. exact H.
Qed.
End b.

(* The shape whose LIBK is the constant T0: under it the kit's run_shape on k >= 1 calls is T0. *)
Definition shape_at (T0 : Fs -> TSet) : lib_shape.
Proof.
refine {| LIBK := fun _ fs _ => T0 fs; lib_delta := fun _ b => b; lib_room := fun _ _ => True |}.
intros pl fs K K' _. apply t_eq_refl.
Defined.

Lemma run_shape_at {LS : lib_shape} : forall pl k fs,
  t_eq (run_shape_r (LS:=LS) pl k fs) (run_shape (LS:=shape_at (fun fs0 => run_shape_r (LS:=LS) pl k fs0)) pl k fs).
Proof.
intros pl [|k] fs; [apply t_eq_refl|].
change (run_shape (LS:=shape_at (fun fs0 => run_shape_r (LS:=LS) pl (S k) fs0)) pl (S k) fs)
  with (run_shape_r (LS:=LS) pl (S k) fs).
apply t_eq_refl.
Qed.

Lemma leaf_shapeX_r_at {LS : lib_shape} : forall data fs r,
  t_eq (leaf_shapeX_r (LS:=LS) data fs r)
       (leaf_shapeX (LS:=shape_at (fun fs0 => run_shape_r (LS:=LS) (payload data) (calls data) fs0)) data fs r).
Proof.
intros data fs [dl a]. destruct dl as [ | | | | | b c q]; cbn [leaf_shapeX_r leaf_shapeX fst];
  first [ exact (t_eq_refl _) | exact (run_shape_at (YO06.payload data) (calls data) fs) ].
Qed.

(* ZTraceSpec.v checksum_shape, with the leaf of the return ret pl *)
Definition ret_shape (ret : list byte -> Z) : lib_shape.
Proof.
refine {| LIBK := fun pl fs K => K (LL (ret pl) fs []);
  lib_delta := fun n b => b;
  lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX |}.
intros pl fs K K' H. apply H.
Defined.

Lemma ret_permitted : forall ret, shape_permitted (ret_shape ret).
Proof. intros ret pl fs K HK. exact (HK _). Qed.

Section Model.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Hypothesis LSP : shape_permitted LS.
(* ZTraceSpec.v zpermitted_run, for run_shape_r *)
Lemma zpermitted_run_r : forall pl k fs, permitted_traces zallowed (run_shape_r pl k fs).
Proof using LSP.
intros pl [|k] fs; cbn [run_shape_r].
- apply permitted_ex. left; reflexivity.
- apply LSP. intros l. apply permitted_wr. apply (zpermitted_iter LSP). intros fs'.
  unfold run_tail_r. destruct k; try apply permitted_wr;
    apply permitted_ex; left; reflexivity.
Qed.
Lemma zpermitted_leafX_r : forall data fs r, permitted_traces zallowed (leaf_shapeX_r data fs r).
Proof using LSP.
intros data fs [dl a]. destruct dl; cbn [leaf_shapeX_r fst];
  try apply zpermitted_leaf; apply zpermitted_run_r.
Qed.
(* ZTraceSpec.v checksum_SPECX_exits_allowed, for SPECX_r *)
Theorem SPECX_r_exits_allowed : forall inp, permitted_traces zallowed (SPECX_r inp).
Proof using LSP.
intros inp. unfold SPECX_r, SPECX_args_r.
destruct (in_argv inp) as [|a [|p [|b rest]]]; try solve [apply zpermitted_diag].
destruct (classify_open p (in_fs inp)) as [| |data].
- apply zpermitted_diag.
- apply permitted_alt2; [apply zpermitted_diag|].
  unfold SPEC_dir. apply permitted_tset. intros [b s].
  destruct b; apply zpermitted_diag.
- apply permitted_alt2; [apply zpermitted_diag|].
  unfold SPECX_loaded_r. apply permitted_tset. apply zpermitted_leafX_r.
Qed.
End Model.
