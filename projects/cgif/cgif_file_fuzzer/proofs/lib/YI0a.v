(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15 YI16 YI17.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition zbytes (pl : list byte) : list Z := map (fun b : byte => bv_unsigned b) pl.
Definition bytes8 (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Definition ff_leaf (K : lleaf -> TSet) (fs : Fs.Fs) : TSet := K (LL 0 fs []).
Definition ff_unl (K : lleaf -> TSet) (fs : Fs.Fs) : TSet :=
unlink_shape fs (ff_leaf K fs) (ff_leaf K (Fs.fs_remove fs sink_path)).
Definition ff_content (g : YO07.gcfg) (loops : Z) (rest : list Z) : list Z :=
if g_sgct_ok g then ff_file g loops rest else [].
Definition ff_libk (pl : list byte) (fs : Fs.Fs) (K : lleaf -> TSet) : TSet :=
match ff_cfg (zbytes pl) with
| None => ff_leaf K fs
| Some (g, loops, rest) =>
if g_opens g
then openat_shape fs (ff_unl K fs) (ff_unl K (Fs.fs_set fs sink_path (bytes8 (ff_content g loops rest))))
else ff_unl K fs
end.
Definition FF_CALLS : Z := 324.
Definition FF_PEAK  : Z := FF_CALLS * MMAX + 3 * 2 ^ 29.
Definition FF_MAXREQ : Z := 2 ^ 28 - 2 ^ 16.
Definition ff_delta (n : Z) (b : rbound) : rbound :=
RB (rb_bytes b + FF_CALLS * MMAX + 2 ^ 24) (rb_cnt b + FF_CALLS) (rb_hand b + 65 * FF_CALLS) (rb_brk b + 2 * PGSZ * FF_CALLS).
Definition ff_peak (b : rbound) : rbound :=
RB (rb_bytes b + FF_PEAK) (rb_cnt b + FF_CALLS) (rb_hand b + 65 * FF_CALLS) (rb_brk b + 2 * PGSZ * FF_CALLS).
Definition ff_room (b : rbound) (n : Z) : Prop := room (ff_peak b) FF_MAXREQ.
Lemma t_alt2_ext : forall A A' B B', t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). tauto. Qed.
Lemma unlink_shape_ext : forall fs A A' B B', t_eq A A' -> t_eq B B' -> t_eq (unlink_shape fs A B) (unlink_shape fs A' B').
Proof.
intros fs A A' B B' HA HB. unfold unlink_shape. destruct (fs_under fs sink_path); [exact HA|].
destruct (Fs.fs_lookup fs sink_path); [apply t_alt2_ext; assumption | exact HA].
Qed.
Lemma openat_shape_ext : forall fs A A' B B', t_eq A A' -> t_eq B B' -> t_eq (openat_shape fs A B) (openat_shape fs A' B').
Proof. intros fs A A' B B' HA HB. unfold openat_shape. destruct (fs_under fs sink_path); [exact HA | apply t_alt2_ext; assumption]. Qed.
Lemma ff_unl_ext : forall K K' fs, (forall l, t_eq (K l) (K' l)) -> t_eq (ff_unl K fs) (ff_unl K' fs).
Proof. intros K K' fs HK. unfold ff_unl, ff_leaf. apply unlink_shape_ext; apply HK. Qed.
Lemma ff_libk_ext : forall pl fs K K', (forall l, t_eq (K l) (K' l)) -> t_eq (ff_libk pl fs K) (ff_libk pl fs K').
Proof.
intros pl fs K K' HK. unfold ff_libk. destruct (ff_cfg (zbytes pl)) as [[[g loops] rest]|]; [| apply HK].
destruct (g_opens g); [apply openat_shape_ext; apply ff_unl_ext; exact HK | apply ff_unl_ext; exact HK].
Qed.
#[global] Instance ff_lib_shape : lib_shape := {|
LIBK := ff_libk;
LIBK_ext := ff_libk_ext;
lib_delta := ff_delta;
lib_room := ff_room |}.
