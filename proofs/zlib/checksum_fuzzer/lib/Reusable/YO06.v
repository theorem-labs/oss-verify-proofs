(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia String Ascii FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK15 YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition payload (data : list byte) : list byte := skipn (Z.to_nat (HDR_MIN + config_len data)) data.
Lemma payload_length data : HDR_MIN + config_len data <= dlen data -> Z.of_nat (length (payload data)) = payload_len data.
Proof.
intros H. unfold payload, payload_len, dlen in *. rewrite length_skipn.
assert (0 <= config_len data) by (unfold config_len; apply Z.mod_pos_bound; lia).
unfold HDR_MIN in *. rewrite Nat2Z.inj_sub by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Definition leaf_shapeX (data : list byte) (fs : Fs) (r : dleaf * astate) : TSet :=
match fst r with
| DL_run _ _ _ => run_shape (payload data) (calls data) fs
| _ => leaf_shape data fs r
end.
Definition SPECX_loaded (data : list byte) (fs : Fs) : TSet :=
tset (driver_tree data) (leaf_shapeX data fs).
Definition SPECX_args (argv : list (list byte)) (fs : Fs) : TSet :=
match argv with
| [_; p] =>
match classify_open p fs with
| OpenFails => diag (msg_cannot_open p) fs
| OpenDir => t_alt2 (diag (msg_cannot_open p) fs) (SPEC_dir p fs)
| OpenFile data => t_alt2 (diag (msg_cannot_open p) fs) (SPECX_loaded data fs)
end
| _ => diag (msg_usage (nth 0 argv [])) fs
end.
Definition SPECX (inp : ProcInput) : TSet := SPECX_args (in_argv inp) (in_fs inp).
Record driver_obligationsX : Prop := {
do_jinvX : forall data fs, jinv (leaf_shapeX data fs) (driver_tree data);
do_gtreeX : forall data, gtree mgrant (driver_tree data)
}.
Theorem do_jinvX_proved : forall data fs, jinv (leaf_shapeX data fs) (driver_tree data).
Proof.
intros data fs. unfold driver_tree, driver_m.
pose proof wf_init as HW.
jwalk.
all: apply jinv_mbind;
[ eapply jinv_malloc_nonesome;
[ eassumption
| unfold payload_len, HDR_MIN, config_len, dlen in *; bool_hyps; lia
| intros; cbv beta iota; cbn [tset ret fst snd leaf_shapeX leaf_shape]; apply t_eq_refl
| intros; cbv beta iota; cbn [tset ret fst snd leaf_shapeX leaf_shape]; apply t_eq_refl ]
| intros ? [?|] ? ?; cbv beta iota; exact I ].
Qed.
Theorem driver_obligationsX_proved : driver_obligationsX.
Proof. split; [exact do_jinvX_proved | exact do_gtree_proved]. Qed.
Lemma leaves_bind_assoc {A B C} (P : C * astate -> Prop) (m : M A) (f : A -> M B) (g : B -> M C) s :
leaves P (bind (bind m f) g s) -> leaves P (bind m (fun a => bind (f a) g) s).
Proof. rewrite bind_assoc. exact (fun H => H). Qed.
Lemma leaves_ibind_inv {A B} (P : B -> Prop) : forall (t : itree astate A) (f : A -> itree astate B),
leaves P (ibind t f) -> leaves (fun a => leaves P (f a)) t.
Proof. induction t as [a | q s0 k IH | e]; cbn; intros f H; auto. Qed.
Lemma leaves_mbind_after {A B} (P : B * astate -> Prop) (m : M A) (f : A -> M B) s tr a s' :
leaves P (bind m f s) -> cpath (m s) tr (a, s') -> leaves P (f a s').
Proof.
intros H Hp. unfold bind in H. apply leaves_ibind_inv in H.
exact (leaves_cpath _ _ _ _ H Hp).
Qed.
End b.
