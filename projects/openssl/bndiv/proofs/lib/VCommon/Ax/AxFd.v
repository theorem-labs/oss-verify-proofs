(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run Fs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliVerdict.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxSys AxEntryRel AxOcc AxFresh.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition std_fds3 : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Definition fd3w : word := Z_to_bv 64 3.

Definition fds_of (ρ : valuation) (f : afd) : list (word * FdEntry) :=
  match f with
  | FDStd => std_fds3
  | FDDir => fd_insert std_fds3 fd3w FdDir
  | FDFile off _ _ _ => fd_insert std_fds3 fd3w (FdFile (dec_str 1 ρ) (Z_to_bv 64 (leval ρ off)))
  | FDDone _ _ _ => std_fds3
  end.

(* [comment removed for export] *)
Definition dec_argvB (ρ : valuation) : list (list byte) :=
  map (fun k => dec_str (Z.of_nat k) ρ) (seq 0 (Z.to_nat (ρ v_argc mod 1025))).

(* [comment removed for export] *)
Definition file_vars_ok (fs0 : Fs.Fs) (ρ : valuation) (vl vb0 vb1 : int) : Prop :=
  exists data, fs_lookup fs0 (dec_str 1 ρ) = Some data /\ Z.min (Z.of_nat (length data)) (2 ^ 62) = ρ vl
    /\ bv_unsigned (nth 0 data (Z_to_bv 8 0)) = ρ vb0 /\ bv_unsigned (nth 1 data (Z_to_bv 8 0)) = ρ vb1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition good_inp (fs0 : Fs.Fs) (ρ : valuation) : Prop := valid_argv (dec_argvB ρ).

Definition fd_rel (fs0 : Fs.Fs) (ρ : valuation) (f : afd) (fds : list (word * FdEntry)) : Prop :=
  good_inp fs0 ρ /\ fds = fds_of ρ f /\
  match f with FDFile _ vl vb0 vb1 | FDDone vl vb0 vb1 => file_vars_ok fs0 ρ vl vb0 vb1 | _ => True end.

Lemma afd_occ_ts (v : int) (off : lin) (vl vb0 vb1 : int) :
  afd_occ v (FDFile off vl vb0 vb1) = entry_var v || (ts_occ v (snd off) || (v =? vl)%uint63 || (v =? vb0)%uint63 || (v =? vb1)%uint63).
Proof. reflexivity. Qed.

Lemma afd_occ_done (v : int) (vl vb0 vb1 : int) :
  afd_occ v (FDDone vl vb0 vb1) = entry_var v || ((v =? vl)%uint63 || (v =? vb0)%uint63 || (v =? vb1)%uint63).
Proof. reflexivity. Qed.

Lemma afd_occ_entry (v : int) (f : afd) : afd_occ v f = false -> entry_var v = false.
Proof. unfold afd_occ. intros H. apply orb_false_iff in H as [H _]. exact H. Qed.

Lemma fds_of_agree (v : int) (ρ ρ' : valuation) (f : afd) :
  (forall x, x <> v -> ρ' x = ρ x) -> afd_occ v f = false -> fds_of ρ' f = fds_of ρ f.
Proof.
  intros Hag Ho. destruct f as [| |off vl vb0 vb1|vl vb0 vb1]; [reflexivity | reflexivity| |reflexivity]. cbn [fds_of].
  rewrite afd_occ_ts in Ho. apply orb_false_iff in Ho as [He Ho]. repeat (apply orb_false_iff in Ho as [Ho ?]). rename Ho into Ht.
  rewrite (dec_str_agree ρ ρ' 1).
  - rewrite (leval_agree v ρ ρ' Hag off Ht). reflexivity.
  - intros x Hx. apply Hag. intros ->. rewrite He in Hx. discriminate Hx.
Qed.

Lemma entry_agree_of (v : int) (ρ ρ' : valuation) :
  (forall x, x <> v -> ρ' x = ρ x) -> entry_var v = false -> forall x, entry_var x = true -> ρ' x = ρ x.
Proof. intros Hag He x Hx. apply Hag. intros ->. rewrite He in Hx. discriminate Hx. Qed.

Lemma dec_argvB_agree (ρ ρ' : valuation) : (forall x, entry_var x = true -> ρ' x = ρ x) -> dec_argvB ρ' = dec_argvB ρ.
Proof.
  intros H. unfold dec_argvB. rewrite (H v_argc) by reflexivity.
  apply map_ext. intros k. apply dec_str_agree. exact H.
Qed.

(* [comment removed for export] *)
Lemma fd_rel_agree (fs0 : Fs.Fs) (v : int) (ρ ρ' : valuation) (f : afd) (fds : list (word * FdEntry)) :
  (forall x, x <> v -> ρ' x = ρ x) -> afd_occ v f = false -> fd_rel fs0 ρ f fds -> fd_rel fs0 ρ' f fds.
Proof.
  intros Hag Ho [HV [Hf Hd]]. pose proof (afd_occ_entry v f Ho) as He. pose proof (entry_agree_of v ρ ρ' Hag He) as Hen.
  split; [unfold good_inp in *; rewrite (dec_argvB_agree ρ ρ' Hen); exact HV|]. split; [rewrite (fds_of_agree v ρ ρ' f Hag Ho); exact Hf|].
  destruct f as [| |off vl vb0 vb1|vl vb0 vb1]; [exact I | exact I| |].
  - rewrite afd_occ_ts in Ho. apply orb_false_iff in Ho as [_ Ho]. repeat (apply orb_false_iff in Ho as [Ho ?]).
    destruct Hd as [data (E1 & E2 & E3 & E4)]. exists data. rewrite (dec_str_agree ρ ρ' 1 Hen).
    repeat match goal with X : (v =? ?y)%uint63 = false |- _ => rewrite (Hag y) by (intros X'; subst y; rewrite Uint63.eqb_refl in X; discriminate X); clear X end.
    repeat split; assumption.
  - rewrite afd_occ_done in Ho. apply orb_false_iff in Ho as [_ Ho]. repeat (apply orb_false_iff in Ho as [Ho ?]).
    destruct Hd as [data (E1 & E2 & E3 & E4)]. exists data. rewrite (dec_str_agree ρ ρ' 1 Hen).
    repeat match goal with X : (v =? ?y)%uint63 = false |- _ => rewrite (Hag y) by (intros X'; subst y; rewrite Uint63.eqb_refl in X; discriminate X); clear X end.
    repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma fds_of_std2 (ρ : valuation) (f : afd) : fd_lookup (fds_of ρ f) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. destruct f; reflexivity. Qed.

Lemma fd_rel_lookup2 (fs0 : Fs.Fs) (ρ : valuation) (f : afd) (fds : list (word * FdEntry)) :
  fd_rel fs0 ρ f fds -> fd_lookup fds (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Proof. intros [_ [-> _]]. apply fds_of_std2. Qed.

Lemma fd_rel_std (fs0 : Fs.Fs) (ρ : valuation) (fds : list (word * FdEntry)) :
  good_inp fs0 ρ -> fds = std_fds3 -> fd_rel fs0 ρ FDStd fds.
Proof. intros HV ->. split; [exact HV | split; [reflexivity | exact I]]. Qed.
