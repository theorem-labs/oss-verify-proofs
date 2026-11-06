(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI5v.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK15 YM06.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI09 YI0m YI5w YI5z YI67.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma flush_upd_wf_frames : forall s i gen' rwcur', cg_frames (flush_upd s i gen' rwcur') =
list_set (cg_frames s) i (option_map (fun f => set_fr_gen f gen') (nth i (cg_frames s) None)).
Proof. intros. reflexivity. Qed.
Lemma inFP_blocks_fp : forall bl a, inFP (blocks_fp bl) a <-> exists b n, In (b, n) bl /\ b <= a < b + n.
Proof.
intros bl a. unfold inFP, blocks_fp. split.
- intros (r & Hr & Ha). apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha. exists b, n. auto.
- intros (b & n & Hin & Ha). exists (b, b + n). split; [| cbn; lia]. apply in_map_iff. exists (b, n). auto.
Qed.
Lemma frames_blocks_cons_some : forall N f fs, frames_blocks N (Some f :: fs) = frame_blocks N f ++ frames_blocks N fs.
Proof. intros. reflexivity. Qed.
Lemma nth_error_list_set_same : forall {X} (l : list X) i x, (i < length l)%nat -> nth_error (list_set l i x) i = Some x.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_error_list_set_other : forall {X} (l : list X) i j x, i <> j -> nth_error (list_set l i x) j = nth_error l j.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [exfalso; lia|]. apply IH. lia.
Qed.
Lemma nth_list_set_other : forall {X} (l : list X) i j x d, i <> j -> nth j (list_set l i x) d = nth j l d.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] [|j] x d Hij; cbn; try reflexivity; [exfalso; lia|]. apply IH. lia.
Qed.
Lemma length_list_set : forall {X} (l : list X) i x, length (list_set l i x) = length l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
End e.
