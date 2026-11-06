(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition kFsLog : Z := 20.
Definition kFsFlagsOffset : Z := 4096.
Definition kFsMinFrameLog : Z := 6.
Definition fs_nframes (cid : Z) : Z := 2 ^ (kFsLog - kFsMinFrameLog - cid).
Definition fs_frame_bytes (cid : Z) : Z := 2 ^ (kFsMinFrameLog + cid).
(* [comment removed for export] *)
Definition fs_flags_off (cid : Z) : Z := if cid =? 0 then 0 else fs_nframes 0.
Definition fs_flags_base (fs cid : Z) : Z := fs + kFsFlagsOffset + fs_flags_off cid.
Definition fs_flag_addr (fs cid pos : Z) : Z := fs_flags_base fs cid + pos.
(* [comment removed for export] *)
Definition fs_frames_base (fs cid : Z) : Z := fs + kFsFlagsOffset + 2 ^ (kFsLog + 1 - kFsMinFrameLog) + cid * 2 ^ kFsLog.
Definition fs_frame_addr (fs cid pos : Z) : Z := fs_frames_base fs cid + fs_frame_bytes cid * pos.
Definition fs_saved_flag_ptr (fs cid pos : Z) : Z := fs_frame_addr fs cid pos + fs_frame_bytes cid - 8.

Record fsstate := mkFS {
  fs_hint : gmap Z Z;          (* [comment removed for export] *)
  fs_live : gmap Z (gset Z)    (* [comment removed for export] *)
}.
Definition fsstate0 : fsstate := mkFS ∅ ∅.

Definition fs_get_hint (s : fsstate) (cid : Z) : Z := match fs_hint s !! cid with Some h => h | None => 0 end.
Definition fs_get_live (s : fsstate) (cid : Z) : gset Z := match fs_live s !! cid with Some l => l | None => ∅ end.

(* [comment removed for export] *)
Fixpoint fs_scan (live : gset Z) (N h : Z) (i : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f => if decide (((h + i) mod N) ∈ live) then fs_scan live N h (i + 1) f else Some i
  end.

(* [comment removed for export] *)
Definition fs_alloc (fs : Z) (s : fsstate) (cid : Z) : fsstate * option Z :=
  let N := fs_nframes cid in
  let h := fs_get_hint s cid in
  let live := fs_get_live s cid in
  (* [comment removed for export] *)
  match fs_scan live N h 0 (S (size live)) with
  | None => (mkFS (<[cid := h + N]> (fs_hint s)) (fs_live s), None)
  | Some i =>
      let pos := (h + i) mod N in
      (mkFS (<[cid := h + i + 1]> (fs_hint s)) (<[cid := {[pos]} ∪ live]> (fs_live s)), Some (fs_frame_addr fs cid pos))
  end.

(* [comment removed for export] *)
Definition fs_free (s : fsstate) (cid pos : Z) : fsstate :=
  mkFS (fs_hint s) (<[cid := fs_get_live s cid ∖ {[pos]}]> (fs_live s)).

Definition fs_pos_of_frame (fs cid frame : Z) : Z := (frame - fs_frames_base fs cid) / fs_frame_bytes cid.

(* [comment removed for export] *)
Example fs_sizes : fs_nframes 0 = 16384 /\ fs_nframes 1 = 8192 /\ fs_frame_bytes 0 = 64 /\ fs_frame_bytes 1 = 128
  /\ kFsFlagsOffset + 2 ^ (kFsLog + 1 - kFsMinFrameLog) + 11 * 2 ^ kFsLog = 11571200.
Proof. repeat split; reflexivity. Qed.

Lemma fs_scan_spec : forall live N h fuel i r,
  fs_scan live N h i fuel = Some r -> i <= r /\ ((h + r) mod N) ∉ live.
Proof.
  induction fuel as [|f IH]; intros i r H; cbn in H; [discriminate|].
  destruct (decide ((h + i) mod N ∈ live)) as [Hin|Hn].
  - apply IH in H. destruct H; split; [lia|assumption].
  - inversion H; subst. split; [lia|assumption].
Qed.
End RC__1.
