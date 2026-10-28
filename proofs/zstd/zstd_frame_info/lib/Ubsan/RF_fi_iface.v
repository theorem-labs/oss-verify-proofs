(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PFI_LTOI : Z := 0x12c8c.      (* [comment removed for export] *)
Definition PFI_ISFRAME : Z := 0x12d48.   (* [comment removed for export] *)
Definition PFI_FHSIZE : Z := 0x12db4.    (* [comment removed for export] *)
Definition PFI_GFHA : Z := 0x12e44.      (* [comment removed for export] *)
Definition PFI_GFH : Z := 0x1335c.       (* [comment removed for export] *)
Definition PFI_GFCS : Z := 0x13364.      (* [comment removed for export] *)
Definition PFI_FDS : Z := 0x133b8.       (* [comment removed for export] *)
Definition PFI_FFCS : Z := 0x1359c.      (* [comment removed for export] *)
Definition PFI_GDS : Z := 0x135c8.       (* [comment removed for export] *)
Definition PFI_DBOUND : Z := 0x13634.    (* [comment removed for export] *)
Definition PFI_FFSI : Z := 0x136ec.      (* [comment removed for export] *)
Definition PFI_GDID : Z := 0x138e8.      (* [comment removed for export] *)
Definition PFI_CBS : Z := 0x13938.       (* [comment removed for export] *)
Definition PFI_DIDTAB : Z := 0x10390.    (* [comment removed for export] *)
Definition PFI_FCSTAB : Z := 0x103b0.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition buf_at (m : fmem) (S : Z) (bl : list Z) : Prop :=
  bytes_at usegs m S (map (Z_to_bv 8) bl) /\ Forall (fun c => 0 <= c < 256) bl.

(* [comment removed for export] *)
Definition Znth (i : Z) (l : list Z) : Z := nth (Z.to_nat i) l 0.

Lemma buf_at_bound : forall m S bl, buf_at m S bl -> 0 <= S /\ S + zlen bl <= 2^64.
Proof. intros m S bl [B _]. pose proof (bytes_at_bound _ _ _ _ B) as H. rewrite length_map in H. exact H. Qed.

Lemma buf_nth : forall m S bl i, buf_at m S bl -> 0 <= i < zlen bl ->
  nth_error (map (Z_to_bv 8) bl) (Z.to_nat i) = Some (Z_to_bv 8 (Znth i bl)) /\ 0 <= Znth i bl < 256.
Proof.
  intros m S bl i [_ F] Hi. unfold Znth.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<2322167807.6000004S2Hi".
assert (L : (Z.to_nat i < length bl)%nat) by lia.
  split.
  - rewrite nth_error_map. rewrite (nth_error_nth' bl 0 L). reflexivity.
  - apply (proj1 (Forall_forall _ _) F). apply nth_In. exact L.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma buf_read : forall m S bl i, buf_at m S bl -> 0 <= i < zlen bl ->
  ov_read_bytes usegs m (wa (S + i)) 1 = Some [Z_to_bv 8 (Znth i bl)].
Proof.
  intros m S bl i B Hi. destruct (buf_nth m S bl i B Hi) as [N _].
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=10357916367.7000004S2Hi".
eapply (u8ro_read usegs m S _ i); [exact (proj1 B)| exact N| lia| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma byte_lit : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48041415315.2000004S2Hc".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma buf_at_skipn : forall m S bl k, buf_at m S bl -> 0 <= k <= zlen bl ->
  buf_at m (S + k) (skipn (Z.to_nat k) bl).
Proof.
  intros m S bl k [B F] Hk. split.
  - rewrite <- (firstn_skipn (Z.to_nat k) bl) in B. rewrite map_app in B.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [_ B].
    rewrite length_map, length_firstn in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=18147260095.7000004S2Hk".
replace (Z.of_nat (Nat.min (Z.to_nat k) (length bl))) with k in B by lia. exact B.
  - apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) F x). revert Hx. generalize (Z.to_nat k). clear.
    induction bl as [|y bl IH]; intros [|n] H; cbn in H; try exact H; [right; exact (IH n H)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma zlen_skipn : forall (bl : list Z) k, 0 <= k <= zlen bl -> zlen (skipn (Z.to_nat k) bl) = zlen bl - k.
Proof. intros bl k Hk. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=68659354476.3000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma buf_at_frame : forall m m' S bl W,
  buf_at m S bl -> munch W m m' -> disjoint_from W S (zlen bl) -> buf_at m' S bl.
Proof.
  intros m m' S bl W [B F] MU HW. split; [|exact F].
  eapply (bytes_at_transport usegs W m m'); [exact B| exact MU|]. rewrite length_map. exact HW.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_bytes_length : forall cs, cells_wf cs -> length (cells_bytes cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; cbn; intros H; [reflexivity|]. destruct H as [Hc Hcs].
  rewrite app_length, (IH Hcs). destruct c; cbn in *; rewrite ?length_le8, ?length_le4, ?length_le2; try lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) <-> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at, wr_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app.
  split.
  - intros [[[W1 W2] B] (Ha & Hn & Hw)]. pose proof (cells_bytes_length cs1 W1) as L1.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in B. destruct B as [B1 B2]. rewrite L1 in B2.
    split.
    + split; [split; [exact W1| exact B1]|]. Local Ltac2 Set LiaHints.tbl := fun () => "00<0>1312117644.12 1312117644.15 19522555985.1819524649394.1424931733050.1224931733050.1531688782959.1239639586408.1448872924203.1253121998162.1853725182937.1463892447207.1800000700?00H00R00\00d00k01501?01F01M01VS2Hn2L1S3Hn22L1S2L12Hi1HS2Hn2L12HiS2Ha2Hn2L1S3Ha12L1S2Hn2L1S2Hn2L12HiS2Ha2Hn2L1S2L12HiS2Hn2L1S2L12Hi1H".
split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
    + split; [split; [exact W2| exact B2]|]. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
  - intros [[[W1 B1] (Ha1 & Hn1 & Hw1)] [[W2 B2] (Ha2 & Hn2 & Hw2)]]. pose proof (cells_bytes_length cs1 W1) as L1.
    split.
    + split; [split; [exact W1| exact W2]|]. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply Hw1; lia|].
      replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Hw2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma rw_cells_reshape : forall m A cs cs',
  rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells usegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] W E Sz. split; [split; [exact W| rewrite E; exact Hb]| rewrite Sz; exact Hw]. Qed.

(* [comment removed for export] *)
Lemma buf_read' : forall m S bl i, bytes_at usegs m S (map (Z_to_bv 8) bl) -> Forall (fun c => 0 <= c < 256) bl -> 0 <= i < zlen bl ->
  ov_read_bytes usegs m (wa (S + i)) 1 = Some [Z_to_bv 8 (Znth i bl)] /\ 0 <= Znth i bl < 256.
Proof.
  intros m S bl i B F Hi. split; [apply buf_read; [split; assumption| exact Hi]|]. exact (proj2 (buf_nth m S bl i (conj B F) Hi)).
Qed.

(* [comment removed for export] *)
Ltac pose_rd k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with
    | PL : bytes_at usegs m ?S (map (Z_to_bv 8) ?bl), PLR : Forall _ ?bl |- _ =>
        let H := fresh "RD" in let R := fresh "RB" in
        destruct (buf_read' m S bl k PL PLR ltac:(lia)) as [H R];
        try (replace (wa (S + 0)) with (wa S) in H by (unfold wa; f_equal; lia))
    end
  end.
(* [comment removed for export] *)
Ltac clear_rd :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    repeat match goal with H : ov_read_bytes _ ?m0 _ _ = Some _ |- _ => lazymatch m0 with m => fail | _ => clear H end end
  end.

(* [comment removed for export] *)
Lemma zx32_small : forall h, 0 <= h < 2^32 -> zx32 (Z_to_bv 64 h) = Z_to_bv 64 h.
Proof.
  intros h Hh. unfold zx32. Local Ltac2 Set LiaHints.tbl := fun () => "0020=50584898410.257703944554.2000004008S2HhS2Hh".
rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
