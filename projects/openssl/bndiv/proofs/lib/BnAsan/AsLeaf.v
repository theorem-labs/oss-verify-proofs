(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr Cells Step Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma acc_tr : forall W m m1 p n0 k n,
  acc segs m p n0 -> munch W m m1 -> offshW W ->
  (0 < n -> 0 <= p + k /\ p + k + n <= 140737488355328) -> 0 <= k -> k + n <= n0 ->
  acc segs m1 (p + k) n.
Proof.
  intros W m m1 p n0 k n AC MU OFF B Hk Hle.
  destruct (Z_le_gt_dec n 0) as [Hn|Hn]. { intros i Hi. exfalso. lia. }
  destruct (B ltac:(lia)) as [B0 B1].
  eapply acc_munch; [ eapply acc_sub; [exact AC | lia | lia] | exact MU | exact OFF | exact B0 | exact B1 ].
Qed.

Lemma limbs_at_b47 : forall m p (l : list Z), limbs_at segs m p l -> mem_inv segs m -> 0 < Z.of_nat (length l) ->
  0 <= p /\ p + 8 * Z.of_nat (length l) <= 140737488355328.
Proof.
  intros m p l RA MI Hn. pose proof (limbs_at_bound _ _ _ _ RA) as B.
  assert (NE : lbytes l <> []) by (intros E; pose proof (lbytes_lengthZ l) as L; rewrite E in L; cbn [length] in L; lia).
  pose proof (bytes_at_below segs m p _ MI RA NE) as T. rewrite lbytes_lengthZ in T. unfold UTOP in T. lia.
Qed.

Lemma wr_at_b47 : forall m p n, wr_at segs m p n -> mem_inv segs m -> 0 < n -> 0 <= p /\ p + n <= 140737488355328.
Proof.
  intros m p n WR MI Hn. pose proof (wr_at_below segs m p n MI WR Hn) as T. unfold UTOP in T. destruct WR as (W0 & _). lia.
Qed.
End WithSegs.

Lemma aptrs3_sub : forall rp ap bp n lo k n', aptrs3 rp ap bp n lo -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  aptrs3 (rp + 8 * k) (ap + 8 * k) (bp + 8 * k) n' lo.
Proof.
  intros rp ap bp n lo k n' (A1 & A2 & A3 & A4 & A5) Hk Hn Hle. unfold aptrs3.
  split; [clear - A1; Z.div_mod_to_equations; lia|]. split; [clear - A2; Z.div_mod_to_equations; lia|].
  split; [clear - A3; Z.div_mod_to_equations; lia|]. split; [lia | exact A5].
Qed.

(* [comment removed for export] *)
Lemma shb_cells_munch : forall segs gotc shbv W m m1,
  shb_cells segs gotc shbv m -> munch W m m1 -> disjoint_from W gotc 8 -> disjoint_from W shbv 8 ->
  shb_cells segs gotc shbv m1.
Proof.
  intros segs gotc shbv W m m1 [G1 G2] MU D1 D2. split.
  - eapply ro_cells_transport; [exact G1 | exact MU | exact D1].
  - eapply ro_cells_transport; [exact G2 | exact MU | exact D2].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge_prefix : forall segs m A pre rest,
  rw_cells segs m A (pre ++ rest) -> rw_cells segs m A (CB (cells_size pre) (cells_bytes pre) :: rest).
Proof.
  intros segs m A pre rest [[Hwf Hb] Hw]. apply cells_wf_app in Hwf. destruct Hwf as [Wp Wr].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply cells_bytes_length; exact Wp | exact Wr].
  - cbn [cells_bytes cbytes]. rewrite cells_bytes_app in Hb. exact Hb.
  - cbn [cells_size csize]. rewrite cells_size_app in Hw. exact Hw.
Qed.
