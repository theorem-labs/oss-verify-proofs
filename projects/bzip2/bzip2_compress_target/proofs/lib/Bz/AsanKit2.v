(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 AsanKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Section Kit2.
Variable segs : list Segment.

Lemma shadow_read_gen : forall W (m0 m : amem) x b,
  disjoint_from W (x / 8 + 2147450880) 1 -> munch W m0 m -> bytes_at segs m0 (shad x) [b] ->
  ov_read_bytes segs m (Z_to_bv 64 (x / 8 + 2147450880)) 1 = Some [b].
Proof.
  intros W m0 m x b D MU Hb. apply bytes_at1_read.
  apply (bytes_at_transport segs W m0 m _ _ Hb MU). cbn [length]. change (Z.of_nat 1) with 1. exact D.
Qed.

(* [comment removed for export] *)
Lemma shzW_of_acc_gen : forall W (m0 : amem) a n lo hi,
  acc segs m0 a n -> 0 <= a -> a <= lo -> 8 * ((hi + 7) / 8) <= a + n ->
  (forall x, lo <= x < hi -> disjoint_from W (x / 8 + 2147450880) 1) -> shzW segs W m0 lo hi.
Proof.
  intros W m0 a n lo hi H Ha Hlo Hhi D m x MU Hx.
  apply (shadow_read_gen W m0 m x z8 (D x Hx) MU).
  apply (acc_byte0 segs m0 a n x H); [lia|].
  assert (x / 8 <= (hi + 7) / 8 - 1).
  { assert (x / 8 < (hi + 7) / 8); [| lia].
    apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (hi + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (hi + 7) 8 ltac:(lia)). lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma shpW_of_acc_gen : forall W (m0 : amem) a n,
  acc segs m0 a n -> (forall x, a <= x < a + n -> disjoint_from W (x / 8 + 2147450880) 1) -> shpW segs W m0 a (a + n).
Proof.
  intros W m0 a n H D m x s MU Hx Hs Hsz.
  destruct (acc_check segs m0 a n x s H Hx Hs Hsz) as (b & Hb & Hok).
  exists b. split; [| exact Hok].
  exact (shadow_read_gen W m0 m x b (D x ltac:(lia)) MU Hb).
Qed.
End Kit2.

(* [comment removed for export] *)
Lemma shd_app : forall x lo hi, 0 <= x < 2^47 -> (hi <= SH_LO \/ SH_HI <= lo) -> (x / 8 + 2147450880 + 1 <= lo \/ hi <= x / 8 + 2147450880).
Proof. intros x lo hi Hx H. pose proof (shad_range x Hx) as R. unfold SH_LO, SH_HI in *. lia. Qed.
(* [comment removed for export] *)
Lemma shd_anchor : forall X SHX q1 q2 x, sanchor X SHX -> (x < X + 8 * q1 \/ X + 8 * q2 <= x) ->
  (x / 8 + 2147450880 + 1 <= SHX + q1 \/ SHX + q2 <= x / 8 + 2147450880).
Proof. intros X SHX q1 q2 x [M E] H. subst SHX. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_bytes_C1s : forall bs, cells_bytes (map C1 bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_bytes cbytes app]; rewrite IH; reflexivity]. Qed.
Lemma cells_size_C1s : forall bs, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_size csize length Nat.add]; rewrite IH; reflexivity]. Qed.
Lemma cells_wf_C1s : forall bs, cells_wf (map C1 bs).
Proof. induction bs as [|b bs IH]; [exact I| cbn [map cells_wf cell_wf]; split; [exact I| exact IH]]. Qed.
Lemma rw_cells_CB_C1s : forall segs m A n bs, rw_cells segs m A [CB n bs] -> rw_cells segs m A (map C1 bs) /\ length bs = n.
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r in Hw.
  split; [| exact Hl]. split; [split; [apply cells_wf_C1s| rewrite cells_bytes_C1s; exact Hb]| rewrite cells_size_C1s, Hl; exact Hw].
Qed.

(* [comment removed for export] *)
Ltac ack_rd_saddr x s AS :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      let kx := az_base x in
      first
      [ match goal with
        | SH : shpW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
            let kl := az_base lo in constr_eq kx kl;
            let b := fresh "shb" in let RD := fresh "RDsh" in let OK := fresh "OKsh" in
            destruct (shpW_rd segs W m0 m lo hi x s SH MU ltac:(lia) ltac:(lia) ltac:(lia)) as (b & RD & OK);
            let E := fresh "Esh" in pose proof AS as E; unfold saddr in E; rewrite <- E in RD; clear E;
            wstep; clear RD
        end
      | fail 1 "ack_rd_saddr: no shpW region fact / munch for" x ]
  end.
