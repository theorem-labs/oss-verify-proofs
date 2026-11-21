(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateSafe ZApiInst ZTaint BoundPat.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition zd_blocks (b : bptr * bptr * bptr * bptr * bptr) (L : dlay) : list block :=
  let '(sp, wp, pp, hp, bp) := b in
  [(bp, dl_Ab L, 65536); (hp, dl_Ah L, 65536); (pp, dl_Ap L, 65536); (wp, dl_Aw L, 65536); (sp, dl_As L, 5968)].

Section WithCeiling0. Context {CE__ : Ceiling}.

Definition dlay_ceil (L : dlay) : Prop :=
  dl_As L + 5968 <= alloc_ceiling /\ dl_Aw L + 65536 <= alloc_ceiling /\ dl_Ap L + 65536 <= alloc_ceiling
  /\ dl_Ah L + 65536 <= alloc_ceiling /\ dl_Ab L + 65536 <= alloc_ceiling.

Definition zr_d (m : mem) (S : Z) (LBz : list block) (x : dstream) : Prop :=
  exists (L : dlay) (sa : deflate_state) (b : bptr * bptr * bptr * bptr * bptr),
    LBz = zd_blocks b L /\ dl_S L = S /\ DREPq m L sa (dz_z x) /\ DREL sa x /\ PAT sa /\ dlay_ceil L /\ zstrm_okP (dz_z x).

Lemma zr_d_intro : forall m L sa b x, DREPq m L sa (dz_z x) -> DREL sa x -> PAT sa -> dlay_ceil L -> zstrm_okP (dz_z x) ->
  zr_d m (dl_S L) (zd_blocks b L) x.
Proof.
  intros m L sa b x H1 H2 H3 H4 H5. exists L, sa, b. split; [reflexivity|]. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|].
  split; [exact H3|]. split; [exact H4| exact H5].
Qed.

Lemma in_zd_blocks : forall b L a,
  (dl_As L <= a < dl_As L + 5968 \/ dl_Aw L <= a < dl_Aw L + 65536 \/ dl_Ap L <= a < dl_Ap L + 65536
   \/ dl_Ah L <= a < dl_Ah L + 65536 \/ dl_Ab L <= a < dl_Ab L + 65536) -> in_block (zd_blocks b L) a.
Proof.
  intros [[[[sp wp] pp] hp] bp] L a H. unfold in_block, zd_blocks.
  destruct H as [H|[H|[H|[H|H]]]].
  - exists (sp, dl_As L, 5968). split; [cbn; tauto| exact H].
  - exists (wp, dl_Aw L, 65536). split; [cbn; tauto| exact H].
  - exists (pp, dl_Ap L, 65536). split; [cbn; tauto| exact H].
  - exists (hp, dl_Ah L, 65536). split; [cbn; tauto| exact H].
  - exists (bp, dl_Ab L, 65536). split; [cbn; tauto| exact H].
Qed.

Lemma zr_d_frame : forall m m' S LBz x, zr_d m S LBz x ->
  (forall a, 0 <= a < 2^64 -> (S + 48 <= a < S + 112 \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) ->
  zr_d m' S LBz x.
Proof.
  intros m m' S LBz x (L & sa & b & -> & <- & DQ & DR & PT) FR. exists L, sa, b.
  split; [reflexivity|]. split; [reflexivity|]. split; [|split; assumption].
  pose proof (st_lay _ _ _ _ (proj2 DQ)) as LAY.
  destruct (lo_s L LAY) as (s1 & _ & s2 & _). destruct (lo_w L LAY) as (w1 & _ & w2 & _). destruct (lo_p L LAY) as (p1 & _ & p2 & _).
  destruct (lo_h L LAY) as (h1 & _ & h2 & _). destruct (lo_b L LAY) as (b1 & _ & b2 & _). destruct (lo_S L LAY) as (S1 & _ & S2).
  apply (DREPq_agree m m' L sa (dz_z x) DQ).
  - unfold ag_blocks. split; [|split; [|split; [|split]]]; intros a0 Ha; (apply FR; [lia| right; apply in_zd_blocks; lia]).
  - intros a0 Ha. apply FR; [lia| left; lia].
Qed.

Lemma zr_d_stream : forall m S LBz x, zr_d m S LBz x -> exists j : list byte, rw_cells psegs m (S + 48) [CB 64 j].
Proof.
  intros m S LBz x (L & sa & b & _ & <- & ((p3 & resv & DZ) & _) & _).
  destruct (rw_cells_forget psegs m _ _ DZ) as (j & H). exists j. exact H.
Qed.
End WithCeiling0.
