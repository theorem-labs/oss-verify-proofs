(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ZApiL ZInstL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_zrd Zg_defl_pathi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateSafe RefDeflSafeI1 DeflateTaintRelG ZApiInst ZApiInstL ZTaintL.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling}.
Local Transparent the_zapiL.

Definition zr_dL (m : mem) (S : Z) (LBz : list block) (x : DSL the_zapiL) : Prop :=
  exists (L : dlay) (sa : deflate_state) (b : bptr * bptr * bptr * bptr * bptr),
    LBz = zd_blocks b L /\ dl_S L = S /\ DREPq m L sa (dz_z x) /\ DRELL sa x /\ PATG sa /\ dlay_ceil L /\ zstrm_okP (dz_z x).

Lemma zr_dL_intro : forall m L sa b (x : DSL the_zapiL), DREPq m L sa (dz_z x) -> DRELL sa x -> PATG sa -> dlay_ceil L -> zstrm_okP (dz_z x) ->
  zr_dL m (dl_S L) (zd_blocks b L) x.
Proof.
  intros m L sa b x H1 H2 H3 H4 H5. exists L, sa, b. split; [reflexivity|]. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|].
  split; [exact H3|]. split; [exact H4| exact H5].
Qed.

Lemma zr_dL_frame : forall m m' S LBz x, zr_dL m S LBz x ->
  (forall a, 0 <= a < 2^64 -> (S + 48 <= a < S + 112 \/ in_block LBz a) ->
     m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  zr_dL m' S LBz x.
Proof.
  intros m m' S LBz x (L & sa & b & -> & <- & DQ & DR & PT & DC & ZO) FR. exists L, sa, b.
  split; [reflexivity|]. split; [reflexivity|]. split; [|split; [exact DR| split; [exact PT| split; [exact DC| exact ZO]]]].
  pose proof (st_lay _ _ _ _ (proj2 DQ)) as LAY.
  destruct (lo_s L LAY) as (s1 & _ & s2 & _). destruct (lo_w L LAY) as (w1 & _ & w2 & _). destruct (lo_p L LAY) as (p1 & _ & p2 & _).
  destruct (lo_h L LAY) as (h1 & _ & h2 & _). destruct (lo_b L LAY) as (b1 & _ & b2 & _). destruct (lo_S L LAY) as (S1 & _ & S2).
  apply (DREPq_agree m m' L sa (dz_z x) DQ).
  - unfold ag_blocks. split; [|split; [|split; [|split]]]; intros a0 Ha; (apply FR; [lia| right; apply in_zd_blocks; lia]).
  - intros a0 Ha. apply FR; [lia| left; lia].
Qed.

Lemma zr_dL_stream : forall m S LBz x, zr_dL m S LBz x -> exists j : list byte, rw_cells usegs m (S + 48) [CB 64 j].
Proof.
  intros m S LBz x (L & sa & b & _ & <- & ((p3 & resv & DZ) & _) & _).
  destruct (rw_cells_forget usegs m _ _ DZ) as (j & H). exists j. exact H.
Qed.

Lemma zr_dL_facts : forall sa (x : DSL the_zapiL), DRELL sa x ->
  DD sa /\ ds_w_size sa = 32768 /\ ds_hash_size sa = 32768 /\ ds_lit_bufsize sa = 16384.
Proof.
  intros sa x DR. destruct (DRELL_facts sa x DR) as (HDD & IG & _).
  split; [exact HDD|]. split; [exact (ig_wsize _ IG)|]. split; [exact (ig_hsize _ IG)| exact (ig_lbs _ IG)].
Qed.
End WithCeiling0.
