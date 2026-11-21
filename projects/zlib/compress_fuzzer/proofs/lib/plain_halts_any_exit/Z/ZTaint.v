(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateInitLib RefDeflSafeI1 RefDeflSafeI5b RefDeflSafeI6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel DeflateTaintCall DeflateTaintCore DeflateTaintInit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inflate HarnessSmall ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dinit_cs : cstrm := cs_init (zc_none zstrm0).

Definition dinit_of (g : N -> Z -> Z) : deflate_state :=
  dFg 0%N 1%N 2%N 3%N 4%N (g 0%N) (g 1%N) (g 2%N) (g 3%N) (g 4%N) dinit_cs 1 15 8 6 0 8.

Definition dinit_zr : ZRet := zret_of_cs (ds_strm (dinit_of (fun _ => g0))) Z_OK.

Lemma hs_dpure_eq : @HarnessSmall.dpure = @DeflateSafe.dpure. Proof. reflexivity. Qed.
Lemma hs_dhooks_eq : HarnessSmall.dhooks = DeflateSafe.dhooks. Proof. reflexivity. Qed.

Definition DREL (s_a : deflate_state) (x : dstream) : Prop := DCALL s_a (dz_s x).

Lemma dinit_cs_ok : 0 <= cs_avail_in dinit_cs /\ 0 <= cs_avail_out dinit_cs.
Proof. split; vm_compute; discriminate. Qed.

Theorem DREL_step : forall s_a x zc flush, DREL s_a x -> dcall_wf zc -> flush = Z_NO_FLUSH \/ flush = Z_FINISH ->
  snd (deflate_m s_a zc flush) = snd (deflate_m (dz_s x) zc flush)
  /\ DREL (fst (deflate_m s_a zc flush)) (mkDZ (fst (deflate_m (dz_s x) zc flush)) (zr_strm (snd (deflate_m (dz_s x) zc flush)))).
Proof. intros s_a x zc flush R Hz Hf. exact (deflate_m_rel s_a (dz_s x) zc flush R Hz Hf). Qed.

Theorem DREL_facts : forall s_a x, DREL s_a x -> dreach s_a /\ DD s_a /\ INV s_a /\ clean s_a = clean (dz_s x).
Proof.
  intros s_a x (Q & I1 & _ & R1 & _). split; [exact R1|]. split; [exact (dreach_DD _ R1)|]. split; [exact I1 | exact (DQ_clean _ _ Q)].
Qed.
