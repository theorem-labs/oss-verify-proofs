(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Frame Exec RegsEquiv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CkP Require Import RegsFull.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk
        OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.SeqExec
        OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module OP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.
Module OC := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.CatSim.
Module OS := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.
Module OF := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Frame.
Module OH := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Hoare.
Module OR := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.RefMemcpyLib.

Lemma mkst_MS : forall (R F : bvmap 5 word) (pc : word) (fc : bv 32) (m ro : word -> option byte),
  @OP.mkst (OP.mkFP F fc) R pc m ro = MS R F pc fc None m ro.
Proof. reflexivity. Qed.

Lemma msteps_conv : forall segs a b, OC.msteps segs a b -> msteps segs a b.
Proof.
  intros segs a b H. induction H as [ms|ms ms' ms'' Hsvc Hstep _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [split; [exact Hsvc| exact Hstep]| exact IH].
Qed.

Lemma rdn_conv : forall segs m a n, OP.rdn segs m a n = rdn segs m a n.
Proof. intros segs m a n. revert a. induction n as [|n IH]; intros a; [reflexivity|]. cbn [OP.rdn rdn]. rewrite IH. reflexivity. Qed.

Lemma getr_reg_get : forall (R : bvmap 5 word) (r : reg), is_x0 r = false -> OP.getr R r = reg_get R r.
Proof. intros R r H. unfold OP.getr. rewrite OP.bv_eqb0_is_x0, H. reflexivity. Qed.

Section GetR.
Variables x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word.
Local Notation RR := (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Lemma getr_mkR :
  OP.getr RR 1 = x1 /\ OP.getr RR 2 = x2 /\ OP.getr RR 3 = x3 /\ OP.getr RR 4 = x4 /\ OP.getr RR 5 = x5 /\ OP.getr RR 6 = x6
  /\ OP.getr RR 7 = x7 /\ OP.getr RR 8 = x8 /\ OP.getr RR 9 = x9 /\ OP.getr RR 10 = x10 /\ OP.getr RR 11 = x11 /\ OP.getr RR 12 = x12
  /\ OP.getr RR 13 = x13 /\ OP.getr RR 14 = x14 /\ OP.getr RR 15 = x15 /\ OP.getr RR 16 = x16 /\ OP.getr RR 17 = x17 /\ OP.getr RR 18 = x18
  /\ OP.getr RR 19 = x19 /\ OP.getr RR 20 = x20 /\ OP.getr RR 21 = x21 /\ OP.getr RR 22 = x22 /\ OP.getr RR 23 = x23 /\ OP.getr RR 24 = x24
  /\ OP.getr RR 25 = x25 /\ OP.getr RR 26 = x26 /\ OP.getr RR 27 = x27 /\ OP.getr RR 28 = x28 /\ OP.getr RR 29 = x29 /\ OP.getr RR 30 = x30
  /\ OP.getr RR 31 = x31.
Proof. repeat split; reflexivity. Qed.
End GetR.

Lemma ret_pc_of_even : forall ra : word, (bv_unsigned ra mod 2 = 0)%Z -> ret_pc ra = ra.
Proof.
  intros ra H. rewrite <- (Z_to_bv_bv_unsigned ra) at 1 2. apply ret_pc_even; [| exact H].
  pose proof (bv_unsigned_in_range 64 ra) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma frame_mod_munch : forall (m m' : word -> option byte) (a n : Z),
  (0 <= a)%Z -> (a < 2^64)%Z ->
  OF.frame_mod m m' [(Z_to_bv 64 a, n)] -> munch [(a, a + n)%Z] m m'.
Proof.
  intros m m' a n Ha0 Ha1 [HE _] x Hx. apply HE. cbn [OF.outside]. split; [| exact I].
  unfold OF.in_rng. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (change (2 ^ Z.of_N 64)%Z with (2^64)%Z; lia).
  cbn [outside] in Hx. destruct Hx as [Hx _]. exact Hx.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [| right; intros [_ K]; exact (H K)].
  destruct (Z_le_dec lo x) as [L|L]; [| left; split; [lia| exact H]].
  destruct (Z_lt_dec x hi) as [U|U]; [right; intros [K _]; apply K; lia| left; split; [lia| exact H]].
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma mem_grows_wmono : forall m m', OS.mem_grows m m' -> wmono segs m m'.
Proof.
  intros m m' HG x Hx. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - specialize (HG x ltac:(rewrite E; discriminate)). destruct (m' x); [discriminate| contradiction].
  - destruct (m' x); [discriminate| exact Hx].
Qed.

Lemma mem_inv_window : forall W m m', mem_inv segs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview segs m x <> None) -> mem_inv segs m'.
Proof.
  intros W m m' MI MU HW a b Hab.
  destruct (outside_dec W (bv_unsigned a)) as [Ho|Hn].
  - apply (MI a b). rewrite <- (MU a Ho). exact Hab.
  - specialize (HW a Hn). destruct (m a) as [b'|] eqn:E; [exact (MI a b' E)| exact (wview_not_ro segs m a HW E)].
Qed.

Lemma evt_of_msteps_mkR : forall (Q : machine_state -> Prop) (R F : bvmap 5 word) (pc pc' : word) (fc : bv 32) (m m' ro : word -> option byte) (R' : bvmap 5 word),
  rfull R ->
  OC.msteps segs (@OP.mkst (OP.mkFP F fc) R pc m ro) (@OP.mkst (OP.mkFP F fc) R' pc' m' ro) ->
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
     R' = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ->
     Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc' fc None m' ro)) ->
  evt segs Q (MS R F pc fc None m ro).
Proof.
  intros Q R F pc pc' fc m m' ro R' HR HS HQ.
  apply msteps_conv in HS. rewrite !mkst_MS in HS.
  pose proof (msteps_rfull segs _ _ HS HR) as HR'. cbn [ms_regs MS] in HR'.
  destruct HR' as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & E).
  exists (MS R' F pc' fc None m' ro). split; [exact HS|]. rewrite E. apply HQ. exact E.
Qed.
End WithSegs.
