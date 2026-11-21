(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* the memset counterpart of IGlue's
   memcpy glue. msteps_memset is the run fact a binary's memset proof gives (the PropExec style of S7Memset, with any
   registers: memset(dst, 0, N) returns to ra with memory wbytes mem dst (zeros N) and every register outside a1-a6
   kept); memset_spec_at is the realizes form the I7S walks call; memset_glue turns the first into the second, as
   memcpy_glue does. Binary-agnostic: the instance for a binary is proved where its memset proof lives. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Fs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim StoreOk Frame Hoare RefMemcpyLib AgentLib FuzzMem ZStores.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import TSet MstepsGrows ZStep ZMem ZPrune ZTac ZArr ZCall ZCallL ZRegKeys IGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

(* musl's memset writes only a1-a6 (x11-x16) besides memory; a0 still holds dst at the ret *)
Definition ms_clob (r : reg) : Prop := In r [11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv].

Definition msteps_memset (segs : list Segment) (pc : Z) (N : nat) : Prop :=
  forall regs (mem0 rom : word -> option byte) (dst ret : word),
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 (Z.of_nat N) ->
    bv_unsigned dst mod 8 = 0 -> bv_unsigned dst + Z.of_nat N < 2 ^ 64 ->
    store_ok segs mem0 dst N = true ->
    exists regs',
      msteps segs (mkst regs (w64 pc) mem0 rom) (mkst regs' ret (wbytes mem0 dst (zeros N)) rom)
      /\ regs_agree ms_clob regs regs'.

Definition memset_spec_at (segs : list Segment) (pc N : Z) : Prop := forall Rb l M MD T d ret,
  m_halted MD = None ->
  zget_l Rb l 11%positive = d -> zget_l Rb l 12%positive = 0 -> zget_l Rb l 13%positive = N ->
  zget_l Rb l 2%positive = ret -> Z.land ret (-2) = ret ->
  mem_wr segs M d N -> 0 <= d -> d + N < two64 -> d mod 8 = 0 ->
  (forall M' R',
     mpost segs M M' d (d + N) 0 0 -> mem_zero segs M' d N -> mem_wr segs M' d N ->
     zget R' 11%positive = d ->
     zget R' 3%positive = zget_l Rb l 3%positive -> zget R' 4%positive = zget_l Rb l 4%positive ->
     zget R' 5%positive = zget_l Rb l 5%positive ->
     zget R' 9%positive = zget_l Rb l 9%positive -> zget R' 10%positive = zget_l Rb l 10%positive ->
     zget R' 19%positive = zget_l Rb l 19%positive -> zget R' 20%positive = zget_l Rb l 20%positive ->
     zget R' 21%positive = zget_l Rb l 21%positive -> zget R' 22%positive = zget_l Rb l 22%positive ->
     zget R' 23%positive = zget_l Rb l 23%positive -> zget R' 24%positive = zget_l Rb l 24%positive ->
     zget R' 25%positive = zget_l Rb l 25%positive -> zget R' 26%positive = zget_l Rb l 26%positive ->
     zget R' 27%positive = zget_l Rb l 27%positive -> zget R' 28%positive = zget_l Rb l 28%positive ->
     realizes segs (zcfg segs ret (zupd R' []) M' MD) T) ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.

(* the registers memset keeps *)
End FXG.
Ltac ms_kept AG :=
  apply AG; unfold ms_clob; cbn [In]; intros HH;
  repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Theorem memset_glue : forall segs pc (N : nat), msteps_memset segs pc N -> memset_spec_at segs pc (Z.of_nat N).
Proof.
  intros segs pc N MS Rb l M MD T d ret Hh Ld L12 Ln Lr Hret HW Hd Hdn Hal K.
  set (R := zupd Rb l). set (regs := zden R).
  assert (G1 : getr regs 1 = w64 ret) by (subst regs R; rewrite (getr_zupd Rb l 1) by reflexivity; key_norm; rewrite Lr; reflexivity).
  assert (G10 : getr regs 10 = w64 d) by (subst regs R; rewrite (getr_zupd Rb l 10) by reflexivity; key_norm; rewrite Ld; reflexivity).
  assert (G11 : getr regs 11 = Z_to_bv 64 0) by (subst regs R; rewrite (getr_zupd Rb l 11) by reflexivity; key_norm; rewrite L12; reflexivity).
  assert (G12 : getr regs 12 = Z_to_bv 64 (Z.of_nat N)) by (subst regs R; rewrite (getr_zupd Rb l 12) by reflexivity; key_norm; rewrite Ln; reflexivity).
  assert (UD : bv_unsigned (w64 d) = d) by (rewrite w64_unsigned, mod_small_u64 by lia; reflexivity).
  assert (ST : store_ok segs M (w64 d) N = true) by (apply (store_ok_of_mem_wr segs M d (Z.of_nat N) d N HW); lia).
  destruct (MS regs M (seg_rom segs) (w64 d) (w64 ret) G1 (ret_ok_of_land ret Hret) G10 G11 G12) as (regs' & RUN & AG).
  { rewrite UD. exact Hal. }
  { rewrite UD. rewrite <- two64_eq. lia. }
  { exact ST. }
  pose proof (msteps_regs_keys segs _ _ RUN) as RK. cbn [ms_regs] in RK.
  set (R' := zback (gres R d) regs').
  specialize (K (wbytes M (w64 d) (zeros N)) R').
  unfold realizes, zcfg, zst. cbn [cfg_ms cfg_model].
  unfold realizes, zcfg, zst in K. cbn [cfg_ms cfg_model zupd] in K.
  assert (ED : zden R' = regs') by (subst R'; apply zden_zback).
  rewrite ED in K.
  destruct K as (ms'' & RUN2 & HQ).
  - pose proof (mpost_of_wbytes segs M d (zeros N) Hd ltac:(rewrite length_zeros; lia)) as MP.
    rewrite length_zeros in MP. exact MP.
  - intros i Hi.
    rewrite (rdn_wbytes_zeros_in segs M (w64 d) (w64 (d + i)) N 1); [reflexivity | | |];
      rewrite ?UD, ?w64_unsigned, ?mod_small_u64 by lia; rewrite ?two64_eq in *; lia.
  - apply mem_wr_frame. exact HW.
  - subst R'. change 11%positive with (bv_key (10%bv : reg)).
    apply (zback_val regs' (gres R d) 10 d); [reflexivity | | lia | reflexivity].
    rewrite (AG 10%bv) by (unfold ms_clob; cbn [In]; intros HH;
      repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH).
    exact G10.
  - subst R' R. apply (kept_back Rb l regs' d 2); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 3); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 4); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 8); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 9); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 18); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 19); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 20); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 21); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 22); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 23); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 24); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 25); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 26); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - subst R' R. apply (kept_back Rb l regs' d 27); [reflexivity | reflexivity | reflexivity | exact RK | ms_kept AG].
  - exists ms''. split; [| exact HQ].
    eapply msteps_trans; [exact RUN | exact RUN2].
Qed.
End FXG.
