(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import StrFun.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ShadowTac AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Set Keyed Unification.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.

Ltac bcase K := if_cases K; zify_cond K.

Section CANSEC1. Context {rc : runConstT}.
Lemma asan_memcpy0_spec : forall (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMCPY_STACK -> KHIGH <= lo ->
  rt_got_ric m -> rt_inited m -> rt_real_mem m ->
  a2 = Z_to_bv 64 0 -> bv_unsigned a0 mod 4 = 0 -> bv_unsigned a1 mod 4 = 0 -> bv_unsigned a0 <> bv_unsigned a1 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc a0 a1 a2 [] lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AMEMCPY) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST LOS KLO RIC INI REAL -> AL0 AL1 NEQ RI RSTK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1. cbn in RA1.
  unfold AMEMCPY_STACK, AMEMCPY, KHIGH in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp + -2224, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (RSTK' : rng RNG (bv_unsigned sp + -2224) 2224) by (eapply rng_sub'; [exact RSTK| lia]).
  carve_frame 96%nat ST.   (* [comment removed for export] *)
  do 12 zstep.
  do 3 zstep. cbv beta. zsimp. zstep. bcase K0. { exfalso. clear - K0. cbv in K0. lia. }
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  rewrite ?Z.add_0_r.
  zstep. bcase K1; try (exfalso; lia). (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply (evtF_cut _ RNG (fun ms' => ms' = _)).
  { zstep. bcase K2.
    - apply evtF_done. reflexivity.
    - zstep. bcase K3; try (exfalso; lia). apply evtF_done. reflexivity. }
  cbv beta. intros ms' ->.
  (* [comment removed for export] *)
  zstep. rewrite zb_lxor_ones by lia. zstep. bcase K4; try (exfalso; lia).
  zstep. zstep. zstep. bcase K5; try (exfalso; clear - K5; lia).
  zstep. bcase K6; try (exfalso; rewrite ?unsigned_lit in K6 by lia; lia). zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. rewrite zb_lxor_ones by lia. zstep. bcase K7; try (exfalso; lia).
  zstep. zstep. bcase K8; try (exfalso; clear - K8; lia).
  zstep. bcase K9; try (exfalso; rewrite ?unsigned_lit in K9 by lia; lia). zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite AL1. (* [comment removed for export] *)
  zstep. bcase K10; try (exfalso; clear - K10; lia). (* [comment removed for export] *)
  zstep. zstep. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite AL0. (* [comment removed for export] *)
  zstep. bcase K11; try (exfalso; clear - K11; lia). (* [comment removed for export] *)
  zstep. zstep. bcase K12; try (exfalso; rewrite ?unsigned_lit in K12 by lia; clear - K12; lia). (* [comment removed for export] *)
  zstep. zstep. bcase K13; try (exfalso; rewrite ?unsigned_lit in K13 by lia; clear - K13; lia). (* [comment removed for export] *)
  zstep. cbn [Z.land]. zstep. bcase K14; try (exfalso; clear - K14; lia). (* [comment removed for export] *)
  zstep. cbn [Z.land]. zstep. bcase K15; try (exfalso; clear - K15; lia). (* [comment removed for export] *)
  zstep. cbn [Z.land]. zstep. bcase K16; try (exfalso; clear - K16; lia). (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 12 zstep.
  release_frame FR0 ST (bv_unsigned sp).
  apply evtF_done. unfold amemcpy_post. rewrite !unsigned_lit by lia.
  apply (munch_weaken _ [(bv_unsigned sp - 2224, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 0)]) in MU.
  2:{ unfold sub_fp; cbn [outside]; intros; lia. }
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split.
  - unfold rw_cells, cells_at, wr_at. cbn.
    split; [split; [split; [reflexivity| exact I]|]|].
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.
End CANSEC1.
