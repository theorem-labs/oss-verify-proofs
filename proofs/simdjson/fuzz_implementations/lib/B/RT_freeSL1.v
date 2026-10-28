(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_depot_defs R_depot_put R_asan_defs R_deallocate.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma dealloc_p1_spec_L : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (M n b1 B TCX T lo : Z) (ctx fr fd : word) (uw : list byte),
  (0x6e0000 <= M)%Z -> (M mod 16 = 0)%Z -> (M + 24 <= lo)%Z -> (1 <= n < 2^32)%Z ->
  (0 <= b1 < 256)%Z -> (b1 mod 4 = 1)%Z ->
  rw_cells bsegs m M [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells bsegs m (M + 16) [CB 8 uw] ->
  rw_cells bsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6e0000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  rw_cells bsegs m (T + 2824) [C8 fr; C8 fd] ->
  (M + 24 <= T + 2824 \/ T + 2840 <= M)%Z -> (M + 24 <= TCX + 152 \/ TCX + 160 <= M)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (dealloc_p1_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc M n b1 B T lo ctx m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 B) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until uw. intros HM HM16 HMl Hn Hb1 Hb14 HD UW FH TC HTCX HTCXl HT HTi HTl STS HMT HMX ST HLO HSP MI.
  unfold deallocate_entry, kHighShadowEnd, g_MFHooks, INST, g_instance in *.
  change (2208832 + 8)%Z with 2208840%Z in FH.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  move KI at bottom. move K0 at bottom. move FH at bottom. move TS at bottom. move T0 at bottom.
  pose proof (hdr_cas b1 Hb1) as (HC1 & HC2).
  assert (RM : (0x6e0000 <= M < 2^47)%Z) by lia.
  pose proof (munch_refl [(M, M + 24); (T + 2824, T + 2840); (bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  do 9 zstep. zstep. ifF.
  do 8 zstep.
  zstep. sp_facts.
  call (run_free_hooks_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  zstep. ifT.
  do 8 zstep.
  assert (ESH : (Z.land (Z.shiftl M 3) 18446744073709551615 mod 32 = 0)%Z).
  { clear - RM HM16. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64).
    rewrite Z.land_ones by lia. rewrite (Z.mod_small (M * 2 ^ 3) (2 ^ 64)) by lia.
    change (2 ^ 3)%Z with 8%Z. Z.div_mod_to_equations; lia. }
  rewrite ESH. fold_reg 14%Z. fold_reg 15%Z. fold_reg 16%Z.
  rewrite land_m4 by (clear - RM; lia). replace (4 * (M / 4))%Z with M by (clear - RM HM16; Z.div_mod_to_equations; lia).
  apply (hdr3_to_c4 _ _ 2 b1 [C4 (Z_to_bv 64 n); C8 ctx]) in HD; [| lia| lia].
  assert (AMO : amo_aligned AW (Z_to_bv 64 M) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. Z.div_mod_to_equations; lia. }
  amo_step AMO. rewrite (sx32_small_A (2 + 256 * b1)) by lia.
  zstep. rewrite ?HC1. zstep. ifF.
  do 3 zstep. rewrite ?HC2.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  do 2 zstep. fold_reg 10%Z.
  zstep; fix_lit_store.
  apply (c4_to_hdr3 _ _ 3 b1 [C4 (Z_to_bv 64 n); C8 ctx]) in HD; [| lia| lia].
  zstep. cbv beta.
  replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256%Z;
                                                   rewrite Z.mod_small by lia; reflexivity).
  assert (E3 : Z.land b1 3 = 1%Z) by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; exact Hb14).
  zstep. rewrite E3. zstep. ifF.
  do 3 zstep. dIf_closed.
  zstep.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  do 10 zstep.
  do 12 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep. zstep.
  finish.
  all: eassumption.
Qed.
