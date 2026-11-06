(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition od_locals0 (j0 j8 j16 j24 j120 j128 j136 j168 j176 j248 j256 j264 j280 j288 j328 j336 j368 j376 j400 j408 j416 j424 j425 j432 : list byte) : list cell :=
  [CB 8 j0; CB 8 j8; CB 8 j16; CB 96 j24; CB 8 j120; CB 8 j128; CB 32 j136; CB 8 j168; CB 72 j176; CB 8 j248; CB 8 j256; CB 16 j264; CB 8 j280;
   CB 40 j288; CB 8 j328; CB 32 j336; CB 8 j368; CB 24 j376; CB 8 j400; CB 8 j408; CB 8 j416; CB 1 j424; CB 7 j425; CB 8 j432].

Definition od_mid0 (usp S1 lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j8 j16 j24 j120 j128 j136 j168 j176 j248 j256 j264 j280 j288 j328 j336 j368 j376 j400 j408 j416 j424 j425 j432 : list byte),
    ms = entry_st (Z_to_bv 64 0x969b4) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) (Z_to_bv 64 288)
                  a1' a2' a3 a4 a5 a6 a7
                  (Z_to_bv 64 n) (Z_to_bv 64 d) s4 s5 s6 (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6 F fc (e_stack_malloc 3) m1
    /\ munch [(S1, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo S1
    /\ rw_cells bsegs m1 S1 (od_locals0 j0 j8 j16 j24 j120 j128 j136 j168 j176 j248 j256 j264 j280 j288 j328 j336 j368 j376 j400 j408 j416 j424 j425 j432)
    /\ stk bsegs m1 (S1 + 440) (usp - 104)
    /\ rw_cells bsegs m1 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma od_walk0_al : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 544 -> 0x679000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (od_mid0 usp (usp - 544) lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, e_stack_malloc, od_mid0, fa_saved, od_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 544, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 544%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 544 _ [] [8; 8; 8; 96; 8; 8; 32; 8; 72; 8; 8; 16; 8; 40; 8; 32; 8; 24; 8; 8; 8; 1; 7; 8;
                                                  8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -544)) by lia.
  replace (32 * ((usp + -544) / 32)) with (usp + -544) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14
                                            :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?c22 :: ?c22b :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: c20 :: c21 :: c22 :: c22b :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22; c22b] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -544 + Z.of_nat 440) with (usp - 104) in FRs by lia.
  replace (usp + -544) with (usp - 544) in * by lia.
  apply evt_done. do 27 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 544 + 440) with (usp - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma od_walk0_un : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 560 -> 0x679000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (od_mid0 usp (usp - 560) lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, e_stack_malloc, od_mid0, fa_saved, od_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 560, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 560%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 560 _ [] [8; 8; 8; 96; 8; 8; 32; 8; 72; 8; 8; 16; 8; 40; 8; 32; 8; 24; 8; 8; 8; 1; 7; 8;
                                                  8; 8;
                                                  8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -544)) by lia.
  replace (32 * ((usp + -544) / 32)) with (usp + -560) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14
                                            :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?c22 :: ?c22b :: ?c23 :: ?c24 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: c19 :: c20 :: c21 :: c22 :: c22b :: c23 :: c24 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21; c22; c22b] ++ [c23; c24] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add] in FRp, FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [_; _] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -560 + Z.of_nat 440 + Z.of_nat 16) with (usp - 104) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at bsegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -560 + Z.of_nat 440 + 16) with (usp - 104) in STp by lia.
  replace (usp + -560 + Z.of_nat 440) with (usp - 560 + 440) in STp by lia.
  replace (usp + -560) with (usp - 560) in * by lia.
  apply evt_done. do 27 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 560 + 440) by lia; replace b with (usp - 104) by lia end. exact STp.
Qed.

Lemma od_prologue : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 560 -> 0x679000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  exists S1, usp - 560 <= S1 <= usp - 544 /\ S1 mod 32 = 0 /\
    evt bsegs (od_mid0 usp S1 lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S16 CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 544). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply od_walk0_al; try assumption; lia.
  - exists (usp - 560). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply od_walk0_un; assumption.
Qed.
