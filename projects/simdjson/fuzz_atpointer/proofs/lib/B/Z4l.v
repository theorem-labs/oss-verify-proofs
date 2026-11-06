(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit D_clx Z87 Z82 I_lkit Zpm Zpl Zq2 Z4a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fa_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition fa_locals0 (j0 j1 j2 j3 j4 j5 jq je jo jn jr j10 j11 j12 j13 : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 16 j4; CB 8 j5; CB 24 jq; CB 16 je; CB 24 jo; CB 16 jn; CB 24 jr; CB 8 j10; CB 8 j11; CB 1 j12; CB 7 j13].

Definition fa_mid0 (usp sp' lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j3 j4 j5 jq je jo jn jr j10 j11 j12 j13 : list byte),
    ms = entry_st (Z_to_bv 64 0x96b24) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 224)
                  a1' a2' a3 a4 a5 a6 a7
                  s2 s3 s4 (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6 F fc (e_stack_malloc 2) m1
    /\ munch [(sp', usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp'
    /\ rw_cells bsegs m1 sp' (fa_locals0 j0 j1 j2 j3 j4 j5 jq je jo jn jr j10 j11 j12 j13)
    /\ stk bsegs m1 (sp' + 184) (usp - 104)
    /\ rw_cells bsegs m1 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma fa_walk0_al : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 288 -> 0x649000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fa_mid0 usp (usp - 288) lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, e_stack_malloc, fa_mid0, fa_saved, fa_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 288, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 288%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 288 _ [] [8; 8; 8; 8; 16; 8; 24; 16; 24; 16; 24; 8; 8; 1; 7; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -288)) by lia.
  replace (32 * ((usp + -288) / 32)) with (usp + -288) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -288 + Z.of_nat 184) with (usp - 104) in FRs by lia.
  replace (usp + -288) with (usp - 288) in * by lia.
  apply evt_done. do 18 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 288 + 184) with (usp - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma fa_walk0_un : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 304 -> 0x649000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fa_mid0 usp (usp - 304) lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, e_stack_malloc, fa_mid0, fa_saved, fa_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 304, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 304%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 304 _ [] [8; 8; 8; 8; 16; 8; 24; 16; 24; 16; 24; 8; 8; 1; 7; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -288)) by lia.
  replace (32 * ((usp + -288) / 32)) with (usp + -304) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ++ [c15; c16] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add] in FRp, FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [_; _] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -304 + Z.of_nat 184 + Z.of_nat 16) with (usp - 104) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at bsegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -304 + Z.of_nat 184 + 16) with (usp - 104) in STp by lia.
  replace (usp + -304 + Z.of_nat 184) with (usp - 304 + 184) in STp by lia.
  replace (usp + -304) with (usp - 304) in * by lia.
  apply evt_done. do 18 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 304 + 184) by lia; replace b with (usp - 104) by lia end. exact STp.
Qed.

Lemma fa_prologue : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 304 -> 0x649000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  exists sp', usp - 304 <= sp' <= usp - 288 /\ sp' mod 32 = 0 /\
    evt bsegs (fa_mid0 usp sp' lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S16 CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 288). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply fa_walk0_al; try assumption; lia.
  - exists (usp - 304). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply fa_walk0_un; assumption.
Qed.
