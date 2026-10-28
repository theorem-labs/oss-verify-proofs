(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Pj_lftoi1A Pj_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition op_locals0 (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10].

Definition op_mid0 (usp sp' lo OSP BUF N : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 : list byte),
    ms = entry_st (wz 0xb816c) (wz sp') gp tp t0 t1 t2 (wz usp) (wz sp') (wz 96) a1' a2' a3 a4 a5 a6 a7
                  s2 (wz OSP) s4 s5 s6 (wz BUF) (wz N) s9 s10 (wz SHB) t3 t4 t5 t6 F fc e_stack_malloc_1 m1
    /\ munch [(sp', usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo sp'
    /\ rw_cells asegs m1 sp' (op_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10)
    /\ stk asegs m1 (sp' + 88) (usp - 104)
    /\ rw_cells asegs m1 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma op_walk0_al : forall (usp lo OSP BUF N : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 192 -> 0x6ca000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> 0 <= OSP < 2^64 -> 0 <= BUF < 2^64 -> 0 <= N < 2^64 ->
  client_consts m -> mem_inv asegs m ->
  evt asegs (op_mid0 usp (usp - 192) lo OSP BUF N ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz OSP) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc PJ_OSPUT_A m).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR BR NR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, PJ_OSPUT_A, e_stack_malloc_1, op_mid0, fa_saved, op_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 192, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 192%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 192 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -192)) by lia.
  replace (32 * ((usp + -192) / 32)) with (usp + -192) by (Z.div_mod_to_equations; lia).
  do 7 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 asegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -192 + Z.of_nat 88) with (usp - 104) in FRs by lia.
  replace (usp + -192) with (usp - 192) in * by lia.
  apply evt_done. do 14 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 192 + 88) with (usp - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma op_walk0_un : forall (usp lo OSP BUF N : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 208 -> 0x6ca000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> 0 <= OSP < 2^64 -> 0 <= BUF < 2^64 -> 0 <= N < 2^64 ->
  client_consts m -> mem_inv asegs m ->
  evt asegs (op_mid0 usp (usp - 208) lo OSP BUF N ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz OSP) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc PJ_OSPUT_A m).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR BR NR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, PJ_OSPUT_A, e_stack_malloc_1, op_mid0, fa_saved, op_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 208, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 208%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 208 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -192)) by lia.
  replace (32 * ((usp + -192) / 32)) with (usp + -208) by (Z.div_mod_to_equations; lia).
  do 7 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ [c11; c12] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add] in FRp, FRs.
  apply (rw_cells_forget_C8 asegs _ _ [_; _] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -208 + Z.of_nat 88 + Z.of_nat 16) with (usp - 104) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at asegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -208 + Z.of_nat 88 + 16) with (usp - 104) in STp by lia.
  replace (usp + -208 + Z.of_nat 88) with (usp - 208 + 88) in STp by lia.
  replace (usp + -208) with (usp - 208) in * by lia.
  apply evt_done. do 14 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 208 + 88) by lia; replace b with (usp - 104) by lia end. exact STp.
Qed.

Lemma op_prologue : forall (usp lo OSP BUF N : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 208 -> 0x6ca000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 <= OSP < 2^64 -> 0 <= BUF < 2^64 -> 0 <= N < 2^64 ->
  client_consts m -> mem_inv asegs m ->
  exists sp', usp - 208 <= sp' <= usp - 192 /\ sp' mod 32 = 0 /\
    evt asegs (op_mid0 usp sp' lo OSP BUF N ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz OSP) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc PJ_OSPUT_A m).
Proof.
  intros until m. intros ST LO GLO SPH S16 OR BR NR CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 192). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply op_walk0_al; try assumption; lia.
  - exists (usp - 208). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply op_walk0_un; assumption.
Qed.

Definition pad_locals0 (j0 j1 j2 : list byte) (oe : Z) (j4 j5 j6 : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; C8 (wz oe); CB 8 j4; CB 8 j5; CB 8 j6].

Definition pad_mid0 (S lo OS BUF N FILL : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j4 j5 j6 : list byte),
    ms = entry_st (wz 0xb8798) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) (wz 96) a1' a2' (wz (BUF + N)) (wz (OS + 136)) (wz FILL) a6 a7
                  s2 (wz OS) (wz SHB) (wz FILL) (wz (OS + 136)) s7 (wz BUF) (wz BUF) s10 s11 t3 t4 t5 t6 F fc e_stack_malloc_1 m1
    /\ munch [(S - 160, S)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (S - 160)
    /\ rw_cells asegs m1 (S - 160) (pad_locals0 j0 j1 j2 (BUF + N) j4 j5 j6)
    /\ stk asegs m1 (S - 160 + 56) (S - 104)
    /\ rw_cells asegs m1 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma pad_walk0 : forall (S lo OS BUF N FILL : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo S -> lo <= S - 160 -> 0x6ca000 <= lo -> S < 2^63 -> S mod 32 = 0 ->
  0 <= OS -> OS + 288 < 2^64 -> 0 <= BUF -> BUF + N < 2^64 -> 0 <= N -> 0 <= FILL < 2^64 ->
  client_consts m -> mem_inv asegs m ->
  evt asegs (pad_mid0 S lo OS BUF N FILL ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (wz S) gp tp t0 t1 t2 s0 s1 (wz OS) (wz BUF) (wz BUF) (wz (BUF + N)) (wz (OS + 136)) (wz FILL) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc PJ_PADOUT_A m).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR OH BR BH NR FR0 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, PJ_PADOUT_A, e_stack_malloc_1, pad_mid0, fa_saved, pad_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(S - 160, S)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 160%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 160 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (S + -160)) by lia.
  replace (32 * ((S + -160) / 32)) with (S + -160) by (Z.div_mod_to_equations; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (S + -160)) = S + -160) by (apply unsigned_lit; lia).
  do 3 zstep. lstep. do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c0; c1; c2; c3; c4; c5; c6] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 asegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (S + -160 + Z.of_nat 56) with (S - 104) in FRs by lia.
  replace (S + -160) with (S - 160) in * by lia.
  apply evt_done. do 9 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (S - 160 + 56) with (S - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.
