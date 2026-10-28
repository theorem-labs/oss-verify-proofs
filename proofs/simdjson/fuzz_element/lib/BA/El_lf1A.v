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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Pj_lftoi1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition el_locals0 (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 24 j8; CB 8 j9; CB 4 j10; CB 4 j11; CB 8 j12; CB 8 j13; CB 1 j14; CB 7 j15; CB 24 jr].
Lemma el_locals0_size : forall j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr,
  cells_size (el_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr) = 152%nat.
Proof. intros. reflexivity. Qed.

Definition el_mid0 (usp sp' lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr : list byte),
    ms = entry_st (Z_to_bv 64 0xb167c) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 608)
                  a1' a2' a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 d) s6 (Z_to_bv 64 SHB) s8 s9 s10 s11 t3 t4 t5 t6 F fc (e_stack_malloc 4) m1
    /\ munch [(sp', usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo sp'
    /\ rw_cells asegs m1 sp' (el_locals0 j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 jr)
    /\ stk asegs m1 (sp' + 152) (usp - 104)
    /\ rw_cells asegs m1 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma el_walk0_al : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 256 -> SEGTOP_A <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv asegs m ->
  evt asegs (el_mid0 usp (usp - 256) lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB, SEGTOP_A in *.
  unfold entry_st, e_fuzz, e_stack_malloc, el_mid0, fa_saved, el_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 256%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 24; 8; 4; 4; 8; 8; 1; 7; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -256)) by lia.
  replace (32 * ((usp + -256) / 32)) with (usp + -256) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 asegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -256 + Z.of_nat 152) with (usp - 104) in FRs by lia.
  replace (usp + -256) with (usp - 256) in * by lia.
  apply evt_done. do 20 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 256 + 152) with (usp - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma el_walk0_un : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 272 -> SEGTOP_A <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv asegs m ->
  evt asegs (el_mid0 usp (usp - 272) lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB, SEGTOP_A in *.
  unfold entry_st, e_fuzz, e_stack_malloc, el_mid0, fa_saved, el_locals0.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 272, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 272%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 272 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 24; 8; 4; 4; 8; 8; 1; 7; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -256)) by lia.
  replace (32 * ((usp + -256) / 32)) with (usp + -272) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: c15 :: c16 :: c17 :: c18 :: rest)
      with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] ++ [c17; c18] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add] in FRp, FRs.
  apply (rw_cells_forget_C8 asegs _ _ [_; _] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -272 + Z.of_nat 152 + Z.of_nat 16) with (usp - 104) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at asegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -272 + Z.of_nat 152 + 16) with (usp - 104) in STp by lia.
  replace (usp + -272 + Z.of_nat 152) with (usp - 272 + 152) in STp by lia.
  replace (usp + -272) with (usp - 272) in * by lia.
  apply evt_done. do 20 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 272 + 152) by lia; replace b with (usp - 104) by lia end. exact STp.
Qed.

Lemma el_prologue : forall (usp lo d n : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 272 -> SEGTOP_A <= lo -> usp < 2^63 -> usp mod 16 = 0 -> client_consts m -> mem_inv asegs m ->
  exists sp', usp - 272 <= sp' <= usp - 256 /\ sp' mod 32 = 0 /\
    evt asegs (el_mid0 usp sp' lo d n ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S16 CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 256). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply el_walk0_al; try assumption; lia.
  - exists (usp - 272). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply el_walk0_un; assumption.
Qed.
