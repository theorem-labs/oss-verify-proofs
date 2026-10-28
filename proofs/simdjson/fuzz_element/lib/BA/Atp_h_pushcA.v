(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_anndefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sj_hkitB Atp_h_defsA Atp_h_vkitA Atp_h_vkit2A Atp_h_swapA Atp_h_emplA Atp_h_pushA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma pcw1_fast : forall (usp V X A size cap lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 96 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo -> 0 <= X < 2^64 ->
  0 <= A -> A + 16 * cap < 2^63 -> 0 <= size < cap ->
  shb_consts m -> v_shz [(usp - 96, usp)] m V ->
  rw_cells asegs m V (vcells A (A + 16 * size) (A + 16 * cap)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j0 j1 j2 j3 j4 j5 : list byte),
      ms = entry_st (Z_to_bv 64 0xb541c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) (Z_to_bv 64 V) (Z_to_bv 64 1)
             (Z_to_bv 64 SHB) a3 a4 a5 a6 a7 (Z_to_bv 64 X) (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc VB_ANNINC m1
      /\ munch [(usp - 96, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
      /\ rw_cells asegs m1 (usp + -96) (pf_junk j0 j1 j2 j3 j4 j5)
      /\ rw_cells asegs m1 (usp + -48) (pf_saved s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m1 V (vcells A (A + 16 * size) (A + 16 * cap)))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_PUSHC m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO XX A0 AH SZ (G1 & G2) SHZ VC MI.
  unfold entry_st, ATPA_PUSHC, VB_ANNINC, vcells, pf_junk, pf_saved, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  zstep. zstep. zstep. rewrite shr3_div. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  replace (usp + -96 + Z.of_nat 48) with (usp + -48) in FRs by lia.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|]. split; [exact FRs| exact VC].
Qed.

Lemma pcw2_fast : forall (usp X e : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= X < 2^64 -> 0 <= e < 2^64 ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb542c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 X) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                 (Z_to_bv 64 X) (Z_to_bv 64 e) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memcpy m))
    (MS (mkR (Z_to_bv 64 0xb541c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 e) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb541c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros XX EE. unfold entry_st, e_asan_memcpy.
  zstep. zstep. zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pcw3_fast : forall (usp V A size cap lo : Z)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= lo -> 0 < V -> V + 24 <= lo -> lo <= usp - 96 -> usp < 2^63 -> 0 <= A -> A + 16 * cap < 2^63 -> 0 <= size < cap ->
  v_shz [(V, V + 24)] m V ->
  rw_cells asegs m V (vcells A (A + 16 * size) (A + 16 * cap)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 0xb542c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 (A + 16 * (size + 1))) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xb54f4) fc None m1 (seg_rom asegs)
      /\ munch [(V, V + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 V (vcells A (A + 16 * (size + 1)) (A + 16 * cap)))
    (MS (mkR (Z_to_bv 64 0xb542c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb542c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LO0 V0 VLO LO SPH A0 AH SZ SHZ VC MI.
  unfold vcells, SHB in *.
  pose proof (munch_refl [(V, V + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1 end.
  zstep. shz_norm. zstep. if_false. clear RD1.
  zstep. zstep. zstep.
  replace (A + 16 * size + 16) with (A + 16 * (size + 1)) in * by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma pcw_tail : forall (usp V b e c lo : Z) (loc : list cell)
    (rax gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s4c s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk asegs m lo (usp + -96) -> lo <= usp - 96 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 <= b < 2^63 -> 16 <= e < 2^63 -> 0 <= c < 2^63 -> Z.of_nat (cells_size loc) = 48 ->
  v_shz [(V, V + 24)] m V ->
  rw_cells asegs m (usp + -96) loc -> rw_cells asegs m (usp + -48) (pf_saved s4c s3c s2c s1c s0c rac) ->
  rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 (e - 16)) a1 a2 a3 a4 a5 a6 a7 s2c s3c s4c s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc rac) fc None m1 (seg_rom asegs)
      /\ munch [(V, V + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 V (vcells b e c))
    (MS (mkR rax (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 e) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb54f4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 LOC SHZ FRl FRs VC MI.
  unfold vcells, pf_saved, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(V, V + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1 end.
  zstep. shz_norm. zstep. if_false. clear RD1.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FRl ST (usp + -48). release_frame FRs ST usp. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; replace (e + -16) with (e - 16) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Lemma pcw1_grow : forall (usp V X A cap lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 96 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo -> 0 <= X < 2^64 ->
  0 <= A -> A + 16 * cap < 2^63 -> 0 <= cap <= 2^25 ->
  shb_consts m -> v_shz [(usp - 96, usp)] m V ->
  rw_cells asegs m V (vcells A (A + 16 * cap) (A + 16 * cap)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' a3' : word) (j0 j1 j2 j3 j4 : list byte),
      ms = entry_st (Z_to_bv 64 0xb549c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) (Z_to_bv 64 V)
             (Z_to_bv 64 (vcap_next cap cap)) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 X) (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc VB_ALLOCATE m1
      /\ munch [(usp - 96, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
      /\ rw_cells asegs m1 (usp + -96) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 V)]
      /\ rw_cells asegs m1 (usp + -48) (pf_saved s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m1 V (vcells A (A + 16 * cap) (A + 16 * cap)))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_PUSHC m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO XX A0 AH CAP (G1 & G2) SHZ VC MI.
  unfold entry_st, ATPA_PUSHC, VB_ALLOCATE, vcells, pf_saved, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 96%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  zstep. zstep. zstep. rewrite shr3_div. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. replace (A + 16 * cap + - A) with (16 * cap) by lia.
  zstep. rewrite (psigned_small (16 * cap)) by lia. rewrite (pshiftr_16_4 cap) by lia.
  zstep. zstep. rewrite (pshiftr_small0 (cap + 1) 60) by lia.
  zstep. if_false.
  zstep. replace (A + 16 * cap + - A) with (16 * cap) by lia.
  zstep. rewrite (psigned_small (16 * cap)) by lia. rewrite (pshiftr_16_3 cap) by lia.
  zstep.
  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
    assert (REST : forall xa1 : word, xa1 = Z_to_bv 64 (vcap_next cap cap) ->
      evt asegs QQ (MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
                           (Z_to_bv 64 (16 * cap)) xa1 (Z_to_bv 64 (cap + 1)) (Z_to_bv 64 0) a4 a5 a6 a7
                           (Z_to_bv 64 X) (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 ((V + 8) / 8 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xb5478) fc None mx (seg_rom asegs))) end.
  2:{ if_cases K; zify_cond K.
      - apply REST. f_equal. unfold vcap_next. lia.
      - zstep. apply REST. f_equal. unfold vcap_next. lia. }
  intros xa1 ->.
  assert (CAP' : cap + 1 <= vcap_next cap cap <= 2 * cap + 1) by (unfold vcap_next; lia).
  zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; lia].
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  replace (usp + -96 + Z.of_nat 48) with (usp + -48) in FRs by lia.
  apply evt_done. do 8 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|]. split; [exact FRs| exact VC].
Qed.

Lemma pcg2 : forall (usp V X cap NEW cap' lo : Z) (j0 j1 j2 j3 j4 : list byte)
    (gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo (usp + -96) -> lo <= usp - 96 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 <= X < 2^64 -> 0 <= V < 2^64 ->
  0 <= cap -> 0 < NEW -> NEW + 16 * cap' < 2^63 -> 0 <= cap' ->
  rw_cells asegs m (usp + -96) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 V)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb54cc) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 (NEW + 16 * cap)) (Z_to_bv 64 X) (Z_to_bv 64 16) a3 a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * cap)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memcpy m1
      /\ munch [(usp - 96, usp - 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
      /\ rw_cells asegs m1 (usp + -96) [CB 8 j0; C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NEW + 16 * cap)); CB 8 j3; C8 (Z_to_bv 64 (NEW + 16 * cap')); C8 (Z_to_bv 64 V)])
    (MS (mkR (Z_to_bv 64 0xb549c) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) (Z_to_bv 64 NEW) (Z_to_bv 64 cap') a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 (16 * cap)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb549c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH XX VV C0 N0 NH C1 FRl MI.
  unfold entry_st, e_asan_memcpy in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 96, usp - 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. replace (Z.shiftl cap' 4) with (16 * cap') by (rewrite Z.shiftl_mul_pow2 by lia; lia). zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FRl].
Qed.

Lemma pcg3 : forall (usp V X cap NEW cap' lo : Z) (j0 j3 : list byte)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo (usp + -96) -> lo <= usp - 96 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 <= V < 2^64 ->
  0 <= cap -> 0 < NEW -> NEW + 16 * cap' < 2^63 -> cap + 1 <= cap' ->
  rw_cells asegs m (usp + -96) [CB 8 j0; C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NEW + 16 * cap)); CB 8 j3; C8 (Z_to_bv 64 (NEW + 16 * cap')); C8 (Z_to_bv 64 V)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb54e0) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 V) (Z_to_bv 64 (usp + -88)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * cap + 16)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_SWAPOUT m1
      /\ munch [(usp - 96, usp - 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
      /\ rw_cells asegs m1 (usp + -96) [CB 8 j0]
      /\ rw_cells asegs m1 (usp + -88) (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V))
    (MS (mkR (Z_to_bv 64 0xb54cc) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * cap)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb54cc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH VV C0 N0 NH CC FRl MI.
  unfold entry_st, VB_SWAPOUT, sb5 in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 96, usp - 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch type of FRl with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FRl end.
  apply rw_cells_app in FRl. destruct FRl as [FR0 FRb]. cbn [cells_size csize Nat.add] in FRb.
  replace (usp + -96 + Z.of_nat 8) with (usp + -88) in FRb by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR0| exact FRb].
Qed.

Lemma pcg4 : forall (usp V b e c lo : Z)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s2x : word) F fc (m : mem),
  0 <= lo -> lo <= usp - 96 -> usp < 2^63 -> 0 < V -> V + 24 <= lo -> 0 <= b < 2^63 -> 0 <= e < 2^63 -> 0 <= c < 2^63 ->
  shz m V 24 -> rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb54f4) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
                 (Z_to_bv 64 (usp + -88)) a1 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 e) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_SBDTOR m))
    (MS (mkR (Z_to_bv 64 0xb54e0) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) a0 a1 a2 a3 a4 a5 a6 a7
             s2x s3 (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb54e0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LO0 LO SPH V0 VLO B0 E0 C0 SHZ VC MI.
  unfold entry_st, VB_SBDTOR, vcells, SHB in *.
  pose proof (SHZ (V + 8) ltac:(lia)) as RD1.
  zstep. shz_norm. zstep. if_false. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Section PushC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem pushc_ok : push_cpsA RT ATPA_PUSHC.
Proof using AF RTF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V X A cap size xd xl els L0 lo
    FDO MST -> -> -> VR VL LPOS SZB XC FOBJ0 UX XT X8 LVB CR ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_range RT AF Σ m f kf ART0 INF) as (_ & _ & _ & FLV).
  destruct VR as (ELS & SZC & CAPB & A0 & AH & SV & BLK). unfold zlength in ELS. unfold vliveA in VL.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -96) mod 16 = 0) by (replace (usp + -96) with (usp + (-6) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (FPC0 : fp_client RT Σ lo [(usp - 96, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp RT AF Σ m lo _ V ART0 LOW FPC0 FOBJ0) as SHZ0.
  assert (LENL : Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX).
  { rewrite VL, length_app. pose proof (ann_block_length A (16 * cap) (16 * size)) as BL. unfold vblockA. destruct (cap =? 0); cbn [length] in *; lia. }
  destruct (Z.ltb_spec size cap) as [LT|GE].
  -
    destruct BLK as [[C0 _]|(C1 & A16 & APOS & BE)]; [lia|].
    assert (VB : vblockA A cap size = ann_block A (16 * cap) (16 * size)).
    { unfold vblockA. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite VB in VL.
    assert (INA : In (A, 16 * size) (rt_live RT Σ)) by (rewrite VL; apply in_or_app; left; apply ann_block_vis).
    pose proof (af_live_range RT AF Σ m A (16 * size) ART0 INA) as (_ & A1 & ASEG).

    pose proof (pcw1_fast usp V X A size cap lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) A0 AH ltac:(lia) (conj G1 G2) SHZ0 SV MI0) as W1.
    rewrite <- ESP in W1.
    lazymatch type of W1 with evt asegs _ ?X0 =>
      assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j0 & j1 & j2 & j3 & j4 & j5 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & FRs1 & VC1) & Hc1'). clear Hc1.
    pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC0 MU1 WM1) as ART1.
    pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC0 MU1 FOBJ0) as FOBJ1.

    apply (anninc_cps RT AF ANN Σ PMc (Z_to_bv 64 0xb541c) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 V) (Z_to_bv 64 1) (Z_to_bv 64 SHB) a3 a4 a5 a6 a7 (Z_to_bv 64 X) (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m1 V A (16 * cap) (16 * size) 1 L0 lo FDO MST eq_refl eq_refl eq_refl VC1 FOBJ1 VL
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia) ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia) ltac:(lia) ART1 MI1);
      [rewrite EU2; exact ST1| exact LOW| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; exact SPA2| exact FRM| split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
    intros c2 ((Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (r2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb541c) in Hc2' by lia.
    cbn [app] in LV1. replace (16 * size + 16 * 1) with (16 * (size + 1)) in LV1 by lia.
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INA1 : In (A, 16 * (size + 1)) (rt_live RT Σ1)) by (rewrite LV1; apply in_or_app; left; apply ann_block_vis).
    pose proof (af_live_range RT AF Σ1 m2 A (16 * (size + 1)) ART2 INA1) as (_ & A2 & _).
    assert (INF1 : In (f, kf) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
    assert (CLV1 : forall sp' x, V <= x < V + 24 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
    { intros sp' x Hx. right; right; right; left. exists f, kf. split; [exact INF1| lia]. }

    pose proof (pcw2_fast usp X (A + 16 * size) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) r2 b1 b2 b3 b4 b5 b6 b7
                  (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 ltac:(ul) ltac:(ul)) as W2.
    lazymatch type of W2 with evt asegs _ ?X0 =>
      assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c2' Hc2''.

    assert (XB2 : bytes_at asegs m2 X (xbytes xd xl)).
    { apply (rw_cells_bytes_at asegs m2 X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)]).
      apply (rw_cells_agree asegs m1 m2 _ _); [apply (rw_cells_agree asegs m m1 _ _ XC); [| exact WM1] | | exact WM2].
      - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I].
      - apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    change (Z_to_bv 64 16) with (Z_to_bv 64 (Z.of_nat (length (xbytes xd xl)))) in Hc2''.
    pose proof (af_acc_live RT AF Σ1 m2 A (16 * (size + 1)) ART2 INA1) as [WRA2 ACA2].
    apply ((rf_asan_memcpy RT RTF) Σ1 PMc (Z_to_bv 64 0xb542c) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 X) (Z_to_bv 64 (Z.of_nat (length (xbytes xd xl)))) b3 b4 b5 b6 b7
             (Z_to_bv 64 X) (Z_to_bv 64 (A + 16 * size)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             F2 fc2 m2 (A + 16 * size) X (xbytes xd xl) lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(rewrite xbytes_length; cbn; lia) XB2);
      [| | | exact ART2| exact MI2| | split; [exact Hc2''| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c2' Hc2''); intros ms0 <-; exact FRM2] |].
    { unfold checked_src. rewrite EU2, xbytes_length. change (Z.of_nat 16) with 16. split; [| right; lia].
      intros _. split; [apply (af_acc_stack RT AF Σ1 m2 X 16 ART2); ul|]. right; right; left. ul. }
    { unfold checked_dst. rewrite EU2, xbytes_length. change (Z.of_nat 16) with 16.
      split; [intros _; split; [exact (acc_sub asegs m2 A (16 * (size + 1)) (A + 16 * size) 16 ACA2 ltac:(lia) ltac:(lia))| left; exists A, (16 * (size + 1)); split; [exact INA1| lia]]|].
      split; [| exact (wr_at_sub m2 A (16 * (size + 1)) (A + 16 * size) 16 WRA2 ltac:(lia) ltac:(lia) ltac:(lia))].
      intros i Hi. right; right; left. exists A, (16 * (size + 1)). split; [exact INA1| lia]. }
    { rewrite xbytes_length. change (Z.of_nat 16) with 16. left. ul. }
    { unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA2]. }
    intros c3 (Hc3 & FC3).
    destruct (ASTA_unpack_f RT Σ1 _ _ c3 Hc3 FC3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3) & FRM3 & Hc3'). clear Hc3.
    destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
    cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. rewrite xbytes_length in PRES3. change (Z.of_nat 16) with 16 in PRES3.
    rewrite (ret_pc_even 0xb542c) in Hc3' by lia.

    assert (LV1' : exists l1, rt_live RT Σ1 = l1 ++ (A, 16 * (size + 1)) :: L0).
    { rewrite LV1. unfold ann_block. destruct (Z.eqb_spec (16 * (size + 1)) (16 * cap)) as [E|NE].
      - exists []. cbn. rewrite <- E. reflexivity.
      - exists [(A, ann_g1 (16 * cap)); (A, ann_g2 (16 * cap))]. reflexivity. }
    destruct LV1' as (l1 & LV1').
    assert (SUBL : forall e, In e L0 -> In e (l1 ++ L0)) by (intros e He; apply in_or_app; right; exact He).
    assert (FPV1 : fp_client RT Σ1 lo [(V, V + 24)]).
    { constructor; [| constructor]. right; right. exists f, kf. cbn [fst snd]. split; [exact INF1| lia]. }
    assert (VC3 : rw_cells asegs m3 V (vcells A (A + 16 * size) (A + 16 * cap))).
    { apply (rw_cells_agree asegs m2 m3 _ _); [apply (rw_cells_agree asegs m1 m2 _ _ VC1); [| exact WM2]| | exact WM3].
      - apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx.
        right; right; right; left. exists f, kf. split; [exact INF| lia].
      - apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3). intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx.
        split; [apply CLV1; lia|]. rewrite <- FRS1 in INF. pose proof (af_frames_range RT AF Σ1 m2 f kf ART2 INF1) as (_ & _ & _ & FLV1). destruct (FLV1 _ _ INA1); lia. }

    pose proof (pcw3_fast usp V A size cap lo gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 (A + 16 * size)) d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 X) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
                  F3 fc3 m3 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) A0 AH ltac:(lia) (v_shz_of_fp RT AF Σ1 m3 lo _ V ART3 LOW1 FPV1 (fobj_pres_ex_live RT AF Σ1 Σ1 _ _ _ _ A (16 * (size + 1)) m2 m3 V 24 ART2
                    (fobj_pres RT AF Σ Σ1 _ _ m1 m2 V 24 ART1 FOBJ1 PRES2 FRS1) PRES3 ltac:(auto) eq_refl INA1 ltac:(lia) ltac:(lia))) VC3 MI3) as W3.
    lazymatch type of W3 with evt asegs _ ?X0 =>
      assert (W3' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes asegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
    destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & VC4) & Hc4'). clear Hc4.
    pose proof (art_fp_client RT AF Σ1 m3 m4 lo _ ART3 LOW1 FPV1 MU4 WM4) as ART4.

    assert (AGF : agree_on (fun x => usp - 96 <= x < usp) m1 m4).
    { intros a Ha. cbv beta in Ha. rewrite (MU4 a); [| cbn [outside]; split; [ul| exact I]].
      rewrite (PRES3 a); [| left; lia| ul]. apply PRES2. left. lia. }
    assert (FRl4 : rw_cells asegs m4 (usp + -96) (pf_junk j0 j1 j2 j3 j4 j5)).
    { apply (rw_cells_agree_nw asegs m1 m4 _ _ FRl1). eapply agree_sub; [exact AGF|]. intros x Hx. unfold pf_junk in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
    assert (FRs4 : rw_cells asegs m4 (usp + -48) (pf_saved s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree_nw asegs m1 m4 _ _ FRs1). eapply agree_sub; [exact AGF|]. intros x Hx. unfold pf_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
    assert (ST4 : stk asegs m4 lo (usp + -96)).
    { apply (stk_agree asegs m3 m4 _ _ ST3); [| exact WM4]. apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbn [outside]. split; [ul| exact I]. }

    pose proof (pcw_tail usp V A (A + 16 * (size + 1)) (A + 16 * cap) lo (pf_junk j0 j1 j2 j3 j4 j5) (Z_to_bv 64 0xb542c) gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 0) d1 d2 d3 d4 d5 d6 d7
                  (Z_to_bv 64 X) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 s4 s3 s2 s1 s0 ra F3 fc3 m4
                  ST4 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul) eq_refl
                  (v_shz_of_fp RT AF Σ1 m4 lo _ V ART4 LOW1 FPV1 (fobj_munch RT AF Σ1 m3 m4 lo _ V 24 ART3 LOW1 FPV1 MU4
                     (fobj_pres_ex_live RT AF Σ1 Σ1 _ _ _ _ A (16 * (size + 1)) m2 m3 V 24 ART2 (fobj_pres RT AF Σ Σ1 _ _ m1 m2 V 24 ART1 FOBJ1 PRES2 FRS1) PRES3 ltac:(auto) eq_refl INA1 ltac:(lia) ltac:(lia))))
                  FRl4 FRs4 VC4 MI4) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 =>
      assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
    clear W4.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W4') Hc4'). clear W4'. intros c5 Hc5.
    destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & ST5 & VC5) & Hc5'). clear Hc5.
    pose proof (art_fp_client RT AF Σ1 m4 m5 lo _ ART4 LOW1 FPV1 MU5 WM5) as ART5.

    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM3].
    exists Σ1, A.
    assert (VCA : vcap_after cap size = cap) by (unfold vcap_after; replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
    rewrite VCA.
    split; [| split; [| split; [exact FRS1| split; [exact SP1|]]]].
    + eapply ASTA_conseq; [exact Hc5'|]. intros ms <-. exists (Z_to_bv 64 (A + 16 * (size + 1) - 16)), m5.
      split; [rewrite ESP; unfold ret_st; do 16 eexists; reflexivity|].
      split; [split; [exact ART5| split; [exact MI5| fold usp; exact ST5]]|].
      split.
      *
        intros a Ha Hout. fold usp in Ha. cbn [outside] in Hout. destruct Hout as [HO _].
        assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
        { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite VL; apply in_or_app; right; exact He| auto| lia]. }
        assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) (bv_unsigned a)).
        { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV1; apply in_or_app; right; exact He| intros e He; rewrite FRS1; exact He| lia]. }
        pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha0) as SPL.
        pose proof (chunk_apart RT AF Σ1 m2 _ A (16 * (size + 1)) L0 L0 usp (bv_unsigned a) ART2 LV1' SUBL ltac:(rewrite SP1; ul) ltac:(rewrite FRS1; exact Ha)) as NIN.
        rewrite (MU5 a), (MU4 a); [| cbn [outside]; split; [exact HO| exact I]| cbn [outside]; split; [exact HO| exact I]].
        rewrite (PRES3 a Ha1 ltac:(lia)). rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha0); auto; lia].
        apply MU1. cbn [outside]. split; [ul| exact I].
      *
        unfold vrepA. split; [unfold zlength; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split; [exact CAPB|]. split; [exact A0|]. split; [exact AH|].
        split; [exact VC5|]. right. split; [exact C1|]. split; [exact A16|]. split; [exact APOS|].
        rewrite velts_app. cbn [velts fst snd]. apply Sj_stage1_kit.rw_cells_app. rewrite velts_size.
        replace (A + Z.of_nat (16 * length els)) with (A + 16 * size) by lia. split.
        --
           apply (rw_cells_agree_nw asegs m1 m5 _ _); [apply (rw_cells_agree asegs m m1 _ _ BE); [| exact WM1]|].
           { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. rewrite velts_size in Hx. cbn [outside]. split; [ul| exact I]. }
           intros a Ha. cbv beta in Ha. rewrite velts_size in Ha.
           rewrite (MU5 a), (MU4 a); [| cbn [outside]; split; [destruct (FLV _ _ INA); lia| exact I]| cbn [outside]; split; [destruct (FLV _ _ INA); lia| exact I]].
           rewrite (PRES3 a); [| right; right; left; exists A, (16 * (size + 1)); split; [exact INA1| lia]| lia].
           apply PRES2. right; right; left. exists A, (16 * size). split; [exact INA| lia].
        --
           apply xcells_of_bytes.
           ++ apply (bytes_at_agree asegs m3 m5 _ _ BY3). intros a Ha. rewrite xbytes_length in Ha. cbv beta in Ha.
              pose proof (af_frames_range RT AF Σ1 m2 f kf ART2 INF1) as (_ & _ & _ & FLV1). destruct (FLV1 _ _ INA1) as [D|D];
              (rewrite (MU5 a), (MU4 a); [reflexivity| cbn [outside]; split; [lia| exact I]| cbn [outside]; split; [lia| exact I]]).
           ++ apply (wr_at_sub m5 A (16 * (size + 1)) (A + 16 * size) 16); [| lia| lia| lia].
              exact (proj1 (af_acc_live RT AF Σ1 m5 A (16 * (size + 1)) ART5 INA1)).
    +
      unfold vliveA, vblockA. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite LV1. reflexivity.
    +
      unfold vcost_push. replace (size <? cap) with true by (symmetry; apply Z.ltb_lt; lia). lia.
  -
    assert (ES : size = cap) by lia. rewrite ES in *. clear ES SZC.
    set (cap' := vcap_next cap cap) in *.
    assert (CAP' : cap + 1 <= cap' <= 2 * cap + 1) by (subst cap'; unfold vcap_next; lia).
    assert (CAPB' : 16 * cap' <= 0x20001000) by lia.
    assert (AR1 : A + 16 * cap <= rt_sp0 RT Σ - STACK_WIN).
    { destruct BLK as [[C0 AZ]|(C1 & _)]; [subst A; rewrite C0; ul|].
      assert (VB : vblockA A cap cap = [(A, 16 * cap)]) by (unfold vblockA; replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia); apply ann_block_plain).
      assert (INA : In (A, 16 * cap) (rt_live RT Σ)) by (rewrite VL, VB; left; reflexivity).
      pose proof (af_live_range RT AF Σ m A (16 * cap) ART0 INA). lia. }

    pose proof (pcw1_grow usp V X A cap lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) A0 AH ltac:(lia) (conj G1 G2) SHZ0 SV MI0) as W1.
    rewrite <- ESP in W1. fold cap' in W1.
    lazymatch type of W1 with evt asegs _ ?X0 =>
      assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & a3' & j0 & j1 & j2 & j3 & j4 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & FRs1 & VC1) & Hc1'). clear Hc1.
    pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC0 MU1 WM1) as ART1.
    pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC0 MU1 FOBJ0) as FOBJ1.

    apply (alloc_cps RT AF RTF Σ PMc (Z_to_bv 64 0xb549c) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 V) (Z_to_bv 64 cap') a2' a3' a4 a5 a6 a7 (Z_to_bv 64 X) (Z_to_bv 64 (16 * cap)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m1 cap' lo FDO MST ltac:(lia) CAPB' eq_refl eq_refl LENL);
      [| exact ART1| exact MI1| rewrite EU2; exact ST1| exact LOW| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; exact SPA2| exact FRM| split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
    { unfold vcost_push in CR. replace (cap <? cap) with false in CR by (symmetry; apply Z.ltb_ge; lia). subst cap'. exact CR. }
    intros c2 ((Σ1 & NEW & Hc2 & LV1 & FRS1 & SP1 & CR1 & N0 & N16 & NTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRN2 & ACN2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb549c) in Hc2' by lia.
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INN1 : In (NEW, 16 * cap') (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    pose proof (af_live_range RT AF Σ1 m2 NEW (16 * cap') ART2 INN1) as (_ & N1 & _).
    assert (INF1 : In (f, kf) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
    pose proof (af_frames_range RT AF Σ1 m2 f kf ART2 INF1) as (_ & _ & _ & FLV1).
    assert (CLV1 : forall sp' x, V <= x < V + 24 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
    { intros sp' x Hx. right; right; right; left. exists f, kf. split; [exact INF1| lia]. }
    assert (FPL1 : fp_client RT Σ1 lo [(usp - 96, usp - 48)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

    assert (FRl2 : rw_cells asegs m2 (usp + -96) [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; C8 (Z_to_bv 64 V)]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FRl1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }

    pose proof (pcg2 usp V X cap NEW cap' lo j0 j1 j2 j3 j4 gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                  F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) N0 ltac:(ul) ltac:(lia) FRl2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X0 =>
      assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3 & FRl3) & Hc3'). clear Hc3.
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPL1 MU3 WM3) as ART3.
    assert (XB3 : bytes_at asegs m3 X (xbytes xd xl)).
    { apply (rw_cells_bytes_at asegs m3 X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)]).
      apply (rw_cells_agree asegs m2 m3 _ _); [apply (rw_cells_agree asegs m1 m2 _ _); [apply (rw_cells_agree asegs m m1 _ _ XC); [| exact WM1]| | exact WM2]| | exact WM3].
      - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I].
      - apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul.
      - apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
    change (Z_to_bv 64 16) with (Z_to_bv 64 (Z.of_nat (length (xbytes xd xl)))) in Hc3'.
    pose proof (af_acc_live RT AF Σ1 m3 NEW (16 * cap') ART3 INN1) as [WRN3 ACN3].
    apply ((rf_asan_memcpy RT RTF) Σ1 PMc (Z_to_bv 64 0xb54cc) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 (NEW + 16 * cap)) (Z_to_bv 64 X) (Z_to_bv 64 (Z.of_nat (length (xbytes xd xl)))) b3 b4 b5 b6 b7
             (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * cap)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             F2 fc2 m3 (NEW + 16 * cap) X (xbytes xd xl) lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(rewrite xbytes_length; cbn; lia) XB3);
      [| | | exact ART3| exact MI3| | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    { unfold checked_src. rewrite EU2, xbytes_length. change (Z.of_nat 16) with 16. split; [| right; lia].
      intros _. split; [apply (af_acc_stack RT AF Σ1 m3 X 16 ART3); ul|]. right; right; left. ul. }
    { unfold checked_dst. rewrite EU2, xbytes_length. change (Z.of_nat 16) with 16.
      split; [intros _; split; [exact (acc_sub asegs m3 NEW (16 * cap') (NEW + 16 * cap) 16 ACN3 ltac:(lia) ltac:(lia))| left; exists NEW, (16 * cap'); split; [exact INN1| lia]]|].
      split; [| exact (wr_at_sub m3 NEW (16 * cap') (NEW + 16 * cap) 16 WRN3 ltac:(lia) ltac:(lia) ltac:(lia))].
      intros i Hi. right; right; left. exists NEW, (16 * cap'). split; [exact INN1| lia]. }
    { rewrite xbytes_length. change (Z.of_nat 16) with 16. left. ul. }
    { unfold call_ok. rewrite EU2. split; [exact ST3|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA2]. }
    intros c4 (Hc4 & FC4).
    destruct (ASTA_unpack_f RT Σ1 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BY4) & FRM4 & Hc4'). clear Hc4.
    destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
    cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite xbytes_length in PRES4. change (Z.of_nat 16) with 16 in PRES4.
    rewrite (ret_pc_even 0xb54cc) in Hc4' by lia.
    assert (FRl4 : rw_cells asegs m4 (usp + -96) [CB 8 j0; C8 (Z_to_bv 64 NEW); C8 (Z_to_bv 64 (NEW + 16 * cap)); CB 8 j3; C8 (Z_to_bv 64 (NEW + 16 * cap')); C8 (Z_to_bv 64 V)]).
    { apply (rw_cells_agree asegs m3 m4 _ _ FRl3); [| exact WM4]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; lia| ul]. }

    pose proof (pcg3 usp V X cap NEW cap' lo j0 j3 gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 (NEW + 16 * cap)) d1 d2 d3 d4 d5 d6 d7
                  (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4
                  ST4 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) N0 ltac:(ul) ltac:(lia) FRl4 MI4) as W3.
    lazymatch type of W3 with evt asegs _ ?X0 =>
      assert (W3' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.
    destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & ST5 & FR05 & SB5) & Hc5'). clear Hc5.
    pose proof (art_fp_client RT AF Σ1 m4 m5 lo _ ART4 LOW1 FPL1 MU5 WM5) as ART5.

    assert (AGV : agree_on (fun x => V <= x < V + 24) m1 m5).
    { intros a Ha. cbv beta in Ha. rewrite (MU5 a); [| cbn [outside]; split; [ul| exact I]].
      rewrite (PRES4 a); [| apply CLV1; lia| destruct (FLV1 _ _ INN1); lia].
      rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]]. apply PRES2. right; right; right; left. exists f, kf. split; [exact INF| lia]. }
    assert (VC5 : rw_cells asegs m5 V (vcells A (A + 16 * cap) (A + 16 * cap))) by (apply (rw_cells_agree_nw asegs m1 m5 _ _ VC1); eapply agree_sub; [exact AGV|]; intros x Hx; exact Hx).
    pose proof (fobj_pres RT AF Σ Σ1 _ _ m1 m2 V 24 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.
    pose proof (fobj_munch RT AF Σ1 m2 m3 lo _ V 24 ART2 LOW1 FPL1 MU3 FOBJ2) as FOBJ3.
    pose proof (fobj_pres_ex_live RT AF Σ1 Σ1 _ _ _ _ NEW (16 * cap') m3 m4 V 24 ART3 FOBJ3 PRES4 ltac:(auto) eq_refl INN1 ltac:(lia) ltac:(lia)) as FOBJ4.
    pose proof (fobj_munch RT AF Σ1 m4 m5 lo _ V 24 ART4 LOW1 FPL1 MU5 FOBJ4) as FOBJ5.

    assert (OLD5 : (cap = 0 /\ A = 0) \/ (1 <= cap /\ A mod 16 = 0 /\ 0 < A /\ rw_cells asegs m5 A (velts els))).
    { destruct BLK as [[C0 AZ]|(C1 & A16 & APOS & BE)]; [left; split; assumption| right].
      split; [exact C1|]. split; [exact A16|]. split; [exact APOS|].
      assert (VB : vblockA A cap cap = [(A, 16 * cap)]) by (unfold vblockA; replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia); apply ann_block_plain).
      assert (INA : In (A, 16 * cap) (rt_live RT Σ)) by (rewrite VL, VB; left; reflexivity).
      assert (INA1 : In (A, 16 * cap) (rt_live RT Σ1)) by (rewrite LV1; right; exact INA).
      pose proof (af_live_disj RT AF Σ1 m2 NEW (16 * cap') A (16 * cap) [] (rt_live RT Σ) ART2 LV1 INA) as DJ.
      apply (rw_cells_agree_nw asegs m m5 _ _ BE). intros a Ha. cbv beta in Ha. rewrite velts_size in Ha.
      rewrite (MU5 a); [| cbn [outside]; split; [ul| exact I]].
      rewrite (PRES4 a); [| right; right; left; exists A, (16 * cap); split; [exact INA1| lia]| lia].
      rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]].
      rewrite (PRES2 a); [| right; right; left; exists A, (16 * cap); split; [exact INA| lia]].
      apply MU1. cbn [outside]. split; [ul| exact I]. }
    assert (EU88 : bv_unsigned (Z_to_bv 64 (usp + -96)) <= usp + -88) by (rewrite EU2; lia).
    assert (LVS : rt_live RT Σ1 = (NEW, 16 * cap') :: vblockA A cap cap ++ L0) by (rewrite LV1, VL; reflexivity).
    apply (swapout_cps RT AF RTF ANN Σ1 PMc (Z_to_bv 64 0xb54e0) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
             (Z_to_bv 64 V) (Z_to_bv 64 (usp + -88)) d2 d3 d4 d5 d6 d7 (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * cap + 16)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
             v3 v4 v5 v6 F4 fc4 m5 V (usp + -88) A cap NEW cap' els L0 lo FDO MST eq_refl eq_refl eq_refl VC5 FOBJ5 SB5 EU88 ltac:(ul) ltac:(clear - SPA; Z.div_mod_to_equations; lia)
             LVS OLD5 ltac:(unfold zlength; lia) ltac:(lia) CAPB' N0 NTOP ART5 MI5);
      [rewrite EU2; exact ST5| exact LOW1| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; exact SPA2| exact FRM4| split; [exact Hc5'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM4] |].
    intros c6 ((Σ2 & Hc6 & LV2 & FRS2 & SP2 & CR2) & FC6).
    destruct (ASTA_unpack_f RT Σ2 _ _ c6 Hc6 FC6) as (ms6 & (r6 & m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & VC6 & SB6 & BY6) & FRM6 & Hc6'). clear Hc6.
    destruct RS6 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
    cbn [ms_fcsr] in FRM6. rewrite EU2 in ST6, PRES6. rewrite (ret_pc_even 0xb54e0) in Hc6' by lia.
    assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
    assert (INF2 : In (f, kf) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF1).
    assert (FP6 : fp_client RT Σ1 lo [(usp + -88, usp + -88 + 32); (V, V + 24); (NEW, NEW + 16 * cap)]).
    { constructor; [left; cbn [fst snd]; ul|]. constructor; [right; right; exists f, kf; cbn [fst snd]; split; [exact INF1| lia]|].
      constructor; [| constructor]. right; left. exists NEW, (16 * cap'). cbn [fst snd]. split; [exact INN1| lia]. }
    pose proof (fobj_pres_fpc RT AF Σ1 Σ2 _ _ lo _ m5 m6 V 24 ART5 FOBJ5 PRES6 FRS2 LOW1 FP6) as FOBJ6.

    assert (LVS1 : rt_live RT Σ1 = [] ++ (NEW, 16 * cap') :: (vblockA A cap cap ++ L0)) by (rewrite LVS; reflexivity).
    assert (NAP : forall sp' a, rt_sp0 RT Σ1 - STACK_WIN <= sp' -> aclient L0 (rt_frames RT Σ1) sp' a -> ~ (NEW <= a < NEW + 16 * cap')).
    { intros sp' a SP' Ha. apply (chunk_apart RT AF Σ1 m2 [] NEW (16 * cap') _ L0 sp' a ART2 LVS1); [| exact SP'| exact Ha].
      intros e He. cbn [app]. apply in_or_app. right. exact He. }

    pose proof (pcg4 usp V NEW (NEW + 16 * (cap + 1)) (NEW + 16 * cap') lo gp (Z_to_bv 64 0x6a7e68) w0 w1 w2 r6 g1 g2 g3 g4 g5 g6 g7
                  (Z_to_bv 64 (NEW + 16 * cap + 16)) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 (Z_to_bv 64 X) F6 fc6 m6
                  ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) (fobj_shz RT AF Σ2 m6 V 24 ART6 FOBJ6) VC6 MI6) as W4.
    lazymatch type of W4 with evt asegs _ ?X0 =>
      assert (W4' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
    clear W4.
    apply (cps_realizes asegs _ _ _ c6 (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc6'). clear W4'. intros c7 Hc7.

    assert (MID : forall (Σ3 : rts RT) (m8 : mem) (c8 : config) (r8 : word) (y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 : word) (F8 : bvmap 5 word) (fc8 : bv 32),
      frm0 fc8 -> rt_live RT Σ3 = ann_block NEW (16 * cap') (16 * (cap + 1)) ++ L0 -> rt_frames RT Σ3 = rt_frames RT Σ2 -> rt_sp0 RT Σ3 = rt_sp0 RT Σ2 ->
      rt_credit RT Σ3 = rt_credit RT Σ2 ->
      ART RT Σ3 m8 -> mem_inv asegs m8 -> stk asegs m8 lo (usp + -96) ->
      rt_pres (rt_live RT Σ3) (rt_frames RT Σ2) (usp + -96) m6 m8 ->
      ASTA RT Σ3 PMc (eq (MS (mkR (Z_to_bv 64 0xb54f4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V) r8 z1 z2 z3 z4 z5 z6 z7
                               (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * (cap + 1))) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
                          F8 (Z_to_bv 64 0xb54f4) fc8 None m8 (seg_rom asegs))) c8 ->
      realizes asegs c8 T).
    2:{ destruct OLD5 as [(C0 & AZ)|(C1 & A16 & APOS & BE5)].
        -
          subst A. rewrite C0 in SB6. change (0 + 16 * 0) with 0 in SB6.
          apply (sbdtor0_cps RT AF Σ2 PMc (Z_to_bv 64 0xb54f4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) w0 w1 w2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
                   (Z_to_bv 64 (usp + -88)) g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * (cap + 1))) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
                   w3 w4 w5 w6 F6 fc6 m6 (usp + -88) 0 0 V lo FDO MST eq_refl eq_refl SB6 EU88 ltac:(ul) ltac:(clear - SPA; Z.div_mod_to_equations; lia)
                   ltac:(lia) ltac:(lia) ltac:(ul) ART6 MI6); [rewrite EU2; exact ST6| exact LOW2| rewrite EU2; ul| rewrite EU2; ul| exact FRM6| |].
          { split; [exact Hc7| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c7 Hc7); intros ms0 <-; exact FRM6]. }
          intros c8 (Hc8 & FC8).
          destruct (ASTA_unpack_f RT Σ2 _ _ c8 Hc8 FC8) as (ms8 & (r8 & m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8) & FRM8 & Hc8'). clear Hc8.
          destruct RS8 as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F8 & fc8 & ->).
          cbn [ms_fcsr] in FRM8. rewrite EU2 in ST8, PRES8. rewrite (ret_pc_even 0xb54f4) in Hc8' by lia.
          assert (LV2' : rt_live RT Σ2 = ann_block NEW (16 * cap') (16 * (cap + 1)) ++ L0) by (rewrite LV2; unfold vblockA; rewrite C0; reflexivity).
          rewrite <- LV2' in *.
          exact (MID Σ2 m8 c8 r8 y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 F8 fc8 FRM8 eq_refl eq_refl eq_refl eq_refl ART8 MI8 ST8 PRES8 Hc8').
        -
          assert (VB : vblockA A cap cap = [(A, 16 * cap)]) by (unfold vblockA; replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia); apply ann_block_plain).
          assert (INA2 : In (A, 16 * cap) (rt_live RT Σ2)) by (rewrite LV2, VB; apply in_or_app; right; left; reflexivity).
          apply (sbdtor_cps RT AF RTF Σ2 PMc (Z_to_bv 64 0xb54f4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x6a7e68) w0 w1 w2 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 V)
                   (Z_to_bv 64 (usp + -88)) g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 X) (Z_to_bv 64 (NEW + 16 * (cap + 1))) (Z_to_bv 64 ((V + 8) / 8 + SHB)) s5 s6 s7 s8 s9 s10 s11
                   w3 w4 w5 w6 F6 fc6 m6 (usp + -88) A A (A + 16 * cap) V (16 * cap) lo FDO MST eq_refl eq_refl SB6 EU88 ltac:(ul) ltac:(clear - SPA; Z.div_mod_to_equations; lia)
                   ltac:(ul) ltac:(ul) ltac:(ul) INA2 ART6 MI6);
            [rewrite EU2; exact ST6| exact LOW2| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2; exact SPA2| | exact FRM6| |].
          { unfold unwind_ok. rewrite EU2, unsigned_lit by ul. left. ul. }
          { split; [exact Hc7| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c7 Hc7); intros ms0 <-; exact FRM6]. }
          intros c8 ((Σ3 & v8 & Hc8 & LV3 & FRS3 & SP3 & CR3) & FC8).
          destruct (ASTA_unpack_f RT Σ3 _ _ c8 Hc8 FC8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & ST8) & PRES8) & FRM8 & Hc8'). clear Hc8.
          destruct RS8 as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F8 & fc8 & ->).
          cbn [ms_fcsr] in FRM8. rewrite EU2 in ST8, PRES8. rewrite (ret_pc_even 0xb54f4) in Hc8' by lia.
          assert (LV3' : rt_live RT Σ3 = ann_block NEW (16 * cap') (16 * (cap + 1)) ++ L0).
          { rewrite LV3, LV2, VB, live_remove_app, live_remove_app. rewrite (live_remove_hd [] A (16 * cap)) by (intros e []).
            rewrite (live_remove_none L0).
            2:{ intros e He E. destruct e as [p2 n2]. cbn in E. subst p2. pose proof (LPOS _ _ He) as POS.
                pose proof (af_live_disj RT AF Σ1 m2 A (16 * cap) A n2 [(NEW, 16 * cap')] L0 ART2 ltac:(rewrite LVS, VB; reflexivity) ltac:(apply in_or_app; right; exact He)). lia. }
            rewrite live_remove_none; [reflexivity|]. intros e He. rewrite (ann_block_fst _ _ _ e He).
            destruct (af_live_disj RT AF Σ1 m2 NEW (16 * cap') A (16 * cap) [] (vblockA A cap cap ++ L0) ART2 LVS1 ltac:(rewrite VB; left; reflexivity)); lia. }
          exact (MID Σ3 m8 c8 v8 y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 F8 fc8 FRM8 LV3' FRS3 SP3 CR3 ART8 MI8 ST8 PRES8 Hc8'). }

    intros Σ3 m8 c8 r8 y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 F8 fc8 FRM8 LV3 FRS3 SP3 CR3 ART8 MI8 ST8 PRES8 Hc8.
    assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW2).
    assert (INF3 : In (f, kf) (rt_frames RT Σ3)) by (rewrite FRS3; exact INF2).
    assert (INN3 : In (NEW, 16 * (cap + 1)) (rt_live RT Σ3)) by (rewrite LV3; apply in_or_app; left; apply ann_block_vis).
    assert (SUB3 : forall e, In e L0 -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; apply in_or_app; right; exact He).
    assert (FPV3 : fp_client RT Σ3 lo [(V, V + 24)]) by (constructor; [right; right; exists f, kf; cbn [fst snd]; split; [exact INF3| lia]| constructor]).
    pose proof (fobj_pres RT AF Σ2 Σ3 _ _ m6 m8 V 24 ART6 FOBJ6 PRES8 FRS3) as FOBJ8.

    assert (AGS : agree_on (fun x => usp - 48 <= x < usp) m1 m8).
    { intros a Ha. cbv beta in Ha.
      rewrite (PRES8 a); [| left; lia]. rewrite (PRES6 a); [| left; lia| cbn [outside]; split; [lia|]; split; [ul|]; split; [ul| exact I]].
      rewrite (MU5 a); [| cbn [outside]; split; [lia| exact I]]. rewrite (PRES4 a); [| left; lia| ul].
      rewrite (MU3 a); [| cbn [outside]; split; [lia| exact I]]. apply PRES2. left. lia. }
    assert (FRs8 : rw_cells asegs m8 (usp + -48) (pf_saved s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree_nw asegs m1 m8 _ _ FRs1). eapply agree_sub; [exact AGS|]. intros x Hx. unfold pf_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
    assert (FRl8 : rw_cells asegs m8 (usp + -96) ([CB 8 j0] ++ sb_cells A A (A + 16 * cap) V)).
    { apply Sj_stage1_kit.rw_cells_app. split.
      - apply (rw_cells_agree_nw asegs m5 m8 _ _ FR05). intros a Ha. cbv beta in Ha. cbn [cells_size csize Nat.add] in Ha.
        rewrite (PRES8 a); [| left; lia]. apply PRES6; [left; lia|]. cbn [outside]. split; [lia|]. split; [ul|]. split; [ul| exact I].
      - cbn [cells_size csize Nat.add]. replace (usp + -96 + Z.of_nat 8) with (usp + -88) by lia.
        apply (rw_cells_agree_nw asegs m6 m8 _ _ SB6). apply (agree_of_pres _ _ _ _ _ _ PRES8). intros x Hx. unfold sb_cells in Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
    assert (VC8 : rw_cells asegs m8 V (vcells NEW (NEW + 16 * (cap + 1)) (NEW + 16 * cap'))).
    { apply (rw_cells_agree_nw asegs m6 m8 _ _ VC6). apply (agree_of_pres _ _ _ _ _ _ PRES8). intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx.
      right; right; right; left. exists f, kf. split; [exact INF2| lia]. }
    pose proof (pcw_tail usp V NEW (NEW + 16 * (cap + 1)) (NEW + 16 * cap') lo ([CB 8 j0] ++ sb_cells A A (A + 16 * cap) V) (Z_to_bv 64 0xb54f4) gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 r8 z1 z2 z3 z4 z5 z6 z7
                  (Z_to_bv 64 X) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 s4 s3 s2 s1 s0 ra F8 fc8 m8
                  ST8 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) eq_refl
                  (v_shz_of_fp RT AF Σ3 m8 lo _ V ART8 LOW3 FPV3 FOBJ8) FRl8 FRs8 VC8 MI8) as W5.
    lazymatch type of W5 with evt asegs _ ?X0 =>
      assert (W5' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W5) end.
    clear W5.
    apply (cps_realizes asegs _ _ _ c8 (asta_evt_c RT AF Σ3 PMc _ _ MST W5') Hc8). clear W5'. intros c9 Hc9.
    destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & ST9 & VC9) & Hc9'). clear Hc9.
    pose proof (art_fp_client RT AF Σ3 m8 m9 lo _ ART8 LOW3 FPV3 MU9 WM9) as ART9.

    apply Hk. split; [| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c9 Hc9'); intros ms0 <-; exact FRM8].
    exists Σ3, NEW.
    assert (VCA : vcap_after cap cap = cap') by (unfold vcap_after; replace (cap <? cap) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    rewrite VCA.
    split; [| split; [| split; [rewrite FRS3, FRS2; exact FRS1| split; [rewrite SP3, SP2; exact SP1|]]]].
    + eapply ASTA_conseq; [exact Hc9'|]. intros ms <-. exists (Z_to_bv 64 (NEW + 16 * (cap + 1) - 16)), m9.
      split; [rewrite ESP; unfold ret_st; do 16 eexists; reflexivity|].
      split; [split; [exact ART9| split; [exact MI9| fold usp; exact ST9]]|].
      split.
      *
        intros a Ha Hout. fold usp in Ha. cbn [outside] in Hout. destruct Hout as [HO _].
        assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)).
        { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite VL; apply in_or_app; right; exact He| auto| lia]. }
        pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha0) as SPL.
        assert (Ha1 : aclient L0 (rt_frames RT Σ1) usp (bv_unsigned a)) by (rewrite FRS1; exact Ha).
        pose proof (NAP usp (bv_unsigned a) ltac:(rewrite SP1; ul) Ha1) as NIN.
        rewrite (MU9 a); [| cbn [outside]; split; [exact HO| exact I]].
        rewrite (PRES8 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB3| intros e He; rewrite FRS2, FRS1; exact He| lia]].
        rewrite (PRES6 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha1); [intros e He; rewrite LVS; right; apply in_or_app; right; exact He| auto| lia]
                            | cbn [outside]; split; [ul|]; split; [exact HO|]; split; [lia| exact I]].
        rewrite (MU5 a); [| cbn [outside]; split; [ul| exact I]].
        rewrite (PRES4 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha1); [intros e He; rewrite LVS; right; apply in_or_app; right; exact He| auto| lia]| lia].
        rewrite (MU3 a); [| cbn [outside]; split; [ul| exact I]].
        rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha0); auto; lia].
        apply MU1. cbn [outside]. split; [ul| exact I].
      *
        unfold vrepA. split; [unfold zlength; rewrite length_app; cbn [length]; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [ul|].
        split; [exact VC9|]. right. split; [lia|]. split; [exact N16|]. split; [exact N0|].
        pose proof (af_acc_live RT AF Σ3 m9 NEW (16 * (cap + 1)) ART9 INN3) as [WRN9 _].
        rewrite velts_app. cbn [velts fst snd]. apply Sj_stage1_kit.rw_cells_app. rewrite velts_size.
        replace (NEW + Z.of_nat (16 * length els)) with (NEW + 16 * cap) by lia. split.
        --
           apply rw_cells_of_bytes; [apply velts_wf| | rewrite velts_size; apply (wr_at_sub m9 NEW (16 * (cap + 1)) NEW); [exact WRN9| lia| lia| lia]].
           apply (bytes_at_agree asegs m8 m9 _ _); [apply (bytes_at_agree asegs m6 m8 _ _ BY6)|].
           ++ apply (agree_of_pres _ _ _ _ _ _ PRES8). intros x Hx. rewrite cells_bytes_length in Hx by apply velts_wf. rewrite velts_size in Hx.
              right; right; left. exists NEW, (16 * (cap + 1)). split; [exact INN3| lia].
           ++ apply (agree_of_munch _ _ _ _ MU9). intros x Hx. rewrite cells_bytes_length in Hx by apply velts_wf. rewrite velts_size in Hx.
              cbn [outside]. split; [destruct (FLV1 _ _ INN1); lia| exact I].
        --
           apply xcells_of_bytes; [| apply (wr_at_sub m9 NEW (16 * (cap + 1)) (NEW + 16 * cap) 16); [exact WRN9| lia| lia| lia]].
           apply (bytes_at_agree asegs m8 m9 _ _); [apply (bytes_at_agree asegs m6 m8 _ _); [apply (bytes_at_agree asegs m5 m6 _ _); [apply (bytes_at_agree asegs m4 m5 _ _ BY4)|]|]|];
             rewrite xbytes_length; change (Z.of_nat 16) with 16.
           ++ apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [ul| exact I].
           ++ intros a Ha. cbv beta in Ha. apply PRES6; [right; right; left; exists NEW, (16 * cap'); split; [exact INN1| lia]|].
              cbn [outside]. split; [ul|]. split; [destruct (FLV1 _ _ INN1); lia|]. split; [lia| exact I].
           ++ apply (agree_of_pres _ _ _ _ _ _ PRES8). intros x Hx. right; right; left. exists NEW, (16 * (cap + 1)). split; [exact INN3| lia].
           ++ apply (agree_of_munch _ _ _ _ MU9). intros x Hx. cbn [outside]. split; [destruct (FLV1 _ _ INN1); lia| exact I].
    +
      unfold vliveA, vblockA. replace (cap' =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exact LV3.
    +
      rewrite CR3, CR2, CR1. unfold vcost_push. replace (cap <? cap) with false by (symmetry; apply Z.ltb_ge; lia). subst cap'. lia.
Qed.
End PushC.
