(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition VB_ANNINC : Z := 0xb4de4.
Definition VB_ANNSHRINK : Z := 0xb4e8c.
Definition VB_SBDTOR : Z := 0xb50a0.
Definition VB_ALLOCATE : Z := 0xb518c.
Definition VB_ANNDEL : Z := 0xb51c8.
Definition VB_ANNNEW : Z := 0xb5268.
Definition VB_OPNEW : Z := 0x163020.

Definition vcells (b e c : Z) : list cell := [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)].

Definition v_shz (W : list ivl) (m0 : mem) (V : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono asegs m0 m' -> shz m' V 24.

Lemma anninc_walk1 : forall (usp V b e c k lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 <= e < 2^63 -> 0 <= c < 2^63 -> 0 <= k < 2^40 -> e + 16 * k < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a5' : word),
      ms = entry_st (Z_to_bv 64 0xb4e58) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 c)
             (Z_to_bv 64 e) (Z_to_bv 64 (e + 16 * k)) (Z_to_bv 64 b) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annotate m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
      /\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells asegs m1 V (vcells b e c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNINC m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 K0 EK (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNINC, e_annotate, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  replace (Z.shiftl k 4) with (16 * k) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| exact VC].
Qed.

Lemma anninc_walk2 : forall (usp lo : Z) (gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  stk asegs m lo (usp + -16) -> lo <= usp - 16 -> usp < 2^63 ->
  rw_cells asegs m (usp + -16) [C8 s0c; C8 rac] -> mem_inv asegs m ->
  evt asegs (fun ms => ret_st rac (Z_to_bv 64 usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 m ms /\ ms_fcsr ms = fc /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb4e58) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4e58) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO SPH FR MI. pose proof ST as (STa & STb & _).
  zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]].
Qed.

Lemma anndel_walk1 : forall (usp V b e c lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 <= e < 2^63 -> 0 <= c < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a4' : word),
      ms = entry_st (Z_to_bv 64 0xb5234) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 c)
             (Z_to_bv 64 e) (Z_to_bv 64 c) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annotate m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
      /\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells asegs m1 V (vcells b e c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNDEL m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNDEL, e_annotate, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| exact VC].
Qed.

Lemma anndel0_walk : forall (usp V e c lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 <= e < 2^63 -> 0 <= c < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells asegs m V (vcells 0 e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a0' a1' a3' : word),
      ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 V (vcells 0 e c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNDEL m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO E0 C0 (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNDEL, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. do 4 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact VC].
Qed.

Lemma annnew_walk1 : forall (usp V b e c sz lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 <= e < 2^63 -> 0 <= c < 2^63 -> 0 <= sz < 2^40 -> b + 16 * sz < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells asegs m V (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a4' : word),
      ms = entry_st (Z_to_bv 64 0xb52c4) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 c)
             (Z_to_bv 64 c) (Z_to_bv 64 (b + 16 * sz)) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annotate m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -16)
      /\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells asegs m1 V (vcells b e c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNNEW m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 SZ0 BSZ (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNNEW, e_annotate, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep. clear G1 G2. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  replace (Z.shiftl sz 4) with (16 * sz) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| exact VC].
Qed.

Lemma annx_walk2 : forall (pc usp lo : Z) (gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  pc = 0xb4e58 \/ pc = 0xb5234 \/ pc = 0xb52c4 ->
  stk asegs m lo (usp + -16) -> lo <= usp - 16 -> usp < 2^63 ->
  rw_cells asegs m (usp + -16) [C8 s0c; C8 rac] -> mem_inv asegs m ->
  evt asegs (fun ms => ret_st rac (Z_to_bv 64 usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 m ms /\ ms_fcsr ms = fc /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros PC ST LO SPH FR MI. pose proof ST as (STa & STb & _).
  destruct PC as [-> | [-> | ->]];
    (zstep; zstep; zstep; release_frame FR ST usp; zstep;
     apply evt_done; split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]]).
Qed.

Definition alloc_frame (n : Z) (s0 ra : word) : list cell := [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0xb51ac); C8 s0; C8 ra].

Lemma alloc_walkA : forall (usp n lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 32 -> usp < 2^63 -> 1 <= n < 2^58 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x16303c) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (16 * n)) s1 (Z_to_bv 64 (16 * n)) (Z_to_bv 64 n)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m1
      /\ munch [(usp - 32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
      /\ rw_cells asegs m1 (usp + -32) (alloc_frame n s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ALLOCATE m).
Proof.
  intros until m. intros ST LO SPH N MI.
  unfold entry_st, VB_ALLOCATE, e_malloc, alloc_frame.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. rewrite (Z.shiftr_div_pow2 n 60), (Z.div_small n (2 ^ 60)) by lia. zstep. if_false. zstep. zstep.
  replace (Z.shiftl n 4) with (16 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  lstep.

  zstep.
  rename FR into FR1. carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. zstep. zstep. zstep.
  replace (Z.b2z (16 * n <? 1)) with 0 by (destruct (Z.ltb_spec (16 * n) 1); [lia| reflexivity]). rewrite Z.add_0_r.
  zstep. zstep.
  try replace (usp + -16 + -16) with (usp + -32) in FR by lia. try replace (usp + -16 + -16) with (usp + -32) in ST by lia.
  lazymatch type of FR with rw_cells _ ?mm _ _ =>
    assert (FRA : rw_cells asegs mm (usp + -32) (alloc_frame n s0 ra));
    [ unfold alloc_frame; change [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0xb51ac); C8 s0; C8 ra] with ([C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0xb51ac)] ++ [C8 s0; C8 ra]);
      apply rw_cells_app; split; [exact FR|]; cbn [cells_size csize Nat.add]; replace (usp + -32 + Z.of_nat 16) with (usp + -16) by lia; exact FR1 |] end.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FRA].
Qed.

Definition ret_st2 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v v1 : word) (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v v1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc' None m' (seg_rom asegs).

Lemma alloc_walkB : forall (usp p n lo : Z) (gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  stk asegs m lo (usp + -32) -> lo <= usp - 32 -> usp < 2^63 -> 0 < p < 2^64 -> 0 <= n < 2^64 ->
  rw_cells asegs m (usp + -32) (alloc_frame n s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => ret_st2 rac (Z_to_bv 64 usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) (Z_to_bv 64 n) m ms /\ ms_fcsr ms = fc
                       /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0x16303c) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16303c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO SPH P N FR MI.
  unfold alloc_frame in FR. pose proof ST as (STa & STb & _).
  change [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0xb51ac); C8 s0c; C8 rac] with ([C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 0xb51ac)] ++ [C8 s0c; C8 rac]) in FR.
  apply rw_cells_app in FR. destruct FR as [FR2 FR1]. cbn [cells_size csize Nat.add] in FR1.
  replace (usp + -32 + Z.of_nat 16) with (usp + -16) in FR1 by lia.
  zstep. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
  zstep. zstep. zstep. release_frame FR2 ST (usp + -16). zstep.
  zstep. zstep. zstep. zstep. release_frame FR1 ST usp. zstep.
  apply evt_done. split; [unfold ret_st2; do 15 eexists; reflexivity| split; [reflexivity| exact ST]].
Qed.

Definition sb_cells (fi bb ce al : Z) : list cell :=
  [C8 (Z_to_bv 64 fi); C8 (Z_to_bv 64 bb); C8 (Z_to_bv 64 bb); C8 (Z_to_bv 64 ce); C8 (Z_to_bv 64 al)].

Definition x_shz (W : list ivl) (m0 : mem) (X n : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono asegs m0 m' -> shz m' X n.

Lemma sbdtor_walk : forall (usp X fi bb ce al lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp <= X -> X + 40 < 2^63 ->
  0 < fi < 2^63 -> 0 <= bb < 2^63 -> fi <= ce < 2^63 -> 0 <= al < 2^64 ->
  shb_consts m -> x_shz [(usp - 16, usp)] m X 32 ->
  rw_cells asegs m X (sb_cells fi bb ce al) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' a3' a4' a5' : word),
      ms = entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fi) (Z_to_bv 64 (ce - fi)) a2' a3' a4' a5' a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_del m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 X (sb_cells fi bb ce al))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_SBDTOR m).
Proof.
  intros until m. intros ST LO GLO UX XH FI BB CE AL (G1 & G2) SHZ SB MI.
  unfold entry_st, VB_SBDTOR, e_del, sb_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1;
    pose proof (SHZ mm MU' WM' (X + 16) ltac:(lia)) as RD2; pose proof (SHZ mm MU' WM' (X + 24) ltac:(lia)) as RD3 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_true.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; replace (ce + - fi) with (ce - fi) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact SB].
Qed.

Lemma sbdtor0_walk : forall (usp X bb ce al lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 16 -> 0x6ca000 <= lo -> usp <= X -> X + 40 < 2^63 ->
  0 <= bb < 2^63 -> 0 <= ce < 2^63 -> 0 <= al < 2^64 ->
  shb_consts m -> x_shz [(usp - 16, usp)] m X 32 ->
  rw_cells asegs m X (sb_cells 0 bb ce al) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a0' a1' a2' a3' a4' a5' : word),
      ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch [(usp - 16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 X (sb_cells 0 bb ce al))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_SBDTOR m).
Proof.
  intros until m. intros ST LO GLO UX XH BB CE AL (G1 & G2) SHZ SB MI.
  unfold entry_st, VB_SBDTOR, sb_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1;
    pose proof (SHZ mm MU' WM' (X + 16) ltac:(lia)) as RD2 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_true.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact SB].
Qed.

Section VKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma shz_stackv : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN + 8 <= a -> 0 <= n -> a + n <= USTACK_TOP -> shz m a n.
Proof using AF.
  intros Σ m a n HA LO N0 HI.
  pose proof (af_sp0_range RT AF Σ m HA) as SPR. pose proof (af_sp0_win RT AF Σ m HA) as SPW.
  set (a' := 8 * (a / 8)). set (e := 8 * ((a + n + 7) / 8)).
  assert (A' : a' <= a < a' + 8) by (subst a'; pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.mod_pos_bound a 8 ltac:(lia)); lia).
  assert (A8 : a' mod 8 = 0) by (subst a'; rewrite Z.mul_comm; apply Z.mod_mul; lia).
  assert (E' : a + n <= e /\ e <= USTACK_TOP) by (subst e; unfold USTACK_TOP in *; Z.div_mod_to_equations; lia).
  assert (L8 : (e - a') mod 8 = 0).
  { subst e a'. replace (8 * ((a + n + 7) / 8) - 8 * (a / 8)) with (((a + n + 7) / 8 - a / 8) * 8) by lia. apply Z.mod_mul. lia. }
  pose proof (af_acc_stack RT AF Σ m a' (e - a') HA ltac:(lia) ltac:(lia)) as AC.
  pose proof (shz_of_acc m a' _ AC A8 ltac:(ul)) as S.
  eapply shz_sub; [exact S| lia|]. pose proof (Z.div_mod (e - a') 8 ltac:(lia)). lia.
Qed.

Lemma in_live_ann_block : forall p n v a, 0 <= n -> in_live (ann_block p n v) a -> p <= a < p + v.
Proof.
  intros p n v a Hn (q & k & Hin & Hq).
  destruct (ann_block_sizes p n v (q, k) Hn Hin) as [E|E]; [injection E as -> ->; exact Hq| cbn in E].
  pose proof (ann_block_fst p n v (q, k) Hin) as F. cbn in F. subst q. lia.
Qed.

Lemma in_live_app : forall l1 l2 a, in_live (l1 ++ l2) a <-> in_live l1 a \/ in_live l2 a.
Proof.
  intros l1 l2 a. split.
  - intros (p & n & Hin & Hp). apply in_app_or in Hin. destruct Hin as [H|H]; [left|right]; exists p, n; auto.
  - intros [(p & n & Hin & Hp)|(p & n & Hin & Hp)]; exists p, n; split; auto; apply in_or_app; auto.
Qed.

Lemma in_live_cons : forall p n l a, in_live ((p, n) :: l) a <-> (p <= a < p + n) \/ in_live l a.
Proof.
  intros p n l a. split.
  - intros (q & k & [E|Hin] & Hq); [injection E as -> ->; left; exact Hq| right; exists q, k; auto].
  - intros [H|(q & k & Hin & Hq)]; [exists p, n; split; [left; reflexivity| exact H]| exists q, k; split; [right; exact Hin| exact Hq]].
Qed.

Lemma fobj_pres_ex_live : forall Σ Σ' live sp d n0 q k m m' a n, ART RT Σ m -> fobj RT Σ m a n ->
  rt_pres_ex live (rt_frames RT Σ) sp d n0 m m' -> (forall e, In e (rt_live RT Σ) -> In e live) -> rt_frames RT Σ' = rt_frames RT Σ ->
  In (q, k) (rt_live RT Σ) -> q <= d -> d + n0 <= q + k -> fobj RT Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp d n0 q k m m' a n HA FO PRES SUB FRS INQ QD DK.
  apply (fobj_agree RT AF Σ Σ' m m' a n HA FO FRS).
  destruct (fobj_shadow_range RT AF Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  pose proof (af_fshadow_apart RT AF Σ m f c HA Hin) as [AL _]. specialize (AL q k INQ).
  intros x Hx. cbv beta in Hx. apply PRES; [| lia].
  right; right; right; right. exists f, c. split; [exact Hin| lia].
Qed.

Lemma x_shz_of_fp : forall Σ m lo W X n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_client RT Σ lo W ->
  rt_sp0 RT Σ - STACK_WIN + 8 <= X -> 0 <= n -> X + n <= USTACK_TOP -> x_shz W m X n.
Proof using AF.
  intros Σ m lo W X n HA LO FP X0 N0 XT m' MU WM. apply (shz_stackv Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ HA LO FP MU WM)| lia| lia| lia].
Qed.

Lemma v_shz_of_fp : forall Σ m lo W V, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_client RT Σ lo W -> fobj RT Σ m V 24 -> v_shz W m V.
Proof using AF.
  intros Σ m lo W V HA LO FP FO m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ HA LO FP MU WM)|].
  exact (fobj_munch RT AF Σ m m' lo _ V 24 HA LO FP MU FO).
Qed.

Lemma fobj_pres_fpc : forall Σ Σ' live sp lo W m m' a n, ART RT Σ m -> fobj RT Σ m a n ->
  rt_pres_fp live (rt_frames RT Σ) sp W m m' -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_client RT Σ lo W ->
  fobj RT Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp lo W m m' a n HA FO PRES FRS LO FP.
  apply (fobj_agree RT AF Σ Σ' m m' a n HA FO FRS).
  destruct (fobj_shadow_range RT AF Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  pose proof (fframe_ranges RT AF Σ m f c HA Hin) as (F0 & F1 & FSZ & SH0 & SH1).
  pose proof (af_fshadow_apart RT AF Σ m f c HA Hin) as (XL & XF).
  intros x Hx. cbv beta in Hx. apply PRES.
  - right; right; right; right. exists f, c. split; [exact Hin| lia].
  - clear PRES. induction W as [|[wl wh] W IH]; [exact I|]. inversion FP as [|? ? H1 H2]; subst. cbn [outside]. split; [| exact (IH H2)].
    cbn [fst snd] in H1. destruct H1 as [H1|[(p & k & Hp & P1 & P2)|(f' & c' & Hf & P1 & P2)]].
    + lia.
    + destruct (XL p k Hp); lia.
    + destruct (XF f' c' Hf); lia.
Qed.

Lemma chunk_apart : forall Σ m l1 q k l2 (L : list (Z * Z)) sp a, ART RT Σ m -> rt_live RT Σ = l1 ++ (q, k) :: l2 ->
  (forall e, In e L -> In e (l1 ++ l2)) -> rt_sp0 RT Σ - STACK_WIN <= sp -> aclient L (rt_frames RT Σ) sp a -> ~ (q <= a < q + k).
Proof using AF.
  intros Σ m l1 q k l2 L sp a HA LV SUB LO Ha.
  assert (INQ : In (q, k) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ m q k HA INQ) as (Q0 & Q1 & Q2).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p & n & Hin & Hp). pose proof (af_live_disj RT AF Σ m q k p n l1 l2 HA LV (SUB _ Hin)). lia.
  - destruct H as (f & c & Hin & Hf). pose proof (af_frames_range RT AF Σ m f c HA Hin) as (_ & _ & _ & X). destruct (X q k INQ); lia.
  - destruct H as (f & c & Hin & Hf). pose proof (af_fshadow_apart RT AF Σ m f c HA Hin) as [X _]. destruct (X q k INQ); lia.
Qed.

Definition ann_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo b n v' : Z) (l1 L0 : list (Z * Z)) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m') c
    /\ rt_live RT Σ' = l1 ++ ann_block b n v' ++ L0 /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ.

Lemma anninc_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n v k : Z) (L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m V (vcells b (b + v) (b + n)) -> fobj RT Σ m V 24 ->
  rt_live RT Σ = ann_block b n v ++ L0 ->
  0 <= v -> 0 <= k -> v + 16 * k <= n -> v mod 16 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNINC m)))
    (ann_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo b n (v + 16 * k) [] L0 m).
Proof using AF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V b n v k L0 lo
    FDO MST -> -> -> VC FOBJ0 LV V0 K0 VK V16 N16 NB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INB : In (b, v) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m b v ART0 INB) as (B0 & B1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : v_shz [(usp - 16, usp)] m V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ V 24 ART0 LOW FPC MU FOBJ0). }

  pose proof (anninc_walk1 usp V b (b + v) (b + n) k lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a5' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  apply (ANN Σ PMc (Z_to_bv 64 0xb4e58) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + v)) (Z_to_bv 64 (b + v + 16 * k)) (Z_to_bv 64 b) a5' a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 b n v (v + 16 * k) [] L0 lo FDO MST);
    try reflexivity; try assumption.
  - constructor.
  - f_equal. lia.
  - lia.
  - lia.
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c2 (Σ1 & r & Hc2 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb4e58) in Hc2' by lia.
    assert (FR2 : rw_cells asegs m2 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (anninc_walk2 usp lo gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F2 fc m2 ST2 ltac:(ul) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (RS3 & _ & ST3). exists r, m2.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact ART2| split; [exact MI2| split; [exact (wmono_trans _ _ _ _ WM1 WM2)| exact ST3]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES2 a), (MU1 a); [reflexivity| |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma anndel_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n v : Z) (l1 L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m V (vcells b (b + v) (b + n)) -> fobj RT Σ m V 24 ->
  rt_live RT Σ = l1 ++ ann_block b n v ++ L0 -> Forall (fun e => fst e <> b) l1 ->
  0 <= v <= n -> v mod 16 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNDEL m)))
    (ann_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo b n n l1 L0 m).
Proof using AF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V b n v l1 L0 lo
    FDO MST -> -> VC FOBJ0 LV L1 VN V16 N16 NB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INB : In (b, v) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; right; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m b v ART0 INB) as (B0 & B1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : v_shz [(usp - 16, usp)] m V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ V 24 ART0 LOW FPC MU FOBJ0). }

  pose proof (anndel_walk1 usp V b (b + v) (b + n) lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a4' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  apply (ANN Σ PMc (Z_to_bv 64 0xb5234) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + v)) (Z_to_bv 64 (b + n)) a4' a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 b n v n l1 L0 lo FDO MST);
    try reflexivity; try assumption.
  - lia.
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c2 (Σ1 & r & Hc2 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb5234) in Hc2' by lia.
    assert (FR2 : rw_cells asegs m2 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annx_walk2 0xb5234 usp lo gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F2 fc m2 ltac:(right; left; reflexivity) ST2 ltac:(ul) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (RS3 & _ & ST3). exists r, m2.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact ART2| split; [exact MI2| split; [exact (wmono_trans _ _ _ _ WM1 WM2)| exact ST3]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES2 a), (MU1 a); [reflexivity| |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma anndel0_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V e cc : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m V (vcells 0 e cc) -> fobj RT Σ m V 24 -> 0 <= e < 2^63 -> 0 <= cc < 2^63 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNDEL m)))
    (ASTA RT Σ PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ rw_cells asegs m' V (vcells 0 e cc))).
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V e cc lo
    FDO MST -> -> VC FOBJ0 E0 C0 ART0 MI0 ST0 LOW LOR SPT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : v_shz [(usp - 16, usp)] m V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ V 24 ART0 LOW FPC MU FOBJ0). }
  pose proof (anndel0_walk usp V e cc lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms (m1 & a0' & a1' & a3' & E & _); rewrite E; exact FRM].
  eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & a0' & a1' & a3' & -> & MU1 & WM1 & MI1 & ST1 & VC1).
  exists a0', m1. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1)| split; [exact MI1| split; [exact WM1| exact ST1]]]|].
  split; [| exact VC1].
  intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  apply MU1. cbn [outside]. split; [ul| exact I].
Qed.

Lemma annnew_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n e sz : Z) (l1 L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 sz -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m V (vcells b e (b + n)) -> fobj RT Σ m V 24 -> 0 <= e < 2^63 ->
  rt_live RT Σ = l1 ++ ann_block b n n ++ L0 -> Forall (fun x => fst x <> b) l1 ->
  0 <= sz -> 16 * sz <= n -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNNEW m)))
    (ann_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo b n (16 * sz) l1 L0 m).
Proof using AF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V b n e sz l1 L0 lo
    FDO MST -> -> -> VC FOBJ0 E0 LV L1 SZ0 SZN N16 NB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INB : In (b, n) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; right; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m b n ART0 INB) as (B0 & B1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : v_shz [(usp - 16, usp)] m V).
  { intros m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)|].
    exact (fobj_munch RT AF Σ m m' lo _ V 24 ART0 LOW FPC MU FOBJ0). }

  pose proof (annnew_walk1 usp V b e (b + n) sz lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a4' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  apply (ANN Σ PMc (Z_to_bv 64 0xb52c4) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + 16 * sz)) a4' a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 b n n (16 * sz) l1 L0 lo FDO MST);
    try reflexivity; try assumption.
  - lia.
  - lia.
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c2 (Σ1 & r & Hc2 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
    rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0xb52c4) in Hc2' by lia.
    assert (FR2 : rw_cells asegs m2 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annx_walk2 0xb52c4 usp lo gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F2 fc m2 ltac:(right; right; reflexivity) ST2 ltac:(ul) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (RS3 & _ & ST3). exists r, m2.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact ART2| split; [exact MI2| split; [exact (wmono_trans _ _ _ _ WM1 WM2)| exact ST3]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES2 a), (MU1 a); [reflexivity| |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Definition alloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (p : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) (Z_to_bv 64 n) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p (16 * n) /\ acc asegs m' p (16 * n)) c
    /\ rt_live RT Σ' = (p, 16 * n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (16 * n) /\ 0 < p /\ p mod 16 = 0 /\ p + 16 * n < USTACK_TOP.

Lemma alloc_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n -> 16 * n <= 0x20001000 -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x6a7e68 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (16 * n) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ALLOCATE m)))
            (alloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).
Proof using AF RTF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
    FDO MST N1 N2 -> -> LVM CR ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (alloc_walkA usp n lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) ltac:(lia) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 32) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).
  apply ((rf_malloc RT RTF) Σ PMc (Z_to_bv 64 0x16303c) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 (16 * n)) s1 (Z_to_bv 64 (16 * n))
           (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (16 * n) lo FDO MST ltac:(lia)); try reflexivity; try assumption;
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -32) with (usp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - unfold unwind_ok. rewrite EU2, unsigned_lit by ul. left. ul.
  - intros c2 ((Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0x16303c) in Hc2' by lia.
    assert (FR2 : rw_cells asegs m2 (usp + -32) (alloc_frame n s0 ra)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold alloc_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (alloc_walkB usp p n lo gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 (16 * n)) s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (_ & E & _); rewrite E; exact FRM2].
    exists Σ1, p. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (RS3 & _ & ST3). exists m2.
    split; [rewrite ESP; exact RS3|].
    split; [split; [exact ART2| split; [exact MI2| split; [exact (wmono_trans _ _ _ _ WM1 WM2)| exact ST3]]]|].
    split; [| split; [exact WR2| exact ACC2]].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES2 a), (MU1 a); [reflexivity| |].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma sbdtor_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X fi bb ce al nf lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 X -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m X (sb_cells fi bb ce al) -> bv_unsigned sp <= X -> X + 40 <= USTACK_TOP -> X mod 8 = 0 ->
  0 <= bb < 2^63 -> fi <= ce < 2^63 -> 0 <= al < 2^64 ->
  In (fi, nf) (rt_live RT Σ) ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_SBDTOR m)))
            (free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fi lo m).
Proof using AF RTF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X fi bb ce al nf lo
    FDO MST -> -> SB UX XT X8 BB CE AL INF0 ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_live_range RT AF Σ m fi nf ART0 INF0) as (FI0 & FI1 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : x_shz [(usp - 16, usp)] m X 32).
  { intros m' MU WM. apply (shz_stackv Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)| ul| lia| ul]. }
  pose proof (sbdtor_walk usp X fi bb ce al lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(ul) BB CE AL (conj G1 G2) SHZ0 SB MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & a3' & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & SB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  apply (del_ok RT AF (rf_free RT RTF) Σ PMc ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 fi) (Z_to_bv 64 (ce - fi)) a2' a3' a4' a5' a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 fi nf lo FDO MST INF0 eq_refl eq_refl ART1 MI1);
    [| exact UOK| exact FRM| split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. fold usp. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA].
  - intros c2 ((Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    apply Hk. split; [| exact FC2]. exists Σ1, v. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc2|]. intros ms (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2). exists m2.
    split; [exact RS2|]. split; [split; [exact ART2| split; [exact MI2| exact ST2]]|].
    intros a Ha. fold usp in Ha.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (rewrite FRS1; exact Ha).
    pose proof (aclient_split_c RT AF Σ1 m2 usp (bv_unsigned a) ART2 Ha1) as SPL. rewrite SP1 in SPL.
    rewrite (PRES2 a Ha). apply MU1. cbn [outside]. split; [ul| exact I].
Qed.

Lemma sbdtor0_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X bb ce al lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 X -> tp = Z_to_bv 64 0x6a7e68 ->
  rw_cells asegs m X (sb_cells 0 bb ce al) -> bv_unsigned sp <= X -> X + 40 <= USTACK_TOP -> X mod 8 = 0 ->
  0 <= bb < 2^63 -> 0 <= ce < 2^63 -> 0 <= al < 2^64 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_SBDTOR m)))
    (ASTA RT Σ PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X bb ce al lo
    FDO MST -> -> SB UX XT X8 BB CE AL ART0 MI0 ST0 LOW LOR SPT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : x_shz [(usp - 16, usp)] m X 32).
  { intros m' MU WM. apply (shz_stackv Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)| ul| lia| ul]. }
  pose proof (sbdtor0_walk usp X bb ce al lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) BB CE AL (conj G1 G2) SHZ0 SB MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms (m1 & a0' & a1' & a2' & a3' & a4' & a5' & E & _); rewrite E; exact FRM].
  eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & a0' & a1' & a2' & a3' & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & SB1).
  exists a0', m1. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1)| split; [exact MI1| split; [exact WM1| exact ST1]]]|].
  intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  apply MU1. cbn [outside]. split; [ul| exact I].
Qed.

End VKit.
