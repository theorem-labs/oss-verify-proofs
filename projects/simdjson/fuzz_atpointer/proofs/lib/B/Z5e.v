(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Z82 Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition VB_ANNOTATE : Z := 0x98620.
Definition VB_ANNINC : Z := 0x98568.
Definition VB_ANNINC_RET : Z := 0x985f0.
Definition VB_ANNDEL : Z := 0x98c4c.
Definition VB_ANNDEL_RET : Z := 0x98cd0.
Definition VB_ANNNEW : Z := 0x98d08.
Definition VB_ANNNEW_RET : Z := 0x98d90.
Definition TPVB : Z := 0x653c30.

Definition vcells (b e c : Z) : list cell := [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)].

Definition v_shz (W : list ivl) (m0 : mem) (V : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' V 24.

Definition x_shz (W : list ivl) (m0 : mem) (X n : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' X n.

Lemma annwrap_walk : forall (usp V b e c om nm lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x676000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 <= e < 2^63 -> 0 < c < 2^63 -> b <= c ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a4' a5' : word),
      ms = entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 c)
             (Z_to_bv 64 om) (Z_to_bv 64 nm) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annotate m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 V (vcells b e c))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 om) (Z_to_bv 64 nm) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNOTATE m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 BC (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNOTATE, e_annotate, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (c <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor].
  zstep. if_false.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact VC].
Qed.

Lemma anninc_walk1 : forall (usp V b e c k lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x676000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 < e < 2^63 -> 0 <= c < 2^63 -> b <= e -> 0 <= k < 2^40 -> e + 16 * k < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a3' a4' a5' : word),
      ms = entry_st (Z_to_bv 64 VB_ANNINC_RET) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 e)
             (Z_to_bv 64 (e + 16 * k)) a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNOTATE m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
      /\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m1 V (vcells b e c) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNINC m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 BE K0 EK (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNINC, VB_ANNINC_RET, VB_ANNOTATE, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (e <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor].
  zstep. if_false.
  zstep. replace (Z.shiftl k 4) with (16 * k) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zstep.
  zstep.
  replace (16 * k + e <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  zstep. if_false.
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; revert K; rewrite ?Z.shiftr_div_pow2 by lia; intros K; lia| clear K].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep.
  replace (16 * k + e) with (e + 16 * k) by lia.
  apply evt_done. do 4 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact VC|].
  split; assumption.
Qed.

Lemma anndel_walk1 : forall (usp V b e c lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x676000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 < e < 2^63 -> 0 < c < 2^63 -> b <= e -> b <= c ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a3' a4' a5' a6' : word),
      ms = entry_st (Z_to_bv 64 VB_ANNDEL_RET) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 e)
             (Z_to_bv 64 c) a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNOTATE m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
      /\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m1 V (vcells b e c) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNDEL m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 BE BC (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNDEL, VB_ANNDEL_RET, VB_ANNOTATE, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (e <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor].
  zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. replace (c <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor]. zstep.
  zstep. if_false.
  zstep.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact VC|].
  split; assumption.
Qed.

Lemma anndel0_walk : forall (usp V lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x676000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  shb_consts m -> v_shz [(usp - 32, usp)] m V ->
  rw_cells bsegs m V (vcells 0 0 0) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' a3' a4' a5' a6' : word),
      ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom bsegs)
      /\ munch [(usp - 32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 V (vcells 0 0 0))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNDEL m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNDEL, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. cbn [Z.ltb Z.b2z Z.lxor Pos.lxor].
  zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. cbn [Z.ltb Z.b2z Z.lxor Pos.lxor]. zstep.
  zstep. if_false.
  zstep.

  zstep.
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST2 end.
  try rewrite (unsigned_lit 64 (usp + -16)) in ST2 by lia.
  carve_frame 16%nat ST2.
  lazymatch goal with H : rw_cells bsegs _ (usp + -32) [CB 16 _] |- _ => rename H into FR2 end.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR2; [| reflexivity].
  cbn [mk_CB_cells app] in FR2.
  repeat match type of FR2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR2; clearbody j end.
  lstep.
  zstep.
  zstep. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0'; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2' end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep. cbn [Z.ltb Z.b2z Z.lxor Pos.lxor].
  zstep. if_false.
  zstep. if_true.
  zstep. zstep. release_frame FR2 ST2 (usp + -16). zstep.
  zstep. zstep. zstep. release_frame FR ST2 usp. zstep.
  apply evt_done. do 8 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST2| exact VC].
Qed.

Lemma annnew_walk1 : forall (usp V b e c sz lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x676000 <= lo -> usp < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> 0 <= e < 2^63 -> 0 < c < 2^63 -> b <= c -> 0 <= sz < 2^40 -> b + 16 * sz < 2^63 ->
  shb_consts m -> v_shz [(usp - 16, usp)] m V ->
  rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a3' a4' a5' a6' : word),
      ms = entry_st (Z_to_bv 64 VB_ANNNEW_RET) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 c)
             (Z_to_bv 64 (b + 16 * sz)) a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNOTATE m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -16)
      /\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m1 V (vcells b e c) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNNEW m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 BC SZ0 BSZ (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNNEW, VB_ANNNEW_RET, VB_ANNOTATE, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (V + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (V + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. zstep.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (c <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor].
  zstep. if_false.
  zstep. replace (Z.shiftl sz 4) with (16 * sz) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zstep.
  zstep.
  replace (16 * sz + b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  zstep. if_false.
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; revert K; rewrite ?Z.shiftr_div_pow2 by lia; intros K; lia| clear K].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep.
  replace (16 * sz + b) with (b + 16 * sz) by lia.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact VC|].
  split; assumption.
Qed.

Lemma annx_walk2 : forall (pc usp lo : Z) (gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  pc = VB_ANNINC_RET \/ pc = VB_ANNDEL_RET \/ pc = VB_ANNNEW_RET ->
  stk bsegs m lo (usp + -16) -> lo <= usp - 16 -> usp < 2^63 ->
  rw_cells bsegs m (usp + -16) [C8 s0c; C8 rac] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ret_st rac (Z_to_bv 64 usp) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 m ms /\ ms_fcsr ms = fc /\ stk bsegs m lo usp)
    (MS (mkR (Z_to_bv 64 pc) (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros PC ST LO SPH FR MI. pose proof ST as (STa & STb & _). unfold VB_ANNINC_RET, VB_ANNDEL_RET, VB_ANNNEW_RET in PC.
  destruct PC as [-> | [-> | ->]];
    (zstep; zstep; zstep; release_frame FR ST usp; zstep;
     apply evt_done; split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]]).
Qed.

Section VKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma v_shz_of_fp : forall Σ m lo W V, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_client RT Σ lo W -> fobj RT Σ m V 24 -> v_shz W m V.
Proof using AF.
  intros Σ m lo W V HA LO FP FO m' MU WM. apply (fobj_shz RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ HA LO FP MU WM)|].
  exact (fobj_munch RT AF Σ m m' lo _ V 24 HA LO FP MU FO).
Qed.

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
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m V (vcells b (b + v) (b + n)) -> fobj RT Σ m V 24 ->
  rt_live RT Σ = ann_block b n v ++ L0 ->
  0 <= v -> 0 <= k -> v + 16 * k <= n -> v mod 16 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
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
  assert (FPC2 : fp_client RT Σ lo [(usp - 32, usp + -16)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp Σ m lo _ V ART0 LOW FPC FOBJ0) as SHZ0.

  pose proof (anninc_walk1 usp V b (b + v) (b + n) k lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a3' & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  pose proof (v_shz_of_fp Σ m1 lo _ V ART1 LOW FPC2 FOBJ1) as SHZ1.
  replace (usp - 32) with (usp + -16 - 16) in SHZ1 by lia.
  pose proof (annwrap_walk (usp + -16) V b (b + v) (b + n) (b + v) (b + v + 16 * k) lo (Z_to_bv 64 VB_ANNINC_RET) gp (Z_to_bv 64 TPVB)
                t0 t1 t2 s0 s1 a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                ST1 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) SHB1 SHZ1 VC1 MI1) as W2.
  unfold entry_st in W2 at 2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc1'). clear W2'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & a4'' & a5'' & -> & MU2 & WM2 & MI2 & ST2 & VC2) & Hc2'). clear Hc2.
  pose proof (art_fp_client RT AF Σ m1 m2 lo _ ART1 LOW FPC2 ltac:(replace (usp - 32) with (usp + -16 - 16) by lia; exact MU2) WM2) as ART2.
  assert (FR2 : rw_cells bsegs m2 (usp + -16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I]. }

  apply (ANN Σ PMc (Z_to_bv 64 VB_ANNINC_RET) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + v)) (Z_to_bv 64 (b + v + 16 * k)) a4'' a5'' a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 b n v (v + 16 * k) [] L0 lo FDO MST);
    try reflexivity; try assumption.
  - constructor.
  - f_equal. lia.
  - lia.
  - lia.
  - Z.div_mod_to_equations. lia.
  - Z.div_mod_to_equations. lia.
  - unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c3 (Σ1 & r & Hc3 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3) & Hc3'). clear Hc3.
    destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & ->).
    rewrite EU2 in ST3, PRES3.
    unfold VB_ANNINC_RET in Hc3'. rewrite (ret_pc_even 0x985f0) in Hc3' by lia.
    assert (FR3 : rw_cells bsegs m3 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. apply (agree_of_pres _ _ _ _ _ _ PRES3).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annx_walk2 VB_ANNINC_RET usp lo gp (Z_to_bv 64 TPVB) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F3 fc m3 (or_introl eq_refl) ST3 ltac:(ul) ltac:(ul) FR3 MI3) as W3.
    unfold VB_ANNINC_RET in W3.
    lazymatch type of W3 with evt bsegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c4 Hc4); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc4|]. intros ms (RS4 & _ & ST4). exists r, m3.
    split; [rewrite ESP; exact RS4|].
    split; [split; [exact ART3| split; [exact MI3| split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)| exact ST4]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES3 a), (MU2 a), (MU1 a); [reflexivity| | |].
    + cbn [outside]. split; [ul| exact I].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma anndel_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n v : Z) (l1 L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m V (vcells b (b + v) (b + n)) -> fobj RT Σ m V 24 ->
  rt_live RT Σ = l1 ++ ann_block b n v ++ L0 -> Forall (fun e => fst e <> b) l1 ->
  0 <= v <= n -> v mod 16 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
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
  assert (FPC2 : fp_client RT Σ lo [(usp - 32, usp + -16)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp Σ m lo _ V ART0 LOW FPC FOBJ0) as SHZ0.

  pose proof (anndel_walk1 usp V b (b + v) (b + n) lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a3' & a4' & a5' & a6' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  pose proof (v_shz_of_fp Σ m1 lo _ V ART1 LOW FPC2 FOBJ1) as SHZ1.
  replace (usp - 32) with (usp + -16 - 16) in SHZ1 by lia.
  pose proof (annwrap_walk (usp + -16) V b (b + v) (b + n) (b + v) (b + n) lo (Z_to_bv 64 VB_ANNDEL_RET) gp (Z_to_bv 64 TPVB)
                t0 t1 t2 s0 s1 a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                ST1 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) SHB1 SHZ1 VC1 MI1) as W2.
  unfold entry_st in W2 at 2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc1'). clear W2'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & a4'' & a5'' & -> & MU2 & WM2 & MI2 & ST2 & VC2) & Hc2'). clear Hc2.
  pose proof (art_fp_client RT AF Σ m1 m2 lo _ ART1 LOW FPC2 ltac:(replace (usp - 32) with (usp + -16 - 16) by lia; exact MU2) WM2) as ART2.
  assert (FR2 : rw_cells bsegs m2 (usp + -16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I]. }

  apply (ANN Σ PMc (Z_to_bv 64 VB_ANNDEL_RET) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + v)) (Z_to_bv 64 (b + n)) a4'' a5'' a6' a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 b n v n l1 L0 lo FDO MST);
    try reflexivity; try assumption.
  all: try (clear Hk Hc2'; lia). all: try (clear Hk Hc2'; Z.div_mod_to_equations; lia).
  - unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c3 (Σ1 & r & Hc3 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3) & Hc3'). clear Hc3.
    destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & ->).
    rewrite EU2 in ST3, PRES3.
    unfold VB_ANNDEL_RET in Hc3'. rewrite (ret_pc_even 0x98cd0) in Hc3' by lia.
    assert (FR3 : rw_cells bsegs m3 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. apply (agree_of_pres _ _ _ _ _ _ PRES3).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annx_walk2 VB_ANNDEL_RET usp lo gp (Z_to_bv 64 TPVB) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F3 fc m3 (or_intror (or_introl eq_refl)) ST3 ltac:(ul) ltac:(ul) FR3 MI3) as W3.
    unfold VB_ANNDEL_RET in W3.
    lazymatch type of W3 with evt bsegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c4 Hc4); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc4|]. intros ms (RS4 & _ & ST4). exists r, m3.
    split; [rewrite ESP; exact RS4|].
    split; [split; [exact ART3| split; [exact MI3| split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)| exact ST4]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES3 a), (MU2 a), (MU1 a); [reflexivity| | |].
    + cbn [outside]. split; [ul| exact I].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma annnew_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n e sz : Z) (l1 L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 sz -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m V (vcells b e (b + n)) -> fobj RT Σ m V 24 -> 0 <= e < 2^63 ->
  rt_live RT Σ = l1 ++ ann_block b n n ++ L0 -> Forall (fun x => fst x <> b) l1 ->
  0 <= sz -> 16 * sz <= n -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
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
  assert (FPC2 : fp_client RT Σ lo [(usp - 32, usp + -16)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp Σ m lo _ V ART0 LOW FPC FOBJ0) as SHZ0.

  pose proof (annnew_walk1 usp V b e (b + n) sz lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a3' & a4' & a5' & a6' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  pose proof (v_shz_of_fp Σ m1 lo _ V ART1 LOW FPC2 FOBJ1) as SHZ1.
  replace (usp - 32) with (usp + -16 - 16) in SHZ1 by lia.
  pose proof (annwrap_walk (usp + -16) V b e (b + n) (b + n) (b + 16 * sz) lo (Z_to_bv 64 VB_ANNNEW_RET) gp (Z_to_bv 64 TPVB)
                t0 t1 t2 s0 s1 a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                ST1 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) SHB1 SHZ1 VC1 MI1) as W2.
  unfold entry_st in W2 at 2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc1'). clear W2'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & a4'' & a5'' & -> & MU2 & WM2 & MI2 & ST2 & VC2) & Hc2'). clear Hc2.
  pose proof (art_fp_client RT AF Σ m1 m2 lo _ ART1 LOW FPC2 ltac:(replace (usp - 32) with (usp + -16 - 16) by lia; exact MU2) WM2) as ART2.
  assert (FR2 : rw_cells bsegs m2 (usp + -16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I]. }

  apply (ANN Σ PMc (Z_to_bv 64 VB_ANNNEW_RET) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + 16 * sz)) a4'' a5'' a6' a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 b n n (16 * sz) l1 L0 lo FDO MST);
    try reflexivity; try assumption.
  all: try (clear Hk Hc2'; lia). all: try (clear Hk Hc2'; Z.div_mod_to_equations; lia).
  - unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c3 (Σ1 & r & Hc3 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3) & Hc3'). clear Hc3.
    destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & ->).
    rewrite EU2 in ST3, PRES3.
    unfold VB_ANNNEW_RET in Hc3'. rewrite (ret_pc_even 0x98d90) in Hc3' by lia.
    assert (FR3 : rw_cells bsegs m3 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. apply (agree_of_pres _ _ _ _ _ _ PRES3).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annx_walk2 VB_ANNNEW_RET usp lo gp (Z_to_bv 64 TPVB) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F3 fc m3 (or_intror (or_intror eq_refl)) ST3 ltac:(ul) ltac:(ul) FR3 MI3) as W3.
    unfold VB_ANNNEW_RET in W3.
    lazymatch type of W3 with evt bsegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c4 Hc4); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc4|]. intros ms (RS4 & _ & ST4). exists r, m3.
    split; [rewrite ESP; exact RS4|].
    split; [split; [exact ART3| split; [exact MI3| split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)| exact ST4]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES3 a), (MU2 a), (MU1 a); [reflexivity| | |].
    + cbn [outside]. split; [ul| exact I].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Lemma anndel0_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V e cc : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m V (vcells 0 e cc) -> fobj RT Σ m V 24 -> e = 0 -> cc = 0 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNDEL m)))
    (ASTA RT Σ PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ rw_cells bsegs m' V (vcells 0 e cc))).
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V e cc lo
    FDO MST -> -> VC FOBJ0 -> -> ART0 MI0 ST0 LOW LOR SPT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (FPC : fp_client RT Σ lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp Σ m lo _ V ART0 LOW FPC FOBJ0) as SHZ0.
  pose proof (anndel0_walk usp V lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms (m1 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & E & _); rewrite E; exact FRM].
  eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & -> & MU1 & WM1 & MI1 & ST1 & VC1).
  exists a0', m1. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1)| split; [exact MI1| split; [exact WM1| exact ST1]]]|].
  split; [| exact VC1].
  intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  apply MU1. cbn [outside]. split; [ul| exact I].
Qed.

End VKit.
