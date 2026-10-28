(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_mm_syscalls RF_ntf_A RF_am_A RF_am_K RF_am_C.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma ram_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (p : aptr) (r : region),
rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c54) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15ab4) fc None m (seg_rom usegs)).
Proof.
intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite AMA in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). atop_facts.
pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
assert (AL : Z.land (conc st p) 4095 = 0).
{ rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). Local Ltac2 Set LiaHints.tbl := fun () => "0060>16075393784.5117210665673.5317260316077.2743735480156.5143737297015.5553519027360.5100000400500J00N00f00gS2CRSS3SAL4RBAL1H2H02H42H9S2PBS2S02S13RB03RBC5ATOPR2CpS".
rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
assert (PB : 0 <= conc st p < 2^64) by lia.
clear RBAL RU RBC RL0 WR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
st1. st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
rewrite CF.
st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
st1. st1.
st1. st1. rewrite ?AL, ?AL'. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
apply evt_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (P : Z),
evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15c64) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
(Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c54) fc None m (seg_rom usegs)).
Proof.
intros.
st1. st1. st1. st1.
apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.
#[using="Type"] Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte),
evt usegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15bc4) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c64) fc None m (seg_rom usegs)).
Proof.
intros.
st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.
#[using="Type"] Lemma ram_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
rmrep st m -> mem_inv usegs m -> tp = Z_to_bv 64 0x2ef30 ->
rw_cells usegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono usegs m0 m ->
rw_cells usegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk usegs m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
evt usegs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
/\ rw_cells usegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c64) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
subst tp. Local Ltac2 Set LiaHints.tbl := fun () => "00@0>12367362435.6721918414723.6736423605256.6036993589379.673945979267.68 41631605457.6041809558659.6642838452580.5843060403331.6849345641752.5951481786499.675264119696.58 64891813684.588420494966.64 8832910886.61 8841017104.58 00000100200800900:00C00D00H00I00J00K00L00P00Q00Z00[SSS4LOLESSS2LO4LOLESS2ERSSSSS2ERSS4LOLE2HxS".
rewrite (unsigned_lit 0x2ef30) in * by lia. change (192304 + -164) with 192140 in *.
change (Z_to_bv 64 e) with (wz e) in ERR.
unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *. atop_facts.
st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
st1. st1. st1. st1.
st1. rewrite sx32_wz by lia. st1. st1.
assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
rewrite CF; clear CF.
st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; atop_facts; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. split.
- unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
- cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
