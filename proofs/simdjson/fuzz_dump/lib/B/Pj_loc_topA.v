(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA Pj_defsA Pj_loc_akitA Pj_loc_getA Pj_loc_get0A.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold PJ_LOC_STACK_A, USTACK_TOP, SEGTOP_A, STACK_WIN, RT_STACK in *; lia.

Theorem loc_get_okA : loc_get_cpsA RT PMc.
Proof using AF RTC MCI FDO MST.
  intros Σ K P q lo ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jp
    _ _ LOC NL LK (g & GOT & CAN) DST P8 PCL PBL ART0 MI ST LOR LO SPT SPA HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).

  pose proof (aclient_split_c RT AF Σ m q (P + 0) ART0 (PCL 0 ltac:(lia))) as S0.
  pose proof (aclient_split_c RT AF Σ m q (P + 7) ART0 (PCL 7 ltac:(lia))) as S7.
  pose proof (aclient_bounds RT AF Σ m q (P + 0) ART0 ltac:(ul) (PCL 0 ltac:(lia))) as B0.
  unfold libc_nl, LIBC_NL in NL. unfold lockwA, PJ_LOCKW_A in LK.
  eapply (locale_ctor_aevt RT AF RTC MCI PMc FDO MST Σ K ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A)
            t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P jp g);
    rewrite ?EQ; [exact ST | ul | exact LOR | exact SPT | exact SPA | ul | exact LOC | exact DST | lia | ul | unfold PJ_LOC_LO_A in PBL; lia
    | exact PCL | exact GOT | exact CAN | exact NL | exact LK | exact MI | exact ART0 |].
  intros ms' PO. unfold locale_ctor_postA in PO. rewrite ?EQ in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m' & -> & PR & WM & MI' & ART' & ST' & D' & LB').
  apply (HK t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' LB').
  - unfold PJ_LOC_IMP_A. exact D'.
  - unfold PJ_LOC_LO_A, PJ_LOC_HI_A. intros a Ha Ho. apply (PR a Ha). cbn [outside] in *. tauto.
Qed.
End Top.
