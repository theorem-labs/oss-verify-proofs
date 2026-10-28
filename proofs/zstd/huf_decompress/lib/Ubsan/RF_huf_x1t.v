(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufTableX1 HufPure_HufTableX1RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model RF_huf_rs_pure RF_huf_rs
  RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_top RF_huf_x1t_rsc RF_huf_x1t_rk RF_huf_x1t_so RF_huf_x1t_sob.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC. Context {rc : runConstT}.

Lemma huf_rdt_x1_proof : huf_rdt_stmt huf_dt_ok PHUF_RDT_X1.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DT W S mtl flags src jdt jw lo
    MTL RDT RW SRC SRCB SRCN S16 DT0 DTA W0 WA S0 DTL WL SL DJ1 DJ2 DJ3 ST LOS SPA SPB MI FL HA0 HA1 HA2 HA3 HA4 HA5.
  subst a0 a1 a2 a3 a4 a5. unfold PHUF_RDT_X1. unfold HUF_RDT_STACK in LOS. unfold DTABLE_BYTES, HufHarness.DT_BYTES in *.
  assert (P2 : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  pose proof (rw_cells_CB_length usegs _ _ _ _ RW) as LJW0.
  assert (LJW : zlen jw = 8704) by (rewrite LJW0; reflexivity). clear LJW0.
  apply (u8arr_of_rw_cells usegs) in RW.
  pose proof (u8arr_sub _ _ _ 0 52 RW ltac:(lia) ltac:(lia) ltac:(lia)) as RKa. rewrite Z.add_0_r in RKa.
  pose proof (u8arr_sub _ _ _ 52 52 RW ltac:(lia) ltac:(lia) ltac:(lia)) as RSa.
  pose proof (u8arr_sub _ _ _ 104 876 RW ltac:(lia) ltac:(lia) ltac:(lia)) as STa.
  pose proof (u8arr_sub _ _ _ 980 256 RW ltac:(lia) ltac:(lia) ltac:(lia)) as SYa.
  pose proof (u8arr_sub _ _ _ 1236 256 RW ltac:(lia) ltac:(lia) ltac:(lia)) as HWa.
  assert (LSUB : forall k n, 0 <= k -> 0 <= n -> k + n <= 8704 -> zlen (firstn (Z.to_nat n) (skipn (Z.to_nat k) jw)) = n).
  { intros k n K N KN. rewrite firstn_length, skipn_length. lia. }
  pose proof (LSUB 0 52 ltac:(lia) ltac:(lia) ltac:(lia)) as LRK. pose proof (LSUB 52 52 ltac:(lia) ltac:(lia) ltac:(lia)) as LRS.
  pose proof (LSUB 104 876 ltac:(lia) ltac:(lia) ltac:(lia)) as LST. pose proof (LSUB 980 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LSY.
  pose proof (LSUB 1236 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LHW. clear LSUB.
  set (jrk := firstn (Z.to_nat 52) (skipn (Z.to_nat 0) jw)) in *. set (jrs := firstn (Z.to_nat 52) (skipn (Z.to_nat 52) jw)) in *.
  set (jst := firstn (Z.to_nat 876) (skipn (Z.to_nat 104) jw)) in *. set (jsy := firstn (Z.to_nat 256) (skipn (Z.to_nat 980) jw)) in *.
  set (jhw := firstn (Z.to_nat 256) (skipn (Z.to_nat 1236) jw)) in *. clearbody jrk jrs jst jsy jhw.
  clear RW.
  apply (proj1 (rw_cells_app' usegs m DT [C4 _] [CB _ jdt])) in RDT. destruct RDT as [RDT RDJ]. cbn [cells_size csize Nat.add Z.of_nat] in RDJ.
  pose proof (rw_cells_CB_length usegs _ _ _ _ RDJ) as LJD0.
  assert (LJD : zlen jdt = 4 * 2^mtl) by (rewrite LJD0; rewrite Z2Nat.id by lia; reflexivity). clear LJD0.
  apply (u8arr_of_rw_cells usegs) in RDJ. replace (DT + Z.of_nat 4) with (DT + 4) in RDJ by lia.
  assert (WA4 : Z.land W 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 4096, bv_unsigned sp); (DT, DT + 4 * (1 + 2 ^ mtl)); (W, W + 8704)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  assert (DTA4 : Z.land DT 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
  carve_frame 240%nat ST.
  x1w_walk. x1w_zbr.
pose proof (rw_cells_nth _ _ _ _ 0 (C1 (Z_to_bv 8 0)) FR ltac:(cbn; lia)) as STK. cbn in STK. rewrite Z.add_0_r in STK.
  apply (proj1 (rw_cells_app' usegs _ _ [_; _; _; _; _] _)) in FR. destruct FR as [FRa FR].
  apply (proj1 (rw_cells_app' usegs _ _ [_] _)) in FR. destruct FR as [NSPc FR].
  apply (proj1 (rw_cells_app' usegs _ _ [_] _)) in FR. destruct FR as [TLPc FRb].
  cbn [cells_size csize Nat.add] in NSPc, TLPc, FRb.
  replace (bv_unsigned sp + -240 + Z.of_nat 128) with (bv_unsigned sp + -112) in NSPc by lia.
  replace (bv_unsigned sp + -240 + Z.of_nat 128 + Z.of_nat 4) with (bv_unsigned sp + -108) in TLPc by lia.
  replace (bv_unsigned sp + -240 + Z.of_nat 128 + Z.of_nat 4 + Z.of_nat 4) with (bv_unsigned sp + -104) in FRb by lia.
  pose proof (proj2 NSPc) as WNS. pose proof (proj2 TLPc) as WTL. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4 in WNS, WTL.
  eapply evt_cut.
  { eapply huf_rstats_proof with (HW := W + 1236) (RK := W) (NSP := bv_unsigned sp + -112) (TLP := bv_unsigned sp + -108) (S := S) (W := W + 104)
      (src := src) (jh := jhw) (jr := jrk) (jw := jst) (nsv := Z_to_bv 64 0) (tlv := Z_to_bv 64 0) (lo := lo);
    rewrite ?unsigned_lit by lia; unfold HUF_RSTATS_STACK;
    first [ assumption | reflexivity | lia | (f_equal; lia) | (apply bv_eq; rewrite !unsigned_lit by lia; lia) | idtac ].
    all: fail. }
  intros ms' PO. unfold huf_rstats_post, HUF_RSTATS_STACK in PO. rewrite !unsigned_lit in PO by lia. revert ms' PO.
  post_call usegs m1.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
  destruct (read_stats src) as [h|e| |] eqn:RS.
  3,4: contradiction.
  2: { destruct POST as (RET & E0). subst.
       x1w_zbr. x1w_norm. x1w_br Q0; [ | exfalso; lia ]. x1w_zto 2996.
       pose proof (stk_of_rw_cells usegs _ _ _ FRa) as S1. cbn [cells_size csize Nat.add] in S1.
       pose proof (stk_of_wr_at _ _ _ WNS) as S2. pose proof (stk_of_wr_at _ _ _ WTL) as S3.
       pose proof (stk_merge usegs _ _ _ _ ST S1 ltac:(lia)) as S4.
       pose proof (stk_merge usegs _ _ _ _ S4 ltac:(replace (bv_unsigned sp + -240 + Z.of_nat 128) with (bv_unsigned sp + -112) by lia; exact S2) ltac:(lia)) as S5.
       pose proof (stk_merge usegs _ _ _ _ S5 ltac:(replace (bv_unsigned sp + -112 + 4) with (bv_unsigned sp + -108) by lia; exact S3) ltac:(lia)) as S6.
       replace (bv_unsigned sp + -108 + 4) with (bv_unsigned sp + -104) in S6 by lia.
       eapply x1_epi; [lia | lia | exact FRb | exact S6 | lia | eassumption | eassumption | eassumption | lia | intros; lia]. }
  destruct POST as (RET & (jrest & HWr & LJR) & RKr & NSr & TLr). subst.
  destruct (read_stats_safe src read_ncount_safe (Forall_all_bytes _ SRCB)) as [(h' & RS' & SOK) | (e & RS')]; rewrite RS in RS'; [injection RS' as <- | discriminate].
  pose proof (read_stats_ret src h (Forall_all_bytes _ SRCB) RS) as RET1.
  pose proof (x1_396 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT W S mtl lo src (x1_1012 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT W S mtl lo src (x1_1520 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT W S mtl lo src))) as X396.
  pose proof (x1_232 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT W S mtl lo src X396) as X232.
  eapply (x1_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT W S mtl lo src X396 X232); try eassumption; unfold hk; try lia; try (exact DJ1).
Qed.
End CANSEC.
