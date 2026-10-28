(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs Virgin.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RF_enframe HP_RMallocKit_A HP_RMalloc_fp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_malloc_enf () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ctx_head_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_mmap_counter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.renframe_entry"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.undersized"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_enf.enf_leaf"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_stride"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Corelib.Init.Datatypes.snd"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.slot_ok"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.under_virgin"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.enframe_full"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ret"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.havoc"; "RP_1.renf_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"].

Section RP_1. Context {hRP : run_params}.
Local Unset Keyed Unification.

(* [comment removed for export] *)
#[using="Type"] Lemma renf_glue_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_enf ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pnw,(0.&40.)Pgw,(0.&40.)Piw,(0.&40.)Prav,(0.&40.)Ps0v,(0.&40.)Ps1v,(0.&40.)Ps2v,(0.&40.)Ps3v,(0.&40.)Ps4v,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,$2.Pst,$3.P,(4.$5.R2.$6.(7.R1.))P,(4.$5.R3.$8.(9.$:.(;.(<.=))(=.$:.)))P,(4.$5.R4.(>.(?.&40.R2:.)-30.)(9.$:.(10.R7.)(9.$:.(10.R8.)(9.$:.(10.R9.)(9.$:.(10.R:.)(9.$:.(10.R;.)(9.$:.(10.R<.)(=.$:.))))))))P,(11.+30.(?.&40.R2;.))P,(12.(11.=(13.(14.R5.)))(15.(13.(14.R5.))(16.+2.+20.)))(17.$5.Lms',$18.(19.$18.R1.(1:.(1;.R10.R2>.R2=.R2<.R2;.R2:.R29.R?.R>.R12.R11.R13.(<.(1<.(13.(14.R7.))))R24.R23.R22.R21.R=.R<.R;.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R:.(1=.&40.$1>.)R9.(1?.(0.&40.))R8.(20.$5.)))(1:.(1;.R13.(1=.&40.(>.(?.&40.R2=.)-30.))R2<.R2;.R2:.R29.R28.R12.(1=.&40.$8.)R27.R26.R25.R24.R23.R22.R21.R20.R11.R10.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R9.(1=.&40.+4088<.)R8.(1?.(0.&40.))R7.(20.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until st. intros CH LK FR SP48 CTR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RCTX, RMLOCK in *. unfold ctx_head_cells in CH.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. step.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x40898)) with (Z_to_bv 64 0x40898) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  do 12 step.
  apply evt_done. unfold renframe_entry. reflexivity.
Qed.

(* [comment removed for export] *)
Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (o m0 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
    (r : mstate * optr) (ms' : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_enf ()) "(21.$3.Lst',$3.(21.$22.Lp,$22.(21.(0.&40.)Lt0,(0.&40.)(21.(0.&40.)Lt1,(0.&40.)(21.(0.&40.)Lt2,(0.&40.)(21.(0.&40.)La1,(0.&40.)(21.(0.&40.)La2,(0.&40.)(21.(0.&40.)La3,(0.&40.)(21.(0.&40.)La4,(0.&40.)(21.(0.&40.)La5,(0.&40.)(21.(0.&40.)La6,(0.&40.)(21.(0.&40.)La7,(0.&40.)(21.(0.&40.)Lt3,(0.&40.)(21.(0.&40.)Lt4,(0.&40.)(21.(0.&40.)Lt5,(0.&40.)(21.(0.&40.)Lt6,(0.&40.)(21.P,(0.&40.)(23.(0.&8.))Lm',P,(0.&40.)(23.(0.&8.))(12.(19.(24.$3.$25.)O2.(26.$3.(23.$22.)R11.(27.$22.R10.)))(12.(19.$18.O1.(1:.(1;.O1=.O1<.O1;.O1:.R?.R>.R=.O19.O18.(<.(28.R11.R10.))R<.R;.R:.R9.R8.R7.R6.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R5.R4.R3.R2.)O=.(29.O1=.)O<.(1?.(0.&40.))R1.(20.$5.)))(12.(2:.$5.R1.)(12.(2;.$5.R1.O;.(?.&40.O1<.))(12.(2<.VhRP,R11.R1.)(12.(2=.R11.)(12.(2>.O8.O9.R1.)(12.P,(2?.(30.O7.O6.))(31.$5.R2.(28.R12.R11.)(32.(0.&8.)(33.=)(34.O3.)))(35.O:.O7.O6.O5.O4.O3.R11.R10.))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_zeros m a n : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_enf ()) "P,(11.=O2.)P,(11.(>.O2.(36.O1.))(16.+2.+40.))P,Pi,$37.P,(38.R1.O1.)(31.$5.O3.(>.O2.(36.R2.))(9.(0.&8.)(33.=)(=.(0.&8.))))(31.$5.O3.O2.(32.(0.&8.)(33.=)O1.))")
(* [comment removed for export] *).
Proof.
  intros A0 AN H. split; [exact A0|]. rewrite repeat_length. split; [exact AN|].
  intros i Hi. dpose (H i Hi) as (_ & _ & B). specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error] in B.
  rewrite Nat2Z.inj_0, Z.add_0_r in B. rewrite B. symmetry. apply nth_error_repeat. exact Hi.
Qed.

#[using="Type"] Lemma bytes_at_inj m a bs1 bs2 : bytes_at rsegs m a bs1 -> bytes_at rsegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  (intros dd_H; ddestruct dd_H as (_ & _ & B1); intros dd_H; ddestruct dd_H as (_ & _ & B2); intros L). apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [LT|GE].
  - rewrite <- (B1 i LT), <- (B2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i) GE), (proj2 (nth_error_None bs2 i) ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma renf_implT : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_enf ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pra',(0.&40.)Pra,(0.&40.)Ps0v,(0.&40.)Ps1v,(0.&40.)Ps2v,(0.&40.)Ps3v,(0.&40.)Ps4v,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Po,$2.Pm0,$2.Pm1,$2.Ps,$39.Pst1,$3.Pg,$22.Pb,$22.Pr,$3:.Pidx,$3;.Pn,$3;.Plo,$3;.PC,P,$3;.SpZmr,$3<.(30.R8.R7.)Zstride,$3;.(3=.R1.)Zctr,$3;.(13.(14.R:.))P,(2<.VhRP,R;.R=.)P,(2=.R<.)P,(3>.R=.R11.R?.)P,(2:.$5.R10.)P,(2;.$5.R11.R9.(>.(?.&40.R36.)-30.))P,(11.(3?.VhRP,)R:.)P,(11.R;.(40.(?.&40.R38.)+30.))P,(4.$5.R14.(>.(?.&40.R39.)-30.)(9.$:.(10.R19.)(9.$:.(10.R1:.)(9.$:.(10.R1;.)(9.$:.(10.R1<.)(9.$:.(10.R1=.)(9.$:.(10.R1>.)(=.$:.))))))))P,(2>.R<.R16.R15.)P,Pa,$3;.P,(12.(11.R?.R1.)(15.R1.(?.&40.R3<.)))A1.R?.R2.P,Pa,$3;.P,(12.(11.(40.(>.(>.(>.(41.R13.)(42.$43.$3;.R14.))+10.)(44.R=.R12.))+4.)R1.)(15.R1.(40.(>.(>.(>.(>.(41.R13.)(42.$43.$3;.R14.))+10.)(44.R=.R12.))R=.)+4.)))A1.R10.R2.P,(12.(11.=R<.)(15.R<.(16.+2.+20.)))P,(45.R17.R16.R15.R14.R13.R12.)P,(46.R18.R17.R16.R14.)(47.(24.$3.(23.$22.))R1=.(48.(24.$3.(23.$22.))R19.R18.R15.R14.R?.Lst2,$3.Lp,$22.(49.(24.$3.(23.$22.))(26.$3.(23.$22.)(4:.R1.R16.R2.)(27.$22.R1.))))R1:.Lres,(24.$3.(23.$22.))Ls',$39.Lms',$18.(12.(19.$39.R2.R1=.)(4;.R28.R43.R42.R41.R27.R26.R25.R24.R23.R34.R33.R32.R31.R30.R2?.R2>.R22.R21.R16.R20.R1?.R15.R1<.R1;.R1:.R18.R17.R3.R1.))(1:.(1;.R26.(1=.&40.(>.(?.&40.R40.)-30.))R3?.R3>.R3=.R3<.R3;.(1=.&40.R14.)(1=.&40.$8.)R3:.R39.R38.R37.R36.R35.R34.R33.(4<.R19.(27.$22.R18.))(<.R15.)R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R1?.(1=.&40.+4088<.)R1>.(1?.(0.&40.))R1;.(20.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO UV.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
  fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  clear SPAN. rename SPAN1 into SPAN.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rceilb.
  (* [comment removed for export] *)
  ddestruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
  dpose (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  rceilb.
  set (G := conc st1 g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
  set (B := conc st1 b) in *.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  (* [comment removed for export] *)
  pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  (* [comment removed for export] *)
  unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
  assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
  { unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
  rewrite Hp0. unfold aadd. cbn [fst snd].
  apply rimplT_rd8. rewrite E3.
  change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
  set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
  set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
  set (off := fold_off off0 slack).
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
  pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
  assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
  match goal with |- rimplT _ _ _ ?Q ?ms => 
  assert (GOAL : rimplT o (K off) s Q ms) end.
  2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
      assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
      { intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
      clearbody off.
      destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
      - rewrite (OFFa E0). exact GOAL.
      - apply rimplT_rd16. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). exact GOAL. }
  subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.
  (* [comment removed for export] *)
  dpose MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
  eapply evt_cut.
  { eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
      [exact CH| exact LK| exact FR| lia| exact CTR]. }
  intros ms' ->.
  unfold renframe_entry.
  eapply evt_mono.
  { eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
         | |- _ => idtac end.
    all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  ddestruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  split; [reflexivity|].
  fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
  set (res := enframe_at st1 g idx n off) in *.
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - n < 2^31) by lia.
  ddestruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear -IDX LI32; lia) ltac:(unfold stride, mr in SPAN; clear -SPAN S16; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
    as (MRr & TKr & CONCr & FSTr & SNDr).
  fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
  change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
  fold res in MRr, TKr, CONCr, FSTr, SNDr.
  set (P0 := B + 16 + stride * idx) in *.
  rewrite <- EM in MRr.
  destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].
  (* [comment removed for export] *)
  assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
  { rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
    intros x Hx. exact Hx. }
  assert (ST' : stk rsegs m' lo (bv_unsigned sp + -48)).
  { eapply rpres_except_stk; [exact PE0| exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
  assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE0| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
  release_frame FR' ST' (bv_unsigned sp).
  unfold renf_post. dexists (havoc (snd res) n (fst res)), (snd res). deexists 14. exists m'.
  split; [reflexivity|].
  split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|]. split; [exact TK'|].
  split.
  { rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
    intros x Hx. apply CSL. unfold B in Hx. lia. }
  split.
  { (* [comment removed for export] *)
    intros UND. rewrite conc_havoc.
    assert (EC : conc (fst res) (snd res) = P0 + 16 * off) by (unfold res; rewrite conc_enframe_at; exact CONCr). rewrite EC.
    pose proof (enframe_at_virgin st1 g b idx n off Hmem (proj1 OFF) N0 ltac:(unfold UNIT, IB; fold mr stride; lia) (UV UND)) as VG0.
    cbv zeta in VG0. destruct VG0 as [VG _]. fold mr stride res in VG.
    dpose MRr as (WFr & _ & _ & _ & _ & SHr).
    assert (Hr' : s_regions (fst res) !! (fst b) = Some r) by (unfold res; rewrite MI_Kit.s_regions_enframe_at; exact Hr).
    destruct (SHr (fst b) r Hr' Hk) as [_ BY].
    apply bytes_at_zeros; [lia| lia|].
    intros i Hi. replace (P0 + 16 * off + Z.of_nat i) with (r_base r + (snd b + 16 + stride * idx + UNIT * off + Z.of_nat i)) by (unfold P0, UNIT; rewrite CB; lia).
    apply (BY _ 0); [unfold UNIT; lia|]. apply (span_virgin_read _ _ _ _ _ VG). unfold UNIT. lia. }
  exists off. split; [exact (proj1 OFF)|]. split; [exact FIT|].
  split. { clear - FSTr SNDr. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity.
Qed.

End RP_1.
