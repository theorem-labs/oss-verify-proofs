(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_C F_ntf_E MallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A HP_RF_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_ntf_E () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rat9c_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocModel_B.deq_mid"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.LActive"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_prev"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rat9c_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc : Z) (fr : list cell) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_E ()) "Lms',$0.(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R4.(6.(7.O23.(8.&40.(9.(:.&40.O22.)-60.))O21.O20.O14.O13.O12.O1?.O1>.(8.&40.(;.O6.O3.))(8.&40.(9.$<.(=.O2.+8.)))O11.R3.R2.O10.O?.O>.(8.&40.$<.)O1=.O1<.O1;.O1:.O19.O18.O17.O16.O15.O=.O<.O;.O:.)O9.(8.&40.+4007<.)O8.(>.(2.&40.))R1.(?.$10.)))(4.(11.(12.O6.O7.(:.&40.O22.))O5.R1.)(4.(13.$10.O5.R1.)(4.(14.$10.R1.)(4.(15.$10.R1.O7.(9.(:.&40.O22.)-60.))(4.(16.$10.R1.(9.(:.&40.O22.)-60.)O1.)(17.VhRP,O4.R1.))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L18600826357.56L22374889542.58L25069450385.56L29759295589.54L49702840724.56L52163693840.56L57029150466.56L57039425177.54L57770730260.55L8832910886.58 00000\00m01Y01k02A02W02j03903H03dS3hRP3RCB2sp2fr2sc2lo2SC3FRL2LO4LOLE3LFR3LENS2fr3FRL3LFR1x2HxS3hRP3RCB2sp2fr2sc2lo2SC3FRL2LO4LOLE3LFR3LENS2fr2sc2SC3FRL3LFRS2fr2sc2SC3FRL3LFR3LENS2fr2sc2SC3FRL3LFR3LENS2fr2sc3FRL3LFR3LENS2fr2sc3FRL3LFRS2fr2sc3FRL3LFRS2sp2fr2lo3FRL4LOLE3LFR1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_deqself : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_E ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pfr,(19.$1:.)Pst,$1;.Pg,$1<.Psc,$1=.Plo,$1=.P,(17.VhRP,R4.R6.)P,(14.$10.R7.)P,(1>.R6.R5.)P,(4.(1?.=R5.)(20.R5.+30.))P,(5.$21.(22.(23.R8.R7.))(24.$1<.R7.))P,(16.$10.R;.(9.(:.&40.R28.)-60.)R:.)P,(5.$25.(26.R;.)#60.)P,(15.$10.R=.R8.(9.(:.&40.R2:.)-60.))P,(1?.(27.VhRP,)R9.)P,(1?.R:.(28.(:.&40.R2<.)+60.))(29.$10.(2:.R2>.R2=.R2<.R2;.R27.R26.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R2:.R29.R28.R25.R22.R21.R20.R16.R15.R14.R13.R12.R11.R;.R>.R10.(2;.(2<.R<.)R=.R>.)R=.R<.R?.)(6.(7.R2>.(8.&40.(9.(:.&40.R2=.)-60.))R2<.R2;.R2:.R29.R28.R27.R26.(8.&40.(;.R>.R=.))(8.&40.(9.$<.(=.R<.+8.)))R25.R24.R23.R22.R21.R20.(8.&40.$<.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(8.&40.+40074.)R11.(>.(2.&40.))R10.(?.$10.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros MR MI MSL SC GN FR FRL ST LO LOLE.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  rceilb; unfold RCTX in *.
  st1.
  dpose MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (512968 + sc * 8 + 80)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc None MR SC) as MR2; unfold RCTX in MR2 end.
  clear ACTS.
  rraw_store_finish (512968 + 80 + 8 * sc) (le8 (pw st None)) FR ST MU WM SOK.
  assert (EQ : deq_mid (LActive sc) g st = set_active sc None st).
  { unfold deq_mid. rewrite GN, optr_eqb_refl. reflexivity. }
  rewrite EQ.
  apply evt_done. unfold rat9c_post. deexists 3. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
  split.
  { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. repeat split; intros x Hx.
    + apply rfree_fp_stack. lia.
    + apply rfree_fp_ctx. unfold RCTX. lia. }
  split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L1748580572.78 L1748580572.80 L18596693647.70L18596693647.75L18600826357.81L18970007208.80L22374889542.78L22374889542.80L28522121551.78L28522121551.80L29759295589.79L34215541718.77L34223696575.77L46231211805.78L46231211805.80L49702840724.81L52163693840.81L52564885613.81L53512850223.77L5443706936.80 L57029150466.81L57029183119.74L57039425177.79L57770730259.80L59314923118.77L8832910886.78 L8832910886.80 00000F00\01a02f03R03g04804I04`05705I06106Y07007G07]08308j09609c0:60:E0:T0:c0;I0;e0<AS2fr2st1g3FRL3LFR1x2HxS2fr2st1g3FRL3LFR1x2HxS3hRP3RCB2sp2fr2st1g2nx2pv2lo3FRL2LO4LOLE2GB2NB2PB3LFR2HB5Ha_st5Hl_stS3hRP3RCB2sp2fr2st1g2nx2pv2lo3FRL2LO4LOLE2GB2NB2PB3LFR2HB5Ha_st5Hl_stS3hRP3RCB2sp2fr2sc2lo2SC3FRL2LO4LOLE3LFR3LENS2fr2st1g1q3FRL3LFR1KS2fr3FRL3LFR1x2HxS2fr3FRL3LFR1x2HxS2fr2st2nx3FRL3LFR1x2HxS2fr2st2nx3FRL3LFR1x2HxS2fr2sc2SC3FRL3LFRS3hRP3RCB2fr2st1g2nx2pv3FRL2GB2NB2PB3LFRS3hRP3RCB2fr2st1g2nx2pv3FRL2GB2NB2PB3LFRS2fr2st2pv3FRL3LFR1x2HxS2fr2st2pv3FRL3LFR1x2HxS2fr2sc2SC3FRL3LFR3LENS2fr2sc2SC3FRL3LFR3LENS3hRP3RCB2sp2fr2st1g2nx2pv2sc2lo2SC3FRL2LO4LOLE3LFR3LENS2fr3FRL3LFRS3hRP3RCB2fr2st1g2nx2pv1q3FRL2GB2NB2PB3LFR2QBS2fr2sc3FRL3LFR3LENS2fr2sc3FRL3LFRS2fr2sc3FRL3LFRS2fr2sc3FRL3LFRS3hRP2fr2st1g2nx2pv3FRL2GB2NB2PB3LFR1KS2sp2fr2lo3FRL4LOLE3LFR1x2HxS2sp2fr2lo3FRL4LOLE3LFR1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_deq : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_E ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pfr,(19.$1:.)Pst,$1;.Pg,$1<.Pnx,$1<.Ppv,$1<.Psc,$1=.Plo,$1=.P,(17.VhRP,R6.R8.)P,(14.$10.R9.)P,(1>.R8.R7.)P,(4.(1?.=R5.)(20.R5.+30.))P,(5.$21.(22.(23.R:.R9.))(24.$1<.R8.))P,(5.$21.(2=.(23.R;.R:.))(24.$1<.R8.))P,(2>.(5.$1<.R:.R;.))P,(2>.(5.$1<.R:.R<.))P,(1>.R>.R<.)P,(1>.R?.R<.)P,(2?.(5.$21.(30.R10.R<.)(>.$1<.))(1.$1<.Lq,$1<.(4.(5.$21.(30.R11.R=.)(24.$1<.R1.))(1>.R11.R1.))))P,(5.(2.&40.)R27.(31.R11.(30.R11.R=.)))P,(16.$10.R14.(9.(:.&40.R30.)-60.)R13.)P,(5.$25.(26.R14.)#60.)P,(15.$10.R16.R?.(9.(:.&40.R32.)-60.))P,(1?.(27.VhRP,)R10.)P,(1?.R11.(28.(:.&40.R34.)+60.))(29.$10.(2:.R36.R35.R34.R33.R2?.R2>.R28.R27.R26.R25.R24.R23.R22.R21.R20.R32.R31.R30.R2=.R2;.R2:.R29.R1?.R1>.R1=.R1<.R1;.R1:.R12.R17.R19.(2;.(2<.R13.)R16.R17.)R16.R13.R18.)(6.(7.R36.(8.&40.(9.(:.&40.R35.)-60.))R34.R33.R32.R31.R30.R2?.R2>.(8.&40.(;.R17.R16.))(8.&40.(9.$<.(=.R13.+8.)))R2=.(8.&40.(;.R17.R15.))R2<.R2;.R2:.R29.(8.&40.$<.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(8.&40.+3???0.)R1:.(>.(2.&40.))R19.(?.$10.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until lo. intros MR MI MSL SC GN GP NEn NEp MSn MSp ACT HA2 FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as NB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  rceilb; unfold RCTX in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (512968, 512968 + 928)]%Z m) as MU.
  (* [comment removed for export] *)
  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st pv) MUp WMp.
  rmeta_chunk MR MSp CH.
  st1.
  rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 GP GN.
  set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
  assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
  assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
  (* [comment removed for export] *)
  rmeta_chunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
  rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. clear CH.
  (* [comment removed for export] *)
  rmeta_open (conc st nx) MUn WMn.
  rmeta_chunk MR1 MSn1 CH.
  st1.
  rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 GP GN.
  set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
  assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st2 _ sc (wa (RCTX + 80 + 8 * sc)) MR2 SC eq_refl) as RDA. unfold RCTX in RDA.
  replace (wa (512968 + 80 + 8 * sc)) with (Z_to_bv 64 (512968 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
  assert (HACT : active st2 sc = active st sc) by reflexivity. rewrite HACT in RDA.
  assert (HPW : forall q, pw st2 q = pw st q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
  st1. clear RDA.
  assert (EQmid : deq_mid (LActive sc) g st =
                  if optr_eqb (active st sc) (Some g) then set_active sc (Some nx) st2 else st2).
  { unfold deq_mid. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head].
    rewrite !upd_meta_put. fold st1. fold st2. rewrite HACT. reflexivity. }
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (HA : optr_eqb (active st sc) (Some g) = false).
    { destruct (active st sc) as [q|]; [|reflexivity]. cbn [optr_eqb]. apply aptr_eqb_neq. intros ->. apply K.
      unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
    rewrite HA in EQmid. rewrite <- EQmid in MR2. subst a2.
    apply evt_done. unfold rat9c_post. deexists 3. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR2].
  - (* [comment removed for export] *)
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq ltac:(lia)). reflexivity. }
    rewrite HA, optr_eqb_refl in EQmid.
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. clear CH. st1.
    dpose MR2 as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (Z_to_bv 64 (512968 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
    clear ACTS.
    rraw_store_finish (512968 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) FR ST MU WM SOK.
    rewrite <- EQmid in MR3. subst a2.
    apply evt_done. unfold rat9c_post. deexists 3. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSn | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact MR3].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L2424960062.6000006S1n2Hn". (* [comment removed for export] *)
#[using="hRP"] Lemma land_mod_pow2 a b n : 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof. rceilb.
  intros Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros k Hk. rewrite !Z.land_spec.
  destruct (Z.testbit a k), (Z.testbit b k), (Z.testbit (Z.ones n) k); reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L11140256745.12L1741505800.12 L28604762702.10L36498457996.12L38331789298.11L38954701265.9 L42165092875.11L44015325356.12L61382798992.12L61765445516.12L68191963033.11L8929561888.12 L9206326456.10 00000@00H00P00Z00d00i01301801B01L01T01^01gS1f1y1z2Hf2Hy2H1S1y1z2HyS1y1z2H0S1f1y1z2R2S1f1y1z2HfS1y1zS1f1y1z2HfS1y1zS1f1y1z2HfS1f1y1z2R2S1y1z2HyS1f1y1z2R1S1f1y1z1H". (* [comment removed for export] *)
#[using="hRP"] Lemma act_mask_le4 f y z : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_E ()) "P,(4.(1?.=O3.)(20.O3.(32.+2.+20.)))P,(4.(1?.+1.O2.)(1?.O2.(32.+2.+20.)))P,(5.$1=.(33.O1.(32.+2.+20.))(33.(28.O2.+1.)(32.+2.+20.)))(5.(19.(2.&8.))(34.(8.&40.(35.(36.O3.)(:.&40.(8.&40.O1.)))))(34.(37.(35.O3.(28.O2.+1.)))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros Hf Hy Hz. apply le4_congr.
  pose proof (sxv_range f). rewrite (unsigned_lit_wrap z). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
  assert (R1 : 0 <= Z.land (sxv f) (z mod 2^64) < 2^64) by (apply land_range64; lia).
  assert (R2 : 0 <= Z.land f (y - 1) < 2^32).
  { split; [apply Z.land_nonneg; lia|]. pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)). lia. }
  rewrite unsigned_lit, wz_unsigned by lia.
  rewrite land_mod_pow2, sxv_mod32, mod64_mod32, Hz by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rat00_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (fr : list cell) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_E ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R:.(6.(7.O1=.(8.&40.(9.(:.&40.O1<.)-60.))O1;.O1:.R9.O>.O=.O19.O18.(8.&40.(;.O5.O2.))R8.R7.R6.R5.R4.R3.R2.(8.&40.$<.)O17.O16.O15.O14.O13.O12.O11.O10.O?.O<.O;.O:.O9.)O8.(8.&40.+400>0.)O7.(>.(2.&40.))R1.(?.$10.)))(4.(11.(12.O5.O6.(:.&40.O1<.))O4.R1.)(4.(13.$10.O4.R1.)(4.(14.$10.R1.)(4.(15.$10.R1.O6.(9.(:.&40.O1<.)-60.))(4.(16.$10.R1.(9.(:.&40.O1<.)-60.)O1.)(17.VhRP,O3.R1.))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@L11603572554.95 L16073328201.88 L16073575531.89 L16073609113.90 L17923894603.93 L18596693647.64 L18596693647.65 L18596693647.92 L18596693647.93 L18704057131.64 L28237801799.63 L29315121884.81 L29315332781.91 L30774224968.82 L32843961557.98 L41416041421.94 L41422331168.77 L42162764076.93 L42165092875.96 L42165240331.95 L43202716371.82 L46129623291.65 L46129623291.98 L48079606183.91 L52065212613.90 L57029086357.65 L57484866120.94 L59308628433.77 L59562328577.88 L61382798615.98 L61765444619.98 L63397113457.90 L63397145987.89 L66149329410.130L68191782809.95 L68191963033.96 L9917858133.90  L9922156749.83  00000O01301Q01n02M03G04A05S06e07B07]07i08E08X09=09Y0:;0:[0;;0;[0;n0<E0<l0=K0=L0=[0>:0>X0?I0?i0@i0AC0A]0BS0C20CQ0Ci0CjS2fr3st11a2gh1y3FRL3LFR1f2AI2w8S2fr3st11a3FRL3LFR3FRR2gh2w81y2RF2RYS2fr3st11a3FRL3LFR3FRR2gh2w81yS2fr3st11a2gh1y3FRL3LFR2w82RFS2fr3st11a2gh1y3FRL3LFR1f2AI2w8S3hRP3RCB2sp2fr3stm1g2lo3FRL2LO4LOLE2GB3LFR2HB5Ha_st5Hl_stS3hRP3RCB2sp2fr3stm1g2lo3FRL2LO4LOLE2GB3LFR2HB5Ha_st5Hl_stS3hRP3RCB2sp2fr3stm1g2lo3st11a2gh1y3FRL2LO4LOLE2GB3LFR2AI2AB2w83W8R2HB5Ha_st5Hl_stS3hRP3RCB2sp2fr3stm1g2lo3st11a2gh1y3FRL2LO4LOLE2GB3LFR2AI2AB2w83W8R2HB5Ha_st5Hl_stS3hRP3RCB2fr3stm1g3FRL2GB3LFRS2a22fr3stm1g3HA23FRL3LFR1KS2fr3FRL3LFRS2fr3st11a2gh1y3FRL3LFR1f2w8S2fr3FRL3LFR2w83W8RS2fr3stm3st11a2gh1y3FRL3LFR1f2w81x2HxS2fr3st11a2gh1y3FRL3LFR1f2w8S3hRP3RCB2fr3stm1g1a3FRL2GB3LFR2ABS2fr3st11a2gh1y3FRL3LFR1f3FRR2w8S2fr3st11a2gh1y3FRL3LFR1f3FRR2w8S2fr3st11a2gh1y3FRL3LFR1f3FRR2w8S2fr3FRL3LFR2w83W8RS2fr3stm1g3FRL3LFR1x2HxS2fr3stm1g3st11a2gh1y3FRL3LFR1f2w81x2HxS2fr3st11a2gh1y3FRL3LFR1f2AI2w8FS2fr2sc3FRL3LFRS2fr3st11a2gh1y3FRL3LFR1f2AI2w8S3hRP2fr3stm1g1a3FRL3LFR2AB2K2S3hRP3RCB2fr3stm1g1a3FRL2GB3LFR2gh2AI2AB2w83W8R1yS2fr3st11a2gh1y3FRL3LFR1f3FRR2w8S3hRP2fr3stm1g3st11a2gh1y3FRL2GB3LFR1f3FRR2AI2AB2w83W8R2Y12R22R3S2fr3st11a2gh1y3FRL3LFR2w8S2fr3st11a3FRL3LFR2gh2w81yS3hRP2fr3stm1a3FRL3LFR2gh2AI2r12r22AB1y1q1r1H2H02q12H9S2fr3st11a2gh1y3FRL3LFR1f2w82Y1S2fr3st11a2gh1y3FRL3LFR1f2w82Y1S2fr2gh1y3FRL3LFR2w83RY1F". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_postdeq : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (fr : list cell) stm (g : aptr) (sc lo : Z) (an : bool),
  let st1 := upd_meta g clr_links stm in
  rmrep stm m -> mem_inv rsegs m -> meta_slot stm g -> 0 <= sc < 48 ->
  (if an then bv_unsigned a2 = conc stm g else bv_unsigned a2 <> conc stm g) ->
  (an = true -> forall a, active st1 sc = Some a ->
     meta_slot st1 a /\ a <> g /\ m_avail (get_meta_rec st1 a) = 0 /\ 0 <= m_freed (get_meta_rec st1 a) < 2^32
     /\ exists ba gh, m_mem (get_meta_rec st1 a) = Some ba /\ (s_groups st1) !! ba = Some gh /\ 0 <= g_active_idx gh <= 31) ->
  rw_cells rsegs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
  stk rsegs m lo (bv_unsigned sp + -96) -> rceil <= lo -> lo <= bv_unsigned sp - 96 ->
  evt rsegs (rat00_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t1 t2 t3 t4 t5 t6 F fc lo stm m (pd_st an st1 sc) g fr)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc stm g)) (Z_to_bv 64 (RCTX + sc * 8)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x4007c) fc None m (seg_rom rsegs)).
Proof. rceilb.
  intros until an. intros st1 MR MI MSL SC HA2 HACT FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ a2) as A2R. change (bv_modulus 64) with (2^64) in A2R.
  pose proof (rmeta_slot_bounds stm m g MR MSL) as GB.
  pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
  rceilb; unfold RCTX in *.
  pose proof (munch_refl [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m) as MU.
  (* [comment removed for export] *)
  rmeta_open (conc stm g) MUg WMg.
  rmeta_chunk MR MSL CH.
  st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st1 mX)
      by (unfold st1; rewrite upd_meta_put; eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WMg |];
          eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
    clear MUg WMg CH
  end.
  assert (COV : forall m', munch [(conc stm g, conc stm g + 40); (conc stm g, conc stm g + 40)]%Z m m' -> wmono rsegs m m' ->
                 rpres_except (rfree_fp stm lo (bv_unsigned sp)) m m').
  { intros m' MU' WM'. apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU'; [exact MU'|exact WM'|].
    cbn [ivs_covered]. repeat split; intros x Hx; (eapply rfree_fp_meta; [exact MR | exact MSL | lia]). }
  assert (MSg1 : meta_slot st1 g) by (unfold st1; rewrite upd_meta_put; apply meta_slot_put_meta; exact MSL).
  assert (Hconc : forall q, conc st1 q = conc stm q) by (intros; reflexivity).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    destruct an. { exfalso. apply K. rewrite ?unsigned_lit by lia. lia. }
    cbn [pd_st].
    apply evt_done. unfold rat00_post. deexists 9. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
    split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR1].
  - (* [comment removed for export] *)
    destruct an. 2:{ exfalso. apply HA2. rewrite ?unsigned_lit in K by lia. lia. }
    cbn [pd_st].
    (* [comment removed for export] *)
    pose proof (rmrep_active_read st1 _ sc (wa (RCTX + 80 + 8 * sc)) MR1 SC eq_refl) as RDA. unfold RCTX in RDA.
    assert (HPW : forall q, pw st1 q = pw stm q) by (intros [q|]; reflexivity). rewrite HPW in RDA.
    replace (wa (512968 + 80 + 8 * sc)) with (Z_to_bv 64 (512968 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
    st1. clear RDA.
    (* [comment removed for export] *)
    st1. destruct (active st1 sc) as [a|] eqn:HA1.
    + ddestruct (HACT eq_refl a eq_refl) as (MSa & NEa & AV0 & FRR & ba & gh & Hmem & Hgh & AI).
      pose proof (rmeta_slot_bounds st1 _ a MR1 MSa) as AB. rewrite !Hconc in AB.
      munch_grow MU (conc stm a, conc stm a + 40).
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
      (* [comment removed for export] *)
      rmeta_chunk MR1 MSa CHa. rewrite AV0, Hmem in CHa. cbn [oconc] in CHa.
      st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. rewrite ?unsigned_lit by lia. reflexivity. } clear K3.
      (* [comment removed for export] *)
      st1.
      (* [comment removed for export] *)
      destruct (rmrep_group_read st1 _ ba gh MR1 Hgh) as [_ (w8 & RD8 & Hw8)].
      rewrite Hconc in RD8.
      st1.
      pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
      assert (MOD8 : bv_unsigned w8 mod 32 = g_active_idx gh).
      { rewrite <- Hw8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
      (* [comment removed for export] *)
      st1. st1. unfold zxb. rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite MOD8.
      set (y := 2 ^ (g_active_idx gh + 1)).
      st1. st1. rewrite negw_word.
      (* [comment removed for export] *)
      clear CHa. rmeta_open (conc stm a) MUa WMa.
      rmeta_chunk MR1 MSa CHa. rewrite Hmem in CHa. cbn [oconc] in CHa.
      pose proof (sxv_range (m_freed (get_meta_rec st1 a))) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range y) as RY1.
      st1. rewrite sx32_wz_sxv by lia.
      st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
      (* [comment removed for export] *)
      assert (AMO : amo_aligned AW (Z_to_bv 64 (conc stm a + 28)) = true).
      { apply amo_aligned_intro; [lia|]. Z.div_mod_to_equations. lia. }
      amo_step AMO. rewrite ?sx32_wz_sxv by lia.
      st1. if_false.
      amo_step AMO.
      st1. if_false.
      st1. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. st1. if_false.
      (* [comment removed for export] *)
      st1. st1. st1.
      (* [comment removed for export] *)
      set (f := m_freed (get_meta_rec st1 a)) in *.
      assert (AI31 : Z.land (g_active_idx gh) 31 = g_active_idx gh).
      { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
      assert (ACT : act_of st1 a = y - 1).
      { unfold act_of. rewrite Hmem. cbn [default]. unfold group_active_idx, get_group. rewrite Hgh, AI31. unfold mask_upto, y. reflexivity. }
      assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
      assert (Y1 : 1 <= y <= 2^32).
      { unfold y. split; [pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh + 1)); lia| apply Z.pow_le_mono_r; lia]. }
      pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
      pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
      pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (MR2 : rmrep (act_st st1 a (act_of st1 a)) mX)
      end.
      { unfold act_st. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR1 | exact MSa | exact MUa | exact WMa |].
        eapply rw_cells_congr; [ | | | exact CHa]; [ | reflexivity | cbn; tauto].
        unfold meta_cells. unfold pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen oconc].
        fold f. rewrite E1. rewrite (act_mask_le4 f y) ; [| lia | exact Y1 | rewrite <- Zplus_mod_idemp_l, swrap32_mod32, Zplus_mod_idemp_l; reflexivity].
        rewrite !le4_sxv by lia. rewrite Hmem. cbn [oconc]. reflexivity. }
      clear MUa WMa CHa.
      apply evt_done. unfold rat00_post. deexists 9. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split. { apply (rpres_except_of_munch_cov (rfree_fp stm lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
               cbn [ivs_covered]. repeat split; intros x Hx.
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSa | lia].
               - eapply rfree_fp_meta; [exact MR | exact MSL | lia]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR2.
    + (* [comment removed for export] *)
      unfold pw, wz; cbn [oconc]. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. rewrite ?unsigned_lit by lia. reflexivity. } clear K2.
      apply evt_done. unfold rat00_post. deexists 9. split; [cbv delta [mkR]; unfold RCTX; reflexivity|].
      split; [apply COV; [exact MU|exact WM]|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
      unfold pd_st. rewrite ?HA1. exact MR1.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
