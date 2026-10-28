(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocModel_B F_ntf_B F_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_ntf_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; tauto]);
    clear MUq WMq CH end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_ntf_C () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_prev"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_C.qa_facts"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rqpath_post"; "RocqVerifyHarness.AgentSubmission.Heap.F_ntf_C.qpath_st"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rqpath_post (ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (g : aptr) (m : word -> option byte) (st' : mstate) (fr : list cell) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_C ()) "Lms',$0.(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R6.(6.(7.O22.(8.&40.(9.(:.&40.O21.)-60.))O20.O1?.O11.O10.O?.O1>.O1=.R5.O1<.R4.R3.(8.&40.(9.(;.O5.O4.)+1<.))R2.O>.O=.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O<.O;.O:.O9.)O8.(8.&40.+40238.)O7.(<.(2.&40.))R1.(=.$>.)))(4.(?.(10.O5.O6.(:.&40.O21.))O3.R1.)(4.(11.$>.O3.R1.)(4.(12.$>.R1.)(4.(13.$>.R1.O6.(9.(:.&40.O21.)-60.))(4.(14.$>.R1.(9.(:.&40.O21.)-60.)O1.)(15.VhRP,O2.R1.))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308579152.42000019S2st1g1q1a1k2Hk2a'2k'3Hk'1E2ra2Ca3Sa03ra'3Ca'4Sa0'4Sa1'2HG2HQ1H2H13Sa12H0". (* [comment removed for export] *)
#[using="Type"] Lemma rconc_meta_inj : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_C ()) "Pst,$16.Pm,P,(2.&40.)(3.(2.&8.))Pg,$17.Pq,$17.P,(15.VhRP,R4.R3.)P,(18.R5.R3.)P,(18.R6.R3.)P,(5.$19.(;.R7.R4.)(;.R7.R5.))(5.$17.R5.R6.)")
(* [comment removed for export] *).
Proof.
  (intros st m g q MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & Eg); intros dd_H; ddestruct dd_H as (a' & ar' & k' & Ha' & Hk' & Eqq); intros E).
  pose proof MR as (WF & _). dpose WF as (_ & WR & DJ & _).
  ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  ddestruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L10086800794.66L10593135347.67L11129160142.66L1748580572.67 L1748580572.83 L18596693647.64L18596693647.65L18596693647.73L18596693647.78L18596693647.80L18596693647.85L18598734403.66L22374889542.67L26494879000.66L29759295589.62L29786659053.54L34223696575.54L34223927221.55L46231211805.83L49704932898.66L52161606310.66L53512850223.54L5443706936.57 L57039425177.62L57768186390.55L57770289189.54L57770304171.63L59308628179.54L59314923118.54L59314923118.58L59314923118.67L7441128902.54 L7442851829.54 L7828579971.83 L8832910886.67 L8832910886.83 00000K00o01J01`02202g03\04^05`06b07d08U08f09Z09h0:00:H0:`0;30;N0;i0<10<N0<Y0<d0<o0=:0=K0=a0>00>L0>Z0>h0?;0?W0?oS2fr1g2sc2SC3stB3FRL3LFR2L8S3hRP2fr2st1g2hd3FRL2GB3RCB2pv2HB2PBS2fr1g2sc2SC3stB3FRL3LFR2L8S2fr2st1g3FRL3LFR1x2HxS2fr2st1g3FRL1x2HxS3hRP2sp2fr2st1g2lo3FRL2LO4LOLE2GB3RCB2HB5Ha_st5Hl_stS3hRP2sp2fr2st1g2lo3FRL2LO4LOLE2GB3RCB2HB5Ha_st5Hl_stS3hRP2sp2fr2st1g2lo2hd3FRL2LO4LOLE2GB3RCB2pv2HB2PB3HB05Ha_st5Hl_stS3hRP2sp2fr2st1g2lo2hd2pv3FRL2LO4LOLE2GB3RCB2HB2PB3HB05Ha_st5Hl_stS3hRP2sp2fr2st1g2lo2hd2pv3FRL2LO4LOLE2GB3RCB2HB2PB3HB05Ha_st5Hl_stS3hRP2sp2fr2st1g2lo2hd2pv3FRL2LO4LOLE2GB3RCB2HB2PB3HB05Ha_st5Hl_stS3hRP2sp2fr1g2sc2lo2SC3FRL2LO4LOLE3RCB3stB3LFR2L8S2fr3FRL3LFR1x2HxS3hRP2sp2fr2st1g2sc2lo2SC3stB3FRL2LO4LOLE3RCB3LFR2L8S2fr2sc2SC3FRLS2fr3FRLS3hRP2fr2st1g3FRL2GB3RCBS3hRP2fr2st1g3FRL2GB3RCBS2fr2st2pv3FRL1x2HxS2fr1g2sc2SC3FRL3stB3LFR2L8S2fr1g2sc2SC3FRL3stB3LFR2L8S2fr3FRLS3hRP2fr2st1g1q3FRL2GB3RCB2QBS2fr2sc3FRLS2fr2sc3FRLS2fr2sc3FRLS2fr2sc3FRLS2fr2sc2SC3FRL2K0S3hRP2fr2st1g3FRL2GB1KS2fr2st1g3FRL1KS3hRP2fr2st1g2hd3FRL2pv2HB1KS2fr2sc2SC3FRLS2fr2sc2SC3FRLS2fr2st2hd3FRL1x2HxS2sp2fr2lo3FRL4LOLE3LFR1x2HxS2sp2fr2lo3FRL4LOLE1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma rntf_qpath : ltac2:(CDefT.buildp (gd_tbl_HP_RF_ntf_C ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa3,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pfr,(1;.$1<.)Pst,$16.Pg,$17.Psc,$19.Plo,$19.P,(15.VhRP,R4.R6.)P,(12.$>.R7.)P,(18.R6.R5.)P,(4.(1=.=R5.)(1>.R5.+30.))P,(1?.(5.$20.(21.R8.R6.)(<.$17.))(1.$17.Lq,$17.(4.(5.$20.(21.R9.R7.)(22.$17.R1.))(18.R9.R1.))))P,P,(23.(5.$20.(21.R9.R7.)(22.$17.R8.)))(4.(5.$20.(24.(25.R:.R9.))(<.$17.))(5.$20.(26.(25.R:.R9.))(<.$17.)))P,(27.R:.R8.R9.)P,(14.$>.R=.(9.(:.&40.R2:.)-60.)R<.)P,(5.$28.(29.R=.)#60.)P,(13.$>.R?.R:.(9.(:.&40.R2<.)-60.))P,(1=.(2:.VhRP,)R;.)P,(1=.R<.(2;.(:.&40.R2>.)+60.))(2<.$>.(2=.R30.R2?.R2>.R2=.R29.R28.R27.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R2<.R2;.R2:.R24.R23.R18.R17.R16.R15.R14.R13.R=.R10.R?.R12.(2>.R10.R>.R?.)R11.)(6.(7.R30.(8.&40.(9.(:.&40.R2?.)-60.))R2>.R2=.R2<.R2;.R2:.R29.R28.(8.&40.(;.R10.R?.))R27.(8.&40.R>.)R26.(8.&40.(9.(;.R10.R?.)+1<.))R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(8.&40.+4001<.)R13.(<.(2.&40.))R12.(=.$>.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MR MI MSL SC ACT GNP QF FR FRL ST LO LOLE.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
  rceilb; unfold RCTX in *.
  (* [comment removed for export] *)
  st1. st1. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st m sc (wa (RCTX + 80 + 8 * sc)) MR SC eq_refl) as RDA. unfold RCTX in RDA.
  st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1. st1.
  replace (Z_to_bv 64 (512968 + sc * 8 + 80)) with (wa (512968 + 80 + 8 * sc)) by (unfold wa; f_equal; lia).
  st1. clear RDA.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  { (* [comment removed for export] *)
    assert (HA : active st sc = Some g).
    { destruct ACT as [A0|(q & Aq & MSq)].
      - exfalso. rewrite A0 in K. unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia.
      - rewrite Aq in K |- *. unfold pw, wz in K; cbn [oconc] in K.
        pose proof (rmeta_slot_bounds st m q MR MSq) as QB. rewrite ?unsigned_lit in K by lia.
        rewrite (rconc_meta_inj st m g q MR MSL MSq K). reflexivity. }
    unfold qpath_st. rewrite HA, optr_eqb_refl.
    apply evt_done. unfold rqpath_post. deexists 5. split; [cbv delta [mkR]; reflexivity|].
    split; [apply rpres_except_refl|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|exact MR]. }
  assert (HA : active st sc <> Some g).
  { intros E. apply K. rewrite E. unfold pw, wz; cbn [oconc]. rewrite ?unsigned_lit by lia. reflexivity. }
  destruct (GNP HA) as [GN GP].
  assert (QS : qpath_st st sc g = queue_st (LActive sc) g st).
  { unfold qpath_st. destruct (active st sc) as [h|]; [|reflexivity].
    replace (optr_eqb (Some h) (Some g)) with false; [reflexivity|]. symmetry. cbn [optr_eqb]. apply aptr_eqb_neq. congruence. }
  rewrite QS. clear QS K.
  (* [comment removed for export] *)
  rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. rewrite ?unsigned_lit by lia. reflexivity. } clear K.
  clear CH.
  (* [comment removed for export] *)
  st1. destruct (active st sc) as [hd|] eqn:HD.
  - (* [comment removed for export] *)
    ddestruct (QF hd HD ltac:(congruence)) as (MSh & pv & Hpv & NEp & MSp).
    assert (NEh : hd <> g) by congruence.
    pose proof (rmeta_slot_bounds st m hd MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (conc st pv, conc st pv + 40); (conc st hd, conc st hd + 40)]%Z m) as MU.
    (* [comment removed for export] *)
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) MRa GP GN.
    set (stA := put_meta g (m_set_next (Some hd) (get_meta_rec st g)) st) in MRa.
    assert (MSha : meta_slot stA hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta; exact MSL).
    (* [comment removed for export] *)
    rmeta_chunk MRa MSha CHh. unfold stA in CHh. rewrite get_meta_rec_put_other in CHh by exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
    st1. clear CHh.
    (* [comment removed for export] *)
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MRa MSga CH. unfold stA in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_next] in CH. rewrite ?GP in CH. cbn [oconc] in CH.
    st1.
    rmeta_close2 MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) stA) MR1 GP GN.
    unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga stA.
    set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some hd) (get_meta_rec st g))) st) in MR1.
    assert (MSh1 : meta_slot st1 hd) by (apply meta_slot_put_meta; exact MSh).
    assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
    assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta; exact MSp).
    (* [comment removed for export] *)
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR1 MSp1 CH. unfold st1 in CH. rewrite !get_meta_rec_put_other in CH by (exact NEp).
    st1.
    rmeta_close2 MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2 GP GN.
    set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
    assert (MSh2 : meta_slot st2 hd) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).
    (* [comment removed for export] *)
    rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_same in CH.
    cbn [m_prev m_next m_mem m_avail m_freed meta_word m_set_prev m_set_next oconc] in CH.
    st1. clear CH. st1.
    (* [comment removed for export] *)
    rmeta_open (conc st hd) MUh WMh.
    rmeta_chunk MR2 MSh2 CH.
    st1.
    rmeta_close2 MR2 MSh2 MUh WMh CH (put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2) MR3 GP GN.
    assert (EQ3 : queue_st (LActive sc) g st = put_meta hd (m_set_prev (Some g) (get_meta_rec st2 hd)) st2).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_link.
      rewrite !upd_meta_put, Hpv. cbn iota. rewrite !upd_meta_put.
      unfold st2, st1. rewrite (get_meta_rec_put_other st g _ pv NEp). reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3.
    apply evt_done. unfold rqpath_post. deexists 5. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSp | lia].
      + eapply rfree_fp_meta; [exact MR | exact MSh | lia]. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
  - (* [comment removed for export] *)
    unfold pw, wz; cbn [oconc]. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); (512968, 512968 + 928)]%Z m) as MU.
    (* [comment removed for export] *)
    st1.
    rmeta_open (conc st g) MUg WMg.
    rmeta_chunk MR MSL CH. rewrite GN, GP in CH. cbn [oconc] in CH.
    st1. st1.
    rmeta_close2 MR MSL MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) MRb GP GN.
    set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) (get_meta_rec st g))) st) in MRb.
    (* [comment removed for export] *)
    dpose MRb as (_ & (_ & ACTS & _) & _).
    pose proof (u64arr_store_ok rsegs _ _ (actives stB) sc (Z_to_bv 64 (512968 + sc * 8 + 80)) ACTS
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (RCTX + 80 + 8 * sc)) (le8 (pw stB (Some g))))
        by (unfold RCTX, pw, wz; cbn [oconc]; f_equal; unfold wa; f_equal; lia);
      pose proof (rmrep_set_active stB mX sc (Some g) MRb SC) as MR3
    end.
    assert (EQ3 : queue_st (LActive sc) g st = set_active sc (Some g) stB).
    { unfold queue_st. cbn [get_head]. rewrite HD. unfold fm_single. rewrite upd_meta_put. reflexivity. }
    rewrite <- EQ3 in MR3. clear EQ3 SOK.
    (* [comment removed for export] *)
    pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX (wa ?A) ?bs) _) =>
      pose proof (length_le8 (pw stB (Some g))) as L8;
      apply (rw_cells_frame rsegs mX _ _ A bs) in FR; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8, FRL; unfold RCTX; cbn; lia];
      apply (stk_write rsegs mX _ _ A bs) in ST; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia];
      apply (munch_write _ _ mX A bs) in MU; [|unfold RCTX; lia|rewrite L8; unfold RCTX; lia|rewrite L8; unfold RCTX; cbn [inside]; lia];
      apply (wmono_write rsegs _ mX (wa A) bs) in WM;
      lazymatch goal with HI : mem_inv rsegs mX |- _ =>
        apply (mem_inv_store rsegs mX (wa A) bs) in HI;
        [| rewrite L8; destruct ACTS as [_ AW]; unfold RCTX; apply (wr_at_store_ok rsegs mX _ _ (8 * sc) 8 AW); [lia| rewrite actives_length; lia] ]
      end;
      remember (write_to_mem mX (wa A) bs) as m3 eqn:Em3; clear Em3 L8 ACTS
    end.
    apply evt_done. unfold rqpath_post. deexists 5. split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. repeat split; intros x Hx.
      + apply rfree_fp_stack. lia.
      + eapply rfree_fp_meta; [exact MR | exact MSL | lia].
      + apply rfree_fp_ctx. unfold RCTX. lia. }
    split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|exact MR3].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
