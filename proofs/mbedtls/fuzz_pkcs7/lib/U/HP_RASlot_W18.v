(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W18.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3 HP_RF_ntf_A HP_RASlot_W2 HP_RASlot_W4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RASlot_W18 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_free_meta_head"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.sparams"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_free_meta_head"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_prev"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_W2.rta_frame"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RP_2.FAILM.rfailW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W18.as_fm_st"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11805579945.13L14860932568.16L16668613848.16L16681248472.16L41376909528.16L45922951796.13L49146603224.16L56953632769.13L9033555229.16 00000900B00K00T00]00f00o01801AS2st1v2L8S2st1v2L8S2st1v2L8S2st1v2L8S2st1v2L8S2st1v2L8S2st1v2L8S2st1v2L8S2st1v2L8". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_set_free_head : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W18 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pv,$3.P,(4.VhRP,R3.R2.)(4.VhRP,(5.(6.R2.)R4.)(7.R3.(8.(9.$:.+10.))(;.(<.R4.R2.))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m v MR. dpose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (pw st v)) as L8.
  pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
  - left.
    pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
    cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    exact W.
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma rmrep_extW : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W18 ()) "PstX,$0.PstY,$0.Pm,P,(1.&40.)(2.(1.&8.))P,(4.VhRP,R3.R1.)P,(=.(>.$?.$10.$11.$12.)(13.R3.)(13.R4.))P,(=.$14.(15.R4.)(15.R5.))P,Pq,$16.(=.$17.(18.R6.R1.)(18.R7.R1.))P,(=.(>.$16.(19.$?.$10.$1:.$1;.)(1<.$?.$10.$11.$1:.$1;.$1=.)$1>.)(1?.R6.)(1?.R7.))P,(=.(>.$16.(19.$?.$10.$1:.$1;.)(1<.$?.$10.$11.$1:.$1;.$1=.)$20.)(21.R7.)(21.R8.))P,Prid,$?.(=.$22.(23.R9.R1.)(23.R:.R1.))P,(=.(24.(24.(24.(25.(24.$1:.$1:.))$1:.)$1:.)$1:.)(26.R9.)(26.R:.))(4.VhRP,R:.R9.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros stX stY m dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros ER EC EM EA EG ES ERs).
  assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - destruct WF as [RP0 WF']. split; [exact (rparams_ok_same _ _ RP0 ERs)|]. rewrite ER, EA, EG. exact WF'.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

(* [comment removed for export] *)
End RP_1.
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section RP_2. Context {hRP : run_params}.
Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W18 ()) "Ph,$16.P,(=.$3.(27.(15.Vst,))(28.$16.R1.))(29.(2:.Vst,R2.)(29.(2;.(=.$16.R2.Vmt,))(2<.$16.Lp,$16.(29.(=.$3.(2=.(18.Vst,R3.))(28.$16.R1.))(29.(2:.Vst,R1.)(2;.(=.$16.R1.Vmt,)))))))")
(* [comment removed for export] *).

Definition rfailW (spv : Z) : list (Z * Z) :=
  (spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L2020932186.71  L2020932186.72  L21473875220.71 L21473875220.72 L26492795566.76 L33412135623.76 L36495594395.74 L36495594395.75 L45799703203.86 L45920853442.76 L54557901199.103L54557901199.108L54651921874.74 L54651921874.75 L54651921874.76 L54651921874.77 L54651921874.91 L54651921874.97 L56951523255.76 L59314923118.86 L63926921586.70 00000[01F02202^02n03O03j04E04c05005]06K07607a08L09709d0:Q0:^0;00;DS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G3RCB2sp3SPC4Gpos2HB5Ha_st5Hl_stS3hRP2st2mt1G3RCB2sp3SPC4Gpos2HB5Ha_st5Hl_stS2st2mt1G2sp3LENS3hRP2st2mt1G3RCB2sp3SPC4Gpos3LENS2st2mt1G2GI2HB5Ha_st5Hl_stS2st2mt1G2GI2HB5Ha_st5Hl_stS3hRP2st1G1h3RCB4Gpos4Hpos3HC'S2st2mt1G3LENS3hRP2st2mt1G2sp3SPC4Gpos1p2PC2HB5Ha_st5Hl_stS3hRP2st2mt1G1h2sp3SPC4Gpos3HC'2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G1h2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC1p2HB5Ha_st5Hl_stS2st2mt1G3LENS2st2mt1G1h4Hpos1KS3hRP2st2mt1G2sp3SPC". (* [comment removed for export] *)
#[using="MST FL"] Lemma rfailm1_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W18 ()) "Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Px1,(1.&40.)Ps9v,(1.&40.)Ps8v,(1.&40.)Ps7v,(1.&40.)Ps6v,(1.&40.)Ps5v,(1.&40.)Ps4v,(1.&40.)Ps3v,(1.&40.)Ps2v,(1.&40.)Ps1v,(1.&40.)Ps0v,(1.&40.)Prav,(1.&40.)PF,(2>.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pjunk,(25.(1.&8.))P,(4.VhRP,Vst,R2.)P,(2?.$30.R3.)P,(31.$30.R4.(9.(32.&40.R2>.)-90.)(33.VhRP,R3.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.))P,(34.(35.VhRP,)(36.(32.&40.R2?.)+90.))(37.$30.Lms',$38.(2<.(1.&40.)La1',(1.&40.)(2<.(1.&40.)Ls6',(1.&40.)(2<.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(2<.(25.(1.&8.))Ljunk',(25.(1.&8.))(29.(=.$38.R5.(39.(3:.R19.(3;.&40.(9.(32.&40.R35.)-90.))R34.R33.R32.R31.R30.R2?.(3;.&40.VG,)(3;.&40.-1.)R4.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R3.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R=.(3;.&40.+41138.)R<.(3<.(1.&40.))R2.(3=.$30.)))(29.(31.$30.R2.(9.(32.&40.R35.)-90.)(33.VhRP,R1.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.))(29.(3>.(3?.(32.&40.R35.))R;.R2.)(29.(40.$30.R;.R2.)(29.(2?.$30.R2.)(4.VhRP,(41.Vst,Vmt,)R2.))))))))))(39.(3:.R14.(3;.&40.(9.(32.&40.R30.)-90.))R2?.R2>.R2=.R2<.R2;.R2:.(3;.&40.VG,)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(3;.&40.$42.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R8.(3;.&40.+40=30.)R7.(3<.(1.&40.))R6.(3=.$30.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. rceilb; unfold RCTX, RMLOCK, rta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt rsegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x40d8c) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz rp_canary); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40d30) fc None m (seg_rom rsegs))).
  { intros W HW1 HW2.
    dpose MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz rp_canary); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. deexists 2. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    ddestruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
    dpose (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
    dpose (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (512968 + 16, 512968 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
    (intros ms' dd_H; ddestruct dd_H as (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. deexists 4. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (rmrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (512968 + 16, 512968 + 24)]%Z); cbn; tauto|]. cbv beta.
    (intros ms' dd_H; ddestruct dd_H as (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    dpose MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (512960 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (512968 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. deexists 4. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L2020932186.71  L2020932186.72  L21473875220.71 L21473875220.72 L26492795566.76 L33412135623.76 L36495594395.74 L36495594395.75 L45799703203.86 L45920853442.76 L54557901199.103L54557901199.108L54651921874.74 L54651921874.75 L54651921874.76 L54651921874.77 L54651921874.91 L54651921874.97 L56951523255.76 L59314923118.86 L63926921586.70 00000[01F02202^02n03O03j04E04c05005]06K07607a08L09709d0:Q0:^0;00;DS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G3RCB2sp3SPC4Gpos2HB5Ha_st5Hl_stS3hRP2st2mt1G3RCB2sp3SPC4Gpos2HB5Ha_st5Hl_stS2st2mt1G2sp3LENS3hRP2st2mt1G3RCB2sp3SPC4Gpos3LENS2st2mt1G2GI2HB5Ha_st5Hl_stS2st2mt1G2GI2HB5Ha_st5Hl_stS3hRP2st1G1h3RCB4Gpos4Hpos3HC'S2st2mt1G3LENS3hRP2st2mt1G2sp3SPC4Gpos1p2PC2HB5Ha_st5Hl_stS3hRP2st2mt1G1h2sp3SPC4Gpos3HC'2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G1h2sp3SPC4Gpos2GC2HB5Ha_st5Hl_stS3hRP2st2mt1G2sp3SPC4Gpos2GC1p2HB5Ha_st5Hl_stS2st2mt1G3LENS2st2mt1G1h4Hpos1KS3hRP2st2mt1G2sp3SPC". (* [comment removed for export] *)
#[using="MST FL"] Lemma rfailm2_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W18 ()) "Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Px1,(1.&40.)Ps9v,(1.&40.)Ps8v,(1.&40.)Ps7v,(1.&40.)Ps6v,(1.&40.)Ps5v,(1.&40.)Ps4v,(1.&40.)Ps3v,(1.&40.)Ps2v,(1.&40.)Ps1v,(1.&40.)Ps0v,(1.&40.)Prav,(1.&40.)PF,(2>.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(2.(1.&8.))Pjunk,(25.(1.&8.))P,(4.VhRP,Vst,R2.)P,(2?.$30.R3.)P,(31.$30.R4.(9.(32.&40.R2>.)-90.)(33.VhRP,R3.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.))P,(34.(35.VhRP,)(36.(32.&40.R2?.)+90.))(37.$30.Lms',$38.(2<.(1.&40.)Ls6',(1.&40.)(2<.P,(1.&40.)(2.(1.&8.))Lm',P,(1.&40.)(2.(1.&8.))(2<.(25.(1.&8.))Ljunk',(25.(1.&8.))(29.(=.$38.R4.(39.(3:.R18.(3;.&40.(9.(32.&40.R34.)-90.))R33.R32.R31.R30.R2?.R2>.(3;.&40.VG,)(3;.&40.-1.)R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R3.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R<.(3;.&40.+41138.)R;.(3<.(1.&40.))R2.(3=.$30.)))(29.(31.$30.R2.(9.(32.&40.R34.)-90.)(33.VhRP,R1.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.))(29.(3>.(3?.(32.&40.R34.))R:.R2.)(29.(40.$30.R:.R2.)(29.(2?.$30.R2.)(4.VhRP,(41.Vst,Vmt,)R2.)))))))))(39.(3:.R14.(3;.&40.(9.(32.&40.R30.)-90.))R2?.R2>.R2=.R2<.R2;.R2:.(3;.&40.VG,)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(3;.&40.$42.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R8.(3;.&40.+410;0.)R7.(3<.(1.&40.))R6.(3=.$30.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  unfold rfailW. rceilb; unfold RCTX, RMLOCK, rta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt rsegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x41108) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz rp_canary); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 512960) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x410b0) fc None m (seg_rom rsegs))).
  { intros W HW1 HW2.
    dpose MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    rmchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
    clear MUs.
    rmeta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : rmrep (put_meta mt meta0 st) mX);
      [ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz rp_canary); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. deexists 2. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    ddestruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
    dpose (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _).
    dpose (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (512968 + 16, 512968 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
    (intros ms' dd_H; ddestruct dd_H as (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    rmeta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rmeta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    step.
    rmchunk MR3 MSh3 CH.
    rmeta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. deexists 3. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (rmrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (512968 + 16, 512968 + 24)]%Z); cbn; tauto|]. cbv beta.
    (intros ms' dd_H; ddestruct dd_H as (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0)). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    rmeta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    dpose MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (512960 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (512968 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. deexists 3. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (rmrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FAILM.

End RP_2.
