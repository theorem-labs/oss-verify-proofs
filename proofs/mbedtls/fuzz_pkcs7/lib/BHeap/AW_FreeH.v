(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeRB AW_FreeFam AW_FreeRM AW_FreeFF.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AInstFree AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_FreeA AW_QPut AW_Enqueue AW_Drain AW_Blist AW_RecTop AW_FreePhD.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AW_FreeHMS AW_FreeHMX AW_FreeHMQ AW_MunmapCfg AW_RecStep AW_RecLoop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapR AMallocPost AHeapL AFreePost AW_FreePres.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_FreeH () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_QPUT_RA1"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "ARUN_1.FH.FFM"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_quar"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.put_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_PC_FREE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeA.A_FREE_RA2"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeRM.WFC"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bsum"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.bn_of"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstFree.fCS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHMX.fkeepR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.qs_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.rp_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.Lists.List.incl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.FR_MAXm"; "ARUN_1.FH.phaseP_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeA.A_FREE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_chunks'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.in_qs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcsA"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)

Section FH.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation AL := AL0.

  #[using="Type"] Lemma ALWF : al_wf AL. Proof. exact AL0_wf. Qed.
  #[using="Type"] Lemma ASB : al_sb AL = 0x7fff8000. Proof. reflexivity. Qed.
  #[using="Type"] Lemma IMLE : al_img_lo AL = 0x10000. Proof. reflexivity. Qed.
  #[using="Type"] Lemma IMH : al_img_hi AL = 0x65f000. Proof. reflexivity. Qed.
  #[using="hAR"] Lemma GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0. Proof. cbn. lia. Qed.
  #[using="hAR"] Lemma GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0. Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Definition FFI : ffam AL := ffam_i AL ALWF ASB IMLE IMH GOT64 GSB64.
  Definition FFM (mo : Model) : ffam AL := ffam_fr AL FFI mo.

  #[using="Type"] Lemma FFM_K : forall mo h mo', ff_K AL (FFM mo) h mo' <-> (HK AL h mo' /\ mo_frame mo mo'). Proof. intros; reflexivity. Qed.
  
  (* [comment removed for export] *)
  Definition phaseP_post (mo : Model) (h : ahst) (m : mem) (LB LF : list (Z * Z)) (A SP lo d : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeH ()) "Lcf,$0.(1.$2.Lh2,$2.(1.P,(3.&40.)(4.(3.&8.))Lm2,P,(3.&40.)(4.(3.&8.))(1.$5.Lmo2,$5.(1.(3.&40.)Lt0,(3.&40.)(1.(3.&40.)Lt1,(3.&40.)(1.(3.&40.)Lt2,(3.&40.)(1.(3.&40.)La0,(3.&40.)(1.(3.&40.)La1,(3.&40.)(1.(3.&40.)La2,(3.&40.)(1.(3.&40.)La3,(3.&40.)(1.(3.&40.)La4,(3.&40.)(1.(3.&40.)La5,(3.&40.)(1.(3.&40.)La6,(3.&40.)(1.(3.&40.)La7,(3.&40.)(1.(3.&40.)Lt3,(3.&40.)(1.(3.&40.)Lt4,(3.&40.)(1.(3.&40.)Lt5,(3.&40.)(1.(3.&40.)Lt6,(3.&40.)(1.$6.Lp,$6.(1.$6.Ln,$6.(1.$6.Lct,$6.(1.(7.$8.)Lcsj,(7.$8.)ZSTK,$6.(9.O13.+850.)ZT,$6.(:.(;.O18.))(<.(=.$0.R19.(>.(?.(10.(11.&40.$12.)(11.&40.(13.R2.-50.))O?.(11.&40.$14.)R15.R14.R13.(11.&40.(13.$15.+2=8.))(11.&40.(13.R1.+50.))R12.R11.R10.R?.R>.R=.R<.R;.(11.&40.R5.)(11.&40.R2.)(11.&40.(13.R1.+=0.))(11.&40.(13.R6.-10.))(11.&40.$16.)O7.O6.O5.O4.O3.R:.R9.R8.R7.)O2.(11.&40.$12.)O1.(17.(3.&40.))R17.(18.$19.))R16.))(<.(1:.VhAR,$1;.(1<.O19.)R18.R16.)(<.(1=.R17.R16.)(<.(1>.$19.R17.)(<.(1?.VhAR,R18.O15.R17.)(<.(20.VhAR,R18.R17.)(<.(21.R17.R2.R1.R2.O8.(11.&40.(13.O13.-51.))(11.&40.R2.)(11.&40.+1.)(11.&40.$22.)(11.&40.R6.)(11.&40.O13.)(11.&40.$23.))(<.(24.$19.R17.O12.(9.R2.+50.))(<.(25.$19.R17.R2.R3.)(<.(=.$6.(26.(27.R3.))+818.)(<.(25.$19.R17.(13.O13.-38.)(28.$8.(29.O9.)(28.$8.(29.O:.)(28.$8.(29.O;.)(28.$8.(29.O<.)(28.$8.(29.O=.)(28.$8.(29.O>.)(28.$8.(29.O10.)(2:.$8.)))))))))(<.(2;.VhAR,R18.R4.$2<.)(<.(2=.(=.(7.$2>.)(2?.(30.R18.))(2:.$2>.)))(<.(31.(32.(33.$2>.$34.$35.(2?.(30.R18.))))(36.+2.+27.))(<.(=.$37.(;.R18.)(;.O18.))(<.(=.$6.(38.R18.)(38.O18.))(<.(39.(3:.R18.)(13.(3:.O18.)(13.O11.+3.)))(<.(=.(7.(3;.$6.$6.))(3<.R18.)(3=.O14.(3<.O18.)))(<.(=.(7.(3;.$6.$6.))(3>.(3?.R18.))(3>.(3?.O18.)))(<.(=.$40.(41.R18.)(41.O18.))(<.Px,$6.P,(42.$1;.O18.R1.)(42.$1;.R1:.R2.)(<.(43.(;.O18.)(3<.R18.)(44.R18.)(45.R18.)(46.(47.R18.))(48.(47.R18.))O12.O13.O17.R17.)(<.(49.$19.O17.R17.)(<.(4:.$6.(46.(47.O18.))(46.(47.R18.)))(<.(4:.$6.(48.(47.O18.))(48.(47.R18.)))Pc,$6.P,(2=.(=.$6.R1.$4;.))(=.$6.(4<.(4=.R1:.R2.))(4<.(4=.O18.R2.))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

  Definition phaseP_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeH ()) "PQ,P,$0.SpPra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4>.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(4.(3.&8.))Pmo,$5.Ph,$2.PLB,(7.(3;.$6.$6.))PLF,(7.(3;.$6.$6.))PA,$6.Pn,$6.Plo,$6.Pd,$6.P,(4?.VhAR,VSTKLO,R7.)P,(50.VhAR,R8.R7.R6.R:.)P,(51.$19.R;.(13.$52.+30.)(28.$8.(53.(11.&40.=))(2:.$8.)))P,(54.VhAR,$1;.R:.R;.)P,(1=.R=.R<.)P,(55.(3;.$6.$6.)(56.$6.$6.R9.R8.)R;.)P,(24.$19.R?.R8.(57.&40.R2?.))P,(39.VSTKLO,R9.)P,(39.R:.(9.(57.&40.R31.)+1000.))P,(39.(57.&40.R32.)(58.(;.R10.)))P,(=.$6.(59.(57.&40.R33.)+10.)=)P,(1>.$19.R14.)P,(=.(3.&40.)R33.(11.&40.$14.))P,(=.(3.&40.)R2>.(11.&40.R11.))P,(39.(38.R15.)$5:.)P,(5;.$19.R18.VSTKLO,(5<.(;.R16.))(57.&40.R32.)(57.&40.R38.)R10.)P,(39.(13.(3:.R17.)(13.R11.+3.))$5=.)P,Pcf,$0.P,(5>.R1:.R19.R1;.R18.R17.R16.(57.&40.R3;.)R14.R13.R3<.R3:.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R1.)(5?.$19.R3>.R2.)(5?.$19.R3=.(>.(?.(10.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(11.&40.$60.)R1<.(17.(3.&40.))R1;.(18.$19.))R1:.))")
(* [comment removed for export] *).
  Hypothesis PHP : phaseP_T.
  (* [comment removed for export] *)
  #[using="Type"] Lemma CK32 : forall h k, wf_chunks' h -> In k (h_chunks h) -> ck_n k < 2^32.
  Proof. (intros h k dd_H; ddestruct dd_H as (WKF & _ & _); intros Hk). pose proof (proj1 (proj1 (Forall_forall _ _) WKF k Hk)). lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stack_above_keptG : ltac2:(CDefT.buildp (gd_tbl_AW_FreeH ()) "Phx,$2.Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))Plo,$6.PSP0,$6.PA,$6.Pk,$6.PNB,(7.$6.)PBL,(7.$6.)P,(61.VhAR,(;.R9.))P,(62.VhAR,R:.)P,(63.R;.)P,(64.R<.)P,(43.(;.R=.)(3<.R=.)(44.R=.)(45.R=.)R6.R5.R:.R9.R<.R;.)P,Pb,$6.P,(55.$6.R1.R8.)(1.$65.Lj,$65.(=.(4.$6.)(66.$6.(46.(47.R11.))R1.)(67.$6.R3.)))P,Pb,$6.P,(55.$6.R1.R8.)(1.$65.Lj,$65.(=.(4.$6.)(66.$6.(48.(47.R12.))R1.)(67.$6.R3.)))P,(39.(68.(;.R10.))R=.)P,(39.R>.R=.)P,(39.R>.R=.)P,(39.(13.R>.R=.)(5<.(;.R13.)))(69.R13.R12.R?.R>.)")
(* [comment removed for export] *).
  Proof.
    intros hx m m' lo SP0 A k NB BL WL WK WS GEO K HNB HBL LOL SPL HA HK x Hx.
    dpose WL as (_ & _ & _ & _ & _ & B6d & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _). pose proof aceil_bounds as ACB.
    dpose WK as (WKF & _ & _).
    pose proof (z_T_stk hx GEO) as Y1. pose proof (z_hull_stk hx GEO) as Y2. pose proof (z_pa_stk hx GEO) as Y3.
    unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3.
    apply (K x); cbv zeta.
    - clear - Hx HA. lia.
    - clear - Hx Y1 LOL SPL HA HK; lia.
    - intros [IH _]. unfold in_hull in IH. clear - Hx Y2 LOL SPL HA HK IH; lia.
    - intros [SH _]. unfold shad in SH. clear - Hx SH LOL SPL HA HK STK0 B6d ACB; lia.
    - (intros dd_H; ddestruct dd_H as (q & Hq & RR)). unfold qs_of in Hq. apply in_map_iff in Hq. ddestruct Hq as (kq & <- & Hkq). apply filter_In in Hkq as [Hkq Pq].
      apply andb_prop in Pq as [Pq _]. apply Bool.negb_true_iff in Pq. cbn [fst snd] in RR.
      pose proof (proj1 (Forall_forall _ _) WKF kq Hkq) as (_ & _ & _ & Xq). rewrite Pq in Xq.
      ddestruct Xq as (iq & Nq & _ & _ & CEILq & _). pose proof (z_sec_stk hx GEO iq _ Nq) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y.
      unfold shad in RR. clear - Hx RR Y LOL SPL HA HK STK0 CEILq ACB; lia.
    - unfold free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT. cbn. clear - Hx LOL SPL HA STK0 ACB; lia.
    - (intros dd_H; ddestruct dd_H as (b & Hb & RR)). destruct (HNB b Hb) as [jb Hjb]. pose proof (z_node_stk hx GEO jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y.
      clear - Hx RR Y LOL SPL HA HK; lia.
    - (intros dd_H; ddestruct dd_H as (b & Hb & RR)). destruct (HBL b Hb) as [jb Hjb]. pose proof (z_store_stk hx GEO jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y.
      clear - Hx RR Y LOL SPL HA HK; lia.
    - clear - Hx Y3 LOL SPL HA HK; lia.
    - (intros dd_H; ddestruct dd_H as (r & Hr & RR)). unfold rp_of in Hr. apply in_map_iff in Hr. ddestruct Hr as (sh & <- & Hsh). cbn [fst snd] in RR.
      destruct (In_nth_error _ _ Hsh) as [ish Nsh]. pose proof (z_sec_stk hx GEO ish _ Nsh) as Y. unfold zapart in Y. cbn [fst snd] in Y.
      dpose WS as (_ & _ & _ & _ & _ & _ & _ & WS8). pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & M4 & _).
      clear - Hx RR Y LOL SPL HA HK M4; lia.
  Qed.

  #[using="Type"] Lemma IMG0 : asan_img_ok AL. Proof. exact AL0_img. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma free_tramp : ltac2:(CDefT.buildp (gd_tbl_AW_FreeH ()) "PCS,P,$6.SpPra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4>.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(4.(3.&8.))P,(6:.$1;.R23.)(6;.$19.$1;.R24.Lms',$6<.(=.$6<.R1.(?.(10.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(11.&40.$60.)R4.(17.(3.&40.))R3.(18.$19.)))(?.(10.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(11.&40.+6947<.)R3.(17.(3.&40.))R2.(18.$19.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG0 as IMG'; unfold asan_img_ok in IMG'.
    unfold A_FREE. zstep. apply evtA_done. reflexivity.
  Qed.

  #[using="hAR"] Lemma in_qs_dec : forall QS x, in_qs QS x \/ ~ in_qs QS x.
  Proof.
    intros QS x. induction QS as [|q QS IH].
    - right. (intros dd_H; ddestruct dd_H as (q & Hq & _)). exact Hq.
    - destruct (Z_le_gt_dec (fst q) x) as [A|A]; [destruct (Z_lt_ge_dec x (fst q + snd q)) as [B|B]|].
      + left. exists q. split; [left; reflexivity| lia].
      + destruct IH as [(q' & Hq' & Rq')|N]; [left; exists q'; split; [right; exact Hq'| exact Rq']| right].
        (intros dd_H; ddestruct dd_H as (q' & [E|Hq'] & Rq')); [subst q'; lia| apply N; exists q'; exact (conj Hq' Rq')].
      + destruct IH as [(q' & Hq' & Rq')|N]; [left; exists q'; split; [right; exact Hq'| exact Rq']| right].
        (intros dd_H; ddestruct dd_H as (q' & [E|Hq'] & Rq')); [subst q'; lia| apply N; exists q'; exact (conj Hq' Rq')].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hcsA_after : ltac2:(CDefT.buildp (gd_tbl_AW_FreeH ()) "Ph,$2.Ph2,$2.Ph',$2.Pmo,$5.Pmo',$5.Px,$6.P,(54.VhAR,$1;.R6.R3.)P,(54.VhAR,$1;.R5.R3.)P,(6=.VhAR,R6.)P,Py,$6.P,(42.$1;.R:.R1.)(42.$1;.R:.R2.)P,Py,$6.P,(42.$1;.R:.R1.)P,(2=.(6>.(44.R;.)R2.))(42.$1;.R;.R3.)P,(=.(7.(3;.$6.$6.))(3>.(3?.R:.))(3>.(3?.R;.)))P,(4:.(3;.$6.$6.)(3>.(3?.R;.))(3>.(3?.R:.)))P,Pk,$6?.P,(55.$6?.R1.(70.R=.))P,(=.$71.(72.R2.)$73.)(74.(55.$6?.R3.(70.R>.))(55.(3;.$6.$6.)(56.$6.$6.(75.R3.)(76.R3.))(3>.(3?.R>.))))P,(77.R>.R9.)(77.R=.R:.)")
(* [comment removed for export] *).
  Proof.
    intros h h2 h' mo mo' x HK HK' AWF' CSP CSD EGH IGH GH2 [V|G].
    - pose proof (proj2 (fCS_iff AL ALWF IMLE IMH GOT64 GSB64 h mo x HK) V) as C1. apply CSP in C1.
      destruct (in_qs_dec (qs_of h2) x) as [(q & Hq & Rq)|NQ].
      + unfold qs_of in Hq. apply in_map_iff in Hq as (k & <- & Hk). apply filter_In in Hk as [Hk Pk]. apply andb_prop in Pk as [Pk _]. apply Bool.negb_true_iff in Pk. cbn [fst snd] in Rq.
        destruct (GH2 k Hk Pk) as [IN|GST].
        * left. dpose AWF' as (WL' & _ & WR' & (WKF & _ & _) & _).
          pose proof (proj1 (Forall_forall _ _) WKF k IN) as (_ & _ & _ & X4). rewrite Pk in X4. ddestruct X4 as (i & Ni & _).
          pose proof (F_cs_sec AL ALWF IMLE IMH GOT64 GSB64 h' mo' _ HK' (nth_error_In _ _ Ni)) as CR. cbn [s_map_beg s_map_size] in CR.
          apply (proj1 (fCS_iff AL ALWF IMLE IMH GOT64 GSB64 h' mo' x HK')). apply CR. exact Rq.
        * right. exists (ck_map_beg k, ck_map_size k). exact (conj GST Rq).
      + left. apply (proj1 (fCS_iff AL ALWF IMLE IMH GOT64 GSB64 h' mo' x HK')). exact (CSD x C1 NQ).
    - right. ddestruct G as (g & Hg & Rg). exists g. split; [apply IGH; rewrite EGH; exact Hg| exact Rg].
  Qed.

  #[using="PHP"] Theorem freeH_of_phases : freeH_T STKLO.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF A n lo d
      HOK HM0 XF0 HK0 HJ0 GX0 HIN ST LOL SPL SPT SPA MI TP A0 HV CH HFR.
    dpose HOK as (ESL & AWF & VWF). dpose HM0 as ((_ & HLB) & _).
    dpose AWF as (WL' & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). dpose WL' as (WL & WL24 & WLD).
    dpose WL as (_ & B6a & B6b & _ & B6c & B6d & B6e & _ & _ & _ & _ & _ & HTOPLO & HTOPHI & _ & _ & STK0 & STKH & _). pose proof aceil_bounds as ACB.
    ddestruct (L_GT (h_L h) WL) as ((T0 & T1) & T2 & _).
    set (SP := bv_unsigned sp) in *. set (STK := SP - 2128).
    assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (fCS AL h) (fK AL h) _ _ _ mo (F_kinv AL h) HK0); [exact HJ0| |].
    { apply free_tramp. exact (F_csok AL ALWF ASB IMLE IMH GOT64 GSB64 h). }
    cbn beta. intros ms1 mo1 -> HK1 MM1 HJ1.
    (* [comment removed for export] *)
    apply (PHP _ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo1 h LB LF A n lo d
             HOK HM0 XF0 HK1 HJ1 HIN ST LOL SPL SPT SPA MI TP A0 HV CH HFR).
    intros cf PP. unfold phaseP_post in PP. cbv zeta in PP.
    ddestruct PP as (h2 & m2 & mo2 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & p & n2 & ct & csj & -> &
                    HK2 & HJ2 & MI2 & HMQ2 & HQ2 & PF2 & ST2 & CSJ & SZJ & SAV2 & WF2 & TNE2 & TB2 & EL2 & EHV2 & HFR2 & EB2 & EGH2 & ESEC2 & CSP & FK2 & WM2 & INB & IBL & RU2).
    pose proof (proj1 (FFM_K mo1 h2 mo2) HK2) as [HK2' MF2]. fold STK in CSJ, PF2, ST2. fold STK.
    dpose WF2 as (WL2' & WC2 & WR2 & WK2 & WQ2 & WS2 & WD2 & WB2 & WBIG2 & WX2 & WG2).
    assert (WFK2 : WFK h2) by (exact (WFK_of_WFC h2 ct kQuarantineMax WF2 ltac:(rewrite EHV2; exact HV))).
    pose proof (F_geom AL h2 mo2 WFK2 HK2') as GEO2.
    assert (H322 : forall k, In k (h_chunks h2) -> nfix (ck_n k) < 2^32).
    { intros k Hk. pose proof (CK32 h2 k WK2 Hk) as B. unfold nfix. clear - B. lia. }
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (SP - 2128 + -80)) with (Z_to_bv 64 (STK + -80)) by (subst STK; reflexivity).
    rewrite <- EL2.
    apply (phase_D AL IMG0 ALWF ASB (FFM mo1) h2 ct m2 LF STK lo STK p n2 gp (Z_to_bv 64 A_TP) F fc _
             (Z_to_bv 64 A_FREE_RA2) (Z_to_bv 64 SP) (Z_to_bv 64 p) (Z_to_bv 64 A_PC_FREE) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11
             eq_refl WF2 ltac:(rewrite EHV2; exact HV) H322 TNE2 TB2);
      [rewrite EL2, ESL; exact LOL| subst STK; clear - SPL; lia| rewrite EL2; subst STK; clear - SPT HTOPHI; lia
      | subst STK; replace (SP - 2128) with (SP + (-133) * 16) by (clear; lia); rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by (clear; lia); exact SPA
      | subst STK; clear - SPL LOL ESL STK0 ACB SPT HTOPHI STKH; lia
      | exact GEO2| | exact HK2| exact HJ2| exact MI2| exact HMQ2| exact HQ2| rewrite EL2; exact PF2| exact ST2].
    (* [comment removed for export] *)
    intros h' m' mo' z0 z1 z2 w0 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 DP.
    dpose DP as (AWF' & HMQ' & HQ' & HK' & HJ' & MI' & ST' & CSR' & FK' & WMX' & EL' & ED' & EB' & EHV' & EFK' & EIA' & EPA' & ECI' & ERU' & SUBK' & SUBS' & GH1 & GH2 & GH3).
    pose proof (proj1 (FFM_K mo1 h' mo') HK') as [HKh' MF'].
    pose proof (WFR_of_awf' h' AWF') as WFR'. dpose AWF' as (WLh' & WCh' & WRh' & WKh' & WQh' & WSh' & WDh' & _).
    assert (ELh : h_L h' = h_L h) by (rewrite EL'; exact EL2).
    assert (HVh : h_havol h' <= AVOL_MAX) by (rewrite EHV', EHV2; exact HV).
    pose proof (F_geom AL h' mo' (WFK_of_WFR h' WFR' HVh) HKh') as GEOh.
    (* [comment removed for export] *)
    assert (ABOVE : kept m2 m' STK 2128).
    { apply (stack_above_keptG h2 m2 m' lo STK STK 2128 (d_nb (h_dep h2)) (d_bl (h_dep h2)) (proj1 WL2') WK2 WS2 GEO2 FK');
        [intros b Hb; exact (In_nth_error _ _ Hb)| intros b Hb; exact (In_nth_error _ _ Hb)| rewrite EL2, ESL; exact LOL| subst STK; clear - SPL; lia| clear; lia| rewrite EL2; subst STK; clear - SPT HTOPHI; lia]. }
    assert (CSJ' : rw_cells asegs m' STK csj) by (eapply krw; [exact CSJ| eapply kept_sub; [exact ABOVE| clear; lia| rewrite SZJ; clear; lia]]).
    assert (SAV' : rw_cells asegs m' (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply krw; [exact SAV2| eapply kept_sub; [exact ABOVE| subst STK; clear; lia| subst STK; cbn; clear; lia]]. }
    replace (ret_pc (Z_to_bv 64 A_FREE_RA2)) with (Z_to_bv 64 A_FREE_RA2) by (symmetry; apply ret_pc_even; [unfold A_FREE_RA2; clear; lia| reflexivity]).
    replace (Z_to_bv 64 STK) with (Z_to_bv 64 (SP + -2128)) by (subst STK; f_equal; clear; lia).
    eapply (evtA_aevtS_KJ AL (fCS AL h') (ff_K AL (FFM mo1) h') _ _ _ mo' (ff_kinv AL (FFM mo1) h') HK'); [exact HJ'| |].
    { eapply (free_epi AL IMG0 ALWF (fCS AL h') (F_csok AL ALWF ASB IMLE IMH GOT64 GSB64 h') ra gp (Z_to_bv 64 A_TP) z0 z1 z2 s0 s1 s2 s3 s4 s5 _ _ _ _ _ _
                w0 w1 w2 w3 w4 w5 w6 w7 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6 SP lo F fc m' m' csj []);
        [exact CSJ'| exact SZJ| exact SAV'| subst STK; replace (SP + -2128) with (SP - 2128) by (clear; lia); exact ST'
        | clear - LOL ESL STK0 ACB; lia| exact SPL| clear - SPT HTOPHI STKH; lia| apply munch_refl| apply wmono_refl| exact MI'|].
      apply (F_cs_stack AL IMLE IMH GOT64 GSB64 h' lo (SP - lo) (WFK_of_WFR h' WFR' HVh)); rewrite ELh; [rewrite ESL; exact LOL| clear - SPT HTOPHI; lia]. }
    cbn beta. intros ms3 mo3 P3 HK3 MM3 HJ3. ddestruct P3 as (m3 & -> & MU3 & WM3 & MI3 & ST3).
    pose proof (proj1 (FFM_K mo1 h' mo3) HK3) as [HK3' MF3].
    (* [comment removed for export] *)
    assert (BSh : forall b0, In b0 (q_batches (h_tq h') ++ q_batches (h_gq h')) -> exists i, 0 <= i < carved h' kBatchClass /\ b_addr b0 = chunk_at (h_L h') kBatchClass i).
    { intros b0 Hb0. exact (batch_slot h' b0 WFR' Hb0). }
    assert (FKT : fkeepR (h_L h) (blocks h2) (qs_of h2) (rp_of h2) (d_nb (h_dep h2)) (d_bl (h_dep h2)) lo SP m m3).
    { eapply fkeepR_trans; [exact FK2| | apply incl_refl| apply incl_refl].
      pose proof FK' as FK''. rewrite EL2 in FK''.
      eapply fkeepR_trans; [exact (fkeepR_sp_mono _ _ _ _ _ _ lo STK SP m2 m' FK'' ltac:(subst STK; clear; lia))| | apply incl_refl| apply incl_refl].
      apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m' m3 MU3). apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]. }
    assert (WMT : wmono_ex (qs_of h2) m m3).
    { eapply wmono_ex_trans; [exact (wmono_ex_of_wmono _ m m2 WM2)|]. eapply wmono_ex_trans; [exact WMX'| exact (wmono_ex_of_wmono _ m' m3 WM3)]. }
    destruct (free_pres STKLO h h2 LB LF m m3 lo SP HOK HM0 WR2 WK2 WS2 WD2 GEO2 EL2 FKT WMT LOL ltac:(clear - SPL; lia) ltac:(clear - SPT HTOPHI; lia)) as [PRES IK].
    apply aevtS_now. unfold freeH_post.
    dexists z0, z1, z2, w0, w1, w2, w3, w4, w5, w6, w7, z3, z4, z5, z6, m3, mo3, h'.
    split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|].
    split; [eapply mo_frame_trans; [apply mo_mat_frame; exact MM1| exact MF3]|].
    assert (GX' : gxok h').
    { unfold gxok. rewrite ELh. apply Forall_forall. intros g Hg. destruct (GH3 g Hg) as [Old|(k & Hk & PK & ->)].
      - rewrite EGH2 in Old. exact (proj1 (Forall_forall _ _) GX0 g Old).
      - dpose WK2 as (WKF2 & _ & _). pose proof (proj1 (Forall_forall _ _) WKF2 k Hk) as (_ & _ & _ & WXk). rewrite PK in WXk. ddestruct WXk as (i & Ni & _). rewrite ESEC2 in Ni.
        apply Forall_forall. intros r Hr. cbn [fst snd].
        destruct (tr_apart AL h mo _ _ HK0 (tr_of_sec h _ (nth_error_In _ _ Ni)) (tr_of_extra h r Hr)) as [E|[X|X]];
          [exfalso; unfold sec_tr in E; discriminate E| left| right]; unfold t_hi, sec_tr in X; cbn [t_lo t_len s_map_beg s_map_size] in X; exact X. }
    split; [exact HK3'|]. split; [cbn [ms_mem] in HJ3; exact HJ3|]. split; [exact GX'|]. split; [exact ELh|].
    split; [intros x Hx; exact (hcsA_after h h2 h' mo mo3 x HK0 HK3' AWF' CSP (fun y Hy NQ => CSR' y Hy NQ) EGH2 GH1 GH2 Hx)|].
    split; [rewrite EHV', EHV2; reflexivity|].
    split; [replace (hfr h') with (hfr h2) by (unfold hfr; rewrite ED'; reflexivity); exact HFR2|].
    rewrite HLB, <- EB2.
    split; [exact PRES|]. split; [exact IK|].
    split.
    { apply (proj2 (HMc_iff h' (blocks h2) LF m3)). split; [split; [exact AWF'| symmetry; exact EB']|].
      split.
      { apply (HMq_keepQ h' m' m3 LF WLh' WRh' WKh' WSh' WDh' GEOh BSh WM3); [| exact HMQ'].
        intros A1 k NZ x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros R1. apply (NZ (bv_unsigned x) Hx). left. rewrite ELh. clear - R1 LOL ESL SPT HTOPHI; lia. }
      apply (hm_quar_keepS h' m' m3 lo SP (proj1 WLh') WRh' GEOh BSh); rewrite ?ELh; [rewrite ESL; exact LOL| clear - SPT HTOPHI; lia| exact HQ'| exact MU3| exact WM3]. }
    intros c Hc. rewrite (ERU' c). exact (RU2 c Hc).
  Qed.
End FH.
End ARUN_1.
