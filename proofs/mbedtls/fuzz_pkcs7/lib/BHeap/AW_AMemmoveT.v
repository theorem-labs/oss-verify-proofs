(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rip A_amem_lib A_amemset A_amemcpy A_imemcpy A_bcmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame AW_DepotB AW_DepotTop AW_MallocB
     AW_Poison AW_Refill AW_FakeDefs AW_FakeRep AW_SetShadow AHeapR AHeapB AHeapZ AHeapZW AHeapM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_AMemmove AW_AMemmove0 AHeapL0 AHeapL.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Open Scope Z_scope.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_AMemmoveT () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Section L.
  Variable STKLO : Z.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation hst := (hst STKLO).
  Local Notation HM := (HM_i STKLO).
  Local Notation hcs := (hcs_i STKLO).

  #[using="Type"] Theorem amemmove_i : ltac2:(CDefT.buildp (gd_tbl_AW_AMemmoveT ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Ps',(3.VhAR,VSTKLO,)PLB,(4.$5.)PLF,(4.$5.)PDST,$6.PSRC,$6.Pn,$6.Plo,$6.Pds,(4.(0.&8.))Pss,(4.(0.&8.))P,(7.VhAR,VSTKLO,R9.R8.R7.R:.)P,(8.$9.R;.R7.R3.)P,(:.$9.R<.R7.R3.)P,(;.$6.(<.(=.(0.&8.)R5.))R7.)P,(;.$6.(<.(=.(0.&8.)R5.))R8.)P,(>.$9.$?.(10.VhAR,VSTKLO,R>.)R?.R;.R9.)P,(>.$9.$?.(10.VhAR,VSTKLO,R?.)R10.R;.R:.)P,(11.$9.R11.R:.(12.&40.R31.))P,(13.(14.VR,)R;.)P,(13.R<.(15.(12.&40.R33.)(16.VR,)))P,(17.(10.VhAR,VSTKLO,R13.)R=.(15.(12.&40.R34.)R=.))P,(18.$9.R15.)P,(19.(13.(1:.R12.R10.)R?.)(13.(12.&40.R36.)R12.))P,(19.(13.(1:.R12.R11.)R10.)(13.(12.&40.R37.)R12.))P,(19.(;.$6.R12.=)(13.(1:.(1:.R14.R12.)+8.)(1;.+2.+2?.)))P,(19.(;.$6.R13.=)(13.(1:.(1:.R14.R13.)+8.)(1;.+2.+2?.)))P,(1<.R14.(1;.+2.+28.))P,(1=.(1>.VR,)(1?.$5.R19.(20.R18.))(14.VR,)(21.VhAR,VSTKLO,R1:.)R17.R15.)P,(13.(12.&40.R3<.)(21.VhAR,VSTKLO,R1;.))P,(;.(0.&40.)R35.(22.&40.R19.))P,(;.(0.&40.)R35.(22.&40.R19.))P,(;.(0.&40.)R35.(22.&40.R19.))(23.$9.$?.(10.VhAR,VSTKLO,R1?.)(24.$9.R41.R40.R3?.R3>.R3:.R39.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R22.R21.Lr,(0.&40.)Lm',P,(0.&40.)(2.(0.&8.))(25.(26.(27.(28.$6.$6.)(29.$6.$6.R1>.(1:.R1>.R1<.))(27.(28.$6.$6.)(29.$6.$6.R1;.(12.&40.R42.))(2:.(28.$6.$6.))))R22.R1.)(25.(2;.$9.R22.R1.)(25.(18.$9.R1.)(25.(;.(0.&40.)R2.(22.&40.R1>.))(25.(8.$9.R1.R1>.R19.)(25.(11.$9.R1.R1;.(12.&40.R42.))(7.VhAR,VSTKLO,R21.R20.R1?.R1.))))))))(2<.(2=.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(22.&40.+68498.)R21.(2>.(0.&40.))R20.(2?.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m [h HOK] LB LF DST SRC n lo ds ss
      HM1 ARR BS LEN LENS OBJ OBJS ST LO SPL CRS MI DISJ DISJS TOP8 TOP8S N40 CW SPT -> -> ->.
    pose proof HM1 as [HM0 [XR0 HA0]]. unfold hcs_i, htop_i in *. cbn [hh arl_stklo arl_amemcpy arl_memcpy_i arl_amemmove arl_need_amem arl_L R R0] in *.
    dpose HOK as (EL & AW & VW). dpose (hok_L STKLO h HOK) as (_ & _ & SLO & SHI & _ & T1 & T2).
    pose proof XR0 as [RTC _]. pose proof (amem_consts_of_rtc m RTC) as AC.
    assert (HSElo : HSE < lo) by (clear - LO SLO EL; lia).
    assert (N0 : 0 <= n) by (clear - LEN; lia).
    assert (POST : forall ms', amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST n lo ss m ms' ->
              call_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun r m' =>
                munch [(DST, DST + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                /\ r = Z_to_bv 64 DST /\ u8arr asegs m' DST ss /\ stk asegs m' lo (bv_unsigned sp) /\ HM (HS STKLO h HOK) LB LF m') ms').
    { (intros ms' dd_H; ddestruct dd_H as (x5 & x6 & x7 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ARR' & ST')).
      unfold call_postA. deexists 16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [reflexivity|].
      split; [exact ARR'|]. split; [exact ST'|].
      apply (hm_frame_i STKLO (HS STKLO h HOK) LB LF m m' HM1); [| exact WM].
      intros a Ha NW. apply MU. cbn. rewrite wa_unsigned by exact Ha. unfold htop_i in NW. cbn [hh] in NW.
      split; [| split; [| exact I]]; intros IN; apply NW; left.
      - exact (CW a IN).
      - left. cbn [arl_stklo R0]. clear - IN LO SPT. lia. }
    destruct (Z.eq_dec n 0) as [NZ0|NZ].
    - (* [comment removed for export] *)
      assert (D64 : 0 <= DST <= 2^64) by (destruct ARR as [(B0 & B1 & _) _]; rewrite LEN, NZ0 in B1; clear - B0 B1; lia).
      assert (S64 : 0 <= SRC <= 2^64) by (ddestruct BS as (B0 & B1 & _); rewrite LENS, NZ0 in B1; clear - B0 B1; lia).
      assert (ES : ss = []) by (destruct ss; [reflexivity| cbn in LENS; clear - LENS NZ0; lia]). subst ss.
      rewrite NZ0 in POST |- *.
      eapply evtA_mono; [| exact POST].
      eapply (amemmove0_walk AL0 AL0_img AL0_wf (hcsA h)) with (DST := DST) (SRC := SRC); try reflexivity; try eassumption;
        [exact (hcsA_ok STKLO h HOK)| clear - SPL; lia].
    - (* [comment removed for export] *)
      assert (NP : 0 < n) by (clear - N0 NZ; lia).
      pose proof OBJ as [CRD _]. pose proof OBJS as [CRSR _].
      destruct (leaf_obj_facts STKLO h LB LF m DST n HOK HM0 CRD NP TOP8) as [AR HULL].
      destruct (leaf_obj_facts STKLO h LB LF m SRC n HOK HM0 CRSR NP TOP8S) as [ARS HULLS].
      pose proof (leaf_apart STKLO h LB LF m DST n HOK HM0 NP CW) as AP.
      eapply evtA_mono; [| exact POST].
      eapply (amemmove_spec AL0 AL0_img AL0_wf (hcsA h) (hcsA_ok STKLO h HOK) eq_refl); try eassumption; try reflexivity.
      + intros c Hc. exact (leaf_shrd STKLO h LB LF m c HOK HM0 Hc).
      + clear - SPL; lia.
  Qed.
End L.
End ARUN_1.
