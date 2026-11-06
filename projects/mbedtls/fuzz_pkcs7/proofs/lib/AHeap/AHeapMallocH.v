(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow ARt AUnw ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AModelX AVmLib AVm AVst HMLib HM HMFrame AHeapR AMallocPost AHeapMalloc
     AW_Populate AHeapMallocP AHeapMallocPI AJ.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AInstEmb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AHeapMallocH () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.AHeap.AModel.ahst"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.AHeap.AHeapR.hok"; "OSSVerify.KrLib.AHeap.HM.HMc"; "OSSVerify.KrLib.AHeap.AVst.HK"; "OSSVerify.KrLib.AHeap.AHeapR.AL0"; "OSSVerify.KrLib.AHeap.AJ.J"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.AHeap.AModel.l_htop"; "OSSVerify.KrLib.AHeap.AModel.h_L"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.AHeap.AModel.A_TP"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.AHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.AHeap.AModel.l_stk_hi"; "OSSVerify.KrLib.AHeap.AModelX.hfr"; "OSSVerify.KrLib.AHeap.AModelX.FR_MAXm"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.AHeap.AModel.from_primary"; "Corelib.Init.Datatypes.false"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.AHeap.AMallocPost.mallocH_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].

Section ARUN_1. Context {hAR : arun}.
Section MH.
  Variable STKLO : Z.

  (* [comment removed for export] *)
  Definition malloc_sec_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapMallocH ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,$4.PLB,(5.(6.$7.$7.))PLF,(5.(6.$7.$7.))Pn,$7.Plo,$7.Pd,$7.P,(8.VhAR,VSTKLO,R6.)P,(9.VhAR,R7.R6.R5.R9.)P,(:.VhAR,$;.R8.R9.)P,(<.R;.R:.)P,(=.$>.R<.R6.(?.&40.R2<.))P,(10.VSTKLO,R7.)P,(10.R8.(11.(?.&40.R2>.)+1000.))P,(10.(?.&40.R2?.)(12.(13.R=.)))P,(14.$7.(15.(?.&40.R30.)+10.)=)P,(16.$>.R11.)P,(14.(0.&40.)R30.(17.&40.$18.))P,(14.(0.&40.)R2;.(17.&40.R>.))P,(19.(10.=R?.)(1:.R?.(1;.+2.+1<.)))P,(10.(1<.(1=.R13.)(1>.+2.R10.))(1;.+2.+24.))P,(1?.$>.R16.VSTKLO,(20.(13.R14.))(?.&40.R30.)(?.&40.R36.)R?.)P,(10.(1<.(21.R15.)(1<.R10.+3.))$22.)P,(14.$23.(24.R13.)$25.)(26.$>.(27.VhAR,VSTKLO,R3:.R38.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R14.R13.R12.(?.&40.R39.)R19.R18.)(28.(29.(2:.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(17.&40.+68?0<.)R1:.(2;.(0.&40.))R19.(2<.$>.))R18.))")
(* [comment removed for export] *).

  Hypothesis B12 : b12_siteT.   (* [comment removed for export] *)
  Hypothesis MS : malloc_sec_T.

  #[using="B12 MS"] Theorem mallocH_of_parts : mallocH_T STKLO.
  Proof.
    unfold mallocH_T.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
      HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 NB BUD CH HFR XC.
    destruct (from_primary n) eqn:FP.
    - destruct (h_cinit h) eqn:CI.
      + exact (malloc_prim_fieldH STKLO B12 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
                 HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 NB BUD CH HFR XC FP CI).
      + exact (malloc_prim_init_fieldH STKLO B12 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
                 HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 NB BUD CH HFR XC FP CI).
    - rewrite (vchg_sec n (proj1 NB) FP) in BUD.   (* [comment removed for export] *)
      exact (MS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
               HOK HM0 HK0 HJ0 ST LO SPL SPT SPA MI TP A0 NB BUD CH HFR FP).
  Qed.
End MH.

End ARUN_1.
