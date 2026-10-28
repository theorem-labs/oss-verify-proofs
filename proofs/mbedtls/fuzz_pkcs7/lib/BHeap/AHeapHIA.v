(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM HMFrame
     AHeapL0 AW_FakeDefs AW_FakeRep AHeapR AHeapK AHeapB AHeapZ AHeapZW AHeapM AHeapL AMallocPost AHeapMalloc AFreePost AHeapFree AHeapFreeNull AW_Populate AHeapMallocH
     AW_MmapDie AW_MapOrDie AW_MallocSecS AHeapMallocS
     ACallocPost AHeapCalloc AHeapCallocP AHeapCallocPI AHeapCallocS AHeapCallocH.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AInstEmb AW_B12Walk AInstEmbT.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AHeapHIA () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocSecS.dstat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocSecS.DIE_NEED"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.R0"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HM_i"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.HK_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hcs_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.htop_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hstkhi_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hflag_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.havol_i"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hfr_i"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AMAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.vchg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.win24"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.call_postA"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b12_T : Prop := b12_walk_T.
#[using="Type"] Lemma b12_T_S : b12_T -> b12_siteT.
Proof. exact b12_siteT_of_walk. Qed.
(* [comment removed for export] *)
Definition mod_die_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapHIA ()) "PCS,P,$0.SpPgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pa6,(1.&40.)Pra,(1.&40.)PSP0,$0.PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(3.(1.&8.))Pmm,P,(1.&40.)(3.(1.&8.))Paddr,$0.Psize,$0.Plo0,$0.Pfr,(4.(1.&8.))P,(5.$6.R21.)P,(7.(8.=R5.)(9.R5.(:.+2.+2?.)))P,(7.(9.=R5.)(8.R5.(:.+2.+28.)))P,(;.$<.R8.(=.R<.-60.)(>.$?.(10.(11.&40.+32.))(>.$?.(12.#2<.R4.)(>.$?.(13.R1:.)(>.$?.(13.R1;.)(>.$?.(13.R1<.)(>.$?.(13.R1=.)(>.$?.(13.R1>.)(>.$?.(13.R=.)(14.$?.))))))))))P,(15.R9.)P,(16.$<.R:.R7.(=.R>.-60.))P,(8.+65?000.R8.)P,(8.R9.(17.R10.$18.))P,(8.R11.(:.+2.+3?.))P,(19.(>.(1:.$0.$0.)(1;.$0.$0.R;.R12.)(14.(1:.$0.$0.)))R?.R>.)P,(1<.$<.R10.R?.)P,(1=.$<.R10.)P,(1>.R2=.R>.(17.R15.R>.))(1?.$<.$6.R2>.(20.R14.$21.)(22.(11.&40.(17.(:.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).

Section HIA.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.
  (* [comment removed for export] *)
  #[using="Type"] Lemma RIP0 : rip0_T. Proof. exact (rip0_walk AL0 AL0_img AL0_wf). Qed.
  #[using="Type"] Lemma JMS : jstep_T 0x67db4 0x68808. Proof. exact (jstep_walk_memset AL0 AL0_img AL0_wf). Qed.
  #[using="Type"] Lemma AMS0 : amemset0_T 0x68258 2208. Proof. exact (amemset0_walk AL0 AL0_img AL0_wf 0x68258 2208 (or_introl (conj eq_refl eq_refl))). Qed.
  #[using="Type"] Lemma IMS0 : amemset0_T 0x68808 2224. Proof. exact (amemset0_walk AL0 AL0_img AL0_wf 0x68808 2224 (or_intror (conj eq_refl eq_refl))). Qed.
  #[using="Type"] Lemma JMC : jstep_T 0x67db8 0x68af8. Proof. exact (jstep_walk_memcpy AL0 AL0_img AL0_wf). Qed.
  #[using="Type"] Lemma AMC0 : amemcpy0_T 0x67dbc 2224. Proof. exact (amemcpy0_walk AL0 AL0_img AL0_wf 0x67dbc 2224 (or_introl (conj eq_refl eq_refl))). Qed.
  #[using="Type"] Lemma IMC0 : amemcpy0_T 0x68af8 2240. Proof. exact (amemcpy0_walk AL0 AL0_img AL0_wf 0x68af8 2240 (or_intror (conj eq_refl eq_refl))). Qed.
  #[using="Type"] Lemma BC0 : bcmp0_T. Proof. exact (bcmp0_walkZ AL0 AL0_img AL0_wf). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis B12 : b12_T.
  Hypothesis MOD_DIE : mod_die_T.
  #[using="MOD_DIE"] Lemma MSEC : malloc_sec_T STKLO. Proof. exact (malloc_sec_fieldH STKLO MOD_DIE). Qed.
  #[using="B12 MOD_DIE"] Lemma CH : callocH_T STKLO. Proof. exact (callocH_of_parts STKLO (b12_T_S B12) MOD_DIE). Qed.
  Hypothesis FH : freeH_T STKLO.
  (* [comment removed for export] *)
  Definition calloc_T : Prop := ltac2:(CDefT.buildp (gd_tbl_AHeapHIA ()) "Zsegs,(4.$23.)$<.ZR,$24.(25.VhAR,VSTKLO,)ZHST,Ss(26.VhAR,VSTKLO,)ZHM,Ps,(26.VhAR,VSTKLO,)PLB,(4.$27.)PLF,(4.$27.)Pm,P,(1.&40.)(3.(1.&8.))Sp(28.VhAR,VSTKLO,)ZHK,Ps,(26.VhAR,VSTKLO,)Pmo,$29.Sp(2:.VhAR,VSTKLO,)Zhcs,Ps,(26.VhAR,VSTKLO,)P,$0.Sp(2;.VhAR,VSTKLO,)Zhtop,Ps,(26.VhAR,VSTKLO,)$0.(2<.VhAR,VSTKLO,)Zhstkhi,Ps,(26.VhAR,VSTKLO,)$0.(2=.VhAR,VSTKLO,)Zhflag,Ps,(26.VhAR,VSTKLO,)$0.(2>.VhAR,VSTKLO,)Zhavol,Ps,(26.VhAR,VSTKLO,)$0.(2?.VhAR,VSTKLO,)Zhfr,Ps,(26.VhAR,VSTKLO,)$0.(30.VhAR,VSTKLO,)Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))Pmo,$29.Ph,R2<.PLB,(4.$27.)PLF,(4.$27.)Pcnt,$0.Psz,$0.Plo,$0.Pd,$0.P,A4.R32.R7.R6.R5.R9.P,A2.R32.R8.R9.P,(16.R37.R;.R4.(31.&40.R2;.))P,(8.(32.R37.)R5.)P,(8.R6.(17.(31.&40.R2=.)(33.R38.)))P,(8.(31.&40.R2>.)A1.R34.R<.)P,(34.$0.(35.(31.&40.R2?.)+10.)=)P,(1=.R3<.R10.)P,(34.(1.&40.)R2?.(11.&40.(36.R3<.)))P,(34.(1.&40.)R2:.(11.&40.R=.))P,(34.(1.&40.)R2:.(11.&40.R=.))P,(8.=R?.)P,(8.=R?.)P,(9.(37.R11.R10.)$38.)P,(8.(=.A1.R3:.R15.(39.(37.R12.R11.)))$3:.)P,(3;.R44.R18.(32.R43.)A1.R3=.R16.(31.&40.R32.)(31.&40.R38.)R10.)P,(8.(=.A1.R3;.R17.(3<.R11.))$3=.)P,P,(34.$3>.(3?.(37.R15.R14.))$40.)(9.(41.R18.)$42.)(43.R47.Lc,$44.(45.$46.Lms',$46.(45.$29.Lmo',$29.(7.(34.$44.R3.(47.R2.R1.))(48.R4:.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.Lr,(1.&40.)Lm',P,(1.&40.)(3.(1.&8.))(7.(1=.R4<.R1.)(7.(16.R4<.R1.R19.(31.&40.R40.))(7.(49.R1?.R3.)(7.(1<.R4<.R20.R1.)(7.(4:.R4<.R4;.R1=.R1<.(31.&40.R40.)(32.R4;.)A1.R45.R1>.(14.$4;.)R20.R1.)(45.(26.VhAR,VSTKLO,)Lh',(26.VhAR,VSTKLO,)(7.(34.$0.A1.R47.R1.A1.R47.R1?.)(7.(34.$0.A1.R46.R1.A1.R46.R1?.)(7.(34.$0.A1.R45.R1.A1.R45.R1?.)(7.A2.R49.R1.R4.(7.Px,$0.P,A2.R49.R20.R1.A2.R4:.R3.R2.(7.(8.A1.R44.R1.(=.A1.R44.R1?.(39.(37.R1<.R1;.))))(7.(8.A1.R43.R1.(=.A1.R43.R1?.(3<.R19.)))(4<.(7.(34.(1.&40.)R3.(11.&40.=))A4.R4:.R1.R1>.R1=.R2.)(45.$0.LA,$0.(7.(34.(1.&40.)R4.(11.&40.R1.))(7.(34.$0.(35.R1.+10.)=)(7.(4=.R4=.R1?.R1>.R1.(37.R1=.R1<.))(7.(4<.(8.(=.R1.(37.R1=.R1<.))(32.R4=.))(8.A1.R47.R20.R1.))(7.A4.R4;.R2.(>.(1:.$0.$0.)(1;.$0.$0.R1.(37.R1=.R1<.))R1?.)R1>.R3.(;.R4>.R3.R1.(>.$?.(12.(4>.(37.R1=.R1<.))(4?.(1.&8.)(11.&8.=)(4>.(37.R1=.R1<.))))(14.$?.)))))))))))))))))))))))R2.))))(47.(50.(51.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(11.&40.(52.R46.))R1<.(53.(1.&40.))R1;.(54.R47.))R1:.))")
(* [comment removed for export] *).
  #[using="B12 MOD_DIE"] Lemma CA : calloc_T. Proof. exact (calloc_field STKLO CH). Qed.

  Definition artA_i : artA asegs (R0 STKLO).
  Proof.
    unshelve eapply (ART asegs (R0 STKLO) (hst STKLO) (HM_i STKLO) (HK_i STKLO) (hcs_i STKLO) (htop_i STKLO) (hstkhi_i STKLO) (hflag_i STKLO)
                          (havol_i STKLO) (hfr_i STKLO) (fun _ => False)).
    - exact (hk_halted_i STKLO).
    - exact (hk_mat_i STKLO).
    - exact (hk_vmonly_i STKLO).
    - exact AL0_wf.
    - cbn. unfold A_UAR_GOT. lia.
    - cbn. clear - STKLO_OK. lia.
    - intros [h HOK]. exact (hcsA_ok STKLO h HOK).
    - exact (hm_top_i STKLO).
    - (* [comment removed for export] *)
      intros [h HOK] LB LF m [HM0 _]. cbn [hh] in HM0. ddestruct HM0 as ((AWF & HLB) & _). rewrite HLB.
      ddestruct AWF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WX & _). ddestruct WX as (_ & _ & _ & _ & _ & _ & _ & _ & X9). exact X9.
    - exact (hm_top16_i STKLO).
    - intros [h HOK]. exact (hcsA_stack STKLO h HOK).
    - exact (hcs_block_i STKLO).
    - exact (hcs_fake_i STKLO).
    - intros [h HOK] a Ha. exact (hcsA_static STKLO h a Ha).
    - intros [h HOK] x Hx. exact (hcsA_below_top STKLO h x HOK Hx).
    - intros [h HOK] c Hc. exact (hcsA_shadow_band STKLO h c HOK Hc).
    - cbn. lia.
    - intros [h HOK] a n CR N. exact (hcsA_app STKLO h a n HOK CR N).
    - cbn. clear - STKLO_OK. lia.
    - intros [h HOK] a n H1 H2 H3 H4. exact (hcsA_img h a n H1 H2 H3 H4).
    - intros [h HOK] x y Hx Hy. exact (hcsA_hull64 STKLO h x y HOK Hx Hy).
    - exact (hm_flag_img_i STKLO).
    - exact (hm_abase_i STKLO).
    - exact (hm_auar_i STKLO).
    - exact (hm_rtc_i STKLO).
    - exact (hm_shadow_rd_i STKLO).
    - exact (hm_img_shadow_i STKLO).
    - exact (hm_aobj_block_i STKLO).
    - exact (hm_apart_i STKLO).
    - exact (hm_stack_readable_i STKLO).
    - exact (hm_frame_i STKLO).
    - exact (hm_stack_shadow_w_i STKLO).
    - exact (hm_fake_free_i STKLO).
    - (* [comment removed for export] *) exact (malloc_field STKLO (mallocH_of_parts STKLO (b12_T_S B12) MSEC)).
    - (* [comment removed for export] *) exact CA.
    - (* [comment removed for export] *) exact (free_field STKLO FH).
    - (* [comment removed for export] *) exact (free_null_field STKLO STKLO_OK).
    - exact (artA_amemcpy_i STKLO JMC AMC0 IMC0).
    - exact (artA_amemset_i STKLO JMS AMS0 IMS0).
    - exact (artA_bcmp_i STKLO BC0).
    - exact (artA_set_shadow_i STKLO).
    - exact (art_rip_i STKLO RIP0).
    - exact (art_smalloc_i STKLO).
    - exact (art_sfree5_i STKLO).
  Defined.
End HIA.

End ARUN_1.
