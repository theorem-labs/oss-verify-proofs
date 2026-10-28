(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_pkcs7_parse_A A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_parse_san_A A_x509_seq_stmts A_x509_seq_stmtsE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C A_x509_san_ext_D A_x509_san_ext_E A_x509_san_ext_F A_x509_san_ext_G A_x509_san_ext_H A_x509_san_ext_I A_x509_san_ext_J.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_x509_san_ext_K () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.and"; "Walk.Call.PHIy"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "Walk.Call.FFRy"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_bud.PHIx"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_bud.FFRx"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_C.sfr"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_C.svA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_C.nLB"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmtsE.seq_parser_postE"; "RocqVerifyHarness.AgentSubmission.B.A_x509_san_ext_bud.CNTx"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Walk.Call.LoopOb"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z).
  Hypothesis STKp0 : 0 <= STKp.
  Hypothesis PSAN : x509_parse_san_stmtA asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  (* [comment removed for export] *)
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.
  Hypothesis PHIp_add : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_add : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_add : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.

  (* [comment removed for export] *)
  Local Notation STKx := (A_x509_san_ext_A.STKx R STKp).
  Local Notation CNTx := A_x509_san_ext_bud.CNTx.
  Local Notation PHIx := (A_x509_san_ext_bud.PHIx PHIp CNTp).
  Local Notation FFRx := (A_x509_san_ext_bud.FFRx FFRp CNTp).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 5)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HCUR : rw_cells asegs m CUR (seq_cells ct cpad 0 0 0).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold A_x509_san_ext_A.STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHb := A_x509_san_ext_A.FSHb.
  Local Notation rsl := (A_x509_san_ext_A.rsl CUR).
  Local Notation LF' FB := ((FB, 256) :: LF).
  Local Notation POST := (seq_parser_postE asegs R HIA PHIx FFRx CNTx (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF NB lo slo d m mo0).
  Local Notation sfr := (A_x509_san_ext_C.sfr R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP CUR P END BUF lo slo bs).
  Local Notation svA := (A_x509_san_ext_C.svA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs).
  Local Notation Wc := (A_x509_san_ext_C.Wc PP).
  Local Notation nLB := (A_x509_san_ext_C.nLB LB).
  Local Notation nfreshA := (A_x509_san_ext_C.nfreshA R LB LF PP CUR).
  Local Notation curFA := (A_x509_san_ext_C.curFA CUR).
  Local Notation headrep := (A_x509_san_ext_C.headrep CUR END BUF).
  Ltac sfr_open D :=
    destruct D as (HHc & HTc & HSc & HCSc & SUBL & SP1 & SP1M & F64 & FRSH & CFB & PRES
                   & FHD & TLc & TSN & FSH & SAVE & RSL & TSB & STb & STlo & PPc & Hpc & BYc & OPP & OBUF & OCUR & CURc & OCc & CURF & MIc & SSc).
  Ltac svA_open D :=
    let S := fresh "SFR" in
    destruct D as (S & HKc & MFc & HFc & HVc & HFRc & SUBN & HND & HFR & HCF & HHD & HLS & CBUF).
  (* [comment removed for export] *)
  Ltac fin_sfr t :=
    unfold A_x509_san_ext_C.sfr;
    spine; first [ eassumption | (unfold A_x509_san_ext_A.FSHb; eassumption) | (unfold A_x509_san_ext_A.rsl; eassumption)
                 | (repeat split; eassumption) | reflexivity | solve [t] | match goal with |- ?g => idtac "SFR-LEFT:" g end ].
  Local Notation ERRQ := (A_x509_san_ext_D.ERRQ R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation CALLQ1 := (A_x509_san_ext_D.CALLQ1 R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).
  Local Notation EXITP := (A_x509_san_ext_E.EXITP R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP CUR P END BUF lo slo bs).

  (* [comment removed for export] *)
  Hypothesis BUD : havol asegs R HIA h + PHIx NB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FFRx NB d <= FR_MAX.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Local Notation KSL := (Z_to_bv 64 CUR) (only parsing).

  (* [comment removed for export] *)
  Definition PHIy (c : Z) : Z := PHIp c + CNTp c * AVOL_CALL.
  Definition FFRy (c : Z) : Z := FFRp c (d + 1) + CNTp c * fr_charge 0 + (c / 2) * fr_charge (d + 1).

  #[using="PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add"] Lemma bud_iter : ltac2:(CDefT.buildp (gd_tbl_A_x509_san_ext_K ()) "Pc,$0.PLw,$0.Pdl,$0.P,(1.=R3.)P,(1.=R3.)P,(1.(2.R4.+2.)R3.)P,(1.=Vd,)(3.(1.(2.(2.(4.R7.)A1.VPHIp,R6.)(5.A1.VCNTp,R6.$6.))(4.(2.R7.R5.)))(1.(2.(2.(2.(7.R7.)A2.VFFRp,R6.(2.Vd,+1.))(5.A1.VCNTp,R6.(8.=)))(8.(2.Vd,+1.)))(7.(2.R7.R5.))))")
(* [comment removed for export] *).
  Proof.
    clear - PHIp_mono FFRp_mono CNTp_mono PHIp_add FFRp_add CNTp_add. intros c Lw dl Hc HL Hd D0. unfold PHIy, FFRy, AVOL_CALL, fr_charge.
    pose proof (PHIp_add c Lw Hc HL) as A1. pose proof (PHIp_mono (c + Lw) (c + dl) ltac:(lia)) as M1.
    pose proof (FFRp_add c Lw (d + 1) Hc HL) as A2. pose proof (FFRp_mono (c + Lw) (c + dl) (d + 1) ltac:(lia)) as M2.
    pose proof (CNTp_add c Lw Hc HL) as A3. pose proof (CNTp_mono (c + Lw) (c + dl) ltac:(lia)) as M3.
    pose proof (A_x509_san_ext_bud.div2_step c dl Hc ltac:(lia)) as DS2.
    split; [lia|]. nia.
  Qed.

  #[using="PHIp_mono FFRp_mono CNTp_mono"] Lemma bud_top : ltac2:(CDefT.buildp (gd_tbl_A_x509_san_ext_K ()) "Pc,$0.Pk,$0.P,(3.(1.=R2.)(1.R2.(9.VEND,VP,)))P,(3.(1.=R2.)(1.(5.+2.R2.)R3.))P,(1.=Vd,)(3.(1.(2.(4.R5.)(5.R4.$6.))(:.VPHIp,VCNTp,(9.VEND,VP,)))(1.(2.(7.R5.)(5.R4.(8.=)))(;.VFFRp,VCNTp,(9.VEND,VP,)Vd,)))")
(* [comment removed for export] *).
  Proof.
    clear - PHIp_mono FFRp_mono CNTp_mono. intros c k Hc Hk D0. unfold PHIy, FFRy, A_x509_san_ext_bud.PHIx, A_x509_san_ext_bud.FFRx, AVOL_CALL, fr_charge.
    pose proof (PHIp_mono c NB ltac:(lia)) as M1. pose proof (FFRp_mono c NB (d + 1) ltac:(lia)) as M2. pose proof (CNTp_mono c NB ltac:(lia)) as M3.
    pose proof (A_x509_san_ext_bud.div2_mono c NB ltac:(lia)) as M4. pose proof (A_x509_san_ext_bud.cnt2_div k c c (proj2 Hk) ltac:(lia)) as M5.
    rewrite (Z.max_r 0 (d + 1 + 3)) by lia.
    split; [lia|]. nia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sfr_swap : ltac2:(CDefT.buildp (gd_tbl_A_x509_san_ext_K ()) "Phc,(<.$=.VR,VHIA,)PLh,(>.$?.)PFB,$0.Psp1,$0.Pw0,(10.&40.)Pw1,(10.&40.)Pw2,(10.&40.)Ptl,(10.&40.)Pb,(10.&8.)Pk0,(10.&40.)Pk8,(10.&40.)Pk16,(10.&40.)Pk24,(10.&40.)Pk48,(10.&40.)Pj64,(>.(10.&8.))Ptg,(10.&40.)Ppd,(10.&40.)Pln,(10.&40.)Ppv,(10.&40.)Pjn,(>.(10.&8.))Pp,$0.Pcur,$0.Pctc,(10.&40.)Pcpc,(10.&40.)Pclc,$0.Pcpp,$0.Pcnx,$0.Pmm,P,(10.&40.)(11.(10.&8.))Pc',$0.Pctc',(10.&40.)Pcpc',(10.&40.)Pclc',$0.Pcpp',$0.Pcnx',$0.P,(12.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VCUR,VP,VEND,VBUF,Vlo,Vslo,Vbs,R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(13.$=.R8.R7.(14.$15.(16.R6.)(14.$15.(16.R5.)(14.$15.(17.(18.&40.R4.))(14.$15.(17.(18.&40.R3.))(14.$15.(17.(18.&40.R2.))(19.$15.)))))))P,(1:.$=.(1;.VR,)(1<.$=.VR,VHIA,R24.)R9.R8.+20.)P,(3.(1=.$0.(1>.R9.+8.)=)(3.(1?.=R9.)(3.(1.(2.R9.+20.)Vlo,)(3.(20.(1.(2.VPP,+8.)R9.)(1.(2.R9.+20.)VPP,))(3.(20.(1.(2.R9.+20.)VBUF,)(1.(2.VBUF,(21.(22.(10.&8.)Vbs,)))R9.))(3.(20.(1.(2.R23.+100.)R9.)(1.(2.R9.+20.)R23.))(3.(23.(24.VR,)(25.$?.R24.(26.(14.(27.$0.$0.)(28.$0.$0.R23.+100.)VLF,)))Vlo,(29.$=.VR,VHIA,Vh,)R9.+20.)(2:.VR,VLB,VLF,(2;.&40.Vsp,)(14.(27.$0.$0.)(28.$0.$0.VPP,(2.VPP,+8.))(14.(27.$0.$0.)(28.$0.$0.VCUR,(2.VCUR,+20.))(19.(27.$0.$0.))))R9.+20.))))))))(12.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VCUR,VP,VEND,VBUF,Vlo,Vslo,Vbs,R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R:.R9.R8.R7.R6.R5.R;.)")
(* [comment removed for export] *).
  Proof.
    intros until cnx'. intros D C' O' F'. sfr_open D.
    unfold A_x509_san_ext_C.sfr. spine; first [ exact C' | exact O' | exact F' | assumption ].
  Qed.

  Local Notation K0 := (Z_to_bv 64 CUR) (only parsing).
  Local Notation K8 := (Z_to_bv 64 (-9578)) (only parsing).
  Local Notation K16 := (Z_to_bv 64 (-9472)) (only parsing).
  Local Notation K24 := (Z_to_bv 64 (-9570)) (only parsing).
  Local Notation K48 := (Z_to_bv 64 (-8320)) (only parsing).

  (* [comment removed for export] *)
  Definition LoopOb (p : Z) : Prop :=
    forall (FB sp1 PHIa FFRa : Z) (w0 w1 w2 tl k0 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte) (nodes : list Z) (cur : Z)
           (ctc cpc : word) (clc cpp : Z) (mc : mem) (moc : Model) (hc : HST asegs R HIA)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl (Z_to_bv 8 248) k0 K8 K16 K24 K48 j64 tg pd ln pv jn p nodes cur ctc cpc clc cpp 0 mc moc hc ->
      p < END -> PHIa <= PHIy (p - P) -> FFRa <= FFRy (p - P) -> 2 * Z.of_nat (length nodes) <= p - P ->
      aevtS asegs POST
        (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                        (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) (Z_to_bv 64 p) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
                   F (Z_to_bv 64 0xae6b0) fc None mc (seg_rom asegs)) moc)
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG NS1 NA1 STKp STKp0 PHIp_mono FFRp_mono CNTp_mono LFB PP0 CWP PPLO BIN B1 B2 B3 B5 CUR0 CWC CURLO D1 SLOS SLOL SLO TOP SPH UW"] Lemma loop_tail :
    forall (p0 : Z), (forall p', p0 < p' -> LoopOb p') ->
    forall (FB sp1 PHIa FFRa : Z) (w0 w1 w2 tl k0 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte) (p2 : Z) (nodes : list Z) (c : Z)
           (ctc cpc : word) (clc cpp : Z) (mc : mem) (moc : Model) (hc : HST asegs R HIA) (pc' : Z)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      svA (nLB nodes) FB sp1 PHIa FFRa w0 w1 w2 tl (Z_to_bv 8 248) k0 K8 K16 K24 K48 j64 tg pd ln pv jn p2 nodes c ctc cpc clc cpp 0 mc moc hc ->
      ((pc' = 0xae6b0 /\ p2 < END) \/ (pc' = 0xae878 /\ p2 = END)) ->
      p0 < p2 -> PHIa <= PHIy (p2 - P) -> FFRa <= FFRy (p2 - P) -> 2 * Z.of_nat (length nodes) <= p2 - P ->
      aevtA asegs (KF asegs R HIA hc moc) POST
        (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                 (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 c) (Z_to_bv 64 p2) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
            F (Z_to_bv 64 pc') fc None mc (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros p0 IH. intros until t6. intros D PCQ LT PHI FFR CNT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    destruct PCQ as [[-> PLT]|[-> PEQ]].
    - intros mo1 [HK1 MF1].
      eapply (IH p2 LT); [eapply A_x509_san_ext_H.svA_mo; [exact D| exact HK1| exact MF1] | exact PLT | exact PHI | exact FFR | exact CNT].
    - pose proof D as D'. svA_open D'. dpose SFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpc & _).
      eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
      { eapply A_x509_san_ext_E.exit_walk with (STKp := STKp) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
          first [ exact SFR | eassumption | match goal with |- ?g => idtac "TAIL-X-PRE-LEFT:" g end ]. }
      cbv beta. intros ms2 EX.
      destruct (bud_top (p2 - P) 0 ltac:(clear - Hpc PEQ B2; lia) ltac:(clear - Hpc; lia) D0') as [BT1 BT2].
      eapply A_x509_san_ext_H.exitp_fin with (STKp := STKp) (d := d) (h := h) (m := m) (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (lo := lo) (slo := slo) (bs := bs);
        first [ exact D | exact EX | exact CBUF | eassumption | idtac ].
      + unfold A_x509_san_ext_bud.CNTx. apply (A_x509_san_ext_bud.cnt2_div _ (p2 - P)); [exact CNT| clear - PEQ; lia].
      + clear - PHI BT1. lia.
      + clear - FFR BT2. lia.
  Qed.
  End Call.
End Walk.
