(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signers_A A_pkcs7_signers_B A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_E.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pkcs7_signers_F () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_junk"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signers_C.gvA"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_cells"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.CrtStmts.SNAME"; "Stdlib.Lists.List.rev"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "Stdlib.Lists.List.NoDup"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.NAME_SIZE"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signer_stmt.A_PKCS7_SIGNER"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis STKsi0 : 0 <= STKsi.
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  (* [comment removed for export] *)
  Local Notation STKs := (A_pkcs7_signers_A.STKs R STKsi).
  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
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
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKs.
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
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold A_pkcs7_signers_A.STKs in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Local Notation NB := (END - P).
  Local Notation POST := (pkcs7_getsigners_postA asegs R HIA (PHIs PHIsi CNTsi) (FFRs FFRsi CNTsi) (CNTs CNTsi) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG DALG NB lo slo d dtg dpad dlen dq m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
  Local Notation gvA := (gvA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP P END BUF SIG DALG lo slo bs dtg dpad dlen dq).

  Ltac gvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).


  Local Notation sjZ := (SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)).



  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="IMG NS1 HMND STKsi SIGNER PHIsi_mono FFRsi_mono CNTsi_mono LFB ALP PP0 CWP PPLO BIN B1 B3 B47 B5 B30 DPB CWS SGLO ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma signer_step_node : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_F ()) "PFB,$0.Psp1,$0.PPHIa,$0.PFFRa,$0.Pw0,(1.&40.)Pw1,(1.&40.)Pw2,(1.&40.)Plw,(1.&40.)Pb4,(1.&8.)Pk0,(1.&40.)Pk8,(1.&40.)Pk16,(1.&40.)Pk24,(1.&40.)Pj32,(2.(1.&8.))Pp,$0.Psgc,(2.$3.)PLc,(2.$4.)Pmc,P,(1.&40.)(5.(1.&8.))Pmoc,$6.Phc,(7.$8.VR,VHIA,)PS,$0.Psjs,$9.PENDx,$0.PRET,$0.PQ,P,$:.SpPt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Ps2v,(1.&40.)Ps3v,(1.&40.)Ps4v,(1.&40.)Ps5v,(1.&40.)Ps6v,(1.&40.)Ps7v,(1.&40.)Ps8v,(1.&40.)Ps9v,(1.&40.)Ps10v,(1.&40.)Ps11v,(1.&40.)P,(;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R2>.R2=.(<.(=.$0.$0.)(>.$0.$0.VPP,(?.VPP,+8.))(<.(=.$0.$0.)(>.$0.$0.VSIG,(?.VSIG,+<8.))(10.(=.$0.$0.))))R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)P,(11.(=.$0.$0.)(>.$0.$0.R1;.+<8.)R1?.)P,(12.$8.R1?.R1<.(13.==R1;.))P,(14.$0.(15.R1=.+10.)=)P,(16.=R1>.)P,(17.VR,VLB,VLF,R1?.+<8.)P,(18.R26.R1>.)P,(18.R1?.VEND,)P,(18.(?.(?.(19.$8.VR,VHIA,Vh,)R34.)A1.VPHIsi,(1:.R20.R28.))$1;.)P,(18.(?.(?.(1<.$8.VR,VHIA,Vh,)R34.)A2.VFFRsi,(1:.R21.R29.)(?.Vd,+1.))$1=.)P,(1>.$8.Vm,(1?.VR,)(20.$8.VR,VHIA,Vh,)(21.&40.Vs0,)(21.&40.Vsp,)Vd,)P,(22.(18.=R22.)(16.R22.(23.+2.+40.)))P,(14.$0.(15.R23.+2.)=)P,Pm1,P,(1.&40.)(5.(1.&8.))Pmo1,$6.Ph1,(7.$8.VR,VHIA,)Pr,$0.Pp',$0.Pinext,$0.Psj',$9.Pnodes,(2.$0.)PPHIx,$0.PFFRx,$0.Py0,(1.&40.)Py1,(1.&40.)Py2,(1.&40.)Pya1,(1.&40.)Pya2,(1.&40.)Pya3,(1.&40.)Pya4,(1.&40.)Pya5,(1.&40.)Pya6,(1.&40.)Pya7,(1.&40.)Py3,(1.&40.)Py4,(1.&40.)Py5,(1.&40.)Py6,(1.&40.)P,(;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R53.R52.(<.(=.$0.$0.)(>.$0.$0.VPP,(?.VPP,+8.))(<.(=.$0.$0.)(>.$0.$0.VSIG,(?.VSIG,+<8.))(10.(=.$0.$0.))))(?.R51.R10.)(?.R50.R?.)R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R14.R44.(24.$4.(25.(26.$0.R11.))R43.)R18.R17.R16.)P,(12.$8.R19.R40.(13.R14.=R13.))P,(22.(16.-10000.R17.)(18.R17.=))P,(22.(18.R48.R17.)(18.R17.R40.))P,P,(14.$0.R19.=)(16.R4:.R19.)P,P,(27.(14.$0.R1:.=))(14.(2.$0.)R17.(10.$0.))P,(28.$8.L,(2.$3.)$29.R1>.(24.$4.(24.$4.(25.(26.$0.R17.))R49.)VLB,)R19.R17.)P,(2:.$0.R18.)P,Px,$0.P,(11.$0.R1.R1:.)PB,$0.Pk,$0.P,(11.(=.$0.$0.)(>.$0.$0.R2.R1.)(24.$4.R4?.VLB,))(2;.(18.(?.R5.$2<.)R3.)(18.(?.R3.R2.)R5.))P,(18.(2=.(2>.$0.R1:.))A1.VCNTsi,(1:.VEND,VP,))P,(18.R1:.A1.VPHIsi,(1:.R47.R4?.))P,(18.R1:.A2.VFFRsi,(1:.R48.R50.)(?.Vd,+1.))P,P,(14.$0.R21.=)(22.(18.R1=.A1.VPHIsi,(1:.R21.R52.))(22.(18.R1<.A2.VFFRsi,(1:.R21.R52.)(?.Vd,+1.))(22.(18.(2=.(2>.$0.R1>.))A1.VCNTsi,(1:.R21.R52.))(18.(?.R52.+2.)R21.))))P,(2?.$8.(30.VR,)(24.$4.(24.$4.R50.VLB,)(31.(<.(=.$0.$0.)(>.$0.$0.R60.+40.)VLF,)))R5?.(<.(=.$0.$0.)(>.$0.$0.VPP,(?.VPP,+8.))(<.(=.$0.$0.)(>.$0.$0.R4<.(?.R4<.+<8.))(10.(=.$0.$0.))))R4?.R25.)(32.$8.(33.$8.VR,VHIA,R24.R25.)R49.(34.(35.(36.&40.R4:.)(36.&40.R60.)Vgp,Vtp,R1<.R1;.R1:.Vsp,(36.&40.R60.)(36.&40.R23.)R19.R18.R17.R16.R15.R14.R13.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R12.R11.R10.R?.)VF,(36.&40.R4:.)Vfc,(37.(1.&40.))R26.(38.$8.)))(32.$8.(33.$8.VR,VHIA,R29.R2:.)R24.(34.(35.(36.&40.R25.)(36.&40.R3;.)Vgp,Vtp,R23.R22.R21.Vsp,(36.&40.R3;.)(36.&40.VPP,)(36.&40.R26.)(36.&40.R28.)(36.&40.VDALG,)R20.R1?.R1>.R1=.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R1<.R1;.R1:.R19.)VF,(36.&40.$39.)Vfc,(37.(1.&40.))R2;.(38.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros D SIN CSS SAL S0 SFR HpE HEE BUD BUDF UW RETR RETE KS. pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKsi0 NRT; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    pose proof FRSH as FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 64 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ SIG 200 FB 64 FRSH CWS ltac:(clear; lia) ltac:(clear; lia) LOS) as APSG.
    pose proof (CNTsi_mono (ENDx - p) NB ltac:(clear - HpE HEE Hpc B1 B2; lia)) as CSm.
    pose proof (PHIsi_mono (ENDx - p) NB ltac:(clear - HpE HEE Hpc B1 B2; lia)) as PSm.
    pose proof (FFRsi_mono (ENDx - p) NB (d + 1) ltac:(clear - HpE HEE Hpc B1 B2; lia)) as FSm.
    pose proof (blocks_below_hm R HIA hc _ _ mc (Lc ++ LB) HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc _ ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    assert (SUBc : forall b, In b (LB ++ fdata LF) -> In b ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b [] FB 64 LF); exact Hb]. }
    assert (CWPc : client_wrange L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA hc) PP 8) by (rewrite HTc; eapply client_wrange_mono; [exact CWP| exact SUBc]).
    assert (CWSc : client_wrange L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA hc) SIG 200) by (rewrite HTc; eapply client_wrange_mono; [exact CWS| exact SUBc]).
    assert (CRDc : client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo DALG 24) by (eapply client_range_incl; [exact CRDA| exact SUBc]).
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBc]. }
    assert (INHq : In (FB, 24) ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDq : In (FB + 32, 64 - 40) ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))) by (apply in_or_app; right; cbn; right; left; reflexivity).
    (* [comment removed for export] *)
    destruct (BBc _ ltac:(apply in_or_app; left; exact SIN)) as [_ SCE]. cbn [fst snd] in SCE.
    pose proof (hm_aobj_block asegs R HIA hc _ _ mc S 200 HHc ltac:(apply in_or_app; left; exact SIN)) as OSS.
    pose proof SFR as SF. ddestruct SF as (_ & _ & _ & SF3).
    assert (ASP : S + 200 <= PP \/ PP + 8 <= S) by (eapply (fresh_apart_client R LB LF lo PP 8 S 200 SFR (client_range_of_w L _ _ _ _ _ CWP)); [clear; lia| clear; lia| clear - ALO LOS; lia]).
    assert (ASG : S + 200 <= SIG \/ SIG + 200 <= S) by (eapply (fresh_apart_client R LB LF lo SIG 200 S 200 SFR (client_range_of_w L _ _ _ _ _ CWS)); [clear; lia| clear; lia| clear - ALO LOS; lia]).
    assert (ASD : S + 200 <= DALG \/ DALG + 24 <= S) by (eapply (fresh_apart_client R LB LF lo DALG 24 S 200 SFR CRDA); [clear; lia| clear; lia| clear - ALO LOS; lia]).
    assert (ASB : S + 200 <= BUF \/ BUF + n <= S) by (apply SF3; apply in_or_app; left; exact BIN).
    destruct (hm_apart asegs R HIA hc _ _ _ HHc) as [_ BA].
    pose proof (blocks_apart_app2 _ _ (S, 200) (FB, 64) BA ltac:(apply in_or_app; left; exact SIN) ltac:(left; reflexivity)) as ASF. cbn [fst snd] in ASF. clear BA.
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { rewrite HSc.
      assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKsi0 NRT; lia].
        intros a Ha. cbn. split; [clear - Ha PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Ha SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0']. }
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 STKsi0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof SIGNER as SG'. unfold pkcs7_signer_stmtA in SG'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG' with (h := hc) (LB := Lc ++ LB) (LF := (FB, 64) :: LF) (PP := PP) (P := p) (END := ENDx) (BUF := BUF) (bs := bs) (S := S) (DALG := DALG)
                     (lo := lo) (slo := slo) (d := d + 1) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (sj := sjs); clear SG';
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold SIGNER_SIZE;
        first [ exact HHc | exact HK1 | exact PPc | exact ALP | exact PP0 | exact CWPc | exact PPLO | exact BYc | exact B47 | exact B5 | exact B30 | exact DPB
              | exact DAc | exact ALD | exact DA0 | exact CRDc | exact DALO | exact Q1 | exact Q2 | exact D2 | exact STlo | exact SSlo | exact SLOS | exact SLOL
              | exact MIc | exact TPV | exact UW1 | exact HpE | reflexivity
              | lazymatch goal with
                | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                | |- aobj _ _ _ _ PP 8 => exact (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OPP)
                | |- aobj _ _ _ _ DALG 24 => exact (aobj_cs_mono asegs AL _ _ _ _ _ HCSc ODA)
                | |- In (BUF, _) _ => apply in_or_app; right; exact BIN
                | |- BUF <= p => clear - B1 Hpc; lia
                | |- ENDx <= BUF + _ => clear - HEE B3; lia
                | |- dq + dlen <= _ => exact Q3
                | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
                | |- lo <= sp1 - STKsi => clear - SLO SP1 NS1 STKsi0 NRT; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFRc; lia
                | |- rw_cells _ _ S _ => exact CSS
                | |- S mod 8 = 0 => clear - SAL; Z.div_mod_to_equations; lia
                | |- 0 < S => exact S0
                | |- aobj _ _ _ _ S 200 => exact OSS
                | |- client_wrange _ _ _ _ S 200 => eapply client_wrange_block; [apply in_or_app; left; apply in_or_app; left; exact SIN| clear; lia| clear; lia]
                | |- S + 200 <= lo => clear - SCE ALO LOS; lia
                | |- S + 200 <= BUF \/ _ => exact ASB
                | |- PP + 8 <= S \/ _ => clear - ASP; lia
                | |- DALG + 24 <= S \/ _ => clear - ASD; lia
                end
              | match goal with |- ?g => idtac "SIGNER-PRE-LEFT:" g end ]. }
    try clear SG'.
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & mo3 & h3 & r & p' & inext & sj' & nodes
                    & E2 & Ea0 & Hr & MI3 & ST3 & SS3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT & HSUCC & PP3 & Hp' & HRP & CS3 & HNC & HND3 & HAP3 & HH3 & HRN).
    injection E2 as Ems Emo. subst ms2 mo2x ua0.
    rewrite ?(unsigned_lit sp1) in ST3, SS3, HP3 by exact SP1R. unfold SIGNER_SIZE in HP3.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETR| exact RETE]).
    rewrite (app_assoc (SNAME (rev nodes)) Lc LB) in HH3, HNC.
    (* [comment removed for export] *)
    assert (CSHD : forall c, FB <= c < FB + 64 -> cshd R (Lc ++ LB) ((FB, 64) :: LF) sp1 (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJs : forall a k, sp1 <= a -> disjoint_from [(PP, PP + 8); (S, S + 200)] a k).
    { intros a k H1. cbn. split; [clear - H1 PPLO LOS SLO SP1 NS1 STKsi0 NRT; lia| split; [clear - H1 SCE ALO LOS SLO SP1 NS1 STKsi0 NRT; lia| exact I]]. }
    apply (presA_shadow_cells_sh asegs R CS (Lc ++ LB) ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA hc) [(PP, PP + 8); (S, S + 200)] mc m3 FB _ CSOK) in FSH;
      [| cbn [cells_size csize Nat.add length]; exact CFB | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP3 | cbn [cells_size csize Nat.add length]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in FHD; [| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INHq| clear; lia| clear; lia] | cbn; split; [clear - APP; lia| split; [clear - ASF; lia| exact I]] ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in G4; [| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia] | cbn; split; [clear - APP; lia| split; [clear - ASF; lia| exact I]] ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in SShi; [| clear; lia| rewrite HSc; clear - HT TOP; lia].
    pose proof (sshad_merge asegs AL m3 slo sp1 (bv_unsigned sp) SS3 SShi ltac:(clear - SP1 SLOL SLO NS1 STKsi0 NRT; lia)) as SSm3. clear SS3 SShi.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in DAc; [| cbn [cells_size csize Nat.add length buf_cells]; apply CRo; [exact DALO| exact CRDA]| cbn; split; [clear - D2; lia| split; [clear - ASD; lia| exact I]] ].
    apply (presA_bytes_at0 asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in BYc;
      [| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right]; split;
         [ eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]
         | cbn; split; [clear - DPB; lia| split; [clear - ASB; lia| exact I]] ] ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in CSG; [| rewrite SZC; apply CRo; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| rewrite SZC; cbn; split; [clear - D1; lia| split; [clear - ASG; lia| exact I]] ].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 PP 8 CSOK HP3) in OPP; [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear; lia]].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 SIG 200 CSOK HP3) in OSG; [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| clear; lia]].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 DALG 24 CSOK HP3) in ODA; [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact DALO| exact CRDA]| clear; lia]].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 BUF n CSOK HP3) in OBUF;
      [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy
       | destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right]; split; [| clear; lia];
         eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia] ].
    (* [comment removed for export] *)
    assert (PRES' : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m3).
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (PQ1 : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA hc) [(S, S + 200); (PP, PP + 8)] mc m3).
      { eapply presA_weaken; [exact HP3| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
      pose proof (presA_drop_fresh_gen R LB LF sp1 sp1 (hstkhi asegs R HIA hc) [(PP, PP + 8)] S 200 S (S + 200) mc m3 PQ1 SFR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS SLO SP1 NS1 STKsi0 NRT; lia)) as PQ2.
      rewrite HSc in PQ2.
      eapply presA_weaken; [exact PQ2| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
    clear PRES.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo3) _ _ _ (conj HK3 (mo_frame_refl mo3))).
    eapply (KS m3 mo3 h3 r p' inext sj' nodes (havol asegs R HIA h3 - havol asegs R HIA hc) (hfr asegs R HIA h3 - hfr asegs R HIA hc));
      [ | exact CS3 | exact Hr | exact Hp' | exact HRP | exact HRN | exact HNC | exact HND3 | exact HAP3 | clear - HCNT CSm; lia | clear - HV3; lia | clear - HFR3; lia
        | (intros E0; ddestruct (HSUCC E0) as (U1 & U2 & U3 & U4); split; [clear - U1; lia| split; [clear - U2; lia| split; [exact U3| exact U4]]]) | exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP3) ].
    split; [exact HH3|]. split; [exact HK3|]. split; [eapply mo_frame_trans; [exact MFc| eapply mo_frame_trans; [exact MF1| exact MF3]]|].
    split; [rewrite HT3; exact HTc|]. split; [rewrite HS3; exact HSc|]. split; [rewrite HF3; exact HFc|].
    split; [intros y Hy; exact (HCS3 y (HCSc y Hy))|].
    split; [clear - HVc; lia|]. split; [clear - HFRc; lia|].
    split; [exact PRES'|].
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
    split; [exact FHD|]. split; [exact G4|]. split; [exact FSH|]. split; [exact SAVE|]. split; [exact RSL|]. split; [exact STb|]. split; [exact ST3|].
    split; [exact PP3|]. split; [clear - Hp' Hpc HpE HEE; lia|].
    split; [exact CSG|]. split; [exact SZC|].
    split; [exact DAc|]. split; [exact BYc|].
    split; [exact OPP|]. split; [exact OSG|]. split; [exact ODA|]. split; [exact OBUF|].
    split; [exact MI3|]. exact SSm3.
  Qed.

  #[using="IMG NS1 HMND STKsi SIGNER PHIsi_mono FFRsi_mono CNTsi_mono LFB ALP PP0 CWP PPLO BIN B1 B3 B47 B5 B30 DPB ALS SG0 CWS SGLO DSB ALD DA0 CRDA DALO Q1 Q2 Q3 D1 D2 D3 SLOS SLOL SLO TOP SPA SPH TPV LOS"] Lemma signer_step_head : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_F ()) "PFB,$0.Psp1,$0.PPHIa,$0.PFFRa,$0.Pw0,(1.&40.)Pw1,(1.&40.)Pw2,(1.&40.)Plw,(1.&40.)Pb4,(1.&8.)Pk0,(1.&40.)Pk8,(1.&40.)Pk16,(1.&40.)Pk24,(1.&40.)Pj32,(2.(1.&8.))Pp,$0.Psjs,$9.PLc,(2.$4.)Pmc,P,(1.&40.)(5.(1.&8.))Pmoc,$6.Phc,(7.$8.VR,VHIA,)PENDx,$0.PRET,$0.PQ,P,$:.SpPt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Ps2v,(1.&40.)Ps3v,(1.&40.)Ps4v,(1.&40.)Ps5v,(1.&40.)Ps6v,(1.&40.)Ps7v,(1.&40.)Ps8v,(1.&40.)Ps9v,(1.&40.)Ps10v,(1.&40.)Ps11v,(1.&40.)P,(;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R2<.R2;.(<.(=.$0.$0.)(>.$0.$0.VPP,(?.VPP,+8.))(<.(=.$0.$0.)(>.$0.$0.VSIG,(?.VSIG,+<8.))(10.(=.$0.$0.))))R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(13.==R1=.)R1<.R1;.R1:.R19.)P,(18.R1?.R19.)P,(18.R1:.VEND,)P,(18.(?.(?.(19.$8.VR,VHIA,Vh,)R2=.)A1.VPHIsi,(1:.R1;.R21.))$1;.)P,(18.(?.(?.(1<.$8.VR,VHIA,Vh,)R2=.)A2.VFFRsi,(1:.R1<.R22.)(?.Vd,+1.))$1=.)P,(1>.$8.Vm,(1?.VR,)(20.$8.VR,VHIA,Vh,)(21.&40.Vs0,)(21.&40.Vsp,)Vd,)P,(22.(18.=R1=.)(16.R1=.(23.+2.+40.)))P,(14.$0.(15.R1>.+2.)=)P,Pm1,P,(1.&40.)(5.(1.&8.))Pmo1,$6.Ph1,(7.$8.VR,VHIA,)Pr,$0.Pp',$0.Pinext,$0.Psj',$9.Pnodes,(2.$0.)PPHIx,$0.PFFRx,$0.Py0,(1.&40.)Py1,(1.&40.)Py2,(1.&40.)Pya1,(1.&40.)Pya2,(1.&40.)Pya3,(1.&40.)Pya4,(1.&40.)Pya5,(1.&40.)Pya6,(1.&40.)Pya7,(1.&40.)Py3,(1.&40.)Py4,(1.&40.)Py5,(1.&40.)Py6,(1.&40.)P,(;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo0,VPP,VP,VEND,VBUF,VSIG,VDALG,Vlo,Vslo,Vbs,Vdtg,Vdpad,Vdlen,Vdq,R4<.R4;.(<.(=.$0.$0.)(>.$0.$0.VPP,(?.VPP,+8.))(<.(=.$0.$0.)(>.$0.$0.VSIG,(?.VSIG,+<8.))(10.(=.$0.$0.))))(?.R4:.R10.)(?.R49.R?.)R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R14.(13.R13.=R12.)(24.$4.(25.(26.$0.R11.))R3<.)R18.R17.R16.)P,(22.(16.-10000.R16.)(18.R16.=))P,(22.(18.R40.R16.)(18.R16.R3:.))P,P,(14.$0.R18.=)(16.R42.R18.)P,P,(27.(14.$0.R19.=))(14.(2.$0.)R16.(10.$0.))P,(28.$8.L,(2.$3.)$29.R1=.(24.$4.(24.$4.(25.(26.$0.R16.))R41.)VLB,)R18.R16.)P,(2:.$0.R17.)P,Px,$0.P,(11.$0.R1.R19.)PB,$0.Pk,$0.P,(11.(=.$0.$0.)(>.$0.$0.R2.R1.)(24.$4.R47.VLB,))(2;.(18.(?.R5.$2<.)R3.)(18.(?.R3.R2.)R5.))P,(18.(2=.(2>.$0.R19.))A1.VCNTsi,(1:.VEND,VP,))P,(18.R19.A1.VPHIsi,(1:.R41.R47.))P,(18.R19.A2.VFFRsi,(1:.R42.R48.)(?.Vd,+1.))P,P,(14.$0.R20.=)(22.(18.R1<.A1.VPHIsi,(1:.R20.R4:.))(22.(18.R1;.A2.VFFRsi,(1:.R20.R4:.)(?.Vd,+1.))(22.(18.(2=.(2>.$0.R1=.))A1.VCNTsi,(1:.R20.R4:.))(18.(?.R4:.+2.)R20.))))P,(2?.$8.(30.VR,)(24.$4.(24.$4.R48.VLB,)(31.(<.(=.$0.$0.)(>.$0.$0.R58.+40.)VLF,)))R57.(<.(=.$0.$0.)(>.$0.$0.VPP,(?.VPP,+8.))(<.(=.$0.$0.)(>.$0.$0.VSIG,(?.VSIG,+<8.))(10.(=.$0.$0.))))R47.R24.)(32.$8.(33.$8.VR,VHIA,R23.R24.)R43.(34.(35.(36.&40.R44.)(36.&40.R58.)Vgp,Vtp,R1;.R1:.R19.Vsp,(36.&40.R58.)(36.&40.R22.)R18.R17.R16.R15.R14.R13.R12.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R11.R10.R?.R>.)VF,(36.&40.R44.)Vfc,(37.(1.&40.))R25.(38.$8.)))(32.$8.(33.$8.VR,VHIA,R22.R23.)R1?.(34.(35.(36.&40.R20.)(36.&40.R34.)Vgp,Vtp,R1>.R1=.R1<.Vsp,(36.&40.R34.)(36.&40.VPP,)(36.&40.R21.)(36.&40.VSIG,)(36.&40.VDALG,)R1;.R1:.R19.R18.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R17.R16.R15.R14.)VF,(36.&40.$39.)Vfc,(37.(1.&40.))R24.(38.$8.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros D HpE HEE BUD BUDF UW RETR RETE KS. pose proof D as D0. gvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKsi0 NRT; lia).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0'.
    pose proof FRSH as FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 64 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ SIG 200 FB 64 FRSH CWS ltac:(clear; lia) ltac:(clear; lia) LOS) as APSG.
    pose proof (CNTsi_mono (ENDx - p) NB ltac:(clear - HpE HEE Hpc B1 B2; lia)) as CSm.
    pose proof (PHIsi_mono (ENDx - p) NB ltac:(clear - HpE HEE Hpc B1 B2; lia)) as PSm.
    pose proof (FFRsi_mono (ENDx - p) NB (d + 1) ltac:(clear - HpE HEE Hpc B1 B2; lia)) as FSm.
    pose proof (blocks_below_hm R HIA hc _ _ mc (Lc ++ LB) HHc ltac:(intros b Hb; exact Hb)) as BBc.
    destruct (BBc _ ltac:(apply in_or_app; right; exact BIN)) as [_ BCE]. cbn [fst snd] in BCE.
    assert (SUBc : forall b, In b (LB ++ fdata LF) -> In b ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; apply (fdata_cons_sub b [] FB 64 LF); exact Hb]. }
    assert (CWPc : client_wrange L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA hc) PP 8) by (rewrite HTc; eapply client_wrange_mono; [exact CWP| exact SUBc]).
    assert (CWSc : client_wrange L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA hc) SIG 200) by (rewrite HTc; eapply client_wrange_mono; [exact CWS| exact SUBc]).
    assert (CRDc : client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) lo DALG 24) by (eapply client_range_incl; [exact CRDA| exact SUBc]).
    assert (CRo : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((Lc ++ LB) ++ fdata ((FB, 64) :: LF)) sp1 a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0| exact SUBc]. }
    assert (INHq : In (FB, 24) ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))) by (apply in_or_app; right; cbn; left; reflexivity).
    assert (INDq : In (FB + 32, 64 - 40) ((Lc ++ LB) ++ fdata ((FB, 64) :: LF))) by (apply in_or_app; right; cbn; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA hc) (bv_unsigned sp) sp1 (d + 1)).
    { rewrite HSc.
      assert (UWa : uwc asegs mc (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES)| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STKsi0 NRT; lia].
        intros a Ha. cbn. split; [clear - Ha PPLO LOS SLO NS1 STKsi0 NRT; lia| split; [clear - Ha SGLO LOS SLO NS1 STKsi0 NRT; lia| exact I]]. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0']. }
    destruct (sshad_split asegs AL mc slo sp1 (bv_unsigned sp) SSc ltac:(clear - SP1 SLO SLOL NS1 STKsi0 NRT; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof SIGNER as SG'. unfold pkcs7_signer_stmtA in SG'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG' with (h := hc) (LB := Lc ++ LB) (LF := (FB, 64) :: LF) (PP := PP) (P := p) (END := ENDx) (BUF := BUF) (bs := bs) (S := SIG) (DALG := DALG)
                     (lo := lo) (slo := slo) (d := d + 1) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq) (sj := sjs); clear SG';
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold SIGNER_SIZE;
        first [ exact HHc | exact HK1 | exact PPc | exact ALP | exact PP0 | exact CWPc | exact PPLO | exact BYc | exact B47 | exact B5 | exact B30 | exact DPB
              | exact DAc | exact ALD | exact DA0 | exact CRDc | exact DALO | exact Q1 | exact Q2 | exact D2 | exact STlo | exact SSlo | exact SLOS | exact SLOL
              | exact MIc | exact TPV | exact UW1 | exact HpE | reflexivity
              | lazymatch goal with
                | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                | |- aobj _ _ _ _ PP 8 => exact (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OPP)
                | |- aobj _ _ _ _ DALG 24 => exact (aobj_cs_mono asegs AL _ _ _ _ _ HCSc ODA)
                | |- In (BUF, _) _ => apply in_or_app; right; exact BIN
                | |- BUF <= p => clear - B1 Hpc; lia
                | |- ENDx <= BUF + _ => clear - HEE B3; lia
                | |- dq + dlen <= _ => exact Q3
                | |- List.NoDup _ => exact (HMND _ _ _ _ HHc)
                | |- lo <= sp1 - STKsi => clear - SLO SP1 NS1 STKsi0 NRT; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD HVc; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF HFRc; lia
                | |- rw_cells _ _ SIG _ => exact CSG
                | |- SIG mod 8 = 0 => exact ALS
                | |- 0 < SIG => exact SG0
                | |- aobj _ _ _ _ SIG 200 => exact (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OSG)
                | |- client_wrange _ _ _ _ SIG 200 => exact CWSc
                | |- SIG + 200 <= lo => exact SGLO
                | |- SIG + 200 <= BUF \/ _ => exact DSB
                | |- PP + 8 <= SIG \/ _ => exact D1
                | |- DALG + 24 <= SIG \/ _ => exact D3
                end
              | match goal with |- ?g => idtac "SIGNER-PRE-LEFT:" g end ]. }
    try clear SG'.
    cbv beta. (intros ms2 mo2x dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 & mo3 & h3 & r & p' & inext & sj' & nodes
                    & E2 & Ea0 & Hr & MI3 & ST3 & SS3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT & HSUCC & PP3 & Hp' & HRP & CS3 & HNC & HND3 & HAP3 & HH3 & HRN).
    injection E2 as Ems Emo. subst ms2 mo2x ua0.
    rewrite ?(unsigned_lit sp1) in ST3, SS3, HP3 by exact SP1R. unfold SIGNER_SIZE in HP3.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET : word) by (symmetry; apply ret_pc_even; [exact RETR| exact RETE]).
    rewrite (app_assoc (SNAME (rev nodes)) Lc LB) in HH3, HNC.
    (* [comment removed for export] *)
    assert (CSHD : forall c, FB <= c < FB + 64 -> cshd R (Lc ++ LB) ((FB, 64) :: LF) sp1 (hstkhi asegs R HIA hc) c).
    { intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJs : forall a k, sp1 <= a -> disjoint_from [(PP, PP + 8); (SIG, SIG + 200)] a k).
    { intros a k H1. cbn. split; [clear - H1 PPLO LOS SLO SP1 NS1 STKsi0 NRT; lia| split; [clear - H1 SGLO LOS SLO SP1 NS1 STKsi0 NRT; lia| exact I]]. }
    apply (presA_shadow_cells_sh asegs R CS (Lc ++ LB) ((FB, 64) :: LF) sp1 sp1 (hstkhi asegs R HIA hc) [(PP, PP + 8); (SIG, SIG + 200)] mc m3 FB _ CSOK) in FSH;
      [| cbn [cells_size csize Nat.add length]; exact CFB | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP3 | cbn [cells_size csize Nat.add length]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in FHD; [| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INHq| clear; lia| clear; lia] | cbn; split; [clear - APP; lia| split; [clear - APSG; lia| exact I]] ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in G4; [| cbn [cells_size csize Nat.add length]; eapply client_range_block; [exact INDq| clear; lia| clear; lia] | cbn; split; [clear - APP; lia| split; [clear - APSG; lia| exact I]] ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in SShi; [| clear; lia| rewrite HSc; clear - HT TOP; lia].
    pose proof (sshad_merge asegs AL m3 slo sp1 (bv_unsigned sp) SS3 SShi ltac:(clear - SP1 SLOL SLO NS1 STKsi0 NRT; lia)) as SSm3. clear SS3 SShi.
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in DAc; [| cbn [cells_size csize Nat.add length buf_cells]; apply CRo; [exact DALO| exact CRDA]| cbn; split; [clear - D2; lia| split; [clear - D3; lia| exact I]] ].
    apply (presA_bytes_at0 asegs R _ _ _ _ _ _ mc m3 _ _ HP3) in BYc;
      [| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right]; split;
         [ eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia]
         | cbn; split; [clear - DPB; lia| split; [clear - DSB; lia| exact I]] ] ].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 PP 8 CSOK HP3) in OPP; [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| clear; lia]].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 SIG 200 CSOK HP3) in OSG; [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| clear; lia]].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 DALG 24 CSOK HP3) in ODA; [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy| right; split; [apply CRo; [exact DALO| exact CRDA]| clear; lia]].
    apply (presA_aobj0 asegs R CS _ _ _ _ _ _ mc m3 BUF n CSOK HP3) in OBUF;
      [| intros y Hy; rewrite HSc; eapply hcs_below_top; exact Hy
       | destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right]; split; [| clear; lia];
         eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; exact BIN| clear; lia| clear; lia] ].
    (* [comment removed for export] *)
    assert (PRES' : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X0 m m3).
    { ddestruct PRES as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
      eapply presA_trans; [exact P0|].
      assert (PQ1 : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA hc) [(SIG, SIG + 200); (PP, PP + 8)] mc m3).
      { eapply presA_weaken; [exact HP3| intros b Hb; apply in_or_app; right; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
      rewrite HSc in PQ1.
      eapply presA_weaken; [exact PQ1| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. clear - Hx. tauto. }
    clear PRES.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo3) _ _ _ (conj HK3 (mo_frame_refl mo3))).
    eapply (KS m3 mo3 h3 r p' inext sj' nodes (havol asegs R HIA h3 - havol asegs R HIA hc) (hfr asegs R HIA h3 - hfr asegs R HIA hc));
      [ | exact Hr | exact Hp' | exact HRP | exact HRN | exact HNC | exact HND3 | exact HAP3 | clear - HCNT CSm; lia | clear - HV3; lia | clear - HFR3; lia
        | (intros E0; ddestruct (HSUCC E0) as (U1 & U2 & U3 & U4); split; [clear - U1; lia| split; [clear - U2; lia| split; [exact U3| exact U4]]]) | exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP3) ].
    split; [exact HH3|]. split; [exact HK3|]. split; [eapply mo_frame_trans; [exact MFc| eapply mo_frame_trans; [exact MF1| exact MF3]]|].
    split; [rewrite HT3; exact HTc|]. split; [rewrite HS3; exact HSc|]. split; [rewrite HF3; exact HFc|].
    split; [intros y Hy; exact (HCS3 y (HCSc y Hy))|].
    split; [clear - HVc; lia|]. split; [clear - HFRc; lia|].
    split; [exact PRES'|].
    split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
    split; [exact FHD|]. split; [exact G4|]. split; [exact FSH|]. split; [exact SAVE|]. split; [exact RSL|]. split; [exact STb|]. split; [exact ST3|].
    split; [exact PP3|]. split; [clear - Hp' Hpc HpE HEE; lia|].
    split; [exact CS3|]. split; [reflexivity|].
    split; [exact DAc|]. split; [exact BYc|].
    split; [exact OPP|]. split; [exact OSG|]. split; [exact ODA|]. split; [exact OBUF|].
    split; [exact MI3|]. exact SSm3.
  Qed.
  End Call.
End Walk.
