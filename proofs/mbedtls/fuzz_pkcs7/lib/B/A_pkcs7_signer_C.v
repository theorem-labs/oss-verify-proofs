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
     A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt A_pkcs7_signer_A A_pkcs7_signer_B
     A_pkcs7_signers_A A_pkcs7_signers_C A_pkcs7_signers_D A_pkcs7_signers_G.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pkcs7_signer_C () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_junk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Walk.Call.gvS"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_cells"; "RocqVerifyHarness.AgentSubmission.Spec.CrtStmts.SNAME"; "Stdlib.Lists.List.rev"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.NAME_SIZE"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Walk.CNTsi"; "Stdlib.ZArith.BinInt.Z.sub"; "Walk.PHIsi"; "Walk.FFRsi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signer_stmt.pkcs7_signer_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


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
  (* [comment removed for export] *)
  Variables (PHIn : Z -> Z) (FFRn : Z -> Z -> Z) (CNTn : Z -> Z) (STKn : Z).
  Hypothesis STKn0 : 0 <= STKn.
  Hypothesis PHIn_mono : forall n n', 0 <= n <= n' -> 0 <= PHIn n <= PHIn n'.
  Hypothesis FFRn_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRn n d <= FFRn n' d.
  Hypothesis CNTn_mono : forall n n', 0 <= n <= n' -> 0 <= CNTn n <= CNTn n'.
  (* [comment removed for export] *)
  Definition CNTsi (n : Z) : Z := CNTn n.
  Definition PHIsi (n : Z) : Z := PHIn n + CNTn n * AVOL_CALL.
  Definition FFRsi (n d : Z) : Z := FFRn n (d + 1) + CNTn n * Z.max 0 (fr_charge (d + 1)).   (* [comment removed for export] *)
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  (* [comment removed for export] *)
  Definition STKsg : Z := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signer_C ()) "(0.+=0.(1.(1.VSTKn,+1070.)(1.(0.+130.(2.VR,))(1.(0.+70.(3.VR,))(1.(4.VR,)(5.VR,))))))")
(* [comment removed for export] *).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 2)%nat.
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
  Hypothesis SLO : lo <= bv_unsigned sp - STKsg.
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
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold STKsg in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Local Notation NB := (END - P).
  Local Notation POST := (pkcs7_signer_postA asegs R HIA PHIsi FFRsi CNTsi h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP P END SIG NB lo slo d m mo0).
  Local Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
  Definition gvS (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 lw : word) (b4 : byte) (k0 k8 kE k16 k24 : word) (jA jB : list byte) (p : Z) (sgc : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop :=
    HM asegs R HIA hc (Lc ++ LB) ((FB, 64) :: LF) mc /\ HK asegs R HIA hc moc /\ mo_frame mo0 moc /\
    htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h /\ hflag asegs R HIA hc = hflag asegs R HIA h /\
    (forall x : Z, hcs asegs R HIA h x -> hcs asegs R HIA hc x) /\
    havol asegs R HIA hc <= havol asegs R HIA h + PHIa /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRa /\
    presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m mc /\
    bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 /\ sp1 mod 32 = 0 /\ FB mod 64 = 0 /\
    fresh_apart R LB LF FB 64 /\ crange (hcs asegs R HIA h) FB 64 /\
    rw_cells asegs mc FB [C8 w0; C8 w1; C8 w2] /\ rw_cells asegs mc (FB + 32) [C8 lw] /\
    rw_cells asegs mc (Z.shiftr FB 3 + al_sb (arl_AL R))
      [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 b4; C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] /\
    rw_cells asegs mc (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    rw_cells asegs mc sp1 [CB 24 jA; C8 k8; C8 k0; C8 kE; C8 k16; C8 k24; CB 16 jB; C8 (Z_to_bv 64 FB)] /\
    stk asegs mc (sp1 + 88) (bv_unsigned sp + -104) /\ stk asegs mc lo sp1 /\
    rw_cells asegs mc PP [C8 (Z_to_bv 64 p)] /\ P <= p <= END /\
    rw_cells asegs mc SIG sgc /\ cells_size sgc = 200%nat /\
    rw_cells asegs mc DALG (buf_cells dtg dpad dlen dq) /\ bytes_at asegs mc BUF bs /\
    aobj asegs (arl_AL R) (hcs asegs R HIA h) mc PP 8 /\ aobj asegs (arl_AL R) (hcs asegs R HIA h) mc SIG 200 /\
    aobj asegs (arl_AL R) (hcs asegs R HIA h) mc DALG 24 /\ aobj asegs (arl_AL R) (hcs asegs R HIA h) mc BUF (Z.of_nat (length bs)) /\
    mem_inv asegs mc /\ sshad asegs (arl_AL R) mc slo (bv_unsigned sp).
  Ltac gvS_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & FSH & SAVE & RSL & STb & STlo & PPc & Hpc & CSG & SZC & DAc & BYc & OPP & OSG & ODA & OBUF & MIc & SSc).
  #[using="Type"] Lemma gvS_mo : forall FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc moq,
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc -> HK asegs R HIA hc moq -> mo_frame moc moq ->
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moq hc.
  Proof.
    intros until moq. intros D HKq MFq. gvS_open D.
    split; [exact HHc|]. split; [exact HKq|]. split; [eapply mo_frame_trans; [exact MFc| exact MFq]|].
    repeat match goal with |- _ /\ _ => split end; first [assumption | exact (proj1 SP1) | exact (proj2 SP1) | exact (proj1 Hpc) | exact (proj2 Hpc) | match goal with |- ?g => idtac "GVSMO-LEFT:" g end].
  Qed.
  #[using="Type"] Lemma gvS_bud : forall FB sp1 W PHIa FFRa PHIa' FFRa' w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc,
    gvS FB sp1 W PHIa FFRa w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc -> PHIa <= PHIa' -> FFRa <= FFRa' ->
    gvS FB sp1 W PHIa' FFRa' w0 w1 w2 lw b4 k0 k8 kE k16 k24 jA jB p sgc Lc mc moc hc.
  Proof.
    intros until hc. intros D LP LQ. gvS_open D.
    split; [exact HHc|]. split; [exact HKc|]. split; [exact MFc|]. split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HCSc|].
    split; [clear - HVc LP; lia|]. split; [clear - HFRc LQ; lia|].
    repeat match goal with |- _ /\ _ => split end; first [assumption | exact (proj1 SP1) | exact (proj2 SP1) | exact (proj1 Hpc) | exact (proj2 Hpc) | match goal with |- ?g => idtac "GVSBUD-LEFT:" g end].
  Qed.
  (* [comment removed for export] *)
  #[using="SLO"] Lemma SLO' : lo <= bv_unsigned sp - A_pkcs7_signers_A.STKs R STKn.
  Proof. unfold A_pkcs7_signers_A.STKs. unfold STKsg in SLO. clear - SLO NS1 NAM0 STKn0. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKn NAM0 LFB PP0 CWP PPLO SG0 CWS SGLO DA0 SLOS SLOL SLO TOP SPH LOS"] Lemma ret_walkS : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signer_C ()) "PFB,$6.Psp1,$6.PW,(7.$8.)PPHIa,$6.PFFRa,$6.Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Plw,(9.&40.)Pb4,(9.&8.)Pk0,(9.&40.)Pk8,(9.&40.)PkE,(9.&40.)Pk16,(9.&40.)Pk24,(9.&40.)PjA,(7.(9.&8.))PjB,(7.(9.&8.))Pp,$6.Pinext,$6.Psj',$:.Pnodes,(7.$6.)Pmc,P,(9.&40.)(;.(9.&8.))Pmoc,$<.Phc,(=.$>.VR,VHIA,)Pr,$6.Pxra,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Ps3v,(9.&40.)Ps4v,(9.&40.)Ps5v,(9.&40.)Ps6v,(9.&40.)Ps7v,(9.&40.)Ps8v,(9.&40.)Ps11v,(9.&40.)P,(?.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(10.R1=.=R1<.)(11.(12.$6.R1;.))R1:.R19.R18.)P,(13.$>.L,(7.$14.)$15.R1;.(16.$17.(11.(12.$6.R1<.))VLB,)R1>.R1<.)P,(18.$6.R1=.)P,Px,$6.P,(19.$6.R1.R1?.)PB,$6.Pk,$6.P,(19.(1:.$6.$6.)(1;.$6.$6.R2.R1.)VLB,)(1<.(1=.(0.R5.$1>.)R3.)(1=.(0.R3.R2.)R5.))P,(1=.(1?.(20.$6.R1?.))(21.(22.VEND,VP,)))P,(1=.R31.(23.(22.VEND,VP,)))P,(1=.R31.(24.(22.VEND,VP,)Vd,))P,Px,$6.P,(25.(26.(1:.$6.$6.)(1;.$6.$6.VPP,(0.VPP,+8.))(26.(1:.$6.$6.)(1;.$6.$6.VSIG,(0.VSIG,+<8.))(27.(1:.$6.$6.))))R1.)(25.R36.R2.)P,(28.(29.-10000.R1?.)(1=.R1?.=))P,P,(2:.$6.R20.=)(29.VP,R28.)P,P,(2;.(2:.$6.R21.=))(2:.(7.$6.)R26.(27.$6.))P,P,(2:.$6.R22.=)(28.(1=.R38.(23.(22.R2:.VP,)))(28.(1=.R37.(24.(22.R2:.VP,)Vd,))(28.(1=.(1?.(20.$6.R27.))(21.(22.R2:.VP,)))(1=.(0.VP,+2.)R2:.))))(2<.$>.(2=.$>.VR,VHIA,$23.$24.$21.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VSIG,(22.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(2>.(2?.(30.R22.(31.&40.R3:.)Vgp,Vtp,R21.R20.R1?.Vsp,(31.&40.R3:.)(31.&40.R23.)R1>.R1=.R1<.R1;.R1:.R19.R18.(31.&40.R3;.)R13.R12.R11.R10.R?.R>.(31.&40.(0.(32.R3;.+3.)(33.(34.VR,))))R=.(31.&40.R3;.)R17.R16.R15.R14.)VF,(31.&40.+991?0.)Vfc,(35.(9.&40.))R26.(36.$>.))R25.))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros D HNC HND HAP CNT PHI FFR HW Hr Hrp Hrn SUCC. gvS_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    pose proof SLO' as SLOq.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NAM0 STKn0 NRT TOP HT; lia]).
    pose proof (fresh_apart_grow R HIA hc (SNAME (rev nodes)) LB LF mc FB 64 FRSH HHc) as FRSH3.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (SNAME (rev nodes) ++ LB) LF mc FB 64 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH & IND & AP & _ & F8 & FBLO & _ & _).
    (* [comment removed for export] *)
    chunk_to_stk RSL. stk_merge_into RSL STb.
    pose proof (presW_hmono R HIA h hc LB LF _ _ _ m mc PRES HCSc HSc) as PRESh.
    pose proof (presW_init_at R HIA hc _ _ (SNAME (rev nodes) ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 NAM0 STKn0 NRT; lia)) as PRES2.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply epi_walk with (h := h) (lo := lo) (slo := slo) (bs := bs) (PP := PP) (SIG := SIG) (DALG := DALG) (STKn := STKn)
                           (h3 := hc) (LBn := SNAME (rev nodes)) (m0 := m) (m2x := mc) (WA := W) (WB := []);
        first [ exact HHc | exact HCSc | exact PRESh | exact PRES2 | exact CFB
              | lazymatch goal with |- lo <= bv_unsigned sp - STKsg => exact SLO | |- _ < r < _ => clear - Hr; lia end
              | eassumption | reflexivity
              | match goal with |- ?g => idtac "RETS-EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)) as HPX9f.
    assert (HPX9 : heap_presx asegs L (SNAME (rev nodes) ++ LB) (bv_unsigned sp) [] mc m9).
    { eapply heap_presx_weaken; [exact HPX9f| intros b Hb; apply in_app_iff; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]. }
    assert (CRsp : forall a k, a + k <= lo -> client_range L (LB ++ fdata LF) lo a k -> client_range L ((SNAME (rev nodes) ++ LB) ++ fdata LF) (bv_unsigned sp) a k).
    { intros a k Hk CR0. eapply client_range_lower; [| exact Hk]. eapply client_range_incl; [exact CR0|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    unfold pkcs7_signer_postA.
    deexists 15. dexists m9, mo9, h4, r, p, inext, sj', nodes.
    split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hr|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
    split.
    { pose proof (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES9) as HPF. rewrite HSc in HPF. unfold SIGNER_SIZE.
      eapply presA_weaken; [exact HPF| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| exact HW]. }
    split; [rewrite E4top; exact HTc|]. split; [rewrite E4stk; exact HSc|]. split; [rewrite E4flag; exact HFc|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSc x Hx)|].
    split; [rewrite E4vol; clear - HVc PHI; lia|].
    split; [rewrite E4fr; clear - HFRc FFR; lia|].
    split; [exact CNT|].
    split; [intros Hr0; ddestruct (SUCC Hr0) as (SU1 & SU2 & SU3 & SU4); split; [rewrite E4vol; clear - HVc SU1; lia|]; split; [rewrite E4fr; clear - HFRc SU2; lia|]; split; [exact SU3| exact SU4]|].
    split; [eapply (presA_rw_cells asegs R); [exact (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)| exact PPc| apply CRsp; [exact PPLO| exact (client_range_of_w L _ _ _ _ _ CWP)]| exact I]|].
    split; [exact Hpc|]. split; [exact Hrp|].
    split; [eapply (presA_rw_cells asegs R); [exact (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)| exact CSG| cbn [cells_size csize Nat.add length signer_cells]; apply CRsp; [exact SGLO| exact (client_range_of_w L _ _ _ _ _ CWS)]| exact I]|].
    split.
    { eapply (name_chain_presx0 R mc m9 (SNAME (rev nodes) ++ LB) (SNAME (rev nodes) ++ LB) (bv_unsigned sp) []); [exact HNC| | exact HPX9| intros x _; exact I].
      intros x Hx. eapply (chain_nodes_in asegs); [exact HNC| exact Hx]. }
    split; [exact HND|]. split; [exact HAP|]. split; [exact HH4| exact Hrn].
  Qed.
  End Call.
End Walk.
