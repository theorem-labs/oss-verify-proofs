(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_info P_rsa_parse_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_oid A_oid_pk_alg A_oid_ec_grp_algid
     A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_parse_A A_pk_parse_B A_pk_parse_C A_pk_parse_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pk_parse_E () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_D.DINV"; "WalkPKE.Call.DINV2"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"].


Section WalkPKE.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_PK.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_PK.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP END PKA lo STKk : Z) (P BUF : Z) (bs : list byte).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis STK0 : 176 + arl_need_smalloc R <= STKk.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis PKB : 0 <= PKA /\ PKA + 16 <= 2^64.
  Hypothesis ENDB : 0 <= END < 2^64.

  Local Notation BLEN := (Z.of_nat (length bs)).
  Local Notation X00 := [(PP, PP + 8); (PKA, PKA + 16)].
  Hypothesis HBS0 : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, BLEN) LB.
  Hypothesis BP : BUF <= P. Hypothesis PE : P <= END. Hypothesis EB : END <= BUF + BLEN.
  Hypothesis B47 : BUF + BLEN < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BL30 : BLEN < 2^30.
  Hypothesis PPAL : PP mod 8 = 0. Hypothesis PP0 : 0 < PP. Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PKAL : PKA mod 8 = 0. Hypothesis PK0 : 0 < PKA. Hypothesis PKLO : PKA + 16 <= lo.
  Hypothesis CWK : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PKA 16.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + BLEN <= PP.
  Hypothesis DKB : PKA + 16 <= BUF \/ BUF + BLEN <= PKA.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_PK in UARG; unfold A_SMALLOC_2_PK in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation F1 := (C1 (Z_to_bv 8 241)). Local Notation F2 := (C1 (Z_to_bv 8 242)). Local Notation F3 := (C1 (Z_to_bv 8 243)).
  Local Notation F8 := (C1 (Z_to_bv 8 248)). Local Notation Z0 := (C1 (Z_to_bv 8 0)). Local Notation P4 := (C1 (Z_to_bv 8 4)).
  Local Notation FSH0 :=
    [F1; F1; F1; F1;  F8; F8; F2; F2;  F8; F8; F8; F2;  F2; F2; F2; F2;  Z0; F2; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  P4; F2; P4; F3].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  Definition DINV2 (WX : list ivl) (FB sp1 : Z) (hq : HST asegs R HIA) (LBq : list blk) (sh : list cell) (kv : word) (p2 e1 : Z) (pk0 pk1 : word) (mm : mem) : Prop :=
    exists (w0 w1 w2 pc0 pc1 Lw kpad gv gpad : word) (pp p1v : Z) (ptag ppad plen : word),
      HM asegs R HIA hq LBq ((FB, 256) :: LF) mm
      /\ rw_cells asegs mm FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs mm (FB + 32) [C8 pc0; C8 pc1]
      /\ rw_cells asegs mm (FB + 64) [C8 Lw]
      /\ rw_cells asegs mm (FB + 96) [C4 ptag; C4 ppad; C8 plen; C8 (Z_to_bv 64 pp)]
      /\ rw_cells asegs mm (FB + 160) [C4 kv]
      /\ rw_cells asegs mm (FB + 160 + 4) [C4 kpad]
      /\ rw_cells asegs mm (FB + 176) [C4 gv]
      /\ rw_cells asegs mm (FB + 176 + 4) [C4 gpad]
      /\ rw_cells asegs mm (Z.shiftr FB 3 + al_sb AL) sh
      /\ rw_cells asegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs mm (sp1 + 8)
           [C8 (Z_to_bv 64 p1v); C8 (Z_to_bv 64 PKA); C8 (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL))]
      /\ rw_cells asegs mm (sp1 + 48) [C8 (Z_to_bv 64 FB)]
      /\ stk asegs mm sp1 (sp1 + 8)
      /\ stk asegs mm (sp1 + 32) (sp1 + 48)
      /\ stk asegs mm (sp1 + 56) (bv_unsigned sp + -104)
      /\ stk asegs mm lo sp1
      /\ mem_inv asegs mm
      /\ rw_cells asegs mm PP [C8 (Z_to_bv 64 p2)]
      /\ aobj asegs AL (hcs asegs R HIA hq) mm PP 8
      /\ rw_cells asegs mm PKA [C8 pk0; C8 pk1]
      /\ aobj asegs AL (hcs asegs R HIA hq) mm PKA 16
      /\ bytes_at asegs mm BUF bs
      /\ aobj asegs AL (hcs asegs R HIA hq) mm BUF BLEN
      /\ P <= p2 /\ p2 <= e1 /\ e1 <= END
      /\ P + 2 <= p1v /\ p1v <= p2
      /\ ((pp = 0 /\ bv_unsigned plen = 0 /\ ptag = Z_to_bv 64 0) \/ (BUF <= pp /\ P <= pp /\ pp + bv_unsigned plen <= e1))
      /\ presW asegs R HIA hq LB LF (bv_unsigned sp) (arl_stklo R) WX m mm
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="Type"] Lemma dinv2_of_dinv : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_E ()) "PFB,$2.Psp1,$2.Ph1,(20.$5.VR,VHIA,)Psh,(21.$:.)Pkv,(1.&40.)Pp2,$2.Pe1,$2.Pmm,P,(1.&40.)(22.(1.&8.))P,(23.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R8.R7.R6.R5.R4.R3.R2.R1.)(24.(6.(7.$2.$2.)(8.$2.$2.VPP,(=.VPP,+8.))(6.(7.$2.$2.)(8.$2.$2.VPKA,(=.VPKA,+10.))(<.(7.$2.$2.))))R9.R8.R7.VLB,R6.R5.R4.R3.(?.&40.=)(?.&40.=)R2.)")
(* [comment removed for export] *).
  Proof. intros. assumption. Qed.

  (* [comment removed for export] *)
  #[using="NS1 LF sp PP END PKA lo STKk P BUF bs STK0 SLO LFB PPB PKB BP PE EB PP0 PK0 PKLO DPK DPB DKB"] Lemma presA_weaken_cl : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_E ()) "PLBa,(21.$25.)PLBb,(21.$25.)PLFa,(21.$25.)PLFb,(21.$25.)PSP,$2.PSP',$2.PSSP,$2.PSSP',$2.PTP,$2.PTP',$2.PW,(21.$26.)PW',(21.$26.)Pmx,P,(1.&40.)(22.(1.&8.))Pmy,P,(1.&40.)(22.(1.&8.))P,(27.$5.VR,R>.R<.R:.R8.R6.R4.R2.R1.)P,Pb,$25.P,(28.$25.R1.R?.)(28.$25.R2.R11.)P,Pb,$25.P,(28.$25.R1.R>.)(28.$25.R2.R10.)P,(1;.R=.R<.)P,(1;.R<.R;.)P,(1;.R:.R;.)P,Px,$2.P,(29.(2:.VR,)(2;.$25.R14.(2<.R12.))R10.R1.)P,(2=.R;.R2.)(2=.R=.R3.)(27.$5.VR,R14.R12.R10.R>.R<.R:.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros LBa LBb LFa LFb SP SP' SSP SSP' TP TP' W W' mx my [Pp S] HB HF HS HSS HT HW. split.
    - intros a Ha Hc Ho. apply Pp; [exact Ha| | apply HW; [exact Hc| exact Ho]].
      destruct Hc as [H|[H|(b & Hb & Hr)]]; [left; lia| right; left; exact H| right; right].
      exists b. split; [|exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HB, Hb| right].
      eapply fdata_incl; eauto.
    - intros c Hc Hr. apply S; [|exact Hr].
      destruct Hc as [H|[(b & Hb & Hx)|[(b & Hb & Hx)|H]]]; [left; lia| right; left| right; right; left| right; right; right; exact H].
      + exists b; split; [apply HB, Hb| exact Hx].
      + exists b; split; [apply HF, Hb| exact Hx].
  Qed.

  (* [comment removed for export] *)
  #[using="NS1 PP END PKA lo STKk P BUF bs STK0 SLO LFB PPB PKB BP PE EB PP0 PK0 PKLO DPK DPB DKB"] Lemma presW_step : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_E ()) "PWX,(21.$26.)PFB,$2.Psp1,$2.Phq,(20.$5.VR,VHIA,)Ph2,(20.$5.VR,VHIA,)PLBq,(21.$25.)PW,(21.$26.)Pmc,P,(1.&40.)(22.(1.&8.))Pm2,P,(1.&40.)(22.(1.&8.))P,(1>.$5.VR,VHIA,R6.VLB,VLF,(13.&40.Vsp,)(1?.VR,)R9.Vm,R2.)P,(27.$5.VR,R5.(6.(7.$2.$2.)(8.$2.$2.R9.+100.)VLF,)R8.(1?.VR,)(2>.$5.VR,VHIA,R7.)R4.R3.R2.)P,(1;.R9.(13.&40.Vsp,))P,Pb,$25.P,(28.$25.R1.VLB,)(28.$25.R2.R9.)P,Px,$2.P,(29.(2:.VR,)(2;.$25.VLB,(2<.VLF,))(13.&40.Vsp,)R1.)P,(2=.R?.R2.)(2=.R:.R3.)P,Px,$2.P,(17.$5.VR,VHIA,R<.R1.)(17.$5.VR,VHIA,R<.R2.)P,(1=.$2.(2>.$5.VR,VHIA,R;.)(2>.$5.VR,VHIA,R<.))(1>.$5.VR,VHIA,R<.VLB,VLF,(13.&40.Vsp,)(1?.VR,)R10.Vm,R8.)")
(* [comment removed for export] *).
  Proof.
    intros WX FB sp1 hq h2 LBq W mc m2 PW HP HSP SUB HW HCS HS.
    apply (presW_hmono R HIA hq h2 LB LF _ _ _ m _); [| exact HCS| exact HS].
    ddestruct PW as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
    eapply presA_trans; [exact P0|].
    eapply presA_weaken_cl; [exact HP| exact SUB| intros b Hb; right; exact Hb| exact HSP| clear; lia| clear; lia| exact HW].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO BIN PPLO CWP PKLO CWK"] Lemma dinv2_presA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_E ()) "PWX,(21.$26.)PWX',(21.$26.)PFB,$2.Psp1,$2.Phq,(20.$5.VR,VHIA,)Ph2,(20.$5.VR,VHIA,)PLBq,(21.$25.)PLBp,(21.$25.)PLB2,(21.$25.)Psh,(21.$:.)Pkv,(1.&40.)Pp2,$2.Pe1,$2.Ppk0,(1.&40.)Ppk1,(1.&40.)Ppk0',(1.&40.)Ppk1',(1.&40.)PW,(21.$26.)Pmc,P,(1.&40.)(22.(1.&8.))Pm2,P,(1.&40.)(22.(1.&8.))P,(24.R14.R12.R11.R10.R>.R;.R:.R9.R8.R7.R6.R2.)P,(1=.$2?.(30.R<.)#20.)P,(3.(1;.(31.(13.&40.Vsp,)+;0.)R13.)(1;.R13.(31.(13.&40.Vsp,)+:0.)))P,(1=.$2.(32.R15.+40.)=)P,(33.VR,R12.VLF,R16.+100.)P,(1=.$2.(2>.$5.VR,VHIA,R15.)(2>.$5.VR,VHIA,Vh,))P,Pb,$25.P,(28.$25.R1.VLB,)(28.$25.R2.R15.)P,(27.$5.VR,R14.(6.(7.$2.$2.)(8.$2.$2.R19.+100.)VLF,)R18.(1?.VR,)(2>.$5.VR,VHIA,R17.)R:.R9.R8.)P,(4.$5.VR,VHIA,R17.R14.(6.(7.$2.$2.)(8.$2.$2.R1:.+100.)VLF,)R9.)P,Px,$2.P,(17.$5.VR,VHIA,R1:.R1.)(17.$5.VR,VHIA,R1:.R2.)P,(14.$5.R;.Vlo,R1;.)P,(15.$5.R<.)P,(9.$5.R=.VPKA,(6.$:.(;.R11.)(6.$:.(;.R10.)(<.$:.))))P,(1>.$5.VR,VHIA,R1<.VLB,VLF,(13.&40.Vsp,)(1?.VR,)R20.Vm,R>.)P,PA,$2.Pn,$2.P,(1;.R22.R2.)P,(1;.(=.R3.R2.)(=.R23.+100.))(34.R15.R4.R3.)P,PA,$2.Pn,$2.P,(1;.R22.R2.)(34.R15.R3.R2.)P,(34.R13.VPP,+8.)P,(34.R14.VBUF,(19.(1:.(1.&8.)Vbs,)))(24.R25.R24.R23.R21.R1>.R1=.R1<.R1;.R1:.R17.R16.R13.)")
(* [comment removed for export] *).
  Proof.
    intros WX WX' FB sp1 hq h2 LBq LBp LB2 sh kv p2 e1 pk0 pk1 pk0' pk1' W mc m2 D SHN SP1 F64 FRSHq ESq SUBq HP HH2 HCS2 ST2 MI2 HPKA2 PRES2 WF WS WP WB.
    ddestruct D as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HH & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MI
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1a & Hp1b & PPC & PRES).
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq LBq LF mc FB 256 lo HH eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS. change (256 - 40) with 216 in IND.
    assert (SSPq : arl_stklo R <= sp1) by (clear - LOS SLO STK0 NS1 SP1; lia).
    assert (TOPq : forall x, hcs asegs R HIA hq x -> x < hstkhi asegs R HIA hq) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (INHp : In (FB, 24) (LBp ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; cbn [fdata]; left; reflexivity).
    assert (INDp : In (FB + 32, 216) (LBp ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CRF : forall A n, FB + 32 <= A -> A + n <= FB + 248 -> client_range L (LBp ++ fdata ((FB, 256) :: LF)) sp1 A n).
    { intros A n H1 H2. eapply client_range_block; [exact INDp| clear - H1; lia| clear - H2; lia]. }
    assert (CRS : forall A n, sp1 <= A -> client_range L (LBp ++ fdata ((FB, 256) :: LF)) sp1 A n) by (intros A n H1; apply client_range_stack; exact H1).
    assert (SUBf : forall b, In b (LB ++ fdata LF) -> In b (LBp ++ fdata ((FB, 256) :: LF))).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBq; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]. }
    assert (CRPP : client_range L (LBp ++ fdata ((FB, 256) :: LF)) sp1 PP 8) by (eapply client_range_wsep; [exact CWP| exact SUBf| left; exact PPLO]).
    assert (CRPK : client_range L (LBp ++ fdata ((FB, 256) :: LF)) sp1 PKA 16) by (eapply client_range_wsep; [exact CWK| exact SUBf| left; exact PKLO]).
    assert (CRBUF : client_range L (LBp ++ fdata ((FB, 256) :: LF)) sp1 BUF BLEN).
    { eapply client_range_block; [apply in_app_iff; left; apply SUBq; exact BIN| clear; lia| clear; lia]. }
    unfold DINV2. dexists w0, w1, w2, pc0, pc1, Lw, kpad, gv, gpad, pp, p1v, ptag, ppad, plen.
    split; [exact HH2|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact FHD| eapply client_range_block; [exact INHp| clear; lia| cbn; clear; lia]| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LPKC| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LLEN| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LPAR| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LALGa| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LALGb| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LGIDa| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact LGIDb| apply CRF; cbn; clear; lia| apply WF; cbn; clear; lia]|].
    split.
    { eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hq) LBp ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hq) W mc m2 FB sh CSOKq);
        [rewrite SHN; eapply crange_sub; [exact CFB| clear; lia| clear; lia]| exact F8'| clear - F0; lia| exact HP| exact FSHX|].
      rewrite SHN. intros c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; clear - Hc; lia]. }
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact SAVE| apply CRS; clear - SP1; lia| apply WS; clear - SP1; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact SLOTS| apply CRS; clear; lia| apply WS; clear; lia]|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact SLOT48| apply CRS; clear; lia| apply WS; clear; lia]|].
    split; [eapply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact STlo| clear; lia| apply WS; clear; lia]|].
    split; [eapply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact STmid| clear; lia| apply WS; clear; lia]|].
    split; [eapply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact SThi| clear; lia| apply WS; clear; lia]|].
    split; [exact ST2|]. split; [exact MI2|].
    split; [eapply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact HPP| exact CRPP| exact WP]|].
    split; [eapply aobj_cs_mono; [exact HCS2|]; eapply (presA_aobj asegs R); [exact CSOKq| exact HP| exact OPP| exact CRPP| exact SSPq| exact TOPq]|].
    split; [exact HPKA2|].
    split; [eapply aobj_cs_mono; [exact HCS2|]; eapply (presA_aobj asegs R); [exact CSOKq| exact HP| exact OPKA| exact CRPK| exact SSPq| exact TOPq]|].
    split; [eapply (presA_bytes_at asegs R _ _ _ _ _ _ mc m2 _ _ HP); [exact HBS| exact CRBUF| exact WB]|].
    split; [eapply aobj_cs_mono; [exact HCS2|]; eapply (presA_aobj asegs R); [exact CSOKq| exact HP| exact OBUF| exact CRBUF| exact SSPq| exact TOPq]|].
    split; [exact Hp2a|]. split; [exact Hp2e|]. split; [exact HeE|]. split; [exact Hp1a|]. split; [exact Hp1b|]. split; [exact PPC| exact PRES2].
  Qed.
  End Call.
End WalkPKE.
