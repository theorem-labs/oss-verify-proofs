(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney MpiJourney2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp
     P_mpi_core_mul P_mpi_add_abs_W P_mpi_add_abs_C P_mpi_mul_stmt P_mpi_mul_int_W P_mpi_mul_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_mul_mpi_W () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.MpiJourney.XJ"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Spec.MpiJourney.BJ"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiJourney.JB"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "Corelib.Init.Datatypes.nat"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L61055709130.0L62756896884.2000001006SS1a1b". (* [comment removed for export] *)
Lemma sign_mulmod16 : forall a b, (b mod 2^64 * (a mod 2^64)) mod 2^16 = (a * b) mod 2^16.
Proof.
  intros a b. rewrite <- (Z.mod_mod_divide (b mod 2^64 * (a mod 2^64)) (2^64) (2^16)) by (exists (2^48); reflexivity).
  rewrite <- Z.mul_mod by (clear; lia). rewrite (Z.mod_mod_divide) by (exists (2^48); reflexivity). f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section W.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variables (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m1 : mem) (mo1 : Model) (h1 : HST psegs L HI) (LB1 : list blk) (lo : Z) (MSF : Z) (FRL : list cell)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own)
            (Aa sA nA pA : Z) (ys : list word) (padA : word) (ownA : limb_own)
            (Ba sB nB pB : Z) (zs : list word) (padB : word) (ownB : limb_own)
            (POST : config -> Prop).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation dA := (mkMPD Aa sA nA pA ys padA ownA).
  Local Notation dB := (mkMPD Ba sB nB pB zs padB ownB).
  Local Notation SPJ := (Z_to_bv 64 (bv_unsigned sp - 112)).
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 304 - hl_stack L.
  Hypothesis ACL0 : alloc_ceiling <= lo.
  Hypothesis FRSZ : Z.of_nat (cells_size FRL) = 112%Z.
  Hypothesis JCX : JC psegs L HI h1 LB1 m1 mo1 dX SPJ lo 0 [].
  Hypothesis XS0 : X + 16 <= lo \/ bv_unsigned sp <= X.
  Hypothesis JBA : JB psegs L LB1 m1 dX SPJ lo dA.
  Hypothesis JBB : JB psegs L LB1 m1 dX SPJ lo dB.
  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ psegs L HI h1 LB1 m1 mo1 dX SPJ lo 0 [] []).
  Local Notation XJ1 An cnt := (XJ psegs L HI h1 LB1 m1 mo1 dX SPJ lo 0 [] [(An, 4 * cnt)]).
  Local Notation BJE dE := (BJ psegs SPJ dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L1349803706.7200000PS1L2sp2lo3FRL4SLO23HLS3ACL3SPB1H". (* [comment removed for export] *)
  Lemma SPJU : bv_unsigned SPJ = bv_unsigned sp - 112.
  Proof. jc_open. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos. apply unsigned_lit. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition KCL_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Px8,(0.&40.)Px9,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.Pr,$8.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R6.R5.R4.R3.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R6.R5.R3.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R7.R6.R4.)P,(11.$2.R7.(<.(=.&40.Vsp,)+70.)VFRL,)P,(12.(13.$8.R5.=)(13.$8.R5.$14.))(15.$2.R8.VPOST,(16.(17.R20.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R23.R22.R21.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(;.&40.R6.)R12.R11.R10.Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(;.&40.+201?<.)Vfc,(18.(0.&40.))R9.(19.$2.)))")
(* [comment removed for export] *).
  Hypothesis KCL : KCL_stmt.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L22961730820.62000008S2sp3FRL". (* [comment removed for export] *)
  Lemma fr_presx : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "PLBp,(3.$4.)PXI,(3.$1:.)Pmc,P,(0.&40.)(5.(0.&8.))Pmc',P,(0.&40.)(5.(0.&8.))P,(1;.$2.VL,R4.(<.(=.&40.Vsp,)+70.)R3.R2.R1.)P,(11.$2.R3.(<.(=.&40.Vsp,)+70.)VFRL,)P,(1<.R5.(<.(=.&40.Vsp,)+70.)+70.)(11.$2.R4.(<.(=.&40.Vsp,)+70.)VFRL,)")
(* [comment removed for export] *).
  Proof.
    intros LBp XI mc mc' HP FR D. eapply heap_presx_rw_cells; [exact HP| exact FR| rewrite FRSZ; apply client_range_stack; lia| rewrite FRSZ; exact D].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L10257851201.7 L21516146488.2 L25721051894.2 L39280637297.0 L40362700714.0 L4112444482.2  L41149646033.11L4769765241.0  L49965254466.5 L49965663300.6 L53134281077.4 L5506491570.2  L59308587280.2 L59308664813.4 L6721511659.7  L8111968256.10 00000I00O00U00V00W00_01C01D01T01i02802@02F02U02n03DS2nE2pE2ws4LENE3NE13PE01KS1p2P0S1k2HKSSS2nE3NE1S1L2sp2lo4SLO22pE1n1p3HLS3ACL2PC3ESPSS1L2nE2pE3ACV2R3S1L4IMGC2nE2pE3ACV2I1S1L2lo4ACL03ACPS2nE3NE1S1q2HqS2nE2ws4LENE2ENS2nE2pE2ws4LENE3NE13PE01KS1L2nE2pE1n1p2PI2I02I1". (* [comment removed for export] *)
  Lemma rider_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "PEa,$8.PsE,$8.PnE,$8.PpE,$8.Pws,(3.(0.&40.))PpadE,(0.&40.)PownE,$1=.Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.Pn,$8.Pp,$8.Pxs,(3.(0.&40.))Pk,$8.P,(1>.$2.VL,VLB1,Vm1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,(:.R10.R?.R>.R=.R<.R;.R:.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R:.R9.R8.R7.(:.VX,R6.R5.R4.R3.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.R12.R11.R10.R?.R>.R=.R<.)R:.R9.(:.VX,R7.R6.R5.R4.VpadX,$1?.))P,(20.(21.=R4.)(21.R4.R11.))(20.(22.$2.R;.R11.(23.R10.))(20.(13.$8.(24.(25.(0.&40.)R10.))R12.)(20.(13.$8.(26.R11.+4.)=)(20.(12.(13.$8.R5.=)(27.=R11.))(20.(12.(21.(28.R11.(29.+4.R12.))R7.)(21.(28.R7.(29.+4.R8.))R11.))(20.(27.(28.R11.(29.+4.R12.))(2:.+2.+40.))(20.(12.(21.(28.R11.(29.+4.R12.))Vlo,)(21.(<.(=.&40.Vsp,)+70.)R11.))(20.(11.$2.R;.R14.(2;.$?.(2<.(;.&40.R11.))(2;.$?.(2=.(;.&40.R13.))(2;.$?.(2=.(;.&40.R12.))(2;.$?.(2>.R?.)(>.$?.))))))(20.(12.(13.$8.R13.+1.)(13.$8.R13.-1.))(20.(20.(21.=R12.)(21.R12.+2710.))(20.(27.=R14.)(20.(21.(28.R14.+10.)(2:.+2.+40.))(13.$8.(26.R14.+8.)=)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until k. intros JBE J BE HK. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1 XIN XPAL ARR1 P0 PC PI.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBE _ _ _ BE)) 8%nat. intros E0 E16 EAL LENE NRE ES OWNE0 OWNE1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BE))) 2%nat. intros FLt1 SGE. flat constr:(FLt1) 6%nat. flclear FLt1. intros CE _ _ _ _ OWE. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE, SGE, OWE. unfold mpi_cells in CE.
    pose proof BE as [_ ESS ESL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ESS, ESL.
    destruct ownE.
    - flat constr:((OWNE0 eq_refl)) 2%nat. intros EP EN. subst pE. assert (ws = []) as -> by (destruct ws; [reflexivity| exfalso; cbn [length] in LENE; clear - LENE EN; lia]).
      clear LENE. subst nE.
      split; [unfold bytes_at; rewrite u32s_length; cbn [length Nat.mul]; split; [clear; lia|]; split; [clear; lia|]; intros q Hq; exfalso; clear - Hq; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [left; clear - HK; lia|]. split; [left; clear - P0; lia|]. split; [clear; lia|]. split; [left; clear - ACL0 ACP; lia|].
      split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL].
    - flat constr:((OWNE1 ltac:(discriminate))) 6%nat. intros NE1 PE0 PE4 EBY ELS EIN. flat constr:((EIN eq_refl)) 2%nat. intros EIN1 _.
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ EIN1)) 5%nat. intros _ _ _ R3 _. cbn in R3.
      split; [exact EBY|]. split; [exact LENE|]. split; [exact PE4|]. split; [right; exact PE0|].
      split; [destruct (ESL eq_refl ltac:(discriminate)) as [D|D]; [right; exact D| left; exact D]|]. split; [clear - R3 ACV; lia|]. split; [exact ELS|].
      split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL].
    - flat constr:((OWNE1 ltac:(discriminate))) 6%nat. intros NE1 PE0 PE4 EBY ELS _. destruct OWE as (_ & _ & _ & _ & [ERO|[ESP E64]]).
      2: { (* [comment removed for export] *) rewrite ?SPJU in ESP.
           split; [exact EBY|]. split; [exact LENE|]. split; [exact PE4|]. split; [right; exact PE0|].
           split; [right; clear - ESP PC ACL SLO2 HLS; lia|]. split; [exact E64|]. split; [exact ELS|].
           split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL]. }
      pose proof (ERO 0 ltac:(clear - NE1; lia)) as RO0. rewrite Z.add_0_r in RO0.
      pose proof (bytes_at_bound _ _ _ _ EBY) as K. rewrite u32s_length in K.
      pose proof (ROIMG pE RO0 ltac:(clear - K PE0 LENE NE1; lia)) as I0.
      pose proof (ERO (4 * nE - 1) ltac:(clear - NE1; lia)) as RO1. pose proof (ROIMG (pE + (4 * nE - 1)) RO1 ltac:(clear - K PE0 NE1 LENE; lia)) as I1.
      split; [exact EBY|]. split; [exact LENE|]. split; [exact PE4|]. split; [right; exact PE0|].
      split; [clear - I0 I1 PI N1 NE1; lia|]. split; [clear - I1 IMGC ACV; lia|]. split; [exact ELS|].
      split; [exact CE|]. split; [exact SGE|]. split; [exact NRE|]. split; [exact E0|]. split; [exact E16| exact EAL].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@L10353688608.3  L10642801822.4  L10774442607.194L13087502261.191L13818909004.188L13818909004.199L13818909004.201L15472906570.16 L16256852529.177L16510474006.2  L16937867133.4  L2059982179.4   L2101813681.181 L21649833481.191L22223832499.5  L23100341967.177L23442366185.3  L25069632707.1  L25388449192.3  L26177051425.0  L2747762755.5   L27485105529.16 L3103242059.4   L31696670107.17 L32548716958.189L34966351808.5  L35889131411.3  L38903148377.4  L39365779620.187L39481665289.189L39481665289.197L39481665289.199L41852641444.187L4240987358.17  L43722738364.2  L4414369682.3   L45272757598.3  L48600061776.5  L50496520711.17 L50559615017.17 L52627813746.181L52630056116.182L52921867576.4  L5412464964.9   L54773791151.189L56919334946.5  L59435147825.177L59876101531.17 L59969787773.4  L60396289570.6  L61055709130.0  L61867903003.2  L62404682406.6  L66151427842.16 L66448237584.188L8704533520.188 L9271121718.195 00000:00H00f00g02i05407?07d08?08G08S08\09L09M09Z0:50:?0:B0:K0:L0:Z0;;0;F0;m0=[0=h0>20><0?b0A30BM0Cg0EM0F50F<0FF0FO0F]0GC0Gk0Ha0IW0Ib0J@0KE0KW0L20LY0Le0M70M80M@0MR0N30Ng0O[0P6S2nA1i3HI_S1n2xs4LEN12N1S2sp3FRL1X2Aa2ys2Ba2zs1p2xs2P0FS1L2sp2lo3FRL1X2Aa2pA2ys2Ba2pB2zs4SLO23XS01n1p2xs3HLS3ACL3SPB2XS2X03XAL4LEN12N14XPAL2P02PC3SXA3SXB2A02B03ASS3BSS2XP2HB5Ha_st5Hl_stS1L2sp2lo3FRL1X2Aa2pA2ys2Ba2pB2zs4SLO23XS01n1p2xs3HLS3ACL3SPB2XS2X03XAL4LEN12N14XPAL2P02PC3SXA3SXB2A02B03ASS3BSS2XP3xs'4LEN42HB5Ha_st5Hl_stS1L2sp2lo3FRL1X2Aa2pA2ys2Ba2pB2zs4SLO23XS01n1p2xs3HLS3ACL3SPB2XS2X03XAL4LEN12N14XPAL2P02PC3SXA3SXB2A02B03ASS3BSS2XP3xs'4LEN42HB5Ha_st5Hl_stS1L2sp2lo4SLO24ACL01i1j1n1p2HN3HLS2PCS2sp3FRL1X2Aa2ys2Ba2zs1p2xsS2sB3SGBS2Ba1n1p3BSSS1n1p1a1OS2sp3FRL1X2Aa2ys2Ba2zs1n1p2xs3SPB2X02N12P02A02B0FS2nB2pB1n1p1HS2sp3FRL1X2Aa2ys2Ba2zs1p2xsS2nA1i3HI_S1pS2nB1j2HJSS1i1j1n2HN3NR1S1L2sp2lo4SLO21i1j1n1p2HN3HLS1a1OS1X2nB2pB1HS1L2sp2lo2Aa4SLO21i1j1n1p2HN3HLS2AS3ASSS1L2sp2lo3FRL1X2Aa2pA2ys2Ba2pB2zs4SLO23XS01n1p2xs3HLS3ACL3SPB2XS2X03XAL2N14XPAL2P02PC3SXA3SXB2A02B03ASS3BSS2XPS2nA2pA1n1p1HS1X2Aa3SXAS1X1n1p2XPS1L2sp2lo3FRL1X2Aa2pA2ys2Ba2pB2zs4SLO21n1p2xs3HLS3ACL3SPB2X02N14XPAL2P02PC3SXB3OB42A02B03BAL2BS3BSS2XPS1L2sp2lo3FRL1X2Aa2ys2Ba2zs4SLO24FRSZ3XS01p2xs3HLS3SPB2X02P02A02B02HB5Ha_st5Hl_stS1L2sp2lo3FRL1X2Aa2ys2Ba2zs4SLO24FRSZ3XS01p2xs3HLS3SPB2X02P02A02B03xs'4LEN42HB5Ha_st5Hl_stS1L2sp2lo3FRL1X2Aa2ys2Ba2zs4SLO24FRSZ3XS01p2xs3HLS3SPB2X02P02A02B03xs'4LEN42HB5Ha_st5Hl_stS1L2sp2lo3FRL1X2Aa2pA2ys2Ba2pB2zs4SLO21n1p2xs3HLS3ACL3SPB2X02N14XPAL2P02PC3SXA3OA42A03AAL2AS2B03ASS2XPS1L2sp2lo2nA2pA4SLO21i1j1n1p2HN3HLS1H2H0S2sA2sBS1X2Ba3SXBS2nB1j2HJS1L1n1p3ACV2PCS1L2sp2lo1X4SLO23XS01i1j1n1p2HN3HLS2XPS1L2sp2lo2nB2pB4SLO21i1j1n1p2HN3HLS1H2H0S1L2sp3FRL1X2Aa2ys2Ba2zs1n1p2xs3SPB3ACV2X02N12PC2A02B0S1L2sp3FRL1X2Aa2ys2Ba2zs1n1p2xs3SPB3ACV2X02N12PC2A02B0S1X2nA2pA1HS1L2sp2lo4SLO24ACL01n1p3HLS2PCS1L2sp2lo3FRL1X2Aa2ys2Ba2zs4SLO21n1p2xs3HLS3ACL3SPB2X02N12P02PC2A02B0S1L2sp2lo4SLO23HLSS2sp3FRL1X2Aa2ys2Ba2zs1p2xsS1L2sp2lo2Ba4SLO21i1j1n1p2HN3HLS2BS3BSSS2Aa1n1p3ASSS1L2lo4ACL01n1p2PCSS2sA3SGAS1i1j1n2xs2HN4LEN1S1p2r04XPAL1q1r1H2H02q02H42sp3SPAS2sp3FRL1X2Aa2pA2ys2Ba2pB2zs1p2xs3SXB2HB5Ha_st5Hl_stS2sp3FRL1X2Aa2pA2ys2Ba2pB2zs1p2xs3SXA2HB5Ha_st5Hl_stS2sp3FRL1X2Aa2ys2Ba2zs1p2xs". (* [comment removed for export] *)
  Lemma mm_TAIL : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pj,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.Pn,$8.Pp,$8.Pxs,(3.(0.&40.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R8.R7.R6.R5.(:.VX,R4.R3.R2.R1.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R8.R7.(:.VX,R5.R4.R3.R2.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R9.R8.(:.VX,R6.R5.R4.R3.VpadX,$1?.))P,(11.$2.R9.(<.(=.&40.Vsp,)+70.)VFRL,)P,(20.(21.=R22.)(21.R22.VnA,))P,(20.(21.=R22.)(21.R22.VnB,))P,(21.(28.R24.R23.)R9.)(15.$2.R<.VPOST,(16.(17.R20.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R23.R22.R21.(;.&40.VX,)(;.&40.VBa,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(;.&40.VAa,)(;.&40.R25.)(;.&40.R24.)R17.R16.R15.R14.Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(;.&40.+201<0.)Vfc,(18.(0.&40.))R=.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs. intros J BA BB FRc HI_ HJ HN. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU. rewrite ?SPJU in *.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1 XIN XPAL ARR1 P0 PC PI.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof JBA as [MA0 OA CRA CRAL SXA]. flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    pose proof JBB as [MB0 OB CRB CRBL SXB]. flat constr:(OB) 5%nat. intros OB1 OB2 OB3 OB4 OB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 8%nat. intros A0 A16 AAL LENA NRA AS OWNA0 OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 8%nat. intros B0 B16 BAL LENB NRB BS OWNB0 OWNB1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BA))) 2%nat. intros (CEA & _) SGA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA, SGA. unfold mpi_cells in CEA.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat. intros (CEB & _) SGB. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB, SGB. unfold mpi_cells in CEB.
    pose proof BA as [_ ASS ASL]. pose proof BB as [_ BSS BSL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ASS, ASL, BSS, BSL.
    clear HH1 SOK1 HPX1 FR1.
    specialize (ASS eq_refl). specialize (BSS eq_refl). pose proof (XP1 eq_refl) as XP. rewrite Z.sub_0_r in ST1.
    pose proof (munch_refl [(p, p + 4 * n)] mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok psegs mc p xs 0 _ ARR1 ltac:(clear - N1 LEN1; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write psegs mc p xs 0 v ARR1 ltac:(clear - N1 LEN1; lia)) as ARR2 end.
    replace (p + 4 * 0) with (p + 0) in ARR2 by (clear; lia).
    clear ARR1. store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with ST2 : stk psegs m2 _ _, MI2 : mem_inv psegs m2 |- _ =>
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU WM MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2)
                    ltac:(intros a NO; left; destruct (outside_dec [(p, p + 4 * n)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                    ltac:(cbn; rewrite ?SPJU; clear - PC ACL0 SLO2 HLS; lia) ltac:(cbn; clear - XP; lia) ARR2
                    ltac:(rewrite upd_length; reflexivity)) as J2 end.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA MU WM ltac:(cbn; clear - ASS; lia) ltac:(intros AN; cbn; pose proof (ASL eq_refl AN); clear - H; lia)) as BA2.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB MU WM ltac:(cbn; clear - BSS; lia) ltac:(intros BN; cbn; pose proof (BSL eq_refl BN); clear - H; lia)) as BB2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA2, BB2.
    clear MU WM J JX BA BB MX1.
    (* [comment removed for export] *)
    pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with MI3 : mem_inv psegs m3, CX3 : rw_cells psegs m3 X _ |- _ =>
      pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J2 MU WM MI3 CX3 ltac:(left; reflexivity)) as J3 end.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3.
    assert (BA3 : BJE dA LBc m3 (mkMPD X 1 n p (upd xs (Z.to_nat 0) (Z_to_bv 64 0)) padX LHeap)).
    { pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA2 MU WM ltac:(cbn; clear - SXA; lia) ltac:(intros AN; cbn; pose proof (OA1 AN); clear - H; lia)) as K.
      destruct K as [k1 k2 k3]; constructor; assumption. }
    assert (BB3 : BJE dB LBc m3 (mkMPD X 1 n p (upd xs (Z.to_nat 0) (Z_to_bv 64 0)) padX LHeap)).
    { pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB2 MU WM ltac:(cbn; clear - SXB; lia) ltac:(intros BN; cbn; pose proof (OB1 BN); clear - H; lia)) as K.
      destruct K as [k1 k2 k3]; constructor; assumption. }
    clear MU WM J2 BA2 BB2.
    pose proof (heap_mok _ _ HI _ _ _ _ (xj_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J3)) as MK3.
    clear MI1 ST1 HT1 MF1 AD1 PD1 NS1 OUT1 FRS1 XP1 NM1.
    pose proof J3 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    clear HH1 SOK1 HPX1 FR1 MX1.
    flat constr:((rider_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i JBA J3 BA3 HI_)) 9%nat. intros ABY LENA' PA4 PAZ ASEP A64 ALS CEA3 _.
    flat constr:((rider_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j JBB J3 BB3 HJ)) 9%nat. intros BBY LENB' PB4 PBZ BSEP B64 BLS CEB3 _.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    zstep. zstep. zstep.
    pose proof P_mpi_core_mul_spec as SPc. unfold mpi_core_mul_stmt, P_MPI_CORE_MUL, MPI_CORE_MUL_STACK in SPc.
    eapply aevtM_cut_evt; [exact MK3| eapply SPc with (xs := upd xs (Z.to_nat 0) (Z_to_bv 64 0)) (ys := ys) (zs := zs) (an := i) (bn := j) (X := p) (A := pA) (B := pB) (lo := lo);
      rewrite ?SPJU, ?upd_length; try reflexivity; try eassumption|].
    - clear - HI_; lia. - clear - HJ; lia. - clear - HN NR1; lia. - clear - HN LEN1; lia. - rewrite LENA'; clear - HI_; lia. - rewrite LENB'; clear - HJ; lia.
    - rewrite LENA', LEN1. exact ASEP. - rewrite LENB', LEN1. exact BSEP.
    - clear - XPAL. Z.div_mod_to_equations. lia. - rewrite LEN1. clear - PC ACV; lia. - rewrite LENA'. exact A64. - rewrite LENB'. exact B64.
    - clear - SLO2 HLS; lia. - clear - SPA. Z.div_mod_to_equations. lia.
    - left. rewrite LEN1. clear - PC ACL0. lia. - rewrite LENA'. exact ALS. - rewrite LENB'. exact BLS.
    - cbv beta. intros ms' PO. unfold mpi_core_mul_post in PO.
      flat constr:(PO) 25%nat. flclear PO. intros z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 m4 xs' -> MU4 WM4 MI4 ARR4 LEN4 SK4 ST4.
      unfold MPI_CORE_MUL_STACK in MU4. rewrite ?SPJU in MU4, ST4.
      replace (ret_pc (Z_to_bv 64 131556)) with (Z_to_bv 64 131556) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      rewrite upd_length in LEN4.
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J3 MU4 WM4 MI4 ltac:(rewrite SPJU, Z.sub_0_r; exact ST4)
                    ltac:(intros a NO; destruct (outside_dec [(p, p + 4 * (i + j)); (bv_unsigned sp - 112 - 176, bv_unsigned sp - 112)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; rewrite ?SPJU; clear - O HN HI_ HJ SLO2 HLS; lia])
                    ltac:(cbn; rewrite ?SPJU; clear - PC ACL0 SLO2 HLS HN HI_ HJ; lia) ltac:(cbn; rewrite ?SPJU; clear - XP XS0 HN HI_ HJ SLO2 HLS; lia) ARR4
                    ltac:(rewrite LEN4, upd_length; reflexivity)) as J4.
      pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA3 MU4 WM4 ltac:(cbn; rewrite ?SPJU; clear - ASS AS HN HI_ HJ SLO2 HLS; lia) ltac:(intros AN; cbn; rewrite ?SPJU; pose proof (ASL eq_refl AN); pose proof (OA5 AN); clear - H H0 HN HI_ HJ SLO2 HLS; lia)) as BA4.
      pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB3 MU4 WM4 ltac:(cbn; rewrite ?SPJU; clear - BSS BS HN HI_ HJ SLO2 HLS; lia) ltac:(intros BN; cbn; rewrite ?SPJU; pose proof (BSL eq_refl BN); pose proof (OB5 BN); clear - H H0 HN HI_ HJ SLO2 HLS; lia)) as BB4.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA4, BB4.
      assert (BA4' : BJE dA LBc m4 (mkMPD X 1 n p xs' padX LHeap)) by (destruct BA4 as [k1 k2 k3]; constructor; assumption).
      assert (BB4' : BJE dB LBc m4 (mkMPD X 1 n p xs' padX LHeap)) by (destruct BB4 as [k1 k2 k3]; constructor; assumption).
      clear BA4 BB4. rename BA4' into BA4. rename BB4' into BB4.
      assert (FR4 : rw_cells psegs m4 (bv_unsigned sp - 112) FRL).
      { eapply rw_cells_transport; [exact FRc| exact MU4| exact WM4|]. cbn. rewrite FRSZ. clear - PC ACL0 SLO2 HLS HN HI_ HJ. lia. }
      assert (CX4 : rw_cells psegs m4 X [C8 (Z_to_bv 64 p); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 n); C4 padX]).
      { eapply rw_cells_transport; [exact CX1| exact MU4| exact WM4|]. cbn. rewrite ?SPJU. clear - XP XS0 HN HI_ HJ SLO2 HLS. lia. }
      assert (CEA4 : rw_cells psegs m4 Aa [C8 (Z_to_bv 64 pA); C2 (Z_to_bv 64 sA); C2 (Z_to_bv 64 nA); C4 padA]).
      { eapply rw_cells_transport; [exact CEA3| exact MU4| exact WM4|]. cbn. clear - ASS AS HN HI_ HJ SLO2 HLS. lia. }
      assert (CEB4 : rw_cells psegs m4 Ba [C8 (Z_to_bv 64 pB); C2 (Z_to_bv 64 sB); C2 (Z_to_bv 64 nB); C4 padB]).
      { eapply rw_cells_transport; [exact CEB3| exact MU4| exact WM4|]. cbn. clear - BSS BS HN HI_ HJ SLO2 HLS. lia. }
      clear MU WM J3 JX BA3 BB3 MI1 ST1 CX1 CEA3 CEB3 ARR2 FRc SPc MU4 WM4 SK4.
      clear ASEP BSEP A64 B64 ALS BLS PAZ PBZ ABY BBY PA4 PB4 AS BS PI XIN OA2 OA3 OA4 OA5 OB2 OB3 OB4 OB5 CRA CRAL CRB CRBL.
      pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl psegs m4) as WM.
      (* [comment removed for export] *)
      zstep. if_cases K9; zify_cond K9.
      + (* [comment removed for export] *)
        clear MU WM CEA4 CEB4. pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
        zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
        match goal with MI5 : mem_inv psegs m5, CX5 : rw_cells psegs m5 X _ |- _ =>
          pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J4 MU WM MI5 CX5 ltac:(left; reflexivity)) as J5 end.
        cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        eapply KCL; [exact J5| | | | left; reflexivity].
        * pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA4 MU WM ltac:(cbn; clear - SXA; lia) ltac:(intros AN; cbn; pose proof (OA1 AN); clear - H; lia)) as K.
          destruct K as [k1 k2 k3]; constructor; assumption.
        * pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB4 MU WM ltac:(cbn; clear - SXB; lia) ltac:(intros BN; cbn; pose proof (OB1 BN); clear - H; lia)) as K.
          destruct K as [k1 k2 k3]; constructor; assumption.
        * match goal with FR5 : rw_cells psegs m5 (bv_unsigned sp - 112) FRL |- _ => exact FR5 end.
      + (* [comment removed for export] *)
        zstep. rewrite sx16_small by (clear - SGA; lia). zstep. rewrite sx16_small by (clear - SGB; lia). zstep.
        replace (Z_to_bv 64 (sB mod 18446744073709551616 * (sA mod 18446744073709551616))) with (Z_to_bv 64 (sA * sB))
          by (apply Z_to_bv_eqm; change 18446744073709551616 with (2 ^ 64); rewrite <- (Z.mul_mod sB sA (2 ^ 64)) by (clear; lia); f_equal; clear; lia).
        assert (SP1 : sA * sB = 1 \/ sA * sB = -1) by (clear - SGA SGB; destruct SGA as [-> | ->]; destruct SGB as [-> | ->]; cbn; tauto).
        remember (sA * sB) as sg' eqn:ESG. clear ESG.
        destruct SP1 as [EP|EP]; rewrite EP.
        all: clear MU WM CEA4 CEB4; pose proof (munch_refl [(X, X + 16)] m4) as MU; pose proof (wmono_refl psegs m4) as WM.
        all: zstep; zstep.
        all: match goal with MI5 : mem_inv psegs ?mm, CX5 : rw_cells psegs ?mm X _ |- aevtM _ _ _ (MS _ _ _ _ _ ?mm _) =>
          first [ pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J4 MU WM MI5 CX5 ltac:(left; reflexivity)) as J5
                | pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ (-1) J4 MU WM MI5 CX5 ltac:(right; reflexivity)) as J5 ] end.
        all: cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
        all: eapply KCL; [exact J5| | | | left; reflexivity].
        all: try match goal with FR5 : rw_cells psegs _ (bv_unsigned sp - 112) FRL |- _ => exact FR5 end.
        all: try (pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA4 MU WM ltac:(cbn; clear - SXA; lia) ltac:(intros AN; cbn; pose proof (OA1 AN); clear - H; lia)) as K;
                  destruct K as [k1 k2 k3]; constructor; assumption).
        all: try (pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB4 MU WM ltac:(cbn; clear - SXB; lia) ltac:(intros BN; cbn; pose proof (OB1 BN); clear - H; lia)) as K;
                  destruct K as [k1 k2 k3]; constructor; assumption).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L15864777803.9L16937867133.4L2059982179.4 L22223832499.5L31166230855.7L32027975233.0L34966351808.5L38903148377.4L5412464964.9 L54324727969.0L57097980552.3L58948685323.3L59969787773.4L66928405.3   L68370415057.200000E00Q00Z00g01;01<01I01S02002102<02G02S02]02cS1L2sp2lo4ACL01n1p2PCS2Ba1n1p3BSSS1n1p1a1OS2nB2pB1n1p1HS1L1n1p3ACV2N12P02PCSS2nA2pA1n1p1HS1X1n1p2XPS1L2sp2lo4ACL01n1p3HLS3SLO2PCSS1n2xs4LEN1S1n2xs4LEN1S2Aa1n1p3ASSS1n3NR12N1S1n2N1". (* [comment removed for export] *)
  Lemma mm_MS : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pj,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.Pn,$8.Pp,$8.Pxs,(3.(0.&40.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R8.R7.R6.R5.(:.VX,R4.R3.R2.R1.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R8.R7.(:.VX,R5.R4.R3.R2.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R9.R8.(:.VX,R6.R5.R4.R3.VpadX,$1?.))P,(11.$2.R9.(<.(=.&40.Vsp,)+70.)VFRL,)P,(20.(21.=R20.)(21.R20.VnA,))P,(20.(21.=R20.)(21.R20.VnB,))P,(21.(28.R22.R21.)R9.)(15.$2.R<.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)(;.&40.R9.)R1=.(;.&40.(29.+4.R:.))R1<.R1;.R1:.R19.R18.(;.&40.VAa,)(;.&40.R23.)(;.&40.R22.)R17.R16.R15.R14.Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(;.&40.+201;8.)Vfc,(18.(0.&40.))R=.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs. intros J BA BB FRc HI_ HJ HN. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1 XIN XPAL ARR1 P0 PC PI.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    pose proof BA as [_ ASS ASL]. pose proof BB as [_ BSS BSL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ASS, ASL, BSS, BSL.
    specialize (ASS eq_refl). specialize (BSS eq_refl). pose proof (XP1 eq_refl) as XP.
    clear HH1 SOK1 HPX1 FR1 MX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep.
    pose proof P_memset_spec as SPm. unfold memset_stmt in SPm.
    assert (U1 : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; clear - P0 PC ACV N1; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (4 * n)) = 4 * n) by (apply unsigned_lit; clear - N1 NR1; lia).
    eapply aevtM_cut_evt; [exact MK1| eapply SPm; rewrite ?U1, ?U3; [replace (Z.to_nat (4 * n)) with (4 * length xs)%nat by (clear - LEN1; lia); apply u32arr_cells; exact ARR1| exact MI1]|].
    clear SPm. unfold memset_post. cbv beta. intros ms' PO.
    flat constr:(PO) 20%nat. flclear PO. intros z0 z1 z2 za1 za2 z3 z4 z5 z6 z7 z8 z9 z10 z11 m2 -> MU2 WM2 MI2 PA2.
    rewrite ?U1, ?U3 in MU2. rewrite ?U1, ?U3, ?(unsigned_lit 0) in PA2 by (clear; lia).
    replace (ret_pc (Z_to_bv 64 131520)) with (Z_to_bv 64 131520) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    change (0 mod 256) with 0 in PA2.
    assert (ARR2 : u32arr psegs m2 p (repeat (Z_to_bv 64 0) (Z.to_nat n))).
    { eapply u32arr_of_cells; [exact PA2|]. rewrite u32s_repeat0. f_equal. clear - N1; lia. }
    assert (ST2 : stk psegs m2 lo (bv_unsigned sp - 112)).
    { eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. clear - PC ACL0 SLO HLS. lia. }
    pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2)
                  ltac:(intros a NO; left; destruct (outside_dec [(p, p + 4 * n)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                  ltac:(cbn; rewrite ?SPJU; clear - PC ACL0 SLO HLS; lia) ltac:(cbn; clear - XP; lia) ARR2 ltac:(rewrite repeat_length; clear - LEN1; lia)) as J2.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA MU2 WM2 ltac:(cbn; clear - ASS; lia) ltac:(intros AN; cbn; pose proof (ASL eq_refl AN); clear - H; lia)) as BA2.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB MU2 WM2 ltac:(cbn; clear - BSS; lia) ltac:(intros BN; cbn; pose proof (BSL eq_refl BN); clear - H; lia)) as BB2.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA2, BB2.
    assert (BA2' : BJE dA LBc m2 (mkMPD X sg n p (repeat (Z_to_bv 64 0) (Z.to_nat n)) padX LHeap)) by (destruct BA2 as [k1 k2 k3]; constructor; assumption).
    assert (BB2' : BJE dB LBc m2 (mkMPD X sg n p (repeat (Z_to_bv 64 0) (Z.to_nat n)) padX LHeap)) by (destruct BB2 as [k1 k2 k3]; constructor; assumption).
    assert (FR2 : rw_cells psegs m2 (bv_unsigned sp - 112) FRL).
    { eapply rw_cells_transport; [exact FRc| exact MU2| exact WM2|]. cbn. rewrite FRSZ. clear - PC ACL0 SLO HLS. lia. }
    eapply mm_TAIL; [exact J2| exact BA2'| exact BB2'| exact FR2| exact HI_| exact HJ| exact HN].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L23100341967.135L24912882372.1  L27847860010.0  L38436634709.0  L38852636021.0  L46239897481.134L53258523172.3  L61929606957.13400000=00@00A00B00C00D00N00aS2sp3FRL1X2xsS1nSSSFS1n3NR12N1S2sp3FRL1X1n2xs3NR1". (* [comment removed for export] *)
  Lemma mm_FIN : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pj,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.Pn,$8.Pp,$8.Pxs,(3.(0.&40.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R8.R7.R6.R5.(:.VX,R4.R3.R2.R1.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R8.R7.(:.VX,R5.R4.R3.R2.VpadX,$1?.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R9.R8.(:.VX,R6.R5.R4.R3.VpadX,$1?.))P,(11.$2.R9.(<.(=.&40.Vsp,)+70.)VFRL,)P,(20.(21.=R21.)(21.R21.VnA,))P,(20.(21.=R21.)(21.R21.VnB,))P,(21.(28.R23.R22.)R9.)(15.$2.R<.VPOST,(16.(17.R1?.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R22.R21.R20.(;.&40.VX,)(;.&40.VBa,)R1>.(;.&40.R:.)R1=.R1<.R1;.R1:.R19.R18.(;.&40.VAa,)(;.&40.R24.)(;.&40.R23.)R17.R16.R15.R14.Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(;.&40.+201:<.)Vfc,(18.(0.&40.))R=.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs. intros J BA BB FRc HI_ HJ HN. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 3%nat. intros _ N1 _.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    clear HH1 SOK1 HPX1 FR1 ST1 OUT1 FRS1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep.
    replace ((n ≪ 48 mod 18446744073709551616) ≫ 46) with (4 * n)
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); rewrite Z.mod_small by (clear - N1 NR1; lia);
          change (2 ^ 48) with (4 * 2 ^ 46); rewrite Z.mul_assoc, Z.div_mul by (clear; lia); clear; lia).
    eapply mm_MS; [exact J| exact BA| exact BB| exact FRc| exact HI_| exact HJ| exact HN].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L13917980321.0  L15608972571.2  L22575357144.15 L22717164081.0  L22964727664.1  L23100341967.171L23100341967.177L26295570611.15 L31165791186.177L39481665289.177L39481665289.178L40823183341.15 L46756382136.176L49578233423.171L59308546384.3  L59308633593.6  L61929803692.142L62650482766.5  L6753818301.15  00000100700D00E00I00Y00i01A01a02b03c03d04I04Y04b04m05@05M05NSS1n2KNS1L2sp2lo3SLOSS2spS2sp3FRL1X2xs2AnS2sp3FRL1X2xs2AnS1L2HI2sp2h12hc4HTOP3HT1S2sp3FRL1X1p2xs3SPB2X02EP2An3An0S1L2sp2lo3FRL1X4SLO24FRSZ3XS02xs3HLS3SPB2X02An3An02HB5Ha_st5Hl_stS1L2sp2lo3FRL1X4SLO24FRSZ3XS02xs3HLS3SPB2X02An3An02HB5Ha_st5Hl_stSS1L2sp3FRL1X2xs3SPB3ACV2X02An3An03AnCS2sp3FRL1X2xs2AnS1n2KN2N1S2An3An02KZS2sp3FRL1X1n2xs3NR1S1i1j1n2HN2KNS". (* [comment removed for export] *)
  Lemma mm_L0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pj,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.Pn,$8.Pp,$8.Pxs,(3.(0.&40.))Pown,$1=.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R9.R8.R7.R6.(:.VX,R5.R4.R3.R2.VpadX,R1.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R9.R8.(:.VX,R6.R5.R4.R3.VpadX,R2.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R:.R9.(:.VX,R7.R6.R5.R4.VpadX,R3.))P,(11.$2.R:.(<.(=.&40.Vsp,)+70.)VFRL,)P,(20.(21.=R21.)(21.R21.VnA,))P,(20.(21.=R21.)(21.R21.VnB,))P,(21.(28.R23.R22.)R:.)(15.$2.R=.VPOST,(16.(17.R1?.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R22.R21.R20.(;.&40.VX,)(;.&40.VBa,)R1>.(;.&40.R;.)R1=.R1<.R1;.R1:.R19.R18.(;.&40.VAa,)(;.&40.R24.)(;.&40.R23.)(;.&40.-10.)R17.R16.R15.Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(;.&40.+201:8.)Vfc,(18.(0.&40.))R>.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until own. intros J BA BB FRc HI_ HJ HN. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NR1; lia).
    - (* [comment removed for export] *)
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso. flat constr:((OWN1 ltac:(discriminate))) 3%nat. intros _ N1 _. clear - N1 KN; lia. }
      subst own. flat constr:((OWN0 eq_refl)) 2%nat. intros EP _.
      zstep. zstep. zstep.
      replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
      eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := 1) (sz := 4) (lo := lo);
        rewrite ?SPJU; try eassumption; try reflexivity; clear - SLO HLS ACL ACP HTOP HT1 NR1 SPB; try lia | ].
      intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo'.
      rewrite ?SPJU in PO.
      flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HPc h2 HT2 RES2.
      replace (ret_pc (Z_to_bv 64 131696)) with (Z_to_bv 64 131696) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
      clear MU WM.
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp - 112) FRL).
      { eapply (heap_pres_rw_cells psegs L); [exact HPc| exact FRc| rewrite FRSZ; apply client_range_stack; clear; lia]. }
      destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
      { (* [comment removed for export] *)
        pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPc) HT2 HH2) as J2.
        pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
        pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
        eapply KCL; [exact J2| | | exact FR2| right; reflexivity].
        - eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA); [exact J| exact BA| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2].
        - eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB); [exact J| exact BB| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
      replace (1 * 4) with (4 * 1) in * by (clear; lia).
      destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPc) HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - KN; lia)) as [J2 F2].
      assert (BA2 : BJE dA LBc m2 (mkMPD X sg n p xs padX LNull)).
      { eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA); [exact J| exact BA| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
      assert (BB2 : BJE dB LBc m2 (mkMPD X sg n p xs padX LNull)).
      { eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB); [exact J| exact BB| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
      flat constr:(HBA) 5%nat. intros An0 An16 _ AnC AnI. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1 CX1 AD1 PD1 FRc.
      pose proof J2 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *.
      flat constr:(MX1) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV; lia|].
      zstep. zstep. if_cases KP; zify_cond KP; [| exfalso; apply KP; rewrite EP; reflexivity].
      pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      clear HH1 HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
      pose proof JBA as [_ _ _ _ SXA]. pose proof JBB as [_ _ _ _ SXB]. cbn [md_addr] in SXA, SXB.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ D2 BA2 MU WM) as BA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ D2 BB2 MU WM) as BB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BB5.
      zstep. zstep. replace (Z_to_bv 64 4) with (Z_to_bv 64 (4 * 1)) by reflexivity.
      match goal with FR5 : rw_cells psegs m5 (bv_unsigned sp - 112) FRL |- _ =>
        eapply mm_MS; [exact J5| exact BA5| exact BB5| exact FR5| exact HI_| exact HJ| clear - HN KN; lia] end.
    - (* [comment removed for export] *)
      assert (EO : own = LHeap).
      { destruct own; [(flat constr:((OWN0 eq_refl)) 2%nat; intros _ N0); exfalso; exact (KN N0)| reflexivity| exfalso; exact (NS1 eq_refl)]. }
      subst own. eapply mm_FIN; [exact J| exact BA| exact BB| exact FRc| exact HI_| exact HJ| exact HN].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@L10685100449.0  L12153567628.2  L1237581405.9   L1597150190.18  L16596701601.0  L17843842630.12 L22575357144.22 L22798551387.3  L22964727664.1  L23100341967.170L23100341967.175L23100341967.204L24873264023.142L25033945976.177L25044352195.203L25046316159.142L2606027435.4   L26295570611.22 L28330171465.1  L31413597529.12 L31610334574.1  L31622393865.10 L32431276449.0  L33323889460.2  L37040968109.12 L37522049195.22 L38218545178.3  L38232090108.10 L39172636981.0  L39443110026.7  L39481665289.176L39481665289.177L39481665289.210L39481665289.211L40823183341.22 L41217018961.5  L43785151157.6  L45080762910.2  L46754389927.12 L46756382136.174L48154966246.175L48155112051.7  L49578233423.170L49578233423.204L59308633593.13 L59308972243.3  L64934269637.2  L67601363691.1  L68516385196.12 L8593487581.22  00000100600W01?01@01W01d02102502I02Y03D03m04W05F05[05k06C06H06_06`07A07B07G07]07o08008=08>08W09\0:e0<M0=l0=m0>=0>S0>[0?>0@30@40@M0@a0AL0AW0Ab0Ak0B00BF0BOSS1i1jS1L2sp2lo4ACL03nXc3pXc3HLS3SLO2PCS1L2sp2lo4ACL01i1j3nXc3HLS3SLO2KG2An3AnCSS2nA2pA1i1j3nXc2KG2An1HS1L2sp2lo3SLOS3nXc3NR13N1'S2spS2sp3FRL1X3pXc2xs2AnS2sp3FRL1X2xs2AnS2sp3FRL1X1i1j3nXc3pXc2xs2An4SLEN4DLEN4ZLENS2sp3FRL1X2nA2nB1i1j2xs3HI_2HJ3HIJ3SPB2X0S2sp3FRL1X1i1j3nXc3pXc2xs3NR12An4SLEN4DLENS2sp3FRL1X1i1j3nXc3pXc2xs3NR12An4SLEN4DLEN4ZLENS2sp3FRL1X3nXc2xs3NR1S3nXc3pXc2An3SEPS1L2HI2sp2h12hc4HTOP3HT1S3nXcS2nB2pB1i1j3nXc2KG2An1HFS1L2sp2lo3SPA3HLS3ACL3SLO3SPB3ACPSS1i1jS2Aa1i1j3nXc2KG2An3ESAS2nA2nB1i1j3HI_2HJFS1L2sp2lo3SLOSS1L3nXc3pXc3ACV3N1'2P02PCS1L2sp2lo3FRL1X4SLO24FRSZ3XS03pXc2xs3HLS3SPB2X02An3An02HB5Ha_st5Hl_stS1L2sp2lo3FRL1X4SLO24FRSZ3XS01i1j3pXc2xs3HLS3SPB2X02An3An02HB5Ha_st5Hl_stS1L2sp2lo3FRL1X4SLO24FRSZ3XS01i1j3nXc3pXc2xs3HLS3SPB2X04LEN12An3An03N1'2P04SLEN4DLEN4ZLEN2HB5Ha_st5Hl_stS1L2sp2lo3FRL1X4SLO24FRSZ3XS01i1j3nXc3pXc2xs3HLS3SPB2X02An3An02P04SLEN4DLEN4ZLEN2HB5Ha_st5Hl_stSS1i1j3nXc3HIJ2KGS1L2HI2sp2h14HTOP4SPJUS3nXc2AnS1L2nA2nB1i1j3HI_2HJ3ACV2An3An03AnCS1L2sp3FRL1X1i1j3nXc2xs3SPB3ACV2X04LEN12KG2An3An03AnCFS1L3nXc3pXc3ACV3N1'2P02PCS2sp3FRL1X3pXc2xs2AnS2sp3FRL1X1i1j3nXc3pXc2xs2An4SLEN4DLEN4ZLENS2An3An02KZS3pXc2KP2P0S3nXc3NR1S3nXcS2Ba1i1j3nXc2KG2An3ESBS1i1j3HIJ". (* [comment removed for export] *)
  Lemma mm_G : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pj,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.Psg,$8.PnXc,$8.PpXc,$8.Pxs,(3.(0.&40.))Pown,$1=.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R9.R8.R7.R6.(:.VX,R5.R4.R3.R2.VpadX,R1.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R9.R8.(:.VX,R6.R5.R4.R3.VpadX,R2.))P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R:.R9.(:.VX,R7.R6.R5.R4.VpadX,R3.))P,(11.$2.R:.(<.(=.&40.Vsp,)+70.)VFRL,)P,(20.(21.=R21.)(21.R21.VnA,))P,(20.(21.=R21.)(21.R21.VnB,))P,(21.(28.R23.R22.)+2710.)(15.$2.R=.VPOST,(16.(17.R1?.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R22.R21.R20.(;.&40.VX,)(;.&40.VBa,)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(;.&40.VAa,)(;.&40.R24.)(;.&40.R23.)(;.&40.-10.)(;.&40.(28.R24.R23.))R16.R15.Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(;.&40.+20154.)Vfc,(18.(0.&40.))R>.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until own. intros J BA BB FRc HI_ HJ HIJ. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU as SPJU.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof JBA as [_ _ _ _ SXA]. pose proof JBB as [_ _ _ _ SXB]. cbn [md_addr] in SXA, SXB.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NR1; lia).
    zstep. if_cases KG; zify_cond KG; rewrite ?Z.mod_small in KG by (clear - NR1 HI_ HJ HIJ; lia).
    { (* [comment removed for export] *) eapply mm_L0; [exact J| exact BA| exact BB| exact FRc| exact HI_| exact HJ| exact KG]. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := i + j) (sz := 4) (lo := lo);
      rewrite ?SPJU; try eassumption; try reflexivity; clear - SLO HLS ACL ACP HTOP HT1 HI_ HJ HIJ NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo'.
    rewrite ?SPJU in PO.
    flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HPc h2 HT2 RES2.
    replace (ret_pc (Z_to_bv 64 131432)) with (Z_to_bv 64 131432) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    assert (FR2 : rw_cells psegs m2 (bv_unsigned sp - 112) FRL).
    { eapply (heap_pres_rw_cells psegs L); [exact HPc| exact FRc| rewrite FRSZ; apply client_range_stack; clear; lia]. }
    assert (BA2 : BJE dA LBc m2 (mkMPD X sg nXc pXc xs padX own)).
    { eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA); [exact J| exact BA| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
    assert (BB2 : BJE dB LBc m2 (mkMPD X sg nXc pXc xs padX own)).
    { eapply (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB); [exact J| exact BB| rewrite SPJU, Z.sub_0_r; exact HPc| exact MI2]. }
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPc) HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply KCL; [exact J2| exact BA2| exact BB2| exact FR2| right; reflexivity]. }
    (* [comment removed for export] *)
    replace ((i + j) * 4) with (4 * (i + j)) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ltac:(rewrite SPJU, Z.sub_0_r; exact ST2) MF2 ltac:(rewrite SPJU, Z.sub_0_r; exact HPc) HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - KG HIJ; lia)) as [J2 F2].
    flat constr:(HBA) 5%nat. intros An0 An16 _ AnC AnI. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1 CX1 AD1 PD1 FRc BA BB.
    pose proof J2 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. rewrite Z.sub_0_r in ST1.
    flat constr:(MX1) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV HIJ HI_ HJ; lia|].
    zstep. zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso. flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1' _ _ _ P0 PC _. rewrite Z.mod_small in KP by (clear - N1' P0 PC ACV; lia). clear - KP P0. lia. }
      subst own. pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
      flat constr:((OWN0 eq_refl)) 2%nat. intros EP EN.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      clear HH1 HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ D2 BA2 MU WM) as BA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ D2 BB2 MU WM) as BB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BB5.
      zstep. zstep.
      match goal with FR5 : rw_cells psegs m5 (bv_unsigned sp - 112) FRL |- _ =>
        eapply mm_FIN; [exact J5| exact BA5| exact BB5| exact FR5| exact HI_| exact HJ| clear; lia] end. }
    (* [comment removed for export] *)
    assert (EO : own = LHeap).
    { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. flat constr:((OWN0 eq_refl)) 2%nat. intros EP _. apply KP. rewrite EP. reflexivity. }
    subst own. flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1' XIN XPAL _ P0 PC PI.
    flat constr:((xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl)) 9%nat. intros SBY SLEN DST DLEN SEP _ _ _ _.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
    clear HH1 HH2 HNEW SOK1 FR1 HPX1.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof P_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV HIJ HI_ HJ; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1'; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (nXc * 4)) = nXc * 4) by (apply unsigned_lit; clear - N1' NR1; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (nXc * 4)) with (4 * length (firstn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat (i + j)))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    flat constr:(PO) 21%nat. flclear PO. intros z0 z1 z2 za1 za2 z3 z4 z5 z6 z7 z8 z9 z10 z11 m3 E MUd WMd MI3 PA3 _. subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 131464)) with (Z_to_bv 64 131464) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + nXc * 4) with (An + 4 * nXc) in MUd by (clear; lia). replace (Z.to_nat (nXc * 4)) with (Z.to_nat (4 * nXc)) in PA3 by (clear; lia).
    flat constr:((xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3)) 2%nat. intros J3 F3. cbn [md_limbs md_n] in F3.
    flat constr:((bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ J2 F2 BA2)) 2%nat. intros ESA ELA. cbn [md_addr md_own md_p md_n] in ESA, ELA.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ BA2 MUd WMd ltac:(cbn; clear - ESA HIJ HI_ HJ KG; lia) ltac:(intros BN; cbn; pose proof (ELA BN); clear - H HIJ HI_ HJ KG; lia)) as BA3.
    flat constr:((bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ J2 F2 BB2)) 2%nat. intros ESB ELB. cbn [md_addr md_own md_p md_n] in ESB, ELB.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ BB2 MUd WMd ltac:(cbn; clear - ESB HIJ HI_ HJ KG; lia) ltac:(intros BN; cbn; pose proof (ELB BN); clear - H HIJ HI_ HJ KG; lia)) as BB3.
    assert (FR3 : rw_cells psegs m3 (bv_unsigned sp - 112) FRL).
    { eapply rw_cells_transport; [exact FR2| exact MUd| exact WMd|]. cbn. rewrite FRSZ. clear - AnC ACL0 SLO HLS HIJ HI_ HJ KG NR1. lia. }
    clear J2 F2 BA2 BB2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1 NM1 JX FR2 ESA ELA ESB ELB.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    pose proof J3 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. rewrite ?SPJU in *. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    flat constr:((xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl)) 4%nat. intros ZIN ZCH ZLEN ZB. cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    flat constr:(MX1) 2%nat. intros (CX3 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    eapply aevtM_cut.
    { eapply (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * nXc) (lo := lo) (junk := u32s xs);
        rewrite ?SPJU; try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
      all: try exact ZB.
      all: try (rewrite Z.sub_0_r in ST1; exact ST1).
      all: try (rewrite HT1; clear - HTOP SPJU; rewrite <- SPJU; lia).
      all: try (rewrite <- MSFE; exact CA).
      all: try (f_equal; clear; lia).
      all: clear - SLO SPA SPB HLS ACL ACP SPJU; try lia. all: Z.div_mod_to_equations; lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
    rewrite ?SPJU in PO.
    flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
    replace (ret_pc (Z_to_bv 64 131480)) with (Z_to_bv 64 131480) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ltac:(rewrite SPJU, Z.sub_0_r; exact ST4) MF4 HT4 HH4 ltac:(rewrite SPJU, Z.sub_0_r; exact PX4) SOK4) as D4.
    pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ J3 F3 BA3 eq_refl ltac:(rewrite SPJU, Z.sub_0_r; exact PX4) MI4) as BA4. cbn [md_p] in BA4.
    pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ J3 F3 BB3 eq_refl ltac:(rewrite SPJU, Z.sub_0_r; exact PX4) MI4) as BB4. cbn [md_p] in BB4.
    assert (FR4 : rw_cells psegs m4 (bv_unsigned sp - 112) FRL).
    { eapply fr_presx; [exact PX4| exact FR3| cbn; clear - PC ACL0 SLO HLS; lia]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 BA3 BB3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 NM1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4 JX FR3.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    clear SEP PI AnI.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ _ _ _ _ _ _ D4 BA4 MU WM) as BA5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BA5.
    pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ _ _ _ _ _ _ D4 BB4 MU WM) as BB5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BB5.
    zstep. zstep.
    match goal with FR5 : rw_cells psegs m5 (bv_unsigned sp - 112) FRL |- _ =>
      eapply mm_FIN; [exact J5| exact BA5| exact BB5| exact FR5| exact HI_| exact HJ| clear; lia] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac scan_open J :=
    pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP;
    pose proof alloc_ceiling_bounds as ACV; pose proof SPJU as SPJU;
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1);
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *;
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L2749810556.3   L44894671626.128L52274802212.2  00000800e00jS1i1j2KLS2sp3FRL1X2nA2nB1i1j2xs3HI_2HJ3SPB2X03NRA3NRBS1i1j". (* [comment removed for export] *)
  Lemma mm_SUM : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pj,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R5.R4.R3.R2.R1.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R6.R5.R3.)P,(11.$2.R6.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R5.)VX,)P,(13.(0.&40.)(30.R6.)VpadX,)P,(20.(21.=R21.)(21.R21.VnA,))P,(20.(21.=R21.)(21.R21.VnB,))(15.$2.R:.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(;.&40.VAa,)(;.&40.R23.)(;.&40.R22.)R15.R14.R13.R12.Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(;.&40.+20140.)Vfc,(18.(0.&40.))R;.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP HI_ HJ. jc_open. scan_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 6%nat. intros _ _ _ _ NRA _. flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 6%nat. intros _ _ _ _ NRB _.
    cbn [md_n] in NRA, NRB.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep. zstep. zstep. if_cases KL; zify_cond KL; rewrite ?Z.mod_small in KL by (clear - HI_ HJ NRA NRB; lia).
    { eapply KCL; [exact J| exact BA| exact BB| exact FRc| right; reflexivity]. }
    replace (Z_to_bv 64 (j + i)) with (Z_to_bv 64 (i + j)) by (f_equal; clear; lia).
    eapply mm_G; [exact J| exact BA| exact BB| exact FRc| exact HI_| exact HJ| clear - KL; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L13036769295.4  L19168960846.145L21041645149.3  L23970764156.142L26182189814.2  L52514160176.141L54425651213.3  L59308546259.4  L59308583409.4  L59310648043.6  L59904688831.2  L66607632863.3  L780814420.4    00000<00Z00b01\01b02>02G02S02_03403<03E03QS2nB1r2HR2K2S2sp3FRL1X2Ba2pB2zs1k3dXc1r2HkS1k1r2HkS2sp3FRL1X2Ba2nB2pB2zs1k3dXc1r2Hk2HR3SPB2X02B04LENB3PB02EBS2pB1rS2sp3FRL1X2Ba2pB2zs1k3dXc2HkS2nB1r2HRS2nB1r2HR2N0S2nB1r2Hk2HRS2nB2zs1r2HR4LENB3NTHS2nB3NRBS2nB1r2HRS2nB1r2HR2K2". (* [comment removed for export] *)
  Lemma mm_BLOOP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pk,$31.Pi,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pfl,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pr1,(0.&40.)Pr0,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.Pr,$8.P,(21.R1.(24.R1=.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R7.R6.R5.R4.R3.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R7.R6.R4.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R8.R7.R5.)P,(11.$2.R8.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R7.)VX,)P,(13.(0.&40.)(30.R8.)VpadX,)P,(20.(21.=R23.)(21.R23.VnA,))P,(20.(21.+1.R9.)(21.R9.VnB,))P,(13.(0.&40.)R11.(;.&40.R:.))P,(13.(0.&40.)R11.(;.&40.(<.(28.VpB,(29.+4.R;.))+4.)))(15.$2.R>.VPOST,(16.(17.R23.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R26.R25.R24.(;.&40.VX,)(;.&40.VBa,)R22.R12.R21.R20.R1?.R1>.R1=.R1<.(;.&40.VAa,)(;.&40.R27.)R13.R1;.R1:.R19.R18.Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(;.&40.+200=<.)Vfc,(18.(0.&40.))R?.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J BA BB FRc EA EP HI_ HR -> ->; [exfalso; clear - Hk HR; lia|].
    jc_open. scan_open J.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 8%nat. intros B0 B16 BAL LENB NRB BS OWNB0 OWNB1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    assert (BN : ownB <> LNull) by (intros C; (flat constr:((OWNB0 C)) 2%nat; intros _ N0); clear - N0 HR; lia).
    flat constr:((OWNB1 BN)) 5%nat. intros NB1 PB0 PB4 BBY _. rewrite ?SPJU in *.
    pose proof (u32ro_bound _ _ _ _ BBY) as EB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENB HR; lia].
    pose proof (u32ro_read psegs mc pB zs (r - 1) w _ BBY NTH ltac:(clear - HR; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. eapply mm_SUM; [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - HR; lia].
    - zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply IH with (r := r - 1); try eassumption; [clear - Hk; lia| clear - HR K2; lia| f_equal; clear; lia| f_equal; clear; lia].
      + (* [comment removed for export] *)
        assert (r = 1) as -> by (clear - K2 HR; lia). change (1 - 1) with 0.
        zstep. zstep. zstep. eapply mm_SUM; [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - NRB; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L16256852529.124L30137588842.2  L39172636981.0  L40212035753.3  L43664999485.123L4475913152.2   L65778066483.3  00000A00I00J00V00W00^00fS2sp3FRL1X2Ba3dXcS2nB3HNBSS2nB3HNB3NRBFS2nB2pBS2nB3HNB". (* [comment removed for export] *)
  Lemma mm_BINIT : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pfl,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R5.R4.R3.R2.R1.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R6.R5.R3.)P,(11.$2.R6.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R5.)VX,)P,(13.(0.&40.)(30.R6.)VpadX,)P,(20.(21.=R20.)(21.R20.VnA,))P,(21.+1.VnB,)(15.$2.R:.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(;.&40.VAa,)(;.&40.R22.)(;.&40.VnB,)R15.R14.R13.R12.Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(;.&40.+200<<.)Vfc,(18.(0.&40.))R;.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP HI_ HNB. jc_open. scan_open J.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat. intros (CEB & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB. unfold mpi_cells in CEB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 6%nat. intros _ _ _ _ NRB _. cbn [md_n] in NRB.
    eapply mm_BLOOP with (k := Z.to_nat nB) (r := nB); try eassumption; [clear - HNB; lia| clear - HNB NRB; lia| reflexivity| f_equal; rewrite ?Z.mod_small by (clear - HNB NRB; lia); clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L38260246191.2  L43665064624.125L47219703728.2  L68007334594.3  00000800M00U00`S2nB3NRBS2sp3FRL1X2nB3dXc3NRBS2nB3NRBS2nB3NRB2KB". (* [comment removed for export] *)
  Lemma mm_BENTRY : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pfl,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R5.R4.R3.R2.R1.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R6.R5.R3.)P,(11.$2.R6.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R5.)VX,)P,(13.(0.&40.)(30.R6.)VpadX,)P,(20.(21.=R21.)(21.R21.VnA,))(15.$2.R9.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(;.&40.VAa,)(;.&40.R22.)R15.R14.R13.R12.R11.Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(;.&40.+200<4.)Vfc,(18.(0.&40.))R:.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP HI_. jc_open. scan_open J.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat. intros (CEB & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB. unfold mpi_cells in CEB.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 6%nat. intros _ _ _ _ NRB _. cbn [md_n] in NRB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NRB; lia). zstep. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by (clear - NRB; lia).
    - (* [comment removed for export] *) zstep. eapply mm_SUM with (j := nB); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - NRB; lia].
    - eapply mm_BINIT; [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - KB NRB; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L38260246191.2  L43665064624.125L47219703728.2  L68007334594.3  00000800M00U00`S2nB3NRBS2sp3FRL1X2nB3dXc3NRBS2nB3NRBS2nB3NRB2KB". (* [comment removed for export] *)
  Lemma mm_BENTRY2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pi,$8.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pfl,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R5.R4.R3.R2.R1.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R6.R5.R3.)P,(11.$2.R6.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R5.)VX,)P,(13.(0.&40.)(30.R6.)VpadX,)P,(20.(21.=R21.)(21.R21.VnA,))(15.$2.R9.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(;.&40.VAa,)(;.&40.R22.)R15.R14.R13.R12.R11.Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(;.&40.+20134.)Vfc,(18.(0.&40.))R:.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP HI_. jc_open. scan_open J.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BB))) 2%nat. intros (CEB & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEB. unfold mpi_cells in CEB.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBB _ _ _ BB)) 6%nat. intros _ _ _ _ NRB _. cbn [md_n] in NRB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NRB; lia). zstep. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by (clear - NRB; lia).
    - eapply mm_BINIT; [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - KB NRB; lia].
    - (* [comment removed for export] *) zstep. eapply mm_SUM with (j := nB); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| exact HI_| clear - NRB; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L21041645149.3  L23970764156.141L31024423289.2  L31686774790.144L49887312664.3  L50968257341.2  L54425651213.3  L59308546259.4  L59308583409.4  L59310648043.6  L64912137160.4  L780814420.4    00000801201:01X01a01g02002<02H02]02i035S1k1r2HkS2sp3FRL1X2Aa2nA2pA2ys1k3dXc1r2Hk2HR3SPB2X02A04LENA3PA02EBS2nA3NRAS2sp3FRL1X2Aa2pA2ys1k3dXc1r2HkS2nA1r2HRS2pA1rS2nA1r2HRS2nA1r2HR2N0S2nA1r2Hk2HRS2nA2ys1r2HR4LENA3NTHS2nA1r2HR2K2S2nA1r2HR2K2". (* [comment removed for export] *)
  Lemma mm_ALOOP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pk,$31.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pfl,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pr1,(0.&40.)Pr0,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.Pr,$8.P,(21.R1.(24.R1=.))P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R7.R6.R5.R4.R3.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R7.R6.R4.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R8.R7.R5.)P,(11.$2.R8.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R7.)VX,)P,(13.(0.&40.)(30.R8.)VpadX,)P,(20.(21.+1.R8.)(21.R8.VnA,))P,(13.(0.&40.)R10.(;.&40.R9.))P,(13.(0.&40.)R10.(;.&40.(<.(28.VpA,(29.+4.R:.))+4.)))(15.$2.R=.VPOST,(16.(17.R23.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R26.R25.R24.(;.&40.VX,)(;.&40.VBa,)R22.R11.R21.R20.R1?.R1>.R1=.R1<.(;.&40.VAa,)R12.R1;.R1:.R19.R18.R17.Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(;.&40.+200;0.)Vfc,(18.(0.&40.))R>.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J BA BB FRc EA EP HR -> ->; [exfalso; clear - Hk HR; lia|].
    jc_open. scan_open J.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 8%nat. intros A0 A16 AAL LENA NRA AS OWNA0 OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    assert (AN : ownA <> LNull) by (intros C; (flat constr:((OWNA0 C)) 2%nat; intros _ N0); clear - N0 HR; lia).
    flat constr:((OWNA1 AN)) 5%nat. intros NA1 PA0 PA4 ABY _. rewrite ?SPJU in *.
    pose proof (u32ro_bound _ _ _ _ ABY) as EB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    destruct (nth_error ys (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENA HR; lia].
    pose proof (u32ro_read psegs mc pA ys (r - 1) w _ ABY NTH ltac:(clear - HR; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. eapply mm_BENTRY2; [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| clear - HR; lia].
    - zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply IH with (r := r - 1); try eassumption; [clear - Hk; lia| clear - HR K2; lia| f_equal; clear; lia| f_equal; clear; lia].
      + assert (r = 1) as -> by (clear - K2 HR; lia). change (1 - 1) with 0.
        eapply mm_BENTRY with (i := 0); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| clear - NRA; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L32982742029.2  L35695741325.2  L36979837773.3  L39172636981.0  L47608518001.3  L5290668657.2   L59435147825.125L61814428557.12400000800@00D00E00P00W00h01=S2nA3NRAS2nA3NRAS2nASS2nA3NRA2KAS2nA2pAS2sp3FRL1X2Aa3dXcS2sp3FRL1X2nA3dXc3NRA". (* [comment removed for export] *)
  Lemma mm_AENTRY : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi_W ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Praj,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)Px23,(0.&40.)Px24,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Phc,(1.$2.VL,VHI,)PLBc,(3.$4.)Pmc,P,(0.&40.)(5.(0.&8.))Pmoc,$6.PdXc,$7.P,(9.$2.VL,VHI,Vh1,VLB1,Vm1,Vmo1,(:.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(;.&40.(<.(=.&40.Vsp,)+70.))Vlo,=(>.$?.)(>.$4.)R5.R4.R3.R2.R1.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.R2.)P,(10.$2.(;.&40.(<.(=.&40.Vsp,)+70.))(:.VBa,VsB,VnB,VpB,Vzs,VpadB,VownB,)R6.R5.R3.)P,(11.$2.R6.(<.(=.&40.Vsp,)+70.)VFRL,)P,(13.$8.(2?.R5.)VX,)P,(13.(0.&40.)(30.R6.)VpadX,)(15.$2.R8.VPOST,(16.(17.R1>.(;.&40.(<.(=.&40.Vsp,)+70.))Vgp,Vtp,R21.R20.R1?.(;.&40.VX,)(;.&40.VBa,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(;.&40.VAa,)R15.R14.R13.R12.R11.R10.Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(;.&40.+20094.)Vfc,(18.(0.&40.))R9.(19.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J BA BB FRc EA EP. jc_open. scan_open J.
    flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ BA))) 2%nat. intros (CEA & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CEA. unfold mpi_cells in CEA.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ JBA _ _ _ BA)) 6%nat. intros _ _ _ _ NRA _. cbn [md_n] in NRA.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NRA; lia). zstep. zstep. if_cases KA; zify_cond KA; rewrite ?Z.mod_small in KA by (clear - NRA; lia).
    - (* [comment removed for export] *) eapply mm_BENTRY with (i := nA); [exact J| exact BA| exact BB| exact FRc| exact EA| exact EP| clear - NRA; lia].
    - zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply mm_ALOOP with (k := Z.to_nat nA) (r := nA); try eassumption; [clear - KA NRA; lia| clear - KA NRA; lia| reflexivity| f_equal; rewrite ?Z.mod_small by (clear - KA NRA; lia); clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End W.
