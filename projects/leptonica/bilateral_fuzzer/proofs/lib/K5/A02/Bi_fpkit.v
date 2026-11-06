(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec FP Step.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_fpkit () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem6frm_ofC4ELinuxProcessSemantics5Riscv3Fpu>rmode_of_fieldK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv3Sem9fp_formatC4ELinuxProcessSemantics5Riscv3Fpu6fp_negC4ELinuxProcessSemantics5Riscv3Fpu6fp_fmaC4ELinuxProcessSemantics5Riscv3Sem4c_pcC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem6accrueC4ELinuxProcessSemantics5Riscv3Sem6fwriteK4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics5Riscv3Sem3eff02C4ELinuxProcessSemantics5Riscv3Sem4fgetc69OSSVerify5KrLib2K53A028Bi_fpkit5fma_dC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028Bi_fpkit8fma_fl_dC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvc69OSSVerify5KrLib2K53A028Bi_fpkit7fma_preC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem6c_fcsrK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init5Logic8eq_ind_rK4ELinuxProcessSemantics5Riscv5Instr5instr0KC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics5Riscv3Sem5freadC4ELinuxProcessSemantics5Riscv3Sem4fsetC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr4ffmt02I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv3Sem3eff00C4ELinuxProcessSemantics5Riscv3Fpu:fmt_doubleI4ELinuxProcessSemantics5Riscv3Fpu6fflags00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00K4ELinuxProcessSemantics5Riscv5Instr5fmaop01K4ELinuxProcessSemantics5Riscv5Instr5fmaop02K4ELinuxProcessSemantics5Riscv5Instr5fmaop03K4ELinuxProcessSemantics5Riscv5Instr5fmaop04c69OSSVerify5KrLib2K53A028Bi_fpkit5fma_sC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028Bi_fpkit8fma_fl_sC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7unbox_sC4ELinuxProcessSemantics5Riscv3Sem7nan_boxK4ELinuxProcessSemantics5Riscv5Instr4ffmt01C4ELinuxProcessSemantics5Riscv3Fpu:fmt_single".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition fma_pre (op : fmaop) (f : format) (a z : Z) : Z * Z :=
  match op with
  | F_MADD => (a, z)
  | F_MSUB => (a, fp_neg f z)
  | F_NMSUB => (fp_neg f a, z)
  | F_NMADD => (fp_neg f a, fp_neg f z)
  end.
Definition fma_d (op : fmaop) (md : rmode) (x y w : word) : word :=
  Z_to_bv 64 (fst (fp_fma fmt_double md (fst (fma_pre op fmt_double (bv_unsigned x) (bv_unsigned w))) (bv_unsigned y)
                                          (snd (fma_pre op fmt_double (bv_unsigned x) (bv_unsigned w))))).
Definition fma_fl_d (op : fmaop) (md : rmode) (x y w : word) : fflags :=
  snd (fp_fma fmt_double md (fst (fma_pre op fmt_double (bv_unsigned x) (bv_unsigned w))) (bv_unsigned y)
                            (snd (fma_pre op fmt_double (bv_unsigned x) (bv_unsigned w)))).
Definition fma_s (op : fmaop) (md : rmode) (x y w : word) : word :=
  nan_box (Z_to_bv 32 (fst (fp_fma fmt_single md
     (fst (fma_pre op fmt_single (bv_unsigned (unbox_s x)) (bv_unsigned (unbox_s w)))) (bv_unsigned (unbox_s y))
     (snd (fma_pre op fmt_single (bv_unsigned (unbox_s x)) (bv_unsigned (unbox_s w))))))).
Definition fma_fl_s (op : fmaop) (md : rmode) (x y w : word) : fflags :=
  snd (fp_fma fmt_single md
     (fst (fma_pre op fmt_single (bv_unsigned (unbox_s x)) (bv_unsigned (unbox_s w)))) (bv_unsigned (unbox_s y))
     (snd (fma_pre op fmt_single (bv_unsigned (unbox_s x)) (bv_unsigned (unbox_s w))))).

Lemma exec_fma_d : forall sz op rd rs1 rs2 rs3 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fma op FMT_D rd rs1 rs2 rs3 rm) c =
  EDone (fset rd (fma_d op md (fget c rs1) (fget c rs2) (fget c rs3))
          (accrue (fma_fl_d op md (fget c rs1) (fget c rs2) (fget c rs3)) (with_pc (c_pc c + sz) c))).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_fpkit ()) [] "p'0h01pi001ph11Hh21ch31fi011fh42mdi022mdh51oh62opi032oph72rdh82rmh93rs1h:3rs2h;3rs3h<2szh=1zi041zi052a'i062fli071vi081xi092z'p;1p;2p;3p;5p;4p;6p;7g0000j1>Tg000Uj1ETg0013j1GTg001Vj1ITg002;R0j1`Tg002]j21Tg003Gj1STg0040j2CTg004aj2PTg005Cj3NTg005]R1j2LTg006=j1_Tg006ij24Tg007Rj5FTg008;j1=Tg008bj3;Tg009Gj2<Tg00:1j2DTg00:Zj4HTg00;Cj1BTg00;kj1RTg00<Sj28Tg00=:j5QTg00>4j5OTg00?1j27Tg00?Wj4?Tg00@Sj4KTg00A3j2ZTg00AMj1JTg00B6j1TTg00BTj2YTg00C4j2XTg00CRj6^Tg00D0j7]Tg00D\j3\Tg00ECj3[Tg00Ekj3UTg00FRj3WTg00Foj3VTf1R2g00GLR3f0R43[p=6g00H7R5P5P2P4CKp=0f3R6f2R71D243U#Bp=5g00HUR8?N24p=2g00I=R9P6P7P2P4DFp=3AU724#Bp=MAW554p=@AV554p=Ag00IjR:=W54p=:AV5:4p=9g00JUR;#>R<#>#>#>#>R=#>#ER>#Gg00K:R?%I<R<#E#GR@%I;R;#ERA#Gg00Kfg00LORB%`BRC11A7%S2'C1PB43NPC1PB2P0PBP8P4P1P5P5P8P?1L55RDf:REf4RFf8RG'6RHf6RI,6FRJ'0%_3RK/4JRL,0H14KHRH/0J10HLn01103000400000000P1P5P:P8PKP7P2f9RH,6IP4DFP3f=RLP2%=Gf?5;>/<G,D4CH#Bn2001108000120107106n2001108000120105109%=6=;>E/<6RE#Rn10110800021010200PGPHP7f7RJ,86RM186IRNf5RO,86RPDQPHP7PMPNPPDOPEC5'2X5CP?P1P5P5P8P?PDP411>MRM11>PRP'0149PRC,0M149MRQ/0P10QCn01103000400000000P1P5P:P8PFP218OG,1>P4C3f<RQ17>2RC%=Jf>5;>/<JRR,D4RS3Mn2001108000120107106n2001108000120105109PGP7P4P9PMPPC?RP#@11>N%APC3RP#:,7>%9PPEC5'2PGP2187IRE,1>RP187ORN,1>RM187FRT,1>RUC3RV1L5:RWP1P5P:P1P5P:P8P4f;RX%=I=;>L/<I,D4RL7MCRYn2001108000120107106PH%:4,7>%94%=F=;>X/<FRZC5'2P4PQP5P:P2P4CKR[#:,7>%9[PRC5,Z8X3:X=5P2P4O2n2001100000120104101RRb0P1P5P:P8PVPHPCP4PZC5RZn2001108000120107106PJP2g00M9P9PPPUC?RC#@PM%ACC3RC#:,7>%9C%=7=;>H/<7RCC5'2eP2PPPM149URVC3R[PWPRb0P1P5P:P8P[PZn2001108000120107106PJP2g00MeP9PPPUC?R[#@PM%A[C3R[#:,7>%9[PCC5'2eP2149PR[PMPUC3R\PWPRb0P1P5P:P8P\PZn2001108000120107106PJP2g00NQP9PPPUC?R\#@PM%A\C3R\#:,7>%9\PCC5'2eP2P[PMPVC3R\PWPRb0P1P5P:P8P\PZn2001108000120107106PJP2g00O=P9PPPUC?R9#@PM%A9C3R9#:,7>%99PCC5'2en01101010401010101P1P5P5P8P?PDPG10PU10PV10[U10[Vn01103000400000000P1P5P:P8P6P218FJ,1>P4C3PYn2001108000120107106n2001108000120105109PJPGP2PEPNPTDQPGP2PEPNPTDOPCC5RT'2eP1P5P5P8P?PDPG167IRN167FRE'014KERY,0N14KNRN/0E10NYn01103000400000000P1P5P:P8PKP6P216FJP4DFP3PXP2PLCH#Bn2001108000120107106n2001108000120105109/2Te11A6RA%E=R=%J7'1%T<R<'Y%I;#TR;'X'CP4E^P0PBP8%JC,1=/Y</X;,CAP1P5P5P8P?PDPH166JRD166OR?'014K?R;,0D14KDRD/0?10D;n01103000400000000P1P5P:P8PKP7P216OGP4DFP3PQP2PSCH#Bn2001108000120107106n2001108000120105109RS%RCR2n10110800021010200/2TeP0PBP8%SC,CAPSP2n10110800021010200/2TePGP3PJPIPOPFP6F]=\H7/2TeW1W4W2W8X;@X:@X9@W7W6W<o"). Qed.

Lemma exec_fma_s : forall sz op rd rs1 rs2 rs3 rm c md,
  rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fma op FMT_S rd rs1 rs2 rs3 rm) c =
  EDone (fset rd (fma_s op md (fget c rs1) (fget c rs2) (fget c rs3))
          (accrue (fma_fl_s op md (fget c rs1) (fget c rs2) (fget c rs3)) (with_pc (c_pc c + sz) c))).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_fpkit ()) [] "p'0h01pi001ph11Hh21ch31fi011fh42mdi022mdh51oh62opi032oph72rdh82rmh93rs1h:3rs2h;3rs3h<2szh=1zi041zi052a'i062fli071vi081xi092z'p;1p;2p;3p;5p;4p;6p;7g0000j1<Tg000Uj1GTg0013j1HTg001Vj1ITg002;R0j1dTg002]j2CTg003Gj1STg0040j2DTg004aj2PTg005Cj3NTg005]R1j2MTg006=j1cTg006ij24Tg007Rj5FTg008;j1=Tg008bj3>Tg009Gj2;Tg00:1j2ETg00:Zj4JTg00;Cj1BTg00;kj1RTg00<Sj27Tg00Oij5QTg00Pcj5OTg00?Wj4@Tg00@Sj4KTg00A3j2[Tg00AMj1TTg00B6j1ZTg00BTj2YTg00C4j2XTg00CRj6bTg00D0j7aTg00D\j3`Tg00ECj3_Tg00Ekj3VTg00Q`j1^Tg00?1j2]Tg00RJj1\Tg00FRj3WTg00Foj3UTf1R2g00S4R3f0R43_p=5g00H7R5P5P2P4CKp=0f3R6f2R71E243V#Bp=3g00HUR8?N24p=1%^4,C2p=8g00S_R9P6P7P2P4DFp=21]24#\p=6AV724#Bp=LAW554p=AAU554p=?g00IjR:=W54p=9AU5:4p=:g00JUR;#<R<#<#<#<#<R=#<#GR>#Hg00K:R?%I<R<#G#HR@%I;R;#GRA#Hg00Kfg00LORB%dBRC1CA7%S2'D1PB43NPC1PB2P0PBP8P4P1P5P5P8P?1M55RDf:REf4RFf8RG'5RHf6RI,5FRJ'0%c3RK/4JRL,0H14KHRH/0J10HLn01103000400000000P1P5P:P8PKP7P2f9RH,5IP4DFP3f=RLP2%=Gf?5>>/;G,E4CJ#Bn2001108000120107106n2001108000120105109%=6=>>E/;6RE#Rn10110800021010200PGPHP7f7RJ,76RM176IRNf5RO,76RPDQPHP7PMPNPPDOPEC3'1X5CP?P1P5P5P8P?PDP4%G=R=/8MRM18=PRP'0149PRC,0M149MRQ/0P10QCn01103000400000000P1P5P:P8PFP217OG,8=P4C2f<RQ16=2RC%=Jf>5>>/;JRR,E4RS3Ln2001108000120107106n2001108000120105109PGP7P4P9PMPPC@RP#A18=N%?PC2RP#9,6=%:PPEC3'1PGP2177IRE,8=RP177ORN,8=RM177FRT,8=RUC2RV1M5:RWP1P5P:P1P5P:P8P4f;RX%=I=>>L/;I,E4RL7LCRYn2001108000120107106PH%94,6=%:4%=F=>>X/;FRZC3'1P4PQP5P:P2P4CKR[#9,6=%:[PRC3,[8X3:X=5P2P4O2n2001100000120104101RRb0P1P5P:P8PVPHPCP4PZC3RZn2001108000120107106PJP2g00M9P9PPPUC@RC#APM%?CC2RC#9,6=%:C%=7=>>H/;7R>C3'1eP2PPPM149URCC2RVPWPRb0P1P5P:P8PVPZn2001108000120107106PJP2g00MeP9PPPUC@RV#APM%?VC2RV#9,6=%:VP>C3'1eP2149PRVPMPUC2R[PWPRb0P1P5P:P8P[PZn2001108000120107106PJP2g00NQP9PPPUC@R[#APM%?[C2R[#9,6=%:[P>C3'1eP2PVPMPCC2R[PWPRb0P1P5P:P8P[PZn2001108000120107106PJP2g00O=P9PPPUC@R9#APM%?9C2R9#9,6=%:9P>C3'1en01101010401010101P1P5P5P8P?PDPG10PU10PC10VU10VCn01103000400000000P1P5P:P8P6P217FJ,8=P4C2PYn2001108000120107106n2001108000120105109PJPGP2PEPNPTDQPGP2PEPNPTDOP>C3RT'1eP1P5P5P8P?PDPG157IRN157FRE'014KERY,0N14KNRN/0E10NYn01103000400000000P1P5P:P8PKP6P215FJP4DFP3PXP2PLCJ#Bn2001108000120107106n2001108000120105109/1Te1CA6RA%T7,C=%Z<R<'Y%I;#ZR;'X'DP4EbP0PBP8%T>,C=/Y</X;,DAP1P5P5P8P?PDPH156JRD156OR?'014K?R;,0D14KDRD/0?10D;n01103000400000000P1P5P:P8PKP7P215OGP4DFP3PQP2PSCJ#Bn2001108000120107106n2001108000120105109RS%R>R2n10110800021010200/1TeP0PBP8%S>,DAPSP2n10110800021010200/1TePGP3PJPIPOPFP6Fa=`H7/1TeW1W4W2W8X;@X:@X9@W7W6W<o"). Qed.

(* [comment removed for export] *)
Ltac exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fma ?op FMT_D ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_d sz op rd rs1 rs2 rs3 rm c _ H)
    | Fma ?op FMT_S ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_s sz op rd rs1 rs2 rs3 rm c _ H)
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | Csr ?op ?rd ?rs1 ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | _ => idtac
    end
  end;
  (* [comment removed for export] *)
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.
