(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_dec_iface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface9huf_dt_okC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1;x1_table_okC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface8x1_bytesC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_iface8x2_bytesI47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list02c5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_dec_iface6x1_tabc5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_dec_iface6x2_tabI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or02I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsK47Corelib7Numbers7BinNums8positive03I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX16deltX100I5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHUF_DX1_1X : Z := 0x154ec.     (* [comment removed for export] *)
Definition PHUF_DX2_1X : Z := 0x14900.     (* [comment removed for export] *)
Definition PHUF_DX1_4X : Z := 0x16e6c.     (* [comment removed for export] *)
Definition PHUF_DX2_4X : Z := 0x15a6c.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition x1_tab (m : fmem) (DT mtl : Z) : Prop :=
  exists (tl : Z) (cells : list deltX1),
    bytes_at usegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 0; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ zlen cells = 2^(mtl+1) /\ x1_table_ok cells tl /\ tl <= mtl + 1
    /\ bytes_at usegs m (DT + 4) (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes cells)).

Definition x2_tab (m : fmem) (DT mtl : Z) : Prop :=
  exists (tl : Z) (cells : list deltX2),
    bytes_at usegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ zlen cells = 2^mtl /\ x2_table_ok cells tl /\ tl <= mtl
    /\ bytes_at usegs m (DT + 4) (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes cells)).

Lemma huf_dt_ok_cases : forall m DT mtl, huf_dt_ok m DT mtl -> x1_tab m DT mtl \/ x2_tab m DT mtl.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_dec_iface ()) [] "p'0h05cellsh11Hh22tlh32DBh42tth51Bh61Lh71Th82TLh92DTh:1mh;3mtli001xp%0p;1p;3p;2p;4p;7g0000j1HTg000Uj1\Tg0013j1YTg001Vj1`Tg0028j3fTg0039j23Tg003_j1aTg004?j1XTg004_j1TTg005=j20Tg005Zj2KTg006]j24Tg007:j2RTg007Wj1ATg008Wj2LTg009Zj1BTg00:ZR0j2GTg00;4R1j25Tg00;Nj26Tg00;jj37Tg00<Jj3^Tg00=Lj3]Tg00>NR2j21Tg00>ij4ETg00?Dj4STg00?^j3eTg00@8j7[Tg00@Vj3dTg00A0j3?Tg00AJj2cTg00Ajj1bTg00BJj1UTg00Bjj3VTg00CIj4OTf4R3f3R4f2R5f1R6f0R73737p=8g00D>R8g00D\R97?7p=<1c67#bp=D%U6=V57p=Zg00E:R:P5P6P7COp=9f6R;f5R</435?81656/17,14'1p=C1567,15p=:A?867p=QP:f7R=P;A745697<3CO/17p=@A^<34A]567'Gp=;A?8341167,15'1p=WA?856/17p=JP:P3P4A7567COp=FP:P<P31R56#U=V47COp=214;<9?8=1K341656/17'1'1p=>1L341656/17'1p=I14569?84/17p=P16=;P:P<P31R56#U=V47CO'1p==A?8341L56/17'1p=M14679?85p=N1K341656/17'1p=_g00EoR:#HR>#HR?#HR@#H#H#H#\#Y%\@R@#YRA#`[Af567P1P8P<P3PA13@4RBPA13@6RCPA13@7RDPAPB%aARED8%<6RFg00FTRG#XRH1DG7RI%T>R>%T:R:,03RJ1K76RKP6PJ%T?R?,0<RJ14>6RL,R>%A7RM5ZARN59;FCX0H3:1Q6:ROg00GTRP#XRQ1DP7RRP>P31L76RSP6P31R?L%B7RL5ZART99;JFCX0Q3:'GG@X28,58X48P3P4P5P3P4P5E;P7P=P;PA13@<RJPAPCPAPDPAPJPED8PIP>10;:RUPKP6PUf8RU10=?RV;9NFCX0H9:FHPR14>;RFPS166;A9UVTDWX0Q9:OQ'GG@X28,58P1P8PUP=PA13@;ROPA13@5PAPDPAPOPED8%<5PIP>10=:ROPKP6POf9RO10U?RV;9NFCX0H7:HPR14>=RWPS166=A9OVTDWX0Q,5Q9J5:'GG@X28PUP=P;PUP=P;E;P7f:RVPOPA13@URXPA13@3PAPDPAPXPED8%<3PIP>10O:RXPKP6PXf;RX10V?RY;9NFCX0H7:HPRP>POPSP6POA9XYTFCX0Q,5Q9J3:'GG@P2PXPVPA13@ORYPAPJPAPCA7AYED8DF%<<PIP>10V:RYP7P5P5PYf<RY10X?RJPAP>14>5RZPME2G>X0H7:HPRP>PVP7P5P5PVPYPJPAP?PZPLE2DICPX0Q,5Q9J<:'GPYPXPVPYPXPVE;P7f=RZPYPA13@XRJPA13@=PAPBA7AJED8DF%<UPIP>10Z:RBP7P<P<PBf?RBf>R5/0?R[PAP>14><R\PME2G>X0H7:HPR14>ZR]P7P<P<PZPBP[PAP?P\PLG=DMX0Q,5Q9JU:'GP0%<OPIP>105:R0P7P;P;P0f@R010B?R\PAP>PFPME2G>X0H7:HPRP>P5P7P;P;P5P0P\PAP?PFPLE2DICPX0Q,5Q9JO:P0PBP5P0PBP5E;P7%<VPIP>10B:RFP7P=P=PFfARF100?S00PAP>PWPME2G>X0H7:HP2%<XPIP>100:R\P7PUPUP\fBR\10F?S01PAP>14>US02PME2G>X0H,5HP\PFP0P\PFP0E;S03P7%<ZP8P9fER[fDR^PAfCR_,3@R`PAPDPAPJA7A`ED8DFR`PIP>10[:RJP7PZPZPJfGRJfFRD/0?S04PAP>P]PME2G>X0HRa,5HPJPDP[PJPDP[E;Rb[]3X48P^P_PA13@\Rc13@9R9PA13@VPAPcPED8Rd57ADFPIP>10^:ReP7PYPYPePD10[?S05PAP>14>YS06PME2G>X0H,5HP1PHPaPbP7PIP>10J:RaP7PBPBPafIRafHRe/0?S07PAP>14>BRfPME2G>P21DG610e:Rg7N>P6P0P0PgfJRg10a?S08PAP>14>0Rh%A6E2D_fKRiPgPaPiPgPaE;S09P71DG410g:7N>P3P_P_10i:fMRjfLRk/0?S0:PAP>14>_S0;%A3E2D_P21K<^P^10k:fNRl10j?S0<PAP>14>^Rm%A<G=fORnPlPjPnPlPjE;S0=P71K=DPJ10n:fQRofPRp/0?S0>PAP>14>JRq%AUG=P210p:,6efRRr10o?S0?PAP>14>eRs%AOE2fSRtPrPoPtPrPoE;S0@P710r:,6gfURtfTRu/0?S0APAP>14>iS0B%AYE2fVRv?^tuRwA]vtuRxP8fXRyfWRzPA13@vR{PAP9PAPCPAP{PED8S0CPIP>10v:RCPKP6PC10z?RC=9yNFCG@X0H,5HX28PkPHPzPvPA13@tRNPAP9PA13@jPAPNPED8S0DPIP>10t:RIP7PjPjPIPz10v?S0EPAP>14>jS0FPME2G>G@X0HPZPvPtPA13@uRMPA13@kPAPMPED8RE97A9DF1DGZ10u:RG7N>R91KZkRI16kGRGPv10t?S0GPAP>14>kRK%AZE2R|'1R}'1R~'1PFP9P~POPIP}P<PGP|P6P7CECECECECSCS3eW5W8P6P7O2n2001000000121000000W1W7P6P7O2n2001000000121000000W1W6P6P7O2n2001000000121000000W1X0HP6P7O2n2001000000121100000W1W3P5P7P;F[W1P6P7O2n2001000000121000000W1P7O1PRPfP7P=P=PBPFQ00PAP?PWPLG=DMX0Q,5Q9JV:P21QX:PRPhP7PUPUP0P\Q01PAP?Q02PLG=DMX0Q,5QQ03P71QZ:P8P:PRP>P[P7PZPZP[PJQ04PAP?P]PLE2DICPX0QR],5QPb[^3`X48P^P_PAPc13@:R:=7AdDFPRPmP7PYPYP^PDQ05PAP?Q06PLG=DMX0Q,5QP1PQP]PbP7PRPqP7PBPBPJPaQ07PAP?PfPLG=DMP21DP6/QsP6P0P0PePgQ08PAP?Ph%B6E2DIQ09P71DP4?N>gP3P_P_PiPjQ0:PAP?Q0;%B3E2DIP21L<^P^PkPlQ0<PAP?Pm%B<G=Q0=P71L=DPJPnPoQ0>PAP?Pq%BUG=P216epPrQ0?PAP?Ps%BOE2Q0@P716grPtQ0APAP?Q0B%BYE2P8PyPzPAP{PAP:Q0CPRP>PvPSP6PvA9yCTFCG@X0Q,5QX28PkPQPzPvPAPNPAP:Q0DPRP>PtP7PjPjPtPzQ0EPAP?Q0FPLE2DICPG@X0QPZPvPtPAPMA7A:EDF1DPZ?N>uR>1LZkRP16kuRuPvQ0GPAP?PK%BZE2RZ'1RK'1R?'1PFP>P?POPPPKP<PuPZP6P7CECECECECSCS9dwxW5W8P6P7O2n2001000000121000000W1W7P6P7O2n2001000000121000000W1W6P6P7O2n2001000000121000000W1X0QP6P7O2n2001000000121100000W1W3P5P7P;F[W1P6P7O2n2001000000121000000W1P7O1n200100000021100011000W1W3P6P7O2n2001000000121000000W1X28P6P7O2n2011000000121100000W1X48P6P7O2n2011000000121100000W1X;8X98W:o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Stmts.
  Variable tab : fmem -> Z -> Z -> Prop.

  (* [comment removed for export] *)
  Definition dec1_int_stmt (E : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DST dcap S DT mtl : Z) (src : list Z) (jd : list byte) (lo : Z),
    1 <= mtl <= 12 -> tab m DT mtl ->
    ((DST = 0 /\ dcap = 0) \/ (0 < DST /\ DST mod 8 = 0 /\ rw_cells usegs m DST [CB (Z.to_nat dcap) jd])) ->
    0 <= dcap < 2^32 ->
    bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> 0 < S ->
    0 < DT -> DT mod 8 = 0 ->
    DT + DTABLE_BYTES mtl <= lo -> DST + dcap <= lo -> S + zlen src <= lo ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HUF_DEC_STACK -> bv_unsigned sp mod 16 = 0 ->
    mem_inv usegs m ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    evt usegs (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition dec4_int_stmt (E : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DST dcap S DT mtl flags : Z) (src : list Z) (jd : list byte) (lo : Z),
    1 <= mtl <= 12 -> tab m DT mtl ->
    ((DST = 0 /\ dcap = 0) \/ (0 < DST /\ DST mod 8 = 0 /\ rw_cells usegs m DST [CB (Z.to_nat dcap) jd])) ->
    0 <= dcap < 2^32 ->
    bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
    zlen src < 2^26 -> 16 <= S -> 0 < S ->
    0 < DT -> DT mod 8 = 0 ->
    DT + DTABLE_BYTES mtl <= lo -> DST + dcap <= lo -> S + zlen src <= lo ->
    (DT + DTABLE_BYTES mtl <= DST \/ DST + dcap <= DT) ->
    (DT + DTABLE_BYTES mtl <= S \/ S + zlen src <= DT) -> (DST + dcap <= S \/ S + zlen src <= DST) ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - HUF_DEC_STACK -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned sp <= 2^47 ->
    mem_inv usegs m ->
    0 <= flags < 64 ->
    a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 dcap -> a2 = Z_to_bv 64 S -> a3 = Z_to_bv 64 (zlen src) -> a4 = Z_to_bv 64 DT ->
    a5 = Z_to_bv 64 flags ->
    evt usegs (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E) fc None m (seg_rom usegs)).
End Stmts.

End CANSEC1.
