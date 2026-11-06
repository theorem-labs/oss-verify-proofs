(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export FP ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export StepDiet.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Step () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells=cells_at_readC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic3and00c59OSSVerify5KrLib3Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib4Step=rw_cells_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib3Lib4Step=ro_cells_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cb_split_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsAcells_at_cb_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_at_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsCcells_size_cb_splitC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib5Cells=cell_at_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib3Lib4Step=cell_at_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem>wr_at_store_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Cells>cells_at_writeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3Mem;wr_at_writeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Cells>cells_at_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells>cells_at_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells=cbytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC56Stdlib6ZArith6BinInt1Z3subC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions?bv_add_unsignedC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallc59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=store_bytes_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=store_bytes_4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=store_bytes_2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=store_bytes_1C1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Definition ro_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_at segs m A cs.
Definition rw_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_at segs m A cs /\ wr_at segs m A (Z.of_nat (cells_size cs)).

Lemma rw_cells_read : forall m A cs k c,
  rw_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Ah11Hh22H0h32_Hh41ch52csh61kh71mp;1p;3p;4p;2p;7g0000j10Tg000Uj19Tg0013j14Tg001Vj12Tg0028j1:Tg002Xj3<Tg003Nj47Tg004Ej15Tg005>j11Tg005^j46Tg006Pj2;Tg007Fj23Tg007hj38Tg008Bj2BTg008_j1ATg009Nj1@Tg00:Bj4=Tg00;Gj1>Tg00<<j7?Tg00=8#0#0#0R0#0#0#0#9#4%90#4R0#2[g00=]g00>;R1#:g00?0f4R2f3R3f2R43<g00?Op,4segsR5f5R6P2P3C7P5P6P2%53#1C6%211;23131438%:0R0#2P5f7R4f6R7%12'B#A%@3C=%>3,3038[f0R0P5P4P7P6C7P5f8R3P4%57#1C6P5f9P3P4P7P6f1R6F?W3W1P6P0O2n2001000000120000000W2X41W6W5W0W7o"). Qed.

Lemma ro_cells_read : forall m A cs k c,
  ro_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Ah11Hh21ch32csh41kh51mp;1p;3p;7g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg0028j16Tg00?jj35Tg00<<j74Tg00=8#0#0#0R0#0#0#0#2#1%20#1#3[g00=]g00>;R0#6g00?0f4R1f3R2f2R335p,4segsf5P1P2P3f1f0F4W1X20W4W3W0W5o"). Qed.

Lemma rw_cells_readn : forall m A cs k c n,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01nh11Ah21ch32csh41kh51mp;1p;3p;2p;4p;7p;6g0000j10Tg000Uj16Tg0013j14Tg001Vj12Tg0028j17Tg002Xj3<Tg006Pj2;Tg007Fj25Tg007hj31Tg009Nj13Tg005>j18Tg008Bj29Tg008_j1:Tg00:Bj4@Tg00;Gj1?Tg00@`j7>Tg00A[j6=Tg00=8#0#0#0R0#0#0#0#6#4%60#4R0#2[g00=]g00>;R1#7g00?0R2f5R3f4R4f3R53<%211;45f2R6,5131%359126P2%34%70R0#2p,4segsf9f8R7f6R8#8'9#:f0R9C@%?3,5031X02P7f7P8P3P4P6f1F>P5P9E=UUUX02X21W4W3W1W5o"). Qed.

Lemma ro_cells_readn : forall m A cs k c n,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01nh11Ah21ch32csh41kh51mp;1p;3p;2p;4p;7p;6g0000j10Tg000Uj16Tg0013j14Tg001Vj12Tg0028j17Tg00?jj3<Tg006Pj2;Tg007Fj25Tg007hj31Tg009Nj13Tg005>j18Tg008Bj29Tg008_j1:Tg00:Bj4@Tg00;Gj1?Tg00B9j7>Tg00A[j6=Tg00=8#0#0#0R0#0#0#0#6#4%60#4R0#2[g00=]g00>;R1#7g00?0R2f5R3f4R4f3R53<%211;45f2R6,5131%359126P2%34%70R0#2p,4segsf9f8R7f6R8#8'9#:f0R9C@%?3,5031X02P7f7P8P3P4P6f1F>P5P9E=UUUX02X21W4W3W1W5o"). Qed.

Lemma rw_cells_read_at : forall m A cs k c n a,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01ah11nh21Ah31ch42csh51kh61mp;1p;3p;2p;4p;7p;6g0000j10Tg000Uj17Tg0013j16Tg001Vj13Tg0028j1;Tg002Xj3>Tg006Pj2=Tg007Fj25Tg007hj31Tg009Nj12Tg005>j14Tg008Bj28Tg008_j19Tg00:Bj4<Tg00;Gj1@Tg00@`j7?Tg00A[j6:Tg00=8#0#0#0R0#0#0#0#7#6R1%70#6R0#3[g00=]g00>;R2#;g00?0R3f6R4f5R5f4R63>%321=56f3R7,5231%269137f8R8%44'8#99117P3%24%;0R0#3R9p,4segsR:f;R;P5f0R<C<f7R=#@,50R031X13P1f9R>%4='8#9P:P;P<%2=C<=190X01f:P>P8P=P4P7f2F?P6P<E:P5f1E:UUUUX01X13X32W5W4W2W6o"). Qed.

Lemma ro_cells_read_at : forall m A cs k c n a,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01ah11nh21Ah31ch42csh51kh61mp;1p;3p;2p;4p;7p;6g0000j10Tg000Uj17Tg0013j16Tg001Vj13Tg0028j1;Tg00?jj3>Tg006Pj2=Tg007Fj25Tg007hj31Tg009Nj12Tg005>j14Tg008Bj28Tg008_j19Tg00:Bj4<Tg00;Gj1@Tg00B9j7?Tg00A[j6:Tg00=8#0#0#0R0#0#0#0#7#6R1%70#6R0#3[g00=]g00>;R2#;g00?0R3f6R4f5R5f4R63>%321=56f3R7,5231%269137f8R8%44'8#99117P3%24%;0R0#3R9p,4segsR:f;R;P5f0R<C<f7R=#@,50R031X13P1f9R>%4='8#9P:P;P<%2=C<=190X01f:P>P8P=P4P7f2F?P6P<E:P5f1E:UUUUX01X13X32W5W4W2W6o"). Qed.

Lemma rw_cells_cb_split : forall m A cs cs2 k n,
  rw_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> rw_cells m A cs2.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Hh13cs2h21nh31Ah42Hch53Hokh62Hwh72csh81kh91mp;1p;3p;4p;8p;5p;6g0000j10Tg000Uj1;Tg0013j19Tg001Vj1<Tg0028j1ATg002Xj36Tg003Nj45Tg004Ej12Tg005>j13Tg005^j41Tg00C4j38Tg007hj34Tg00Cnj37Tg00Dej8@Tg00Eej5?Tg00F_j5>Tg00A[j6:Tg00Gaj4=Tg00=8#0#0#0R0#0#0#0#;#9%;0#9#<[g00=]g00>;#AR0g00?0R1f5R2f4R3f3R436g00?Op,4segsR5f6R6P2P3C5P5P6P2%23#3C1g00H<R7f2R89824g00H\R934A76349402f9R3f8R:;66[[f0R;P5P:f7R<P6C5P5P3P:%2<#3C1A8:62=479A73<6940:P0f:R6?7:<R9f=R7f<R2;6;X10P5P2f;R=P9C5P5P2P=%29R9#3C1P5P2P=P6P:P<P4f1R>G@P1%26P5P7P2%3;C1X21P8P9P6P:P<P5P2P=P6P4D?P>D>E:C=P3P;E:W0W5W6W4P>P;O2n2001000000120000000W0X21W8X10W7W3W9o"). Qed.

Lemma ro_cells_cb_split : forall m A cs cs2 k n,
  ro_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> ro_cells m A cs2.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h03cs2h11Ah21Hh32Hch43Hokh52csh61kh71mh81np;1p;3p;8p;6g0000j10Tg000Uj15Tg0013j14Tg001Vj16Tg0028j1:Tg00?jj33Tg00C4j39Tg007hj32Tg00Cnj31Tg00Dej87Tg00A[j68Tg00=8#0#0#0R0#0#0#0#5#4%50#4#6[g00=]g00>;#:R0g00?0R1f5R2f4R3f3R433g00H<f2R5f1R6593g00H\32A12459203P0f6R7?134f9f8R8f0R933X00p,4segsP8f7P7P3P4P5P6G7P2P9E8W2W4W3X81W6X00W5W1W7o"). Qed.

Lemma cell_at_bound : forall cs k c, cell_at cs k = Some c -> (k + csize c <= cells_size cs)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "p'0h04posth12H0h21Hh33preh44__x1h54__x2h64__x3h74__x4h82csh93Hszh:4Hsz0h;2_Hh<7__arithh=4__ffh>8__varmaph?5__with@1chA4cstrhB5cstr0hC5cstr1hD5cstr2hE1ehF1khG1nhH1xi001xhI1yp;1p;2p;3p;5p;<p;4p;6p;7p;Bp;8g0028j1STg001Vj1qTg006Pj2CTg007Fj2ATg007hj30j1LTg00I<j5kTg004Ej11Tg00?OR0j2:Tg00J8R1j2?Tg009Nj18Tg00JRj25Tg00JiR2j26Tg005>R3j12Tg008BR4j2;Tg00KCR5j29Tg00K_j2<Tg00L9j2\Tg00L\j3[Tg00M9l<KTg00M^j4ZTg00NEj1=Tg00Njj1JTg00OIj2FTg00P2j1YTg00PPj2XTg00Q1j3WTg00QZj3ITg00RCj2VTg00Roj1UTg00SOj3GTg00Soj2HTg00TMj1TTg00Tkj4RTg00UIj1pTg00Ugj1oTg00VRj2nTg0000j1PTg00W5j2>Tg00WXj4DTg00XCj1lTg00Xej1iTg00YJj3ETg00Ymj2gTg00ZOj2fTg00[;j3eTg00[Zj4bTg00\Lj4cTg00]7j2aTg00A[j6`j7hTg00^4j3NTg00^Qj3QTg00_HlB_Tg00_nj7^Tg00`Rj8mTg00>;R6f2R7f1R8f0R95G63Np=3g00?0R:?089p=4f5R;f4R<f3R=?Q78;09':p=7AQ=78=0<9p=OAG689p=jP:P:P:g00=]R>P>P>g00a6P3P3P3P4g00aVP;P<P=P7P8P9MB_p=BP:P>P2P3P5g00b9P;P<P=P7P8P9M<Kp=]P8g00b[R5g00c:R2P2g00cZR4P9g00d:F^p=@P=P5P2P2P4P7P8P9Gmp=MAN689p=d%S6R5%q6R?1C781A6930P=P7P8P8P9DkA38=9R@905;%18RA/4<P5P;P<P=P@E7':X05,?5X35,?5P1P5f6R@A38<9RB50514A;P5P@P;P<PBE7':X05,?5X35%8=,5<%1;RB'6P9f8RCA38@9RD505f7RE,4AP5PCPEP@PDE7':X05,?5P1P5f9R1A37E9RD505%17RA/4CP5P1PCPEPDE7':X05%8E,5C%11RD'6P9f;RFA3<19RG505%1<f:RH'4P5PFPHP1PGE7':P0f<RGA3;H8RI50514BFP5PGPFPHPIE7%8F,5Gf=RI#1'6P9f>RBA3EG=505P5A3CI<RCf?RJ,C91A6B50?%1HRKf@RL'4RMP5P8PLPJA3HJ@R@E7fARN%8L'5RO/6A[]2X851CCB1A6I50?14DJP5A31B;RDPJPBPDE7P0PMP5P@PLPJP@DOA3FLE#1,6OP9%1GfBRO'4P5A3IO1RIfCR1POPIDOP:%1BRI1j1HRH#1'5ROfERFfDRE#8'5/69XG:%81R1,5ER@151KRM,5IR0'6%2ERD%21R?';RC%2IRA%2KRP,;?RQ';RR'9P@PCPEPD1<>DRCP1P?1<>?RSEBP0PRPIPA1<>ARRPMPQP1P?PSPKPP1<>PEBEBE]14IEA0>ADRPP:P>%L:P3%L>%28%2950>14891\893[XI:XH:PIPAPRPEPDPCM<KP8CZPP%=Fg00dZRP%2F'9%8FRF#=%2F,9P%1NRN#=%2N,9P%=I19PAg00e8RAg00edRI#JRN#J,F>g00=8RF#Y,X>1F>N5W>1F>I5I>5I>g00fC'V%UA3G%SAP>P>1H><P7%T>CRP81H>=CR%p>%o>RAP>1n>Pg00foRI%PFRN#P,>>RCCD,@A%l2R2PAP>%iF,>>RDg00gV1>>FRFCD,@AP2P>1>>NRN9E>FPIAE>NC9E>DCD,@ACMCM1gA4P9P7g00H<RAg00H\R4'<1f97=0A4dAe>P8Cbb=b>b?X4>X5>X6>X7>19P=A0>=81;7=1;=;,;<'9[[^4>^5>^6>^7>P9%1L#2%1E#2fI#8#2fJ#2P8P;O6b<bDbCbBbAb:Cc16@Oe1dBH#11aBHE`W;W9P8P9O2n2001000000121000000W1W2PJP9PGFhW1P8P9O2n2001000000121000000W1X05P8P9O2n2001000000121100000W1X35P8P9O2n2001000000121100000bEW2X@6XF:W8o"). Qed.

Lemma rw_cells_store_ok : forall m A cs k c (j : nat),
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c ->
  store_ok segs m (wa (A + Z.of_nat k)) j = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h04__x1h11Hh22H0h37__arithh44__ffh58__varmaph65__with74__x2h84__x3h94cstrh:5cstr0h;5cstr1h<1jh=1Ah>2Hch?2Hkh@2HwhA1chB2cshC1khD1mp;1p;3p;4p;2p;9p;6p;Bp;<p;7p;8g0000j14Tg000Uj1JTg0013j1CTg001Vj1>Tg0028j1KTg002Xj3XTg003Nj4FTg004Ej12Tg005>R0j10Tg005^j4@Tg006Pj2?Tg007Fj2ATg007hj37Tg009Nj13Tg008BR1j26Tg008_j1GTg00h=j4ITg00i=j4VTg00JRj2ETg00JiR2j2DTg00KCR3j29Tg00K_j28Tg00M^j4RTg00NEj15Tg00Roj1QTg00Soj2:Tg00UIj1PTg00Ugj1OTg00VRj2NTg00W5j2;Tg00WXj4HTg00XCj1MTg00Ymj2LTg00ZOj2UTg00[;j3bTg00[Zj4aTg00Tkj4`Tg00YJj3_Tg00Xej1^Tg00j8l9\Tg00A[j6YTg00_HlBZTg00M9l<[Tg00_nj7WTg00`Rj8]Tg00H<R4f0R5g00H\R637p=<g00?0R7P7P7g00=]R8P8P8g00a6P0P0P0P1g00aVf5R1f4R9f3R:f2R;f1R<P5MBZp=TP7P8P2P0P3g00b9P1P9P:P;P<P5M<[p=Sg00dZR3/95p=1P<g00b[R0g00c:R2P2g00cZR=P5g00d:FWp==P:P0P2P2P=P;P<P5G]p=Bg00=8R0#4R>#4#4R?#4#4#4#J#C%J?#C#>[g00>;R?#KAX19:g00?Op,4segsR@f6RAP1P9CFP@PAP1%29#0C@%>?RB1?191A?:37%39977:P@f9R1f8RC%0A'6#GP9CI#<[[P5P@PCf7RDPACFP@P1PC%2D#0C@1?CD1A?A57B%3D977AP7%3CRAP@f=RBf<REf:RF#0RG'6#GP5CI#<X<7PFP1PCP<CV1E1A%2F'DP@PBPEf;R@#2RA#0RCPG%31R1P:1EF1RH/DA%01RI,6GRJ/9CRKPHPJPFPG188GP1PI188IETPAPC188CESP5CRRCPK%5@%0@#1%2BRB#5%0B#1%3ERB#5%0B#1g00e8RB#QR@%KBRB1:8<%P8RA%O8RIP81N83g00foR11;80RGCH,=IRJ%M2R2PJCB1LI=R=P5P;18461U5;#<dAb83<CaR3b4b5b6X08%15%1<[^08P5f?#0R6P:O2b3b;b:b9b2PCPK%3FRF#5%0F#1%5E%0E#1f>RE#2RF#5%0F#1P@PBP81:8;P<1:8:C`PAPIP81;8>9_8GP1%^0,;8CH,=IRIP2PICBP=P3b4b5b6X08X78X88165</9;16<;/9:[^08^78^88P5f@#2#0%3E#0P6P9O4b3b;b:b9b2M9\b1PDP5EYW1W?W@W>P<P5O2n2001000000121000000W1X<7XA?XC7WBX=8WDo"). Qed.

Lemma rw_cells_store_ok_at : forall m A cs k c (j : nat) a,
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c -> a = wa (A + Z.of_nat k) ->
  store_ok segs m a j = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01ah11jh21Ah31ch42csh51kh61mp;1p;3p;2p;4p;9p;6g0000j10Tg000Uj16Tg0013j14Tg001Vj13Tg0028j1@Tg002Xj3=Tg006Pj2<Tg007Fj2;Tg007hj31Tg009Nj12Tg005>j17Tg008Bj28Tg008_j15Tg00h=j4:Tg00K_j2?Tg00k3l9>Tg00A[j69Tg00=8#0#0#0R0#0#0#0#6#4R1%60#4#3[g00=]g00>;R0#@g00?0R2f6R3f5R4f4R53=%301<45f3R6,;031%259126f8R7%73'8#59116P2%23R8g00H<R9p,4segsR:f;R;P4f0R<C:g00H\R=31X12P1f9R>f7R?#7'8#5P:P;P<%2?C:=19=X01f:P>P7P?P3P8P6f21?28M9>P5P<E9P4f1E9UUUUX01X12X30W5W4W2W6o"). Qed.

Lemma rw_cells_write : forall m A cs k c c',
  rw_cells m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  rw_cells (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "p'0h01Hh14posth22Hwh32Hch42Hkh51nh63preh72csh81Ah93Hszh:4Hszph;3Hwfh<1ch=2c'h>1eh?1kh@1lhA1mi001xp;1p;3p;4p;2p;;p;5p;6p;7p;9g0000j1=Tg000Uj1QTg0013j1MTg001Vj1JTg0028j1ZTg002Xj3NTg003Nj4BTg004Ej10Tg006Pj2DTg007Fj2FTg007hj36Tg009Nj1?Tg00l2j1OTg00;Gj19Tg00lhj38Tg00^Qj32Tg00mll;XTg00I<j5WTg00?OR0j2>Tg00J8R1j2ETg00JRj2;Tg005>j1ATg005^j4CTg00]7j2KTg00nij6VTg00oEj7UTg00A[j6Gl9RTg00Gaj4STg008Bj2TTg008_j1YTg00SOj3PTg00^4j3ITf3R2f2R3f1R4f0R5#ACCp=@g00?0R6?645p=3%A5,T4#Yp=:P2P3P4%05#ACCp=5g00>;R7AP7457I3p=1A6345,>2p=7AP745p=4AI7459623p=<AI745p=Hf4R8A2234;65p=Lg00=8#=#=#=R9#=#=#=#Q#M%Q9#M#J[g00=]%Z7R9f5R:?N82P0p,4segsR;f6R<P:P8CBP;P<P:%08R=C@%J7R>1D:81F7236%?2%?8'3%O8f:R?f9R@f7RA':%9:38f8RB?2A:7N@[[[P5P;PBPAP<CBP;P@PBPAC51DBA1F7<56>%?<%?A'3%OAP;f=RCf<RD/:?%9B38REPDf;RF?2?BRGCBP;PEPDPGC5P;PCPDPFP?P@PBP8P3P4P5M;XPFP?P@PBP3DWA14F5RG969C%04RE/3DP9A2CD?RHA14?5C7'>X19,E9X69,E9P1P9P9f>RIP414D5C<13ECP9A2ICFPGC7'>X19,E9X69P;f?RG1:ID%9?38PIPHC5P5P9f@RHP414I5RJC<13EGP9A2HGCA14C5C7'>X19,E9P1P9P9fAR1P314G5C<%03/3HP9A21HIRK1H3JC7'>X19P;fCRJfBRL/:H%9I38PLPKC5P5P9PJP81415C<13=LP9A2JLHA18H5C7'>P0P9fDR=P:14L4C<%0:/3JP9A2=J1A1:14C7P;fGRJfFRK/:=%9L38PKfERM?2=LC5P5P9PKPA14=2C<P9A1BM8RMP;fJR=fIRNP5CBP;fKROP=PEC@1D3NfHR3,F756>%0D/3=REP9A22=3A1D3BR2C7P;fNRPfMRQ/:O%9N38RRPQA28ONC5[]4]2]3X79P;PNP3PMCBP;P=PNA1@K:C5A1?J</D31F7J56>%0F/3NP9A1F3A?2NJA1FJAC7P0PEP9A1DNBP=P3P2DLP;PRPQA1C=@?2ONC5P5%0IRNfLR='3P9A1G=FPQPOA1GOFDLP914=DRO,HHRFP;fRR@fQRRfO':R2%9QR338RBPRP5C5X@9P6%0HRE%0O';P;PBPR%A5R0CCX56P614QDRD,HHRA#0P;P@PRP0CCX56P<%0D,;ERE1KHDEVP;PRfPRDPEC@P6%?PREP;fS1:@D%9P38P@%0L1;5N';C@X56P;P@PR%01R1%0C,;E';#AP2P3P5FU%?QPKEGP;PBPR14QC#0,;1C@eb2%0F1KHOEGA2AP=P5EGW0W:P4P5O2n2001000000121000000W0W4W2W3PJP5PHPGPIM9RW0P4P5O2n2001000000121000000W0X19P4P5O2n2001000000121100000W0X69P4P5O2n2001000000121100000b>CSW;W9W4W2W3P4P5O2n2001000000121000000W0X=7X<7X?6W7W8WAo"). Qed.

Lemma rw_cells_frame : forall m A cs (a : Z) bs,
  rw_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  rw_cells (write_to_mem m (wa a) bs) A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Ah11Hh22Hah32Hch42Hdh52Hlh62Hwh71ah82bsh92csh:1mp;1p;3p;4p;2p;:p;7g0000j13Tg000Uj1?Tg0013j19Tg001Vj1@Tg0028j1<Tg002Xj3=Tg003Nj47Tg004Ej14Tg005>j11Tg005^j46Tg00KCj20Tg010=j25Tg008Bj22Tg010]j1>Tg011;j2DTg011Xj2;Tg008_j1:Tg00lhj38Tg0122l:CTg00oEj7BTg00Gaj4ATg00=8#3R0#3#3R1#3#3#3R2#?#9%?1#9R1#@[g00=]R3g00>;#<%<1f4R4f3R5f2R63=g00?Op,4segsR7f5R8P4P5C7P7P8P4%45#1C6g00dZR9/051515#1,24%>0%>2'DR2'0f7R0f6R:#4#1R;'2/081514#1,28/00';f9R<%::;88f8R=;=0[[[f0R>P7P0P:P8C7P7P=P0P;C6109:151:#1,20/02f:R2%4<#1'2/0=1510#1,2=/02';P7f<R0%:<R1;8=R:f;R9P2C7P7P:P9%42#1R:C6P7P0P9P2P<P=P4P6f1R6P>M:CP7P0P9P:P1P=P5FBCAW4W5W2W6W3P6P>O2n2001000000120000000W1W8X73W9W0W:o"). Qed.

Lemma ro_cells_frame : forall m A cs (a : Z) bs,
  ro_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  ro_cells (write_to_mem m (wa a) bs) A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Ah11ah22bsh32csh41mp;1p;3p;2p;:g0000j10Tg000Uj17Tg0013j16Tg001Vj1;Tg0028j18Tg00?jj3<Tg00KCj21Tg010=j25Tg005>j12Tg008Bj23Tg010]j14Tg011;j2:Tg004Ej19Tg011Xj2>Tg0122l:=Tg00=8#0R0#0#0R1#0#0#0R2#7#6%71#6R1#;[g00=]R3g00>;#8%81f4R4f3R5f2R63<g00dZ/161516#2,35%40%42':'1f6R2f5R0#9#2'3/141515#2,34/12'>p,4segsf8f7P2P0P4P5P6f1f0M:=UUUUW2X13W3W0W4o"). Qed.

Lemma rw_cells_bound : forall m A cs, rw_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Ah11Hh22H0h32_Hh42csh51mp;1p;3p;4p;2p;5g0000j10Tg000Uj18Tg0013j14Tg001Vj1:Tg0028j1?Tg002Xj3;Tg003Nj45Tg004Ej11Tg005>j12Tg005^j46Tg00KCj23Tg008Bj29Tg010]j17Tg011;j2>Tg00?OR0j2=Tg012oj5<Tg00=8#0R1#0#0R2#0#0#0R3#8#4%82#4#:[g00=]g00>;#?f2R2f1R4f0R53;P0p,4segsR0f3R6P2P4C5P0P6P2%14#2C6g00dZ/36%12#2,96%71%73'>'3'=P5P0f5R3f4R1P6C5P0f6R6P3%11#2C6P0f7P6P3P4D<W3W1P4P5O2n2001000000120000000W2W4W0W5o"). Qed.
Lemma ro_cells_bound : forall m A cs, ro_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h01Ah11Hh22csh31mp;1p;3p;5g0000j10Tg000Uj12Tg0013j11Tg001Vj13Tg0028j16Tg00?jj35Tg012oj54Tg00=8#0#0#0R0#0#0#0#2#1%20#1#3[g00=]g00>;#6f2R0f1R1f0R235p,4segsf3P0P1P2D4W1W2W0W3o"). Qed.

(* [comment removed for export] *)
Lemma mem_inv_store_cbytes : forall m a c',
  mem_inv segs m -> cell_wf c' -> store_ok segs m a (csize c') = true ->
  mem_inv segs (write_to_mem m a (cbytes c')).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) ["WithSegs"] "h04Hinvh13Hokh23Hwfh31ah42c'h51mh61np;1p;2p;4p;3p;6g0000j10Tg000Uj15Tg0013j14Tg001Vj16Tg013lj2=Tg00l2j1;Tg009Nj13Tg00h=j42Tg007hj31Tg00;Gj17Tg010=j28Tg014`j29Tg00A[j6:Tg015\j6<Tg00=8#0#0#0R0#0#0#0#5#4R1%50#4R0#6[g00>;p,4segsR2f2R3'=f1R4#;g00H<R5P2f4R6f3R7%33C2g00H\R831P2f5R9P6%77R6P3g00?0R3%37P2f6P9f0R9C2=158X63P918061974E:E<W1W2W0W4X31W5o"). Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma unsigned_Z_to_bv_add : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) + d) = Z_to_bv 64 (e + d).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h01zh12b1h22b2h31nh41Hh51dh61ep;1p;3p;2p;6g0013j15Tg007hj39Tg016Vj20Tg017@j3?Tg0000j14Tg000Uj1=Tg017dj27Tg008Bj21Tg018Jj22Tg0190j1<Tg019Yj26Tg00K_j2;Tg01:9j3>Tg00A[j68Tg01:`j2:Tg00=]R0f1R1f0R239p=3g01;OR3%52R4%51R5g00?Of2R6#5?912f3R7/061071'3R8[10611062'3%57?961[R9f4#5?976\8A?612P2n2001000000120000000W2W1W3P9^25^14^33P2g00=8#4#4#4#4#4#4#=R31736,03R4/11R5,73R91161R8,73R:P012351176R;,73,03R<,32X00P01236R=1126,23/3<X00P01238R<1237/16,23/32X00P0%<3R7,68R>16;7,32X001;0>1667/11/67A>617E811=1,23/3<e103:1:38E8P41:36E810391:35E8O4b4X50X60o"). Qed.

Lemma unsigned_Z_to_bv_add_r : forall e d, Z_to_bv 64 (d + bv_unsigned (Z_to_bv 64 e)) = Z_to_bv 64 (d + e).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h01zh12b1h22b2h31nh41Hh51dh61ep;1p;3p;2p;6g0013j15Tg007hj39Tg016Vj20Tg017@j3?Tg0000j14Tg000Uj1=Tg017dj27Tg008Bj21Tg018Jj22Tg0190j1<Tg019Yj26Tg00K_j2;Tg01;mj3>Tg00A[j68Tg01:`j2:Tg00=]R0f1R1f0R239p=3g01;OR3%52R4%51R5g00?Of2R6#5?912f3R7/061071'3R8[10611062'3%57?961[R9f4#5?976\8A?612P2n2001000000120000000W2W1W3P9^25^14^33P2g00=8#4#4#4#4#4#4#=R31736,03R4,11R5,73R91116R8,73R:P012351167R;,73,03R<,32X00P01236R=1162,23/3<X00P01238R<1237,16,23/32X00P0%<3R7,68R>16;7,32X001;0>1667,11/67A>617E8111=,23/3<e103:1:38E8P41:36E810391:35E8O4b4X50X60o"). Qed.

Lemma unsigned_Z_to_bv_sub : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - d) = Z_to_bv 64 (e - d).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h01zh12b1h22b2h31nh41Hh51dh61ep;1p;3p;2p;6g0013j15Tg007hj39Tg016Vj20Tg017@j3?Tg0000j14Tg000Uj1=Tg017dj27Tg01<Tj21Tg018Jj22Tg0190j1<Tg019Yj26Tg00K_j2;Tg01=1j3>Tg00A[j68Tg01:`j2:Tg00=]R0f1R1f0R239p=3g01;OR3%52R4%51R5g00?Of2R6#5?912f3R7/061071'3R8[10611062'3%57?961[R9f4#5?976\8A?612P2n2001000000120000000W2W1W3P9^25^14^33P2g00=8#4#4#4#4#4#4#=R31736,03R4/11R5,73R91161R8,73R:P012351176R;,73,03R<,32X00P01236R=1126,23/3<X00P01238R<1237/16,23/32X00P0%<3R7,68R>16;7,32X001;0>1667/11/67A>617E811=1,23/3<e103:1:38E8P41:36E810391:35E8O4b4X50X60o"). Qed.

Lemma bv_add_canon : forall (x y : word), (x + y : word) = Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h02b1h12b2h21nh31zh41Hh51xh61yp;1p;3p;2p;6g0000j13Tg000Uj1=Tg0013j12Tg007hj31Tg016Vj20Tg017@j3;Tg01=Yj3:Tg008Bj25Tg017dj26Tg018Jj24Tg00K_j28Tg01:`j29Tg00A[j67Tg01>>j3<Tg00=8#3#3#3#3#3#3#=R0#2R1g01;OR2f0R3#2R4f1R5#2R6g00?Of2R7#2?153g00=]R8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A;753P3n2001000000120000000W1W0W2P;^16^04^22P3P0A:075R21007R41005'5R6,60R;P81406R:1009/54R4,60,009183X38P8P:1404=183X38188:100;1906E71002A<075E7O4b4X61W5o"). Qed.

Lemma Z_to_bv_lit_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h02b1h12b2h21nh31Hh41xh51zp;1p;3p;2p;6g0000j13Tg000Uj1;Tg0013j11Tg007hj32Tg016Vj20Tg017@j3:Tg017dj29Tg018Jj25Tg01>lj26Tg01?_j37Tg01:`j24Tg00A[j68Tg00=8#3#3#3#3#3#3#;R0#1g01;OR1f0R2#1R3f1R4#1R5g00?Of2R6#1?242g00=]R7f3R8/06108432R9[10641062527%18?264[R:f4#1?286\9A:642P2n2001000000120000000W1W0W2P:^15^03^21P2P01004R1,90R3P4P7150110069272X571604970110031401E8O4b3W4o"). Qed.

Lemma wa_of_Z_to_bv : forall E e, E = e -> wa e = Z_to_bv 64 E.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h01Eh11ep;3p;1p;2p;6g007hj31Tg0000j10Tg000Uj14Tg0013j13Tg008_j17Tg017dj22Tg00K_j26Tg00A[j65Tg00=]R0f1R1f0R2510P0P1g00=8#0#0#0#0#0#0#4R3#3R4f2R5#7123231X001231,64P5P2E5UX10W0o"). Qed.
Lemma wa_of_var : forall (x : word) e, bv_unsigned x = e -> wa e = x.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "h01eh11xp;1p;2p;3p;6g0000j10Tg000Uj17Tg0013j14Tg016Vj22Tg007hj31Tg008_j13Tg01@Kj16Tg00nij65Tg00=8#0#0#0#0#0#0#7R0#4R1g00=]R2f1R3,20f0R4512P2f2R5,20R0%34f3511X02%65%30=115eP3P4E5UW0W1o"). Qed.

Lemma store_bytes_8' : forall v : word, Z_to_le_bytes 8 (bv_unsigned v) = le8 v.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "g01AIo"). Qed.
Lemma store_bytes_4' : forall v : word, Z_to_le_bytes 4 (bv_unsigned (low32 v)) = le4 v.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "g01BCo"). Qed.
Lemma store_bytes_2' : forall v : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v)) = le2 v.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "g01C=o"). Qed.
Lemma store_bytes_1' : forall v : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v)) = le1 v.
Proof.
ltac2:(KReplay.run1 (kr_t_Step ()) [] "g01D7o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac slia := first [ exact I | lia | split; [lia|exact I] ].

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac fold_closed_in_goal :=
  repeat match goal with
  | |- context [bv_unsigned (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_unsigned (@BV n z p)) in change (bv_unsigned (@BV n z p)) with v
  | |- context [bv_signed (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_signed (@BV n z p)) in change (bv_signed (@BV n z p)) with v
  | |- context [bv_signed (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_signed (bv_concat n a b)) in is_Zlit v; change (bv_signed (bv_concat n a b)) with v
  | |- context [bv_unsigned (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_unsigned (bv_concat n a b)) in is_Zlit v; change (bv_unsigned (bv_concat n a b)) with v
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
        replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
        replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [bv_swrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_swrap n z) in
        replace (bv_swrap n z) with v by (vm_compute; reflexivity)
  | |- context [bv_wrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v by (vm_compute; reflexivity)
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  | |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
        replace (Z.add (Z.add x a) b) with (Z.add x v) by (exact (Z.add_assoc x a b))
  | |- context [Z_to_bv 64 (Z.add ?x 0)] => rewrite (Z.add_0_r x)
  end.

(* [comment removed for export] *)
Ltac fold_lit_load :=
  repeat match goal with
  | |- context [bv_extract 0 ?n (le_bytes_to_word ?bs)] =>
      lazymatch bs with (_ :: _)%list => idtac end;
      let t := constr:(bv_extract 0 n (le_bytes_to_word bs)) in
      let z := eval vm_compute in (bv_unsigned t) in
      is_Zlit z;
      rewrite (bv_lit_eq n t z) by (vm_compute; reflexivity)
  | |- context [@sext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@sext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [@zext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@zext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [low32 (Z_to_bv 64 ?z)] =>
      is_Zlit z;
      let t := constr:(low32 (Z_to_bv 64 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 32 t z') by (vm_compute; reflexivity)
  | |- context [nan_box (Z_to_bv 32 ?z)] =>
      is_Zlit z;
      let t := constr:(nan_box (Z_to_bv 32 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Ltac simp_is_x0 :=
  repeat match goal with
  | |- context [is_x0 ?r] => let v := eval vm_compute in (is_x0 r) in change (is_x0 r) with v
  end; nc_beta_iota.

(* [comment removed for export] *)
Ltac is_concrete_map R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end.
Ltac map_cbv_get := lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [tget] in G in change_no_check G' end.
Ltac map_cbv_set := lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [tset] in G in change_no_check G' end.

Ltac norm_fchain :=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?k ?x (@bvmap_set 5 word ?k' ?y ?R)] =>
      let a := eval vm_compute in (bv_unsigned k) in
      let b := eval vm_compute in (bv_unsigned k') in
      let c := eval vm_compute in (Z.compare a b) in
      lazymatch c with
      | Eq => rewrite (bvmap_set_set_same' k k' x y R) by reflexivity
      | Gt => rewrite (bvmap_set_set_comm k k' x y R) by reflexivity
      end
  end.

Ltac simp_regs :=
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
      map_cbv_get
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      map_cbv_set
  | |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
      first [ rewrite (freg_get_same R k r v) by reflexivity
            | rewrite (freg_get_other R k r v) by reflexivity ]
  end;
  norm_fchain.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac exec_cbv :=
  lazymatch goal with |- ?G =>
    let G' := eval cbv beta iota zeta delta [lift_result interp_eff interp_eff_accesses drop_access_report access_value accessed_ranges
     exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in G in
    change_no_check G' end.

(* [comment removed for export] *)
Ltac vnorm_rw_for i :=
  lazymatch i with
  | OpImm ALU_ADD _ _ _ => rewrite ?alu_addi
  | OpImm ALU_AND _ _ _ => rewrite ?alu_andi
  | OpImm ALU_OR _ _ _ => rewrite ?alu_ori
  | OpImm ALU_XOR _ _ _ => rewrite ?alu_xori
  | OpImm ALU_SLT _ _ _ => rewrite ?alu_slti
  | OpImm ALU_SLTU _ _ _ => rewrite ?alu_sltiu
  | ShiftImm ALU_SLL _ _ _ => rewrite ?alu_slli
  | ShiftImm ALU_SRL _ _ _ => rewrite ?alu_srli
  | ShiftImm ALU_SRA _ _ _ => rewrite ?alu_srai
  | Op ALU_ADD _ _ _ => rewrite ?alu_add
  | Op ALU_SUB _ _ _ => rewrite ?alu_sub
  | Op ALU_SLT _ _ _ => rewrite ?alu_slt
  | Op ALU_SLTU _ _ _ => rewrite ?alu_sltu
  | Op ALU_AND _ _ _ => rewrite ?alu_and
  | Op ALU_OR _ _ _ => rewrite ?alu_or
  | Op ALU_XOR _ _ _ => rewrite ?alu_xor
  | Op ALU_SLL _ _ _ => rewrite ?alu_sll
  | Op ALU_SRL _ _ _ => rewrite ?alu_srl
  | Op ALU_SRA _ _ _ => rewrite ?alu_sra
  | OpImm32 _ _ _ => rewrite ?w_addiw
  | ShiftImm32 ALU_SLL _ _ _ => rewrite ?w_slliw
  | ShiftImm32 ALU_SRL _ _ _ => rewrite ?w_srliw
  | ShiftImm32 ALU_SRA _ _ _ => rewrite ?w_sraiw
  | Op32 ALU_ADD _ _ _ => rewrite ?w_addw
  | Op32 ALU_SUB _ _ _ => rewrite ?w_subw
  | Op32 ALU_SLL _ _ _ => rewrite ?w_sllw
  | Op32 ALU_SRL _ _ _ => rewrite ?w_srlw
  | Op32 ALU_SRA _ _ _ => rewrite ?w_sraw
  | Mul M_MUL _ _ _ => rewrite ?m_mul
  | Mul M_MULH _ _ _ => rewrite ?m_mulh
  | Mul M_MULHSU _ _ _ => rewrite ?m_mulhsu
  | Mul M_MULHU _ _ _ => rewrite ?m_mulhu
  | Mul M_DIV _ _ _ => rewrite ?m_div
  | Mul M_REM _ _ _ => rewrite ?m_rem
  | Mul32 M_MUL _ _ _ => rewrite ?w_mulw
  | Mul32 M_DIV _ _ _ => rewrite ?w_divw
  | Mul32 M_REM _ _ _ => rewrite ?w_remw
  | Mul32 M_DIVU _ _ _ => rewrite ?w_divuw
  | Mul32 M_REMU _ _ _ => rewrite ?w_remuw
  | Lui _ _ => rewrite ?b_lui
  | Auipc _ _ => rewrite ?b_auipc
  | Load _ _ _ _ _ => rewrite ?b_addsext
  | Store _ _ _ _ => rewrite ?b_addsext
  | FLoad _ _ _ _ => rewrite ?b_addsext
  | FStore _ _ _ _ => rewrite ?b_addsext
  | Jalr _ _ _ => rewrite ?b_addsext
  | Jal _ _ => rewrite ?b_addsext
  | Branch _ _ _ _ => rewrite ?b_addsext
  (* [comment removed for export] *)
  | Fsgnj _ _ _ _ _ => rewrite ?sgnj_self, ?sgnjx_self, ?sgnjn_self
  | Fmv _ _ _ _ => rewrite ?fmv_x_w_val; fold_lit_load
  | Fari _ _ _ _ _ _ => idtac
  | Fcmp _ _ _ _ _ => idtac
  | Fcvt _ _ _ _ _ => idtac
  | Fsqrt _ _ _ _ => idtac
  | Fminmax _ _ _ _ _ => idtac
  | Fclass _ _ _ => idtac
  | Csr _ _ _ _ => idtac
  | CsrI _ _ _ _ => idtac
  | _ =>
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc
  end.

Ltac nc_unfold_v :=
  lazymatch goal with |- ?G =>
    let G' := eval unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt in G in
    lazymatch G' with G => idtac | _ => change_no_check G' end end.
Ltac vnorm_tail :=
  (match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end);
  (match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
  (match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end);
  nc_unfold_v;
  (match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r | _ => idtac end);
  fold_closed_in_goal;
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] => rewrite ?ret_pc_fold | _ => idtac end);
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac vnorm_for i := vnorm_rw_for i; vnorm_tail.

Ltac vnorm :=
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc, ?lit_add_lit, ?w0_lit, ?w1_lit;
  nc_unfold_v;
  rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r;
  fold_closed_in_goal;
  rewrite ?Z_to_bv_lit_self, ?ret_pc_fold;
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlit a := lazymatch a with Z0 => a | Zpos _ => a | Zneg _ => a end.

Ltac addr_diff E A :=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
      | X => zlit c1
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  end.

(* [comment removed for export] *)
Ltac addr_expr a :=
  lazymatch a with
  | Z_to_bv 64 ?E => E
  | wa ?E => E
  | _ => constr:(Z.add (bv_unsigned a) 0)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lit_of_nat_in H :=
  repeat match type of H with
  | context [Z.of_nat ?n] =>
      lazymatch n with O => idtac | S _ => idtac end;
      let z := eval vm_compute in (Z.of_nat n) in diet_is_zlit z; change (Z.of_nat n) with z in H
  end.
Ltac lit_of_nat_goal :=
  repeat match goal with
  | |- context [Z.of_nat ?n] =>
      lazymatch n with O => idtac | S _ => idtac end;
      let z := eval vm_compute in (Z.of_nat n) in diet_is_zlit z; change (Z.of_nat n) with z
  end.

Ltac addr_eq_tac := symmetry; first [ apply wa_of_Z_to_bv; lit_of_nat_goal; lia | apply wa_of_var; lit_of_nat_goal; lia | unfold wa; f_equal; lit_of_nat_goal; lia ].

(* [comment removed for export] *)
Ltac cells_cbv :=
  lazymatch goal with |- ?G =>
    let G' := eval cbv beta iota zeta delta [cell_at cell_upd csize cells_size Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add cbytes] in G in
    change_no_check G' end.
Ltac nc_cb_split_cbv :=
  lazymatch goal with |- ?G =>
    let G' := eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in G in
    change_no_check G' end.

Ltac eval_cb_split cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split cs kn n).
Ltac eval_cb_split_ok cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split_ok cs kn n).

(* [comment removed for export] *)
Ltac split_for_access H segs m A cs kn n :=
  let ok := eval_cb_split_ok cs kn n in
  lazymatch ok with
  | true =>
      let cs2 := eval_cb_split cs kn n in
      lazymatch cs2 with
      | cs => idtac
      | _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
                   | apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
             [ | cells_cbv; reflexivity | nc_cb_split_cbv; reflexivity ]
      end
  end.

Ltac eval_cell_at cs kn := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn).



(* [comment removed for export] *)
Ltac load_post :=
  (lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [cbytes] in G in lazymatch G' with G => idtac | _ => change_no_check G' end end);
  rewrite ?load_u64, ?zext_extract_le4, ?sext_extract_le4, ?zext_extract_le2, ?sext_extract_le2,
          ?zext_extract_le1, ?sext_extract_le1, ?zext_extract_byte, ?sext_extract_byte;
  fold_lit_load.

(* [comment removed for export] *)
Ltac solve_load_base :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        (* [comment removed for export] *)
        let inr := eval vm_compute in (Z.leb 0 k && Z.ltb k (Z.of_nat (cells_size cs0)))%bool in
        lazymatch inr with true => idtac | false => fail end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        (* [comment removed for export] *)
        let inr := eval vm_compute in (Z.leb 0 k && Z.ltb k (Z.of_nat (cells_size cs0)))%bool in
        lazymatch inr with true => idtac | false => fail end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | (* [comment removed for export] *)
                replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

(* [comment removed for export] *)

Ltac solve_load := solve_load_base.

Ltac solve_store :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        (* [comment removed for export] *)
        let inr := eval vm_compute in (Z.leb 0 k && Z.ltb k (Z.of_nat (cells_size cs0)))%bool in
        lazymatch inr with true => idtac | false => fail end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          nc_beta_iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                (* [comment removed for export] *)
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        nc_beta_iota
    end
  end.

(* [comment removed for export] *)
Ltac cell_of_bytes bs :=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  end.

(* [comment removed for export] *)
Ltac nc_cbn_sizes :=
  lazymatch goal with |- ?G =>
    let G' := eval cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in G in
    lazymatch G' with G => idtac | _ => change_no_check G' end end.
Ltac nc_cbn_length :=
  lazymatch goal with |- ?G => let G' := eval cbn [length] in G in lazymatch G' with G => idtac | _ => change_no_check G' end end.
Ltac simpl_sizes :=
  rewrite ?app_length;
  nc_cbn_sizes;
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; nc_cbn_length.

Ltac transport_chunks segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac mem_after_store :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          (* [comment removed for export] *)
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rm_proof rm c :=
  let z := eval vm_compute in (bv_unsigned rm) in
  lazymatch z with
  | 7%Z =>
      lazymatch c with
      | Core _ _ _ ?fc _ =>
          lazymatch goal with
          | FRM : frm0 fc |- _ => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) FRM)
          | _ => fail 100 "FP instruction with dynamic rounding mode: need a hypothesis [frm0" fc "]"
          end
      end
  | _ =>
      let md := eval vm_compute in (match rmode_of_Z z with Some md => md | None => RNE end) in
      constr:(rmode_static rm c md (@eq_refl bool false) (@eq_refl (option rmode) (Some md)))
  end.

(* [comment removed for export] *)
Ltac exec_pre i :=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
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

(* [comment removed for export] *)
Ltac prove_frm0 :=
  first [ assumption
        | apply frm0_accrue; prove_frm0
        | apply frm0_slice_set_fflags; prove_frm0 ].

Ltac norm_fcsr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.

Ltac post_step i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => norm_fcsr
  | Fcmp _ _ _ _ _ => norm_fcsr
  | Fcvt _ _ _ _ _ => norm_fcsr
  | Fsqrt _ _ _ _ => norm_fcsr
  | Fminmax _ _ _ _ _ => norm_fcsr
  | Fma _ _ _ _ _ _ _ => norm_fcsr
  | Csr _ _ _ _ => norm_fcsr
  | CsrI _ _ _ _ => norm_fcsr
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac step_body w i sz k :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
        eapply evt_step;
        [ split; [reflexivity|];
          diet_rhs_open;     (* [comment removed for export] *)
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          diet_rhs_close;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i; k ]
  end.

Ltac step_core_k segs pc k :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) => diet_run ltac:(idtac; step_body w i sz k) ltac:(idtac; diet_open i; step_body w i sz k; diet_close)
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step_k k :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_k segs pc k
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Ltac step := step_k ltac:(idtac).
(* [comment removed for export] *)
Ltac step_core segs R F pc fc rv m ro := step_core_k segs pc ltac:(idtac).

(* [comment removed for export] *)
Ltac unfold_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb].
(* [comment removed for export] *)
Ltac fold_lit_ux :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  end.
Ltac solve_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac solve_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec
  | _ => solve_cond_base
  end.
Ltac solve_cond := unfold_cond; fold_lit_ux; solve_cond_rec.
(* [comment removed for export] *)
Ltac if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with true; [nc_iota| symmetry; solve_cond])
               ltac:(idtac; diet_open_cond c; replace c with true; [nc_iota; diet_close | diet_close; symmetry; solve_cond])
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with false; [nc_iota| symmetry; solve_cond])
               ltac:(idtac; diet_open_cond c; replace c with false; [nc_iota; diet_close | diet_close; symmetry; solve_cond])
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with true; [nc_iota| symmetry; exact H])
               ltac:(idtac; diet_open_cond c; replace c with true; [nc_iota; diet_close | diet_close; symmetry; exact H])
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      diet_run ltac:(idtac; replace c with false; [nc_iota| symmetry; exact H])
               ltac:(idtac; diet_open_cond c; replace c with false; [nc_iota; diet_close | diet_close; symmetry; exact H])
  end.
(* [comment removed for export] *)
Ltac if_cases H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      destruct c eqn:H; [ | ]
  end.

(* [comment removed for export] *)
Ltac fold_lit_ux_in H :=
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  | context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  end.
(* [comment removed for export] *)
Ltac zify_bool H :=
  lazymatch type of H with
  | negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H; zify_bool H
  | negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = true => apply Z.eqb_eq in H; apply (proj1 (zb_b2z_zero b)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = false => apply Z.eqb_neq in H; apply (proj1 (zb_b2z_nonzero b)) in H; zify_bool H
  | Z.eqb _ _ = true => apply Z.eqb_eq in H
  | Z.eqb _ _ = false => apply Z.eqb_neq in H
  | Z.ltb _ _ = true => apply Z.ltb_lt in H
  | Z.ltb _ _ = false => apply Z.ltb_ge in H
  | Z.leb _ _ = true => apply Z.leb_le in H
  | Z.leb _ _ = false => apply Z.leb_gt in H
  | andb _ _ = true =>
      apply andb_true_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | orb _ _ = false =>
      apply orb_false_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | _ => idtac
  end.

Ltac zify_cond H :=
  rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H;
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; zsimp_in H;
  zify_bool H.

(* [comment removed for export] *)
Ltac concretize_regs :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let t := eval vm_compute in R in change R with t
  end.

(* [comment removed for export] *)
Ltac zstep := step_k ltac:(zsimp).      (* [comment removed for export] *)
