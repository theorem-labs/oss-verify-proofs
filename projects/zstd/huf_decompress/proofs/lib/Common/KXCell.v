(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KXCell () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common7KXSound3KXS9mem_denotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib6Common6KXExec3KX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK69OSSVerify5KrLib6Common6KXExec3KX26sentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appI69OSSVerify5KrLib6Common6KXExec3KX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib6Common6KXExec3KX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib6Common6KXExec3KX24expr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS8log_flatC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00I47Corelib4Init5Logic3and00C47Corelib4Init5Logic7and_indC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib6Common7KXSound3KXS4flatC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC59OSSVerify5KrLib3Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib3Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C47Corelib7Classes?RelationClasses>iff_TransitiveK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXCell?kx_rw_cells_appC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame9stk_carveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib6Common7KXSound3KXS6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem9log_apartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXCell<log_flat_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?stk_of_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem:kx_stk_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXCell=kx_cell_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem9kx_mem_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXMem?kx_rw_cells_logC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common6KXCell=mem_denot_appC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityc59OSSVerify5KrLib6Common6KXCell=kx_cell_storeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma mem_denot_app : forall E m l1 l2, mem_denot E m (l1 ++ l2) = mem_denot E (mem_denot E m l2) l1.
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) [] "p'0h02l1h11Eh22IHh31ah42a0h51lh62l2h71mh81oh91vh:1wi006e_addri015e_vali027e_widthi031sp;1p;3p;2p;6p;5p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9g001ij13Tg002Nj1:Tg002lj17Tg003Oj1<Tg0041j1BTg004Qj30Tg005Rj31Tg005lj26Tg006Fj1=Tg006fj35Tg007Fj28Tg008Cj29Tg009@j2;Tg00:Hj34Tg00;>j6ATg00;\j3@Tg00<[j5?Tg00==j3>Tg00=ZR0f1R1f0R23>p=2g00>Yg00?U#3#3#3R3#3#3#3#:#7%:3#7#<[R3%B0R4P0f4R5f3R6122130A0561=052513X04f2R7=062R8,63%=0R9/229067A0689513eP0f6R9f5R8122630A0986=092513f7R:A5071R;/25709A0:95=0:;513[^54P2g00@:g00A8g00AWf;R;f:R:f8R9,2230A0;:9=0;2513P3f<R9f9R<909;R=;01R>f=R?/88R819?6,;5R@542A0?9:=0?7?48@513X8318951997,;654>,63121<909;P2EAA@567=501R6/2<909;A09=6513eW2X04W9W:W3P7P1P2O3n01103000131100102101X40P1D?X64W0W7W1o"). Qed.

Lemma log_flat_app : forall E l1 l2, log_flat E (l1 ++ l2) -> log_flat E l1 /\ log_flat E l2.
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) [] "p'0h01Hh12l1h22a0h31Eh42H0h52H1h62H2h72H3h82H4h92H5h:2H6h;2IHh<1ah=1lh>2l2h?1vh@1wi006e_addri015e_vali027e_widthi031sp;1p;2p;4p;3p;5g0041j1BTg00BTj20Tg00CTj49Tg006Fj1=Tg006fj38Tg00Coj15Tg00DNj26Tg00DhR0j21Tg00ECj5ATg00;\j3<Tg00<[j5@Tg00==j3;Tg00E`j1>Tg00F@j3?Tf2R1g00=ZR2f1R3f0R43;'0p=71013/14p=4%>49?13p=2A;234p=:1034,11p=3g00>Y%B2R5P2f3R6?743f4R71071743[X151014g00G<1063R8g00GXP4C9W0%=2R9=714A4698[eP2f5R9?746f6R81087743[A8213=787f7R:A826110:934[[^=5P4g00@:g00A8g00AWf:R;f8R<774f;R=f9R>,0=743[g00H4#5#5#5#5#5#5#5#5R?,66A2=761:3>73='1P0167?f<R@?2971:1;73@169?f=RA?289?3A6'1?3A=P4168?f?RB?2<:1:9A73BP0f@RC?2><f>R<97C816>?fAR8?2;>?38:'1?38BP4fBR:?2=;fCRD?7>8P>P4O1fDR8108:74;P0fER0/0=100D16<?fFRE?2B<?3E@'1?3E8P4fGRF/0AfHRG/0EP<P9O1fIR<10<F74BfJRB/0CRC10BGRG16:?A2BD:/1C'1/1GfK/0<168?R?fLR<?208R010<:R:'1R8'110<BP?P8PAP0P:P>P3C9C9P4C9W:X9CP4DAb8W4W0P3P4O2n2001000000120000000b2W7W6P3P4O2n2001000000120000000W0W5P3P4O2n2001000000121000000W0A<761=823=7=>A<976=82110@;54@[eW;X15W?W@W<P1P3P4O3n01103000131100102101X22P3D@X>5W1W3o"). Qed.

Section Cell.
Variable segs : list Segment.

Lemma kx_rw_cells_app : forall m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) ["Cell"] "p'0h04__x1h14__x2h21ih31Hh44__x3h52L0h67__arithh74cstrh85cstr0h95cstr1h:4__ffh;8__varmaph<5__with=3HN0h>1ni001nh?1xh@4__p1hA2B2hB2HihC3Hi0hD1yhE2B1hF2HahG2L1hH2W1hI2W2hJ6__sat4hK1li011lhL5lemmahM1mhN1zhO1AhP1BhQ2HAhR3HA1hS3HA2hT2HNhU3HN1hV3HN2hW2HWhX3HW1hY3HW2hZ2WRh[6__sat3h\3cs1h]3cs2h^1si021sp%0p%1p&0p;1p;3p;2p;6p;4p;;p;5p;9p;<p;Bp;7p;8g001ij1WTg002Nk10?Tg002lk108Tg003Ok10HTg0041j1~Tg00==j3iTg00HSj16Tg00DhR0j22Tg00IJR1j2\Tg00Icj13Tg00J\k30CTg00KRR2j6{Tg00LDj14Tg00M>j48Tg00E`R3j11Tg00N3R4j20Tg00NPj47Tg00OBk20YTg00Onk20STg00Pij2FTg00Q@k40KTg00Qgm;0ITg00Rbk50GTg00S[k203Tg00T\j2>Tg00U<j6wTg00UXk10<Tg00V6k20]Tg00VSk10;Tg00CTj4MTg00W5R5j2ATg005Rk10:j3NTg00WQk20\Tg00X4k30[Tg00XQj4ETg00Y8k109Tg00YVk40ZTg00Z9j1<Tg006Fk10XTg00Z^j2xTg00[<k10WTg00[Zk10VTg00\Ek206Tg00\hj2cTg00]Kk20QTg005lj2STg00]mk20PTg00^Yk30NTg00_8k40MTg00Coj1uTg00_jj2aTg00`Sj3ZTg00a<j2tTg006fj3vTg00ahk10LTg00bFj4dTg00bdk30JTg00cGR6j2=Tg00ccj3nTg00dIj6`Tg00e2k10FTg00eWj4qTg00fBj4^Tg00fmj1pTg00g\j3bTg00;>j6sTg00hYk20DTg00i=j1TTg00iVS00k20BTg00j6k305Tg00jYj2eTg00k6k20ATg00k^k30RTg00lBk20@Tg00lck60TTg00mGk20UTg00nDk20eTg00oBj4|Tg0108k40dTg010km90cTg011el<}Tg012JmB0>Tg0130m<0bTg013Uk70=Tg0149k80aTg014]k30_Tg015@k70^Tg015dk60`Tf3R7f2R8f1R9f0R:#4C8p=[P7P8P9%1:C7p=op-0R;P1P9P:H0dp=hf5R<f4R='2P7P8P9P:C7'2p=yP=P7P8P9C8,2</2:p=GP;P1g016HP<P=P7P8P9P:N90cp>07P7P8P9P:C7,2=p>0Of6R>P<P=1>89#1,07P:C8'2p=DP=P7P81F9:#1C7p=B12<=P7P8P9%1:C7'2p=r1278/29/2:p=I1289/2:p=m1>9:#1p>00P=P71089P:C8p=]g00A8R??N9:p=J%1:,09p=jg0179R@/A:p=51F9:#1p=L1089/A:p=;1=9:,28p=:1089#p9b=7=N<:#Tp=@P7P8P9P:C8,2=p=z%69/2:p=kg017WRA?N9:p=C1SA:p=9P?PAP:P3P9P8P7P=P<P>f7RBf8RCM<}p=VP?P?P?PAPAPAg0185P3P3P3P4g018UP<P=P7P8P9P:NB0>p=RP?PAPAPAP3P3P<P=P7P8P9P:N<0bp=PPAPAPAPAPAPAP4P:P9P8P4P7P=P<P>PBPCf9R4NB0>p=fPAPAP5PBP5P>P<P=P7P8P9P:M<}p=_P8g0198S01g019WR5P5g01:7R3PAP9g01:WP:C^g01;>RDK0=p=HP7Q01P5P5P3P8P9P:L0ap=?B0_A9:p=KPAPAP6PBP6P>P<P=P7P8P9P:M<}p=lPAP9g01;^P:C^p=YP9Q01P5P5P3P:PDK0=p=OP8Q01P5P5P3P9P:K0^p=Q%3:#1p=UP>P<P=P7P8P9P:CMCMp=X%p99b78=N=:#Tp>0EAN89:#Tp>011>9:#1,08p>02P=P7P8P9C8,2<,2>/2:p=gP9Q01P5P5P3P:J0`p>04g00?US02#WRD#WR6#WRE#W#W#WRF$0?RG$08&0?E$08RE$0HRH[g01<ERI#~S03Q03AiI9:S04#6%69RJ%6:RK'2RL'\AiI89RI#6RMp,4segsRNP=P7PIC[RO'2RPPNP=P7%3ICoRI'2%68S05/2JRQ/2ORR/2IPPPRPMPQP:POPOg01=::0C;1RM/hOE{PIPI1hMIE{Q05PNP=P7%48S06C8ROPNP=P7%38S07#1RREyS08PJPNP=107RRP%49RSPNP=PP%39RP#1RTC7EGS09'2RUPU20Y;URVJ07WL20S9:%~ERW%4:RX9iESRYPQPNP=P7P:PIEG/\UXKWP?%3:RW,FPRIPNP=P7Q06=iESC8RZ,2QR[PNP=P7%1:S0:I0O/\UX>?PNP7P8PYC8PNP7P8PSC8RYPNP7P8PEPSPXFDR\'\PNP=P7Q07PPDBRP,2[POPNP=P7PEQ06PSFDRO,2QR]/2PR^P[P]P;P;^P;P1P;P;P1P1H0KP0P2PQ1hMQPZPOP:N;0IPPPP1hMPE{PUPUPVJ07WLPNP7P8PSPXI0GPLP\PNP7P8PIErS0;PU[PJPYPNP7P8PTC7PKPNP7108TS0<PXPNP7Q0<PWCoEGCIS0=P^[Q0;P0P]PP%67S0>PNP<P=%47S0?C8S0@PNP<P=%37S0A#1RPC7Q05PNP<10=PRPQ06PNP<PPPRC7EGCIP:%6=S0BQ0>PNP>P<%4=RRC8S0CPNP>P<PEPRQ0?FD3mP0%6<S0DQ0B'2PNPBP>%4<S0EC8S0FPNPBP>PEQ0EPRFDPNPCPB%3>S0G%3<S0HDB%6BRRPNP4PC%4BS0IC8S0J'2S0KPNP4PC%3BS0L#1RPC7%6>R]PNP410CPRP%4>S0MPNP4PPQ0G#1S0NC7EG3m[P:12R]S0OP0%6CS0PPRPNf;RRf:R]%44S0QC8PNPRP]PEQ0Q%4CS0RFDPNf<RPPR%3]S0S%34S0TDB%6RS0UPNf=R^PP%4RS0VC8S0WPNP^PP%3RS0X#1RWC7%6]RXPNP^10PWRW%4]S0YPNP^PWQ0S#1S0ZC7EGCI[[P:PNf>RWP^%4PRTC8PNPWP^PEPTQ0VFDP0PNf?RKPW%4^S0[C8PNPKPWQ0[-00EPTD]PNf@RTPK%3WS0\%3^S0]DB%6KS0^PNfARYPT%4KS0_C8S0`PNPYPT%3KS0a#1RJC7%6WS0bPNPY10TJRJ%4WS0cPNPYPJQ0\#1S0dC7EGCI[P:Q0`PNfBRJPY%4T-00EQ0_D]PNfCRUPJ%3YS0e%3TS0fDB203JB%4JS0g,>E%3JS0h'JP?%4US0i,>ES0jPNfFRIfER\Q0:Q0iD]X>?P8%3US0kP:EwPNP\fDRLQ0k'jS0lQ0gC8P0%5\%3LRSQ0k'L&0<DRV&0<FS0m+0]RF5;\%5:RM%3\RO/LS7::PHPNfHRZfGRQP9&0;ER2E@S0n[^2A'2%6\S0oPNPQPI%4\S0pDzPNPQPI%1OS0qC7%6LPNPQQ0q,0IROPLC[PNPQPOPSErS0r3mP8%5Q%3QRS%3IS0s'LS0t=;ZF%3ZRO/LSRS9:M:PHPNfKR1fJR[P9P2E@[^2A'2P0fIR_?;SF%3_RS/LO9:M:PHPNfLR`P1P9P2E@[^2APNP1P[P_C[,k_PNP1P[%1SS0uC7%6ZS0vPNP1Q0u,0[RaPZC[S0wPNP1Pa%1OS0xEy3mP:%3[S0y/LS=;1F%3`RS%31S0z'L9:M:PHPNfOROfNRaP9P2E@[^2A%6`RbPNPafMRc%4`RdC8Re'2RfPNPaPc%1SRgC7Rh'2%61S0{PNPa10cgRi%41S0|C8S0}'2S0~PNPaPiQ0z#1S10C7S11'2PfPhPbPePYPPCM%5c1AiFRe%3cRb#1Rh9:M:S12PHPNfPRfPOP9P2E@[^2ARj'21>EdRd/JS%1dRk/CgS13&0:?S14&0:AS15%19Q0:'C1J9:20\9:40[XD?X??S16PdPk%9kPSPg%9gRkM9VP4CES17Q131FbSRd#1Rl,0aRm/AF10hgRn=;aFS18P:X?ARo1A9:$09XDAX?AS19PmPoPnO1Rm,0aPoPoPoPAPAg01=j109:H0Z#9XMAX>AS1:PaPa%9aPlPmPoPoQ0:#9X??S1;PdPnPbPh%9hS1<PSPgPkEREPM:fPFPF%9FS1=1CFFeS1>G_P8CES1?Q18%4aS1@,>ES1A#<S1BQ1A#1Rk#5S1C%3aRS#<S1D%1SRn#5S1E%3fS1F#<S1GQ1F#1Rd#5S1Hg01>NRm$0XRl%~mRp1xA9&0WARq&0VARr206A@RsQ02,cARt5HrRu&0;5RvPuC?20Qr3RwP:P8g01?:Rxg01?ZRy'S20P:8=NxydB0NA@9H0MRyb:b;b<X0AS1I%59Rx\M^0AS1JP:fSRzPRO2b6b9b8b7b=b5PePjQ17Q13Q1?Q18Q1BQ1CQ1DQ1EQ1GQ1Hg00H4Rj#uRe#uS1K,aAS1L1aAe1aAjS1M5ZAS1N5ZAg01@:S1O't=vmlS1PPpPAPA1xA7S1QP8&0LAS1RCdP9Q1RCdPqPr1cA6R69HrsPvPr1cADRD/K6,Kt206AV>0JAGRG5HrPv1KtDR6=HrGC?C?PwPyb:b;b<X0AX1AX4A%58Rj1087Re=;9FS1S1AeF[[^0A^1A^4AP:fQR{#3S1T#1R|fRR}#3S1U#1R~PzP8P=O5b6b9b8b7b=b5Q12P8P91FSbS1V#1S1W,=9S1X,2x10nhS1Y,=9S1Z,2xPxQ1XPxQ1Z1S;x9nxxPo1=9:$09XDAX?AS1ZP9P9%99Q1WQ1YPoPoQ1;Q1VQ1YPSPn%9nS1YPbPhQ1<EREPGlE`Q1A/JS1CknS1<Q14Q15Q16Q1APk%9kPSPnQ1YM9VPRCES1AQ1<%3ORk/FSS1V#1S1W,0fS1X/AF%1kRb/0nS1[=;fFS1\PoQ19Q1XPoQ1[O1S1X,0fPoPoPoQ1:PfPf%9fQ1WQ1XPoPoQ1;Q1VQ1[PkPb%9bS1VPSPnQ1YEREPS1YM:fPFPFQ1>G_P=CES1XQ1\%4f,>ERS#<S1]%1S#5S1^Q1GQ1HQ1U#<S1_%5~S1`Q1K#u,aAS1KQ1N5ZAQ1O't=vmlPpPA1xA8S1NP9Q1QCdS1QPqPrQ02$0F,cARS9HrsPvPr1YtD,OrS029QruS1aPv1KDSS1b,Yt,OrS1c9QruC?C?PwPyb:b;b<X0AX1AX4A1=98S1d,2x107=9:j8[\j^0A^1A^4AP:%3zS1e#1S1ffTS1g#US1hPBP8P>O5b6b9b8b7b=b5CqO2WBX2ACMFXQ0~Q11Q0{Q0}PTPCCM%5iQ10=;iFS10A:M:gS11PHPNPf10OnS0~/09RiP2I0E[^2AS12'2Q17Q13Q1?Q18Q1BQ1CQ1DQ1EQ1GQ1HQ1PPpPAQ1NP9Q1RCdS1RPqPrAHrsDS1NPvPrPuPvAHrs6S1PC?C?PwPyb:b;b<X0AX1A%5eS1i\x\x^0A^1AP:P~PzP9PRO4b6b9b8b7b=b5Q10Q12Q17Q13Q1?Q18Q1BQ1CQ1DQ1EQ1GQ1HPlPpQ1QPqPrQ1b,KtS1b=HrGS1EPv1K6SRx=HrGS1DC?PwPyb:b;b<X0AX1AX4A1098S1C,0:RG/AFQ1C?;7F[^0A^1A^4AP:P|P~PzP=O4b6b9b8b7b=b5Q11Q1AQ1<Q1XQ1\Q1]Q1^Q1GQ1HQ1_Q1`PlPpQ1QPqPAQ1bg01@fS1bPxC^,OrPwPyb:b;b<X0AX1AX4A10:9S1`/08S1_,CG^0A^1A^4AP:PBQ1hfURGO3b6b9b8b7b=b510n9,0O/CiPA10b8Ri,0f%p:S1H9bN}>01H2XNAP7Pi%5iRxQ1W,=iS1G'2Q1[,=iS1^,2xPxQ1GPxQ1^1S;x9nxxPoQ1ZPiPi%9iQ1WQ1[Q1YGlE`%4OS1Y,>ERi/Jk%1iRx/CbS1[Q14Q15Q16PiPx%9xPkPbQ1VM9VPPCEQ1[Q1F/FkS1[#1S1^,0{S1G/AF10dbRi=;{FS1]PoQ19Q1GPoPiO1S1G,0{PoPoPoQ1:P{P{%9{Q1^Q1GPoPoQ1;Q1[PiQ1FPd%9dPkPbQ1VEREPM:fPFPFQ1>G_P<CEQ1]%4{,>ERk#<%1k#5Q1T#<%5|Q1e#<Q1f#5Q1KQ1LQ1M5ZA5ZAQ1O't=vmlPpQ1QPqPrPuPvPrQ1N1YDS,Or5QrPvQ1P1KtSRm,Y6,Or5QrC?C?PwPyb:b;b<X0AX1AX4AA:j87RjQ1i108=7:e[\M^0A^1A^4AP:Q1hPC%UGReP9PBO5b6b9b8b7b=b5CqO210fb/08P:Ewb3WBX2AFXFXWWWTP9P:O2n2001000000121000000W3WQP9P:O2n2001000000121000000bAbGWZWAWEP9P:O2n2001000000121000000W3XIXXHXP9P:O2n2001000000121000000W3P9P:O2n2001000000121000000W3P9P:O2n2001000000121000000W3Q0=P0Q08Q09Q0>Q05Q0@PNP<P=PEQ0?Q06FDPNP<P=Q0AQ07DBCIP:Q0BQ0CPNP>P<%3=ErP0Q0DQ0F'2PNPBP>Q0H#1RbC7Q0DPNPCQ0N,0BRkQ0EPNPCPkPbC7EGQ0OQ0JPNP4Q0I:02CEQ0MPNP4PCQ0LQ0GDBFg[P:Q0KP0Q0PPNP]P4Q0RC8PNPRP]Q0T#1RbC7%64PNPPQ0Z,0RR4Q0QPNPPP4PbC7EGQ0UPXQ0WPNP^PPPEQ0VQ0YFDPNP^PPQ0XQ0SDBCI[[P:Q0WPNPWP^%3PCoP0%5WRPQ0]#1Rb=;WFQ0d9:M:PHPNPYPTP9P2E@[^2A'2%6^PNPTQ0d,0KRKQ0[PNPTPKPbC7EGQ0^Q0bQ0`PNPYPTPEQ0_Q0cFDPNPYPTQ0aQ0\DBCI[P:%5TQ0f#1=;YFQ0e#1RT9:M:PHPNPLPUP9P2E@[^2A'2P0A;JTFQ0h#1Rb9:M:PHPNP\PLP9P2E@[^2A%6YPNPL10UbRbPYC[PNPLPbPTEy%6J,kUPNP\PLQ0iC8PNP\Q0j,jLQ0gPNP\PLQ0kQ0hDBFg[P:Q0l/AFQ0q9:M:Q0n[^2AQ0rP0Q0oPNPZQ0s,jQRLQ0pDzPNPZPLQ0qC7%6QRL%6IPNP_PZ%4QR\C8PNP_PZPEP\%4IFDPNP_PZQ0tC7CIP:PLPNP[Q0x,0_P\DzP0Q0vQ0wPNP`Q0y,j1Q0uC7Q0{%6[R\PNPcP`Q0|C8PNPcP`PEQ0|%4[FDPNPcP`Q0zQ0yDBCI[P:Q0}PNPO10ahPgC7P0Q0~#5Q0~?;hFA:M:nPHPNP}10{dRnP9P2E@[^2A'2%6a,kOPNP{PfQ1YC8PNP{10fxQ1@PNP{PfQ1WC7FgP:%5n10}|?;dFA:M:|PHPNPGQ1gQ1f'0P9P2E@[^2A'2P010z~?;|FA:M:~PHPNfVR~Q1h,0GR|P9P2E@[^2A%6},kzPNPGQ1g%4zRzC8PNPGQ1g@02Ez%4}PNPGQ1gQ1eQ1UDBFgP:Q1f=;|FA:M:ePHPNfYRefXR|fWRG#3R}#1Rz'0P9P2E@[^2A203~1%4~R0,>E%3~Rd'J%6GRn%6~R~'2RfPNPeP|%4GRGC8R{PNPeP|1>EGRx#1ROP0D]R0'2Ra'2PNPeP|1F}dRh#1RgC7PfPaPnP~P`PRCMP{P0P1P?P}PNfZR1PeQ0:PGD]X>?P]PxP:EsFX%5|10|gR?/AFRG%3|R0/L}9:M:R{PHPNf[RRP1P9P2E@[^2AR~'21Jx}1COzRnQ14Q15Q16PxPO%9OP}Pz%9zROM9VP:CERxPn%4|,>ERa#<Rf%1a#5Ra%<0Rc%10#5R0%31R1#<R[%11R1#5R_Q1IQ1JP:f]RLP`O2b6b9b8b7b5PGP~PG%1dRG,0zR~,0|R`/AFPoQ19P?P`PoPoPoQ1:P|P|%9|PgP~PoPoQ1;PhP~P}PzPOPdPG%9GEREPM:fPFPFQ1=G_PxPnPfPaPcP0P[P_PlPpQ1QPqPrQ1DPvQ1EC?PwPyb:b;b<X0AX1AX4AQ1_/AFQ1S[^0A^1A^4AP:%3RRR#1R_f\R[#3R0#1RcPLPBO4b6b9b8b7b5Cq%UeRe-0D91=9eRe%Te+0BQ001=81R1%T1PHPNPLP[P7P2E@P:1=7_R[PQP=%5=RQ1F0RR1#1Re,==Ra'210c_Rf9:Q=RnPQPaPQPoPfO1Ra,==1S;QAN;QQe9nQQPoQ1ZP=P=%9=PePaPoPoQ1;P1PfP0Pc%9cRfPRP_%9_EREPGlE`P7CER_Pn%4L,>ERR%3LR1'J%1RRa%11Re'CRQQ14Q15Q16PRPa%9aP1Pe%9eRaM9VP>CERRPQf^Rx#4,>ERG#<Rd%1GRO#5Rz%3xR}#<R~%1}Rh#5Rgf`R|#3R`#<R?%1`#5R`PlPpQ1RPqPr204r=9QruPvPrQ02PvQ1aC?C?PwPyb:b;b<X0AX1AX@;12M8Q1dPj[[^0A^1A^@;P:fb#URjfa#3RM#1Ru'0,=]PjP]P<P>O5b6b9b8b7b5bCO2WKP:O1%T[P_PnPRPQPdPzP~PgP?P`PlPpQ1QPqPAB05ASD,K6Q1bPmC^,OrPwPyb:b;b<X0AX1AX4AQ1`1e89'010:8'C^0A^1A^4AP:P]PjfcO3b6b9b8b7b5bC10Lc1e=c'010L='CPA10xe1e<eRL'0Q1H9bN|>01H2XNAPBPL%5<RL1F10R2#1RH,=<R|'210ecRj9:L<RmPLP|PLPoPjO1R|,=<1S;LAN;LLe9nLLPoQ1ZP<P<%9<PHP|PoPoQ1;P2PjP1PePaP0PcPfEREPGlE`P=CEPm1JG}1COhRmQ14Q15Q16PGPO%9OP}Ph%9hM9VPBCEPmf_Rm#4,>ERE#<%1E#5%3mRm#<%1m#5%<M%5uQ0m-0AV1=@VRuQ0m#51=@F[RM[%5VRmg00G<REQ0m>0RV9UWF%5F\E^FmP9g01AM20@@V'SPueO1PMPlPpQ1QPqPr204r<Q1c5QrPvPrPrQ01P5P5P3Q02J0TPvB05AtDRD9Hrs1YDS,Or5QrC?C?PwPyb:b;b<X0AX1AX4AX@;Q1C9:7:Q1dg01B3[1e87Ry#5?:y=[[^0A^1A^4A^@;P:PPfe#Uff#UPWPCP]O6b6bJb[bJb9b8b7b5bCO210x<P:Ewb3W>P:O1n200110200021110111100b^XB{X2ACMFXbGWYWVP9P:O2n2001000000121000000W3WSP9P:O2n2001000000121000000W3WAXI\P9P:O2n2001000000121000000W3P9P:O2n2001000000121000000W3WXWUP9P:O2n2001000000121000000W3WRP9P:O2n2001000000121000000W3WEXHXP9P:O2n2001000000121000000W3P9P:O2n2001000000121000000W3P9P:O2n2001000000121000000W3CMO2Q04#320U9:EsQ04#420e9:EsO2PNP7P8Q04C|PNP7P8P9C|PNP7Q0<P:C|'2'\eW]W\XOAWMo"). Qed.

Lemma kx_rwc_cons : forall m A c cs, rw_cells segs m A (c :: cs) <->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) ["Cell"] "h01Ah11Hh22H0h32H1h41ch52csh65lemmah71mh81np;1p;3p;4p;2p;9p;5p;6g001ij13Tg002Nj1<Tg002lj19Tg003Oj1=Tg0041j1FTg006Fj1DTg006fj36Tg00==j3:Tg00oBj40Tg00Icj18Tg00E`j11Tg00N3j22Tg00Dhj24Tg00IJR0j27Tg01BPj15Tg00OBj2ETg010kl9CTg01CDj4BTg00CTj4;Tg00ECj5?Tg0185j2@Tg01DFj1ATg00;>j6>Tg00?U#3#3#3R1#3#3#3#<#9%<1#9#=[g017Wg01<ER1%F1p,4segsR2f3R3f2R4f1R5%D1R6561R7f0R85:1C0P2P3P4P7C0R9P2P3%87#1,24P8C0'4R:'7p-0R;P0g016HP2f4R0P3A6146R<=:15C0P2P0P3P<C0R=P2P0%8<#1,23P5C0'4P8P2P0%54#1,23P5C0R<,4=R>P>1E;>M9CW6P3P4P7P8CBg00A8R7%55R;P2P0%18,23P5C0,4=/7>X87P2P3%1;,24P8C0,49R9P>[R7P7P=P<P>P2f5R>%53#1,20P4C0P2f6R4P>A6106C0P2P4%50#1,2>P3C0P5P8C;W3X2=P8D?X19R8P8C;g00H4,@;%A;E>17:9eO2W5W4W0W7o"). Qed.

Lemma kx_cell_write : forall m A (w : nat) (c : cell), stk segs m A (A + Z.of_nat w) -> csize c = w -> cell_wf c ->
  rw_cells segs (write_to_mem m (wa A) (cbytes c)) A [c].
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) ["Cell"] "p'0h04junkh14__x1h24__x2h31Wh41Hh52HJh63Hs0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=1zh>1Ah?2Hsh@3HwfhA1ShB2_HhC1ahD1chE1mhF1whG1xi001xhH1yp;1p;2p;4p;3p;7p;6p;9p;<g001ij1;Tg002Nj1PTg002lj1ITg003Oj1ETg00E`R0j10Tg00N3j29Tg01Djj4>Tg01BPj15Tg005Rj31j1FTg01E\j1KTg00WQj2STg00X4j3QTg005lj27Tg00XQj4NTg00Z9j1?Tg00W5j2<Tg006Fj1MTg0041j1LTg00Z^j2^Tg00ahj1]Tg00bFj4\Tg00[<j1[Tg00[Zj1ZTg00\hj2HTg014]j3YTg00j6j3XTg00fBj4GTg00]Kj2WTg00]mj2VTg00^Yj3UTg00_8j4TTg01FRj7RTg00jYj2DTg01GJj24Tg01H?R1j2CTg00DhR2j2gTg00fmj18Tg01HYj1=Tg01INj3:Tg00oBj46Tg00;>j6eTg01JRj2dTg01KHl9cTg01LDj3ATg01M;j1`Tg00U<j6_Tg011el<aTg013Uj7bTg006fj3@Tg00A8R3g017WR4f0R5P0f1R0f2R6f3R7f4R8f5R9f6R:f7R;f8R<M<ap=OP0g0198g019WR=P=g01:7R=P5g01;>Fbp=J1960/D5p=2P8P7P6g01<ER>?@05C6p=3A@>05p=f1460=@>5p=Bg00?UR?#;R@#;#;RA#;#;#;#P#I%PA#IRA#E[p,4segsRBP7P6%00RC,96C>%50=136%K6PBP:P9%08RD,99REP8P6%57RF=138%0FRG=14DRH%F3RI%F4RJ%05914CA13051S053QXH3XG3RCPFPG174GP8PD174DM9OP0CNPH%58RH#?g0179RG%0H'<%?:%0:RH,<Gg01>NRF#MRK%LFRFP41^46P0%]4C\RL%[4RM%Z4RNP41H4?R?g01:W1H4@R@9Y4?=X4@R@CG'J1WN=R=P5P6g01?:ROg01?ZRP'71V56=1OPdAU4G0CTRPb8b9b:X14X24A2500RO,<5^14^24P5%0<f9RQO2b7b<b;b6FRPBP:P91DEDC>%LARAPBP;%09RE=2:ERE1495%M>RDD3X0A'C'gP2PBP;P:PEC>PBP<A2;HH14:5PDD3X0A,CAPB%8;%=95:<P;P9PDD3P5PBPQP<%0;R;=2<;C>PBf;R;f:R<%0QRH;2H14Q5PDD3X0A,CAP1PAPBf<R1%0<RH=2;H14<5PDD3X0APB%8;%=Q5:1P;PQPDD3P5PBf>RQf=R;%01RH;2H1415PDD3%51RH=13;%0HRE%0;R2514RRPIPJPCPHPE174EP;P21742M9OP<CNPR%5;RR#?%0R,<Gf?RR#?%0R,<GPKPFPLPMP4P?g01@fP@CG,JNP=PPb8b9b:X14X24A145O^14^24P5fARO#0fBRPO2b7b<b;b6A2Q22914QP4%0QR2=2R2PBPOP514R7R7/fDR2C6X=4P0PRP5EePBf@R=PR14Q6PDD3PBPOP=P2g00H4R6P7PQP5%E>1d26'7M9c%5Q%57513%KRPBfCR7%06RQ,9P#8%==R23:PPABO9D?A6=R9C6[[P5P;P1O2PB19OQ#8%=R5:PPOAB=8D?A6RC6P419PGPBfD%85%=O3:P7ABP:D?A6OC6X=4P5PP%`PE_PB%8P=:72PPP9C6P5b3b3b3b5b4W5X0AP0P5O2n2001000000121100000W4WBP0P5O2n2001000000121000000bCW@W?WAXD>XF3X>4WEo"). Qed.

Lemma kx_cell_store : forall E m pre a (w : nat) v rest A (c0 c : cell),
  log_flat E (pre ++ SE a w v :: rest) -> rw_cells segs m A [c0] -> csize c0 = w ->
  estart E a = A -> log_apart E pre A (Z.of_nat w) ->
  cbytes c = word_to_le_bytes w (edenot E v) -> csize c = w -> cell_wf c ->
  rw_cells segs (mem_denot E m (pre ++ SE a w v :: rest)) A [c].
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) ["Cell"] "h01nh11Sh22Hfh33Hfrh41Ah51Eh61Hh72Hah83Haph92Hbh:2Hch;3Hfph<2Hsh=3Hs0h>3Hwfh?2_Hh@3_H0hA1ahB1chC2c0hD1lhE1mhF1ohG3prehH4resthI1vhJ1whK1zp;1p;3p;2p;4p;5p;6p;7p;9g001ij15Tg002Nj1PTg002lj1LTg003Oj1STg0041j1QTg00;\j37Tg00==j3DTg00BTj21Tg006Fj1VTg00oBj44Tg01BPj1>Tg005Rj3BTg01M\j2OTg00E`j10Tg01NZj4ATg01HYj1?Tg008Cj2FTg009@j2ETg01E\j1XTg01OUj4WTg00DhR0j2CTg004Qj33Tg00fmj1@Tg01INj3:Tg00Coj12Tg00DNj2MTg00F@j3=Tg00N3j28Tg01PTj5UTg00Icj1KTg01Djj4<Tg00Pij2JTg00U<j6GTg0185j2ITg01DFj1HTg01QRj7RTg01RNj7TTg00;>j6;Tg01SNj6[Tg01TIl9ZTg01UJj4YTg006fj3NTg00=ZR1f1R2f0R33Np=6g01<ER4?N23p=9g00>Yg00?U#5#5#5R5#5#5#5#P#L%P5#LR5#S[R6%Q1R7g00@:g00A8R8g00AWg017WR9f9R:f7R;f6R<f5R=f437f3R>'65D1'1p,4segsR?P:P>f2%V4R@'9C4%>>=B8;f<R>/O:=B9=f=RAf;RBP<%0:CA%Q5R5%?=f:R=f>RC/F:'E3B%><=B8B%X;fARDf?REA7CA>/6BRBP;CW11DE11DB'CP0fBRBf@RF'1A7ECA/6>,1BP?fCRGA7FEC/6A9D1D73BP>19=@C4P3fDR=/1BfER>A7BDF/6E'1P6fFRHA7GBD/6FRI93H>RJ;3=P?P3PF19C@RKC4XF6RLP?PHPJP=PE19A@RMP6A3H>F1OHGR6#@1FHD,EBRN3:PLP9PEP?fGRL?3HDRO%@31FLB,EG3:PFPKC4XK9P5%?AP?%@FR9=:O3PFPKC4XD5P0g00H4R5#2#2#2#2#2#2#2#2RP,MB%0B9=HG11HF'CP?%?C9:O9PFPKC4P31M=PfIRP%0>7=H11PG'CP0fJR0%0H7=L110=P?fKRK?30>%@=%?B3:P=19B@C4P3fLR9fHRO#07=PfMRQ/1LfNRR?3QOPLP0P>P?PRPQPOPL%00,8LP?PQPL19H@R@PGDUP?PQPL%K@#0,8LC<P8%>LP?fOR@PP1J35#0RQ,8PC<X08P3PKPGEGP?PRPO1JK5#0,8OC<P81I95P?fPP0%03RO,80C<X08P3P9%H9EGP?P@PP%09,8PC<P3b1b1b1FRPCPAFTW3W@P2P3O2n2001000000120000000W6W?P2P3O2n2001000000120000000PNP;EGP6P:E;PJPHP>PGPBPDPFE[E;P2P8PBPLP>PFPQCAX08P8PBPLP>PFPOCAX08f81IB5%HBE;%>AP<E;PHP=PE%KM#0CAeM9ZAD1=I93H>PHP>P=PICYE;W3W;P2P3O2n2001000000121000000b2W>W<W9W8W7W=W:W2XB4XC4W4XH7WIWJWAWGWEW5o"). Qed.

Lemma kx_cell_store8 : forall E m pre a v rest A w0,
  log_flat E (pre ++ SE a 8 v :: rest) -> rw_cells segs m A [C8 w0] ->
  estart E a = A -> log_apart E pre A 8 ->
  rw_cells segs (mem_denot E m (pre ++ SE a 8 v :: rest)) A [C8 (edenot E v)].
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) ["Cell"] "h01Ah11Eh22Hah33Haph42Hch52Hfh61ah71mh83preh94resth:1vh;2w0p;1p;3p;2p;4p;Bg001ij11Tg002Nj15Tg002lj14Tg003Oj1<Tg0041j19Tg00Coj10Tg00;\j3@Tg006fj38Tg00==j3>Tg00BTj2=Tg01VJj12Tg006Fj1;Tg00oBj4:Tg01M\j2FTg005Rj3Ej16Tg00UXj1DTg01NZj4CTg008Cj2BTg01W?j13Tg01Wnj47Tg009@j2ATg01X\lB?Tg00>Yg00?U#1#1#1R0#1#1#1#5#4R1%50#4R2#<[g00=ZR3#9R4g00@:g00AWg017WR5f7R6f5R7f4R8g00H4#0#0#0#0#0#0#0#0R9f3R:3@f2R;5835>3'=p,4segsP6P;g01<ER3f1R<#2%;338C:f9R3f6R='F=E5:f:R5f8R>P8%D0CCf;R0P5P3P>P9P6P=P7%281B06R0#2P:P;g00A8R;%6;%3;P9C7R;P<f0%92R2%62%321A90C7P;g00GXMB?W3W2W4W5X;1W0X94W:W6W8W7W1o"). Qed.

Lemma kx_cell_store4 : forall E m pre a v rest A w0,
  log_flat E (pre ++ SE a 4 v :: rest) -> rw_cells segs m A [C4 w0] ->
  estart E a = A -> log_apart E pre A 4 ->
  rw_cells segs (mem_denot E m (pre ++ SE a 4 v :: rest)) A [C4 (edenot E v)].
Proof.
ltac2:(KReplay.run1 (kr_t_KXCell ()) ["Cell"] "h01Ah11Eh22Hah33Haph42Hch52Hfh61ah71mh83preh94resth:1vh;2w0p;1p;3p;2p;4p;Bg001ij10Tg002Nj15Tg002lj14Tg003Oj1<Tg0041j19Tg00Coj11Tg00;\j3@Tg006fj38Tg00==j3>Tg00BTj2=Tg01Y\j12Tg006Fj1;Tg00oBj4:Tg01M\j2FTg005Rj3Ej16Tg00UXj1DTg01NZj4CTg008Cj2BTg01W?j13Tg01Wnj47Tg009@j2ATg01X\lB?Tg00>Yg00?U#0#0R0#0R1#0#0#0#5#4R2%51#4R1#<[g00=ZR3#9R4g00@:g00AWg017WR5f7R6f5R7f4R8g00H4#1#1#1#1R9f3R:3@f2R;5835>3'=p,4segsP6P;g01<ER3f1R<#2%;338C:f9R3f6R='F=E5:f:R5f8R>P8%D0CCf;R0P5P3P>P9P6P=P7%281B06R0#2P:P;g00A8R;%6;%3;P9C7R;P<f0%91R1%61%311A90C7P;g00GXMB?W3W2W4W5X;2W0X94W:W6W8W7W1o"). Qed.

End Cell.

(* [comment removed for export] *)
Ltac kx_estart_z zv :=
  let na := eval vm_compute in (length zv) in
  lazymatch goal with |- estart ?E ?a = ?A =>
    rewrite (estart_ez zv E (kE_atoms zv _) a);
    [ cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia
    | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
  end.

(* [comment removed for export] *)
Ltac kx_cell_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                    | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                              [ change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H
                              | change E with (kE zv xs); kx_estart_z zv
                              | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                        cbv [ez] in Hn; change (length zv) with na in Hn; cbv [nth Nat.ltb Nat.leb] in Hn;
                        rewrite ?Z_to_bv_bv_unsigned in Hn;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "kx_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac kx_cell H := kx_cell_gen H 8%nat.
Ltac kx_cell4 H := kx_cell_gen H 4%nat.

(* [comment removed for export] *)
Ltac kx_rwc_norm H :=
  lazymatch type of H with
  | rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
      tryif is_Zlit b then
        (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) in H by lia)
      else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H)
  | rw_cells _ _ (?a + Z.of_nat ?k) _ =>
      let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac kx_cells_split H :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
      let H1 := fresh "KC" in
      apply (kx_rwc_cons segs m A c (c' :: cs)) in H; destruct H as [H1 H]; cbn [csize] in H; kx_rwc_norm H;
      kx_cells_split H
  | rw_cells _ _ _ [_] => idtac
  end.

(* [comment removed for export] *)
Ltac kx_log_has_off log off :=
  lazymatch log with
  | SE {| a_base := _; a_off := off |} _ _ :: _ => idtac
  | _ :: ?rest => kx_log_has_off rest off
  | [] => fail
  end.
Ltac kx_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off then first [ kx_cell H | kx_cell4 H | kx_frame H ] else kx_frame H
      | _ => first [ kx_cell H | kx_cell4 H | kx_frame H ]
      end
  end;
  try (cbn [cells_size csize]; lia).

(* [comment removed for export] *)
Ltac kx_cells_merge :=
  repeat (lazymatch goal with |- rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
            apply (proj2 (kx_rwc_cons segs m A c (c' :: cs))); split; [eassumption|]; cbn [csize];
            lazymatch goal with
            | |- rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
                tryif is_Zlit b then
                  (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) by lia)
                else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v)
            | |- rw_cells _ _ (?a + Z.of_nat ?k) _ =>
                let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v
            end end);
  eassumption.
