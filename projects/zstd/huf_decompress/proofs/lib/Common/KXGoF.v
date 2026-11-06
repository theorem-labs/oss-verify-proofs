(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_KXGoF () := "C47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib6Common7KXSound3KXS7know_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5KXGoF6win_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib4Init9Datatypes3nat02C56Stdlib5Arith8PeanoNat3Nat3lebC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3fstc59OSSVerify5KrLib6Common5KXGoF7kx_acovC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC59OSSVerify5KrLib6Common6KXFoot4accPC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat6leb_leI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC69OSSVerify5KrLib6Common6KXExec3KX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common6KXExec3KX26a_baseC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX25saddr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS?zf_covers_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common7KXSound3KXS6estartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00C69OSSVerify5KrLib6Common7KXSound3KXS5elenZC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib6Common6KXExec3KX26edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib6Common6KXExec3KX26adenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib6Common6KXExec3KX29zf_coversC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib6Common6KXExec3KX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib6Common6KXExec3KX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common6KXExec3KX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib6Common6KXExec3KX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib5Lists4List6Exists00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib6Common5KXTac4zshzC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterc59OSSVerify5KrLib6Common5KXGoF8acc_autoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbc59OSSVerify5KrLib6Common5KXGoF:kx_accs_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6Common5KXTacCForall_filter_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Common5KXGoF8shz_raccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac7shz_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac8shz_ruleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac>shz_rule_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z;div_le_monoI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr07I46Stdlib;setoid_ring<Ring_polynom3Pol00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_addK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z7div_posK46Stdlib9micromega5Tauto8GFormula03K46Stdlib;setoid_ring<Ring_polynom5PExpr05C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK46Stdlib9micromega=RingMicromega3Op201I46Stdlib;setoid_ring<Ring_polynom3Mon00c59OSSVerify5KrLib6Common5KXGoF9acc_auto2C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00C56Stdlib5Arith8PeanoNat3Nat6eqb_eqc59OSSVerify5KrLib6Common5KXGoF:shz_acc_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib6Common8KXBridge9zatoms_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zsaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8KXBridge4zdenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac2kEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac3zleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo8elen_zleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4KXGo@estart_zsa_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5KXTac6zr_regC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common8KXBridge4zexp00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost2ezC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib6Common5KXTac7kE_atomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6KXPost5ez_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common5KXGoF9adenot_ezC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib6Common5KXGoF;kx_rd_knownC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Common8KXBridge5rdvalC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common6KXExec3KX24expr01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC69OSSVerify5KrLib6Common7KXSound3KXS4extzC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3mulC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3lorC45stdpp9bitvector;definitions8bv_swrapC4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition win_ok (RNG : footprint) (E : env) (w : saddr * expr) : Prop := rng RNG (estart E (fst w)) (elenZ E (snd w)).

Definition kx_acov (kn : list kentry) (ww : list (saddr * expr)) (a : saddr) (n : nat) : bool :=
  existsb (fun w => zf_covers kn (a_base a) (a_off a) n (a_base (fst w)) (a_off (fst w)) (snd w)) ww.

Lemma kx_accs_ok : forall segs RNG E M kn ww accs,
  know_ok segs E M kn -> Forall (win_ok RNG E) ww ->
  forallb (fun an => Nat.leb 1 (snd an) && Nat.leb (snd an) 8 && kx_acov kn ww (fst an) (snd an)) accs = true ->
  Forall (accP RNG E) accs.
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) [] "p'0h02H0h11xi001xh24__x1h34__x2h42Hzh52anh61Ah72Hbh84__x3h94__x4h:1bh;1jh<1lh=2C1h>2C2h?3Hinh@2HwhA7__arithhB4__ffhC8__varmaphD5__withE4cstrhF1ni011nhG2H1hH2H8hI2HchJ1PhK4__x5hL4__x6hM1fhN1mhO1zhP1EhQ1HhR2HKhS2HWhT2HahU1MhV2R1hW2R2hX2R3hY3RNGhZ1ah[2abh\4accsh]2akh^2kbh_2kkh`2knha3lenhb2sbhc4segshd1whe2wwi026a_basei035a_offi041ei051pi061sp%0p&0p;1p;2p;4p;3p;6p;=p;7p;<p;8p-1R0g0000R1p4p710p8P0P1p4p7210p8P0g000MR0p4p710R2p8g000ij1TTg001Ij1KTg001nj1vTg002Lj1lTg002ok10HTg003QR3j2|Tg0041k40ETg0050j2cj3hTg005hj3OTg006Ij1CTP1j3eTg006hj25Tg007Hj2BTg007fj3bTg008Cj4ETg009<j3iTg009Xj34Tg009oj3{Tg00:Qk20Dj3fTg00;Hk30ATg00;kj6sTg00<Fj3qTg00<iR1j2?Tg00=Ck206TP0j3oTg00=fR0j2\Tg00>@k301Tg00>cj10Tg00?_j12Tg00@\j27Tg00AZm=0GTg00Baj2GTg00C_R4j21Tg00D;R5j19Tg00D[R6j2STg00E6j2;Tg00F3j1`Tg00FQk20FTg00Fnj26Tg00GKj2YTg00HHj2=Tg00I2k20CTg00IXj3MTg00J2j2RTg00JLj4]Tg00K3j1xTg00KXj2QTg00LAj3XTg00Ljj2uTg00MVk10@Tg00N6j3rTg00NVj2WTg00O4k10?Tg00ORk10>Tg00P0k10=Tg00P[j2gTg00Q>j1pTg00Qcj2NTg00RFk10<Tg00Rhj3^Tg00SKk30;Tg00Snj4nTg00TYk705Tg00U=k204Tg00U_k203Tg00VKk307Tg00Vjk408Tg00W\j2mTg00X8k102Tg00Xak309Tg00YMj2tTg00Z3k200Tg00Zbj6wTg00[@j2dTg00\=j4_Tg00\]j7kTg00]]l<~Tg00^Bk40BTg00^`j7yTg00_Dj8}Tg00_hR7f0R8g00`HR93Mp=3g00`hR:g00afR;f1R<P8C_p=VAM789,S<p=@f3R=f2R>P:P;P<P8C_3fp=<g00bER?=b:8p=UAe:?8p=>f6R@f5RA#2f4RBP=P>P<P8Fkp=ZP:P?P<P8C_p=JP@PAPBP=P>P<P8Fk=M79p=L17<8,G>p=:1;<8,6>p=j16></18p=81G></68p=aP:P?17><P8C_p=AAb:?8,G<p=Fg00cBRC/18p=I16<8,1>p=zP;g00c`RDP1P5P4g00d>PAPBP=P>P<P8M<~p=[PDP>P<P8H0Bp=PP>g00d`R4g00e?R5P5g00e_R1PDP<g00f?P8Cng00ffREFyp=DP<P4P5P5P1P8PEFyp>0:P=P4P5P5P1P>P<P8G}p=Hg00gF#Tg00hEg00i>g00j:RE#KRF#KS00#KRG#K#K#KRH#vRI#l%vG#l$0H[g00j_#T1|:?RJ#T1|:;RK#TP@PBP=P>H0E1c@A=OJ>g00k^RL#CRMAe:;8RN'5%CMRO#CRP#CRQ#CRR#C#C#CRS,5N'BRTPAPBAb:;8RUPNCE'BX5K=iK>#3g00l=p4p710RVp-0\8RW%T<RXP6AO><8A4B8>RYPBP<O1[^1=RZ[A4=8<R[P=P<O1[^1>AO=><[R\AOB=>\ZA{><8P8n2001000000120000000W<WJW6P\^<X^JW^6VP8PKf9RVf8RW+0DPBP3P:P;A4K8@f<R\f;RZ;f<[P81V<8=4KVf=R]P\PUPNCE,BTX5KR^f:R_5iK#3A4K8\f@R`f?RaPUPNCE,BTX5KP<O1#3[^1K[A4K8ZPaf>RbPUPNCE,BTX5KP<O1#3[^1KPbP]PUPNCE,BTX5K=iKZ#3[B0AK^_f7RT1V><RNP8EsP^PNO1#315M>15>S'BRNP]P\P=P>CER^;q8%3N/@^P615M=15=S'B#3PbP]PBP=CE#3fBR^fARNPAPBC<P815MA15AS'B#3PNP`PTP@CE#315MTRU15TSRc;q<%3U/@cP615MW#315WS#3fGRcfFRUP_PVC<P815M_#315ZS#3P615<8#31?><[Rd1?<815><#3Re[1?=>\e206<8P<n2001000000120000000XN;XF;RePd^N;^F;RdP8PMP]P>O31?M]PePdP8PaPSP=O31?aSP7\8RdP6Ao><8#3P=P8O1,@YX1=,\=[RYP>P8O1,@[X1>,\>Ao=><#3R[[A4A8=PBP8O1'@X1B,\B\[B01><8P<n2001000000120000000X<XWMX62PY^<X^Md^62P8PJfMR2fCRd%0dP^%U8RX#2RY%0XRX%>8R[FZReXdJfKRfP_O4fLRg94J8/@eX1J,\JP0PJA4J82fNR0fDRe%0ePdPYPXP[FZ'@X1JfQRhfPRiPePdC<P8P3P:P?A4J8iPhPc%0cPUPYPXP[FZ'@fUR[fTRXfHRYPcC<[P81J<8R3fSRj54JPXfJRk%0kfI%U3Rl#2%0l%>3FZ'@P61J><R3=4JXP[%2f%0fPk%U3Rl#2%0l%>3FLfYR3fXRlPgPfC<P81JB=fVRm54JPl%20%00P21JABRn#URo#2%0o%>nFLP:1J8@=4J3f[Rn%2h%0hPi%2<S01%0<S02PTFLf_Rof^RpfRPhC<]4]@P@17<8Rh/JVf\Rq54JPp%2X%0XPj17><Rj#2S03%0jS04P_FLfcRjfaRrf`RsPo%2[Rt%0[RuPXP=P>PZPqPeP8N=0G17=>Rv,GrRwA:rtuRu'1%9XAjwrZ58u'SP6fbRu17B=Rw'GRX%2m%0m5:uRt'1%9[AjXu\58tfdRtPjfWPmC<P817@ARX,Gt%2l%0l5:t'1feRu%23%033:%9l17T@1;ua5au38fgRlffR3'cRx=OJjA4J8ufjRufiRy;h<[^1J[A4J8tfhRz=hy<[^1J1czl=OJt[A{JxjPsAAWT`RxP@EsAhl3xP6AAVWNRx,FlR{#I%>x,;l%`FRx%`H+0FRH58{AAZ_d,FyR{/1<%9<,6>R|AA\ZeRZ#U%>Z,;u5auRZ'1flR}P=P>O2[[^;;^:D'SPyPzPqPnC<P8%I{11ZHAAb]U,F}/1<fmRZAAabcR{'FRq%>{7jZR{,1|foRzP=P>O2[[^;;^:D'SP6fkR6fER~9A]\R\'F%>\,;6;8H11q<fnRqAA`aYRa'F%>a,;q5z|fpRaP=P>O2[[^;;^:DPZP}PsPoC<P811{HAA^Nk,Fa/1<fqRa17d^R^/JfRk'F%>k,;a5z|fsR|P=P>O2[[^;;^:DP:1V8j=4K}PzQ01Q02Pt%2^%0^PfFLfrRf?:ed%2>%0>5:f'1%2=%0=5:|%9317~e1;|25a|38fuR|ftPBPlC<]>]=]4]?Pj1Vh3=4KzPfQ03Q04Pl17U~R~#2%0~P0FLA:|cU%2v%0v5:|'1fvR|%2w%0w3:%9y17Yc1;|i5a|38PDfwR|/YA,=I/6BRi-0CIfxRY/Y@,=I/6A9MD8XOD1?uS%9uRc%`GRG'1RyPuPc1RDcPSPG1RDGRcE[fZC]Py1?M6%`ERy%96Rw'1RvPMPy1RDyRUP6Pw1RDwR~E[f]C]Pv%x}%9}Rv#Ig00lZRl1QDR1QDQ1QDO1QDLRL5XD5XD5XDg00mFRO'u1QDP1QDM=XDL5XD/uO&0@lRO5rl3r%TlRl1WDBRL1WD@7P>1WDA&0?DRP7P=7P<&0>DRQ&0=DRR1gDy%pF,NDRf5DR&0<5R3PR%pERh,NDQ00,ND5^DRj%Kh,ND5^DRh1gDx>0;DIRx5DRP3PR1gDCRe=DRjP3PR1NDERE1NDFRF5^DRd=^Df=DRhP3PRADRjdP3PRP4P5P5P1ADRedPDPdg00n2PxCn-0:RK05CHCHCHCHCH204R1R1P8P>1R792038>#3dB07DC<H08RCbBbCbDX2DX3DX8DX9DXKDXLD11yB16=BR9?8@H16BAR7#I16A@Rx/6W989TA8@T7%Ix1mxH'S[[[[[^2D^3D^8D^9D^KD^LDP8f{Rx/;[%9qPg1Yx2,=IPW1YxV,=IP>P]PNPBPAO;bAbEb0b0%Ii&02I,mi'Se:09Ii1tIi,=I200IiEw17ABRB#2,Y|,=I%0B'6Ri,tI,=I=MDie1d|B,=I1G|B5MDRiePiPD1GYXRifzP8P}O2XODPVPiP61?6S11wGRiP6PwP~PSPGPcE[PnC]RnPi1?M}11yvRcPMPyPUP}Pv1RDvE[PpC]RpPc%xZRv%9Z#IRZPOPl1WD>?P<PPQPRADREFRFP3PFCHP1PCbBbCbDX2DX3D118<11<>[^2D^3DP8f|RF?:_VREA:F02R0P@O3bAbEb0b0PnPiPpPcPvPZPOPlAPL>P1WD=7P<PQPRADRdjRdP3PdCHP1PCbBbCbDX2DX3DX8DX9D16>=988<A8<>9[^2D^3D^8D^9DP81;FmP0%9zPEPAO5bAbEb0b0O41dYX,=IP8EwbTPY1VBuRB9b:;,d|,=IAe:;BO2eAfY|BeW>W=W4W?X]DX[?P<P8O2n01106000121102103PrPbP_PVO4WXWWP<P8O2n2001000000121000000W0WVP<P8O2n2001000000121000000b0W>W=P<P8O2n2001000000121000000b0W4W@X_DX^?P<P8O2n01106000121102103P<P8O2W4W@P<P8O2n2001000000121000000W0Xa?Xb:P<P8O2n2001105000121106104X1JP<P8O2n2001000000121100000bIb0bHb0bGb0WHWGP<P8O2n2001000000121000000b7WIW7P<P8O2n2001000000121000000b7b7W?XF;XZ:P<P8O2n2001105000121106101X1KO4b0WQWSWRW\WeW`WUWPWYWco"). Qed.

(* [comment removed for export] *)
Definition acc_auto (kn : list kentry) (ww : list (saddr * expr)) (an : saddr * nat) : bool :=
  Nat.leb 1 (snd an) && Nat.leb (snd an) 8 && kx_acov kn ww (fst an) (snd an).

Lemma kx_accs_ok_part : forall segs RNG E M kn ww accs,
  know_ok segs E M kn -> Forall (win_ok RNG E) ww ->
  Forall (accP RNG E) (List.filter (fun an => negb (acc_auto kn ww an)) accs) ->
  Forall (accP RNG E) accs.
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) [] "p'0h01Hh12H0h22anh32H1h41eh51li001lh61Gh72H2h81Eh92G'h:2HKh;2HWh<2Hah=3Hinh>5Hresth?1Mh@3RNGhA4accshB1bhC2knhD1pi011phE4segshF2wwhG1xi021xp;1p;2p;4p;3p;9p;6p100nYp4p70R0g005hR1p4p710p8P0g00oOR2p4p710p8P0p100l=p4p710p8g000iR0j1:Tg001Ij16Tg001nj1@Tg002Lj1ETg002oj1QTg003Qj2DTg0041j4LTg0050j2KTP1j35Tg00:Qj22j34Tg00ojj3Cj2PTg010dj1GTP2j3FTg009Xj3OTg00MVj1NTg00N6j30Tg011Bl9MTg006Ij13Tg0000j3ATg006hj28Tg007Hj27Tg007fj3?Tg008Cj4;Tg009<j3>Tg00J2j2=Tg00Zbj6<Tg00IXj31Tg012>j6JTg012Zj2ITg0139j6BTg013Vj6HTg00_hR2f0R3g00`HR431p=9g00gF#:g00hEg00i>g00j:#6#6#6R5#6#6#6#@#E%@5#E#Q[g00j_#:g00`hR5g00bE'DR6#:g00afR7,D5R8#:R9f6R:f4R;f3R<f2R=CLf5R>,K:=56=f7R6/2:AC>;3#GX28=F8=558P8f8R?/261P>;P<AO83;f1R@9C6:#9f<RAf;RBf:RCf9RDP?P6%N8RE908=RFP>P;M9Mg00k^#3RGAA573RH'8%3G#3#3#3#3#3#3RI,8H'7RJPDP?A?573RKPHC;'7X28=>8F#912ABA08<ERF558[P2P41734#9XB21=24AA57<R4,8G184I'7PDP?A?57<P4C;'7P@E<PCPDPKPHC;,7JX28=>8F#9RFePFP@P3O1f=RF/2AA08;E558P1P8f>R1/2FA086ERA919@fARJf@RH;4?RK[P3A08>ER4919EA08:ER7919EP9PEP0P8p-0P3g014[g0157R5n10110000020020000000X49g015TPAP3EJP51IK3b1W0P3O1W0fDRKfCR5;4@fERA/2K=58@A08<=A08FE519A08;<A081E519P9P9P0P8P9P3P>P3n10110000020020101100X49A08>;f?R1=08EP3EBA19;EP9P8P0P8P8P3P6P@n10110000020020101100X49A08:>A08HEP@EBA18:HA186JP3fB918?P8P5A19DER5fNRJfMR:;4@fOR>/2JR0=58BfPRBfG74>]1]0[XD8A19?EP3P5P9PEfF94>J12B>=58@fQfH74B]1]0X59A4J:AA580EP@W7W3PCP3E<b7W1PDP3E<b1W0P3O1b0P3O1b0W3P3P=P@O3W3W1W0X59XG8P<P=P@P3O4n200210000000020041102100000000A1937A4H16[X59P4O1P31=97O1b0b6b9b6W<W=X28P3EHW>W;W:WAWFWCW?W8W@WEo"). Qed.

(* [comment removed for export] *)
Definition shz_racc (RNG : footprint) (E : env) (t : zshz) : Prop :=
  let '(off, w, len) := t in rng RNG (off + Z.shiftr (estart E w) 3) (Z.shiftr (elenZ E len + (estart E w) mod 8 + 7) 3).

Definition acc_auto2 (kn : list kentry) (ww : list (saddr * expr)) (ts : list zshz) (an : saddr * nat) : bool :=
  acc_auto kn ww an || (Nat.eqb (snd an) 1 && shz_any kn ts (fst an)).

Lemma shz_acc_ok : forall segs RNG E M kn ts a, know_ok segs E M kn -> Forall (shz_racc RNG E) ts ->
  shz_any kn ts a = true -> accP RNG E (a, 1%nat).
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) [] "p'0h05heq_Ah15heq_Nh21zi001zh34__x1h44__x2h51xi011xh61Hh74__x3h87__arithh94__ffh:8__varmaph;5__with<1bh=4__x4h>1jh?4__p1h@1AhA2E2hB2R2hC2R3hD7fv_listhE8hyp_listhF3lmphG2HahH2R1hI4__x5hJ1fhK1lhL1EhM2E1hN2H0hO3HA8hP2HKhQ2HThR3HinhS2HmhT2HrhU2HxhV1MhW1NhX2Q1hY2Q2hZ3RNGh[1Uh\1ah]1ei021eh^2knh_3leni033lenh`3offi043offha1pi051phb4segshc1ti061thd2tshe1wi071wi081sp%0p&0p;1p;4p;2p;3p;8p;6p;5p;7p;:p;<g000ij1FTg001Ij1TTg001nk104Tg002Lj1|Tg002ok10hTg0041k40ZTg0160j2xj3zTg005hj3vTg016jk30GTg000MR0j3~Tg009Xj3dTg00=fR1j2cTg00>@k30]Tg017cj3STg006Ij1kTg003QR2j2hTg018]k80ITg00Baj23Tg00E6j25Tg00FnR3j20Tg00W\j2KTg00[@j2ITg00Q>j1eTg00F3j1XTg019]j28Tg00IXj3;Tg00D[R4j2[Tg009ok30=Tg00;kk60<Tg01:=j2?Tg00FQk208Tg00C_j26Tg00D;k10[Tg00HHj2bTg01:]j21Tg00MVj1yTg00O4k10YTg00ORk10XTg00P0k10WTg00P[j2aTg00U=k20VTg00J2k205Tg00U_k20UTg00VKk30TTg00Vjk40RTg01;:j3MTg01;ck20PTg01<JR5j2>Tg01<gk30HTg00NVj2lTg00Qck203Tg00RFk10FTg01=Nk500Tg01>3k10ETg01>]j2sTg01?Gj2rTg01@1k30DTg01@[j3qTg01AEk10BTg01AmR6j2NTg01BJk60ATg01Bnj4}Tg00Zbj6YTg00KXj2_Tg00Ljj2mTg00N6j3`Tg01COk30@Tg01D2k30?Tg01DUk10>Tg01E3k20JTg01ETk30KTg00I2k20LTg01F=k20MTg00SKk30;Tg00X8k10NTg00Xak30OTg00YMj2wTg00Z3k20:Tg007fk309Tg0000k30STg00:Qk306Tg00\=j4iTg00Snj4jTg00^`j7{Tg012>k60gTg00^Bk40fTg01F^k60eTg00TYk70dTg00_Dk807Tg01GBk30cTg01Glm:0\Tg01H]m<0^Tg01IJk40_Tg01J0k70`Tg00LAk30aTg00Rhk30bTg00_hR7f0R8g00`HR93;p=Cf1R:A;789'[p=Eg00nYR;?d:8p=@f3R<f2R=g00`hR>g00afR?P:P8Ci406p=JP=g00bER@P:P8Cip=Pg00c`RAP>P:P8Cip=]16=:/[8p=G10:8,w=p=A18:8,0=p=Dg00cBRB/68p=<10=:/08p=W1?:8,0=p==10=:/88p=U10=:/68p=910:8,6=p=L205A8p=4A;A:8p=2P=g00d`RCg00e?RDPDg00e_REPAP:g00f?RFP8Cjg00ffRGF{p=QPAf4RHP<P=P:P8J0gp=HPAP:g00n2P8Cjp=uP:PCPDPDPEP8PGF{p=g1K:8,[=p=fPAP=P:P8H0fp=:203A8p=OP:PCPDPDPEP8J0ep>02P=PCPDPDPEP:P8K0dp=tP<PCPDPDPEP=P:P8L07p>01A`A:8p=ZB0cA:8p=\PAPBP:P3P5P6g01J_RIg01K<RJg01KYRKP8N:0\p>0CPAPBP=P3P5P6PIPJPKg01L:RKP:P8N<0^p=^PAPJP:P8H0_p=pPKPHP<P=P:g015TP8K0`p=nPAP:g01LiP8Cjp=oB0aA:8p=RB0bA:8p=7PHPCPDPDPEP<PCPDPDPEP=PGF{P:P8L07p=BPAP:PFP8Cjp=VP>P?P:P8Cip>0Qg00gF#Fg00hEg00i>g00j:RF#TRG#TS00#TRK#T#T#TRJ$04RI#|R6&04K#|$0h[g00j_#F%F;f6R5PHP<P=H0Zf5R3,x5=v;=B0GH<=#CP0p4p710R0P7\8RL%F:RMP4A~=:8#CAdH8=P<P8O1'EX5<,c<[RNAd<8:P=P8O1'EX5=,c=A~<=:#CRO[Ad38<PHP8O1'EX5H,cH\OB0]=:8P:n2001000000120000000WKWJW@PN^KM^JL^@0P8P;f7R0?S83RLXc;P3P:O41@85/ELX5;,c;P1P;1@80f8RL?S85'EX5;f;RMf:RNP5g00k^S01#kROCJP8P21hA>RPP@1@8Nf9RQ9SM8'Ef?RRf>RSPNPOCJ[P8P2PAP>APP:8RT/@Sf=RU9SRT'EfCRTfBRVPSPOCJ[^]@P81]=:=PP8RWfARX'@f@RY9SVW'EP41]<==PP:RW/@VASTWX#CfGRWfFRZPVPOCJP81]3H=PP<fDR['@1]53=PPH=SZ[#CfKR\fIR]fHR^PW1]05=PP3R_fER`P[P8L0IP2PPP@p-0RaP_P2PAP>PaP:fNR2/3:R_152<,0_,K87G8fJR_,I2Rb%eFRc#XRd,88Re9AI=5;6'[X5A,cAn2001105000120104107n2001106000120105103P1PA13\LR115\0,01,K87G81I\WAAIQe5;6'[X5AfLR1P\PWPOCJP8fMRf/3NRg15fQ,0g,K87G81If]AAIMe5;6'[P4132MRe152N,0e,K:7G:f<Re18:dRg5AI9;6bfPRbfORhP\POCJP813bURi15be,0i,K<7G<fQRi/If18Hd9AIR5;6fSRjfRRk'xRl=v;h1@8ifVRmfURn;z:[^5;[1@8bfTRo=zn:[^5;1xoj=v;b[B0=;lhP11]YR=PPSRlPNJ0<AzjklP413jYRl=DXdRp#<15jR%XKRK,?l%ecS02#XRl3W=Dpd%XGS03%XJ+08RJ13nV=DTdRp/6:&0[:,0=Rq13mTRr/8d15mV?=rK?Uld5W[Rr'6fXRsP<P=O2[[^>?^<A3GPnPoPbPOCJP8%<p13s`/8d=9Z:fYRp/3ZRt=DWdRu15p`1?tK;Wl;DdRt,6qf[RvP<P=O2[[^>?^<A9GrJP4fWR4/3[R[=D`d154T?=[K?Uld;9J16u:fZRu/3WR[=D^d15uZ?=[K?Uld5Lqf\R[P<P=O2[[^>?^<APpPsPoPOCJP816tJ13[]/8d=9_:f]Rt/3_Ru=D\d15t]RZ?=uK?Uld5Lqf_RuP<P=O2[[^>?^<AP618Sd9AI]Pt1bI8POO2X<613v^PA15[^PAPAQ03008dR`,1YPuAAI18,bIPOO2X2APgA92=:10h<1?3K=WHlRg/8dS045LqfcS05P<P=O2[[^>?^<AX2AP=11:`%4Z128ZRZePZf^RZ/3\Rr#412=rRrePrg00lZRr#yRw%FrRx&0YARy&0XARz&0WAR{1aABR|1aAd3Q20V{ER}P8P=20579S0620U8=#CdB0TAB:H0RR9b9b:b;%<dP8b8R7b0b1S079M:dDH11<`S08,0fS09/6:11H`,02A=<HK?Uld5LqfbR~P<P=O2[[^>?^<A18=d10f8A==<K?Uld;9JX2APH11=`S0:15Z_RZ#412:ZRZePZ13u1RZ#412<ZRZePZP7b0b19M=dDHQ0:,01A=:=K?Uld;9J18<d1028#<X2APQQ0815u\Ru#412=uRuePuf`Ru/3fRZ#412HZRZePZP7b0b19M<dDHQ09#<18TdfaRZ/ItAAIh85;6X2APS11T`S0915u1Rt#412<tRtePt13Z2Rt#4123tRtePtP7b0b19MTdDH1Iu[Q099AI25;6Q0411L`,0kR6/6:11Q`,0j=Lq<fgS04P<P=O2[[^>?^<AX2AP<11g`15ZfRZ#412HZRZePZ13~hRh#4125hRhePhP7b0b19MgdDH110`,0iRg/6:1?LKRh=W0l/1`9Lq6ffR6P<P=O2[[^>?^<A1?5K=W3lRq/8dA9g8JX2AP<11q`Rg15~2R~#4123~R~eP~Q05/3bR~#4120~R~eP~P7b0b19MqdDH115`,0b?9gJ20P0K110K,>K?=0K,20fd/5bRb#4120bRbePbfeRb/3kRk#412QkRkePkPwPxPyPz1aAKRk,u|,g{P}P9b9b:b;1KBKS05P8b8S09b0b1:0HLK%<h?fhKPQP^PK15biRb#412LbRbeRhPb136jR6#412N6R6eRgP6Q09b0b1PhPbPgP6PwPx1lA=R6?::yPzP{203AFRg%OGRb5Q{Rh202{H5t{&0FDR`PhH01P}P9b9b:b;X3AX4AX?aAG8:=16:=S08[^3A^4A^?aP810eM,K\P\PePWO4b8b0b1I0011QK11^K'6&0EAR^/h^R^#yS0:%F^S0;1?MKR^%yARW'Z,ZN%FAS0<P8P:1sAFS0=1sAG'\Rh%XFRq,rAR760DAR~1rAKRZ9qA7'\Ru1rAl,\hRhQ0620Cq:S0>g01MP,hA&0BA'h#FS0?A^q8uA^q8h'pbF#CdDnbDbEA=QNKRh/NqS0@1>qKRu'010hlS0A'2RhePh10N^S0B/NqR^/0uS0C118KS0DA=MeK/NqRu/1KRh/0qRT'2X2APA11^K/0qRt128TX2AQ0:Q0;1ZhWQ0<P8P:Q0=/\7R7P7Q06Q0>Q0?A^q87R7/p7bF#CdDnbDbE12tteQ0C/1KP^PqPKQ04/5jRj#412NjRjeRtPjfhS04/3nR7#412e7R7eRhP7PwPxPyPzP{PCPDPDPE1ok|,g{J0AP}P9b9b:b;A;AKBg0157[P8b8S0Cb0b1C}EYQ0B/0lRBP8DHb6Q0A/1KS0AQ0@/1K/0q'2P_11MK,>K/0^R^PKPtPjPhP7Q09b0b1PtPjPhP7%kOS09,_AR71_AOS0@Q01,_ARh'RS01'Rg00mFRj'm=`rwPx1lAHRt?:=yS0B1lA3?:<y7::PzP{P{%eG#ORGB0@AkbRkQ00#ORE'7'oP`P{202{0%OcRD,7G,ug,g{5t{P`17DES0=1aAqRG60?A,7k9Q{gH01DBP}P9b9b:b;X3AX4AX7AX=AXIAX?a1>K:/0<,2H103<9f5:1>K<10H3Rk/Nq5L=[[^3A^4A^7A^=A^IA^?aP816SfPS1?SKRaPU11SKRCPfP5P]O8b8b0b1I0011_KS0E11^K'6Q0:Q0;1?UKR^11UKR_/ZW'Z,ZeQ0<P8P:1sAcRW=qAZ,\~RTAqAZW/\~R~Q06Q0>Q0?A^q8TA^q8~'pbF#CdDnbDbE11eKR~/>K,0u1>K~/0u'2RuePuPA1>K_10e^R^/NqRe'011fKRfQ0D'6X2AP:1>_K,0eReP8EY111K11eK'610Ua/NqRa1>CK'0/1K112KR2/68X2AP811aK/0CRePaPCPKfjRC/5mRa#412UaRaePafkRa/3sRs#412RsRsePsQ0Cb0b1C}DH16fe15a4Ra#412SaRaePafl/3pRa#412YaRaePa&0>F-0JAQ0@60KA/Rh,R7/mj=`rwPxA:tHy?:<y9:6:PzP{P{Q00#e#ORF/7b,VgP`P{P{17FG,oDP`17gG17bD5Q{DBDBP}P9b9b:b;X3AX4AX7AX=AAL8<:10Hq,2<10<H99=q[[^3A^4A^7A^=AP8A=XVKRX/Nq/1K10Xl/1K11VK11iKP<P0O6b8b0b1bAbAb6bAbM11]K11NKQ0A'079qPAQ0E,0nRn-0LI11\K,0mR\,28X2A20MBK%<BQ0510^l/1K#<[[Q04/5oRo#412MoRoeR^Pofi/3mRm#412UmRmeRUPmQ09#kRB,_AQ01'R/mj%kB,_A1R7h'R/mj=`rw5`rPx1lA<Rr9:y=A:yHt7::PzP{P{17bGRt%Tc#ORcQ02#ORy'7'VP`P{P{1VcbP`P{P{17gcRc/7yQ03,aA>0;AIRy'VP`P{P{1V|cP`17gbRc9Q{|1ucy,g{5t{DBDBDBDBP}P9b9b:b;X3AX4AX7AX=A10=<99:qRy16<=10=H?93J10<3#<%<k?fkJ[[[[^3A^4A^7A^=AP81?RK=WSl/1KRl11RKRKP2PpPHP3PLPMO8b8b0b1b6%<n&0NI7fne:0OIn1wIn,bIRM20:InEY12MnPAP\PCP8POO2X2AP5P\POP^PoPUPmPwPxA:6:rPzP{P{1VbDP`17gDRD9Q{cDBP}P9b9b:b;X3AX4AX7AQ0810:=R=10:<R<'6[^3A^4A^7AP8P2PKPpP3O4b8b0b1P^PoPUPmPwPxQ0B?::rPzP{P{Q0=,VtP`17cG17DE5Q{DBP}P9b9b:b;X3AX4AX7AX=A10<H99=q\y^3A^4A^7A^=AP8PlPKP2PpPHO5b8b0b1O41wI\,bIP8EYb[bYbXbSbObBbCbGbHbBbC18YdQ079MYdEYbWb@1Iv4PQEYP[20Q4OR4:09>?,Iv,bIB0S>?4O2eB06[v4eWCWBP:P8O2n2001000000121000000W6WHP:P8O2n2001000000121000000b6WGWUP:P8O2n2001000000121000000W6X5AP:P8O2n2001000000121101000b6WTWRP:P8O2n2001000000121000000W6X_@Xe>X`AP:P8O2n2001105000121100108XaPP:P8O2n2001105000121105102X5;P:P8O2n2001000000121101000b6bNW6WQWPX\>WdW^WVWLWZWbo"). Qed.

Lemma kx_accs_ok_part2 : forall segs RNG E M kn ww ts accs,
  know_ok segs E M kn -> Forall (win_ok RNG E) ww -> Forall (shz_racc RNG E) ts ->
  Forall (accP RNG E) (List.filter (fun an => negb (acc_auto2 kn ww ts an)) accs) ->
  Forall (accP RNG E) accs.
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) [] "p'0h01Hh12H0h22Hah31ni001nh42H1h53Hinh62anh71eh81li011lh91Gh:2H2h;2Hnh<1mh=1xi021xh>1Eh?2G'h@2HKhA2HThB2HWhC5HresthD2HshE1MhF3RNGhG1ahH4accshI1bhJ2knhK1pi031phL4segshM2tshN2wwi041sp;1p;2p;4p;3p;9p;6p;:p;7g000iR0j1>Tg001Ij1=Tg001nj1GTg002Lj1HTg002oj1`Tg003QR1j2ITg0041j4TTg0050j2RTg005hR2j35Tg0160j2OTg00:Qj27j34Tg01N8j4Dj3VTg010dj1LTg00oOj3_Tg009Xj3@Tg00ojj3CTg006Ij1:Tg01O3j28Tg016jj3<Tg007Hj26Tg01OSj3QTg01OoR3j2PTg00MVj1NTg00N6j33Tg011Bl9MTg006hj2?Tg008Cj4ATg009<j3FTg00J2j2ETg00Zbj6Bj7XTg00IXj32Tg012>j6KTg012Zj2STg0139j6JTg00<Fj3^Tg00D[R4j2]Tg01PIj2\Tg01Pll:WTg013Vj6YTg00\=j4UTg0000j3ZTg007fj3[Tg00_hR5f0R6g00`HR732p=1g00`hR8g00afR9f1R:P6CUp=0AZ896p=9A[896p=;g00gF#>g00hEg00i>g00j:#=#=#=R;#=#=#=#G#H%G;#H#`[g00j_#>g00bE,I8R;#>g00nYR<#>1I89R=#>R>f7R?f5R@f4RAf3RBCTf6RC,R?=5;Bf8R;/O?=5<Bf9R</7;P?PCP@P6CD#LX6==_=B55=P=f:RD/7<AV?C@PAP1P8P9A@=6CPDP<P;P:CD#1f>R1f=REf2RF34[[P610:6=@=<PEf<RGf;RH10F:CD#110BFRI9C1ERJ%9Ig00k^#:RK'8%;I9<1G'6RI;Q6%1J%1I'PP3f?R310ABRI7C1#1%9I/8K%;I9<3E'6#1fCRIfBRJ10@ARL34P6f@RM?C3L#1fERNfDROPIPJfARPPM10C@RQ%N=RR53=RSPEPGM9M%96RT,?K%:K#:#:#:#:#:#:RU,?T'6RVPJPP%;6RWPTCA'6X6==F=S#117NO10?CRS=3=RRX55=[P5P71667#1XI51E57%9SR7,?K1?7U'6PJPP%;SRSP7CA'6P:EBPIPJPWPTCA,6VX6==F=X#1RXePXP:P6O1fFRX/7N10;?RV=3=R55=P2P=fGR2/7X10HDRT=3=RRW92>:fJRUfIR510GHRY34RZ[P610<;R[=3=RR\92>R10D<R]=3=RR^92>RP>PRP0P=p-0P6g014[g0157R_n10110100020020000000X7>g015TPWP6EKP_1SZ6b1W0P6O1W0fMRZfLR_;4:fN/7Z=5=:A3=BF10PM=3=R52>A3=AB10JP=3=R52>P>P>P0P=P>P6P@P6n10110100020020103101X7>A3=@A10IJ=3=RP6EJA2>ARP>P=P0P=P=P6P?P:n10110100020020103101X7>A3=C@10OIR@=3=RP:EJA2=C@10NO92=?P610XN92=;P=102XA2><RR?fWROfVR@;4:fXRC/7OR0=5=HfYRAfKRW/0U74C]1]0[XK=A2>;RP6P?P>PR10U594CO17AC=5=:fZ10_W74A]1]0X8>fHRA,0594O@A5=0RP:W:W4PDP6EBb:W1P<P6EBb1W0P6O1b0P6O1b0W4P6PFP:O3W4W1W0X8>X==PBPFP:P6O4n200210100000020041102101000000A2>6^A45AT[X8>P\O1P61E>^O1b0b9b?b9W2P6O1%9L/8K%;L9<M1'6#1%9Q/8KRL%;Q9<P3RP;^6%1L%1P']P4187K#1A<JMS#1A4XNVP6%9[/8K#1%;]9<NI#1P418:6#1A29F:[R4A29:618F:#1R][A29BF\]1\:6P:n2001000000120000000X<9X39P4^<9^39P6%9YRYPKPFO3A29YKP9PK1016=@=X103:94Z_]5X3910EK=@=NPZP_PWPUP5P2P1PNPIPBM:WW5PGP6PHFXb;b0WDW;P:P6O2n2001000000120000000b2W2P6O1n200100000021100011000b2W2W5X39XG8P:P6O2n2001103000121104100X==P6EYWCWAWBW@WHWMWNWJWEW>WFWLo"). Qed.

Section WinZ.
Variable zv : list Z.
Variable xs : list word.
Local Notation E := (kE zv xs).
Local Notation na := (length zv).

Lemma zw_ok : forall RNG a n b c A N,
  zatoms_lt na a = true -> zatoms_lt na n = true -> zsa a = SA b c ->
  0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 -> 0 <= zden zv n < 2^64 ->
  rng RNG A N -> A <= zden zv a -> zden zv a + zden zv n <= A + N ->
  win_ok RNG E (zr_reg (a, n)).
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["WinZ"] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64__x3h74__x4h81zh91Ah:2H1h;2H2h<2HRh=2L1h>2L2h?1Nh@2R1hA2R2hB2R3hC3RNGhD1ShE1ahF1bhG1chH1np;2p;3p;1p;4p;8p;5p;6p;9p;7g01Qhj2`Tg01RHj2_Tg00IXj3;Tg01SFj16Tg00@\j2^Tg01T;j21Tg01Amj2VTg00C_j20Tg001Ij13Tg00F3j1=Tg00FQj2KTg00W\j2@Tg00D[j2BTg01U4j34Tg00Fnj22Tg01Ugj2XTg01V[j19Tg00E6j28Tg00MVj1WTg000ij1UTg00NVj2:Tg00O4j1TTg00^Bj47Tg00ORj1QTg00P0j1PTg00Qcj25Tg00Snj4>Tg00RFj1OTg00U=j2NTg00J2j2JTg00U_j2LTg00VKj3MTg00Vjj4ITg00Rhj3ETg00Q>j1RTg01WPj8HTg01XGj5STg00Zbj6ATg00Baj2GTg01Y@l9]Tg00\=j4FTg007fj3DTg0000j3CTg01ZAj1YTg0050j3ZTg00^`j7[Tg00_Dj8\Tf1R0g00d`R1g00e?R2P2g00e_R3f0R4g00ffF[p=<f3R5P1P2P2P3f2R1P0P4G\p=?g00hEg01[9R6g00bER7g00c`R8g00_hR9p,2zvR:,`8f5R;'_g00`HR<3;R=g00`hR>f7R?#6f4R@,^;3;g00cBRAf8RB,1:/V;RC'0g00j:RD#3RE#=%3ERF#3#3#3#3#='KRG,@C'Bf9RC,1:RH,0A1@HG'BRHf<RGf6RI74?11:GRJ,0Bf=RK,1:RL/2J12CB'0P8f>RJ,1:RMf@RNp,2xsRO,X:RP%9J'8744X88P8PLf?RQ,1:RR=4N4X88PQf:RNPCPMPLP1g00lZRL#WRC%ULRLP81:81P0%T8RSC7%Q8RT%P8RUP8158DRVg00f?RW158EREC>,<URX%O2R2PXC?1NU3R3P4P11J9<1L41=;9<dAM8A0CIRAb3b4b5X08X1810401001[^08^18P4PRf;R<P1O3b2PCPLP8P81:8@P1PSC7P01:85C7PTPUP8AE8VEPW%RD,58158F5E8C>,<URUP2PUC?P3PAb3b4b5X08X18X68X7812401215'01201125@'0[^08^18^68^78P4PNP<PMPRP0O5b2GH%9K,8PP:POPKP?P5DSEA%6J,GPP:POPJPGP<PBPIP;P@M9]EAP>P7P6P6PJPKCFRK9D66#6AC66K#9CFRJ9D>7,GPAC>7J,8P54Qe%YK9ZQPeW>W=W<XBHWAW@WDX;=W:X?8X98WGWFXH6WEWCo"). Qed.
(* [comment removed for export] *)
Lemma zshr_ok : forall RNG off a n b c A N,
  zatoms_lt na a = true -> zatoms_lt na n = true -> zsa a = SA b c ->
  0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 -> 0 <= zden zv n < 2^64 ->
  rng RNG (off + Z.shiftr A 3) (Z.shiftr (N + A mod 8 + 7) 3) -> A = zden zv a -> N = zden zv n ->
  shz_racc RNG E (off, zsa a, zle n).
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["WinZ"] "h02HRh11Ah21Hh31Nh41zh52H1h62H2h72R1h82R2h92R3h:3RNGh;1Sh<1ah=1bh>1ch?1nh@3offp;2p;3p;1p;4p;5p;6p;9p;7g01Qhj2MTg01RHj2LTg00IXj36Tg01SFj18Tg00@\j2KTg01T;j21Tg01Amj2HTg00C_j2<Tg001Ij14Tg00F3j15Tg00FQj2CTg00W\j2;Tg00D[j2:Tg00Q>j1BTg019]j22Tg01:=j23Tg01Ugj2JTg003Qj2ITg00\=j47Tg01V[j1?Tg0160j3=Tg00E6j2>Tg01XGj5FTg00Zbj6Aj7@Tg00Baj2ETg01Y@l9GTg00Fnj29Tg01U4j3DTf6R0f5R1f4R2'9f3f2'9f1R3'9f0R4'23Dp=0g00hEg00c`R5g01[9R6g00bER7g00_hp,2zvR8,M5/L1g00`H36R9g00`hR:f7R;#81K1236g00cBR2f8R<,18/H1R='<g00j:R>#4R?#5%4?#4R?#4#4#4#5'CR@,;=':f9R=,18RA,<21;A@':RAf=R@f<R2%B>R>#5RB,2;P0%5?R?,3;%B>#5R>PBF01182965<P5118@R2f@RCf?RD124BREP=134?RFP>PBF0f:RGf>RH,18RI565fBRJp,2xsRK,J8RL1I5:RMP7P5P:fARN%8CROC7%?DRPC73=RQ[]0X15PDPH122BP<132?P>PBF0A65=2P5PIPJPN118CR2/2BP4132?P>PBF0fCRRPMP7P5P:PJ%8NC7%?CR:C77=L]0X35PNPC118DR7/2BPI137?P>PBF0P5P2PRPJPE1>L:PFP>PBF0X45P5P7PRPJ118NRR/2BP413R?P>PBF0X45P41>LPRPP8PKPDP=P1DFEA1ELOROP8PKPCPHP@PGP<P;P0M9GEAPJPN12OBPP13O?P>PBF0ePQeW0PGP4P3F@W2W0P=P4P3F@W2W0X9AW8W7W;X69W5X35X15X>5W=X?6W<W@W:o"). Qed.
End WinZ.

(* [comment removed for export] *)
Ltac kx_shr1 RNG zv xs :=
  lazymatch goal with
  | |- shz_racc _ _ (?off, zsa ?a, zle ?n) =>
      let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?b ?c =>
        first [ match goal with H : rng RNG (off + Z.shiftr _ 3) _ |- _ =>
                  eapply (zshr_ok zv xs RNG off a n b c _ _);
                  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                  | kx_arith | kx_arith | kx_arith | exact H
                  | cbv [zden nth]; first [reflexivity | ring | lia] | cbv [zden nth]; first [reflexivity | ring | lia] ] end
              | idtac ]
      end
  end.

(* [comment removed for export] *)
Ltac kx_win1 segs RNG zv xs :=
  lazymatch goal with
  | |- win_ok _ _ (zr_reg (?a, ?n)) =>
      let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?b ?c =>
        first [ match goal with H : rng RNG ?A ?N |- _ =>
                  apply (zw_ok zv xs RNG a n b c A N);
                  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                  | kx_arith | kx_arith | kx_arith | exact H | cbv [zden nth]; lia | cbv [zden nth]; lia ] end
              | idtac ]
      end
  end.

Definition kx_pendingF (segs : list Segment) (RNG : footprint) (Q : machine_state -> Prop) (F : bvmap 5 word) (fc : bv 32)
  (m rom : word -> option byte) (pc : Z) (stops : list Z) (fuel : nat) (xl : list word) (zv : list Z)
  (zs : list zexp) (zks : list zk) (zrs zws : list zreg) : Prop :=
  evtF segs RNG Q (MS (mkRl xl) F (Z_to_bv 64 pc) fc None m rom).

Ltac kx_mkR_foldF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => idtac
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let x1 := kx_leaf R 1 in let x2 := kx_leaf R 2 in let x3 := kx_leaf R 3 in let x4 := kx_leaf R 4 in
      let x5 := kx_leaf R 5 in let x6 := kx_leaf R 6 in let x7 := kx_leaf R 7 in let x8 := kx_leaf R 8 in
      let x9 := kx_leaf R 9 in let x10 := kx_leaf R 10 in let x11 := kx_leaf R 11 in let x12 := kx_leaf R 12 in
      let x13 := kx_leaf R 13 in let x14 := kx_leaf R 14 in let x15 := kx_leaf R 15 in let x16 := kx_leaf R 16 in
      let x17 := kx_leaf R 17 in let x18 := kx_leaf R 18 in let x19 := kx_leaf R 19 in let x20 := kx_leaf R 20 in
      let x21 := kx_leaf R 21 in let x22 := kx_leaf R 22 in let x23 := kx_leaf R 23 in let x24 := kx_leaf R 24 in
      let x25 := kx_leaf R 25 in let x26 := kx_leaf R 26 in let x27 := kx_leaf R 27 in let x28 := kx_leaf R 28 in
      let x29 := kx_leaf R 29 in let x30 := kx_leaf R 30 in let x31 := kx_leaf R 31 in
      change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  end.

Ltac kx_prepF STOPS FUEL KZS RRS WWS :=
  kx_mkR_foldF;
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                              ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let l := constr:(@nil Z) in
    let l := kx_reg_atoms x1 l in let l := kx_reg_atoms x2 l in let l := kx_reg_atoms x3 l in let l := kx_reg_atoms x4 l in
    let l := kx_reg_atoms x5 l in let l := kx_reg_atoms x6 l in let l := kx_reg_atoms x7 l in let l := kx_reg_atoms x8 l in
    let l := kx_reg_atoms x9 l in let l := kx_reg_atoms x10 l in let l := kx_reg_atoms x11 l in let l := kx_reg_atoms x12 l in
    let l := kx_reg_atoms x13 l in let l := kx_reg_atoms x14 l in let l := kx_reg_atoms x15 l in let l := kx_reg_atoms x16 l in
    let l := kx_reg_atoms x17 l in let l := kx_reg_atoms x18 l in let l := kx_reg_atoms x19 l in let l := kx_reg_atoms x20 l in
    let l := kx_reg_atoms x21 l in let l := kx_reg_atoms x22 l in let l := kx_reg_atoms x23 l in let l := kx_reg_atoms x24 l in
    let l := kx_reg_atoms x25 l in let l := kx_reg_atoms x26 l in let l := kx_reg_atoms x27 l in let l := kx_reg_atoms x28 l in
    let l := kx_reg_atoms x29 l in let l := kx_reg_atoms x30 l in let l := kx_reg_atoms x31 l in
    let l := kx_kz_atoms KZS l in
    let l := kx_rr_atoms RRS l in
    let l := kx_rr_atoms WWS l in
    let z1 := kx_reg_z x1 l in let z2 := kx_reg_z x2 l in let z3 := kx_reg_z x3 l in let z4 := kx_reg_z x4 l in
    let z5 := kx_reg_z x5 l in let z6 := kx_reg_z x6 l in let z7 := kx_reg_z x7 l in let z8 := kx_reg_z x8 l in
    let z9 := kx_reg_z x9 l in let z10 := kx_reg_z x10 l in let z11 := kx_reg_z x11 l in let z12 := kx_reg_z x12 l in
    let z13 := kx_reg_z x13 l in let z14 := kx_reg_z x14 l in let z15 := kx_reg_z x15 l in let z16 := kx_reg_z x16 l in
    let z17 := kx_reg_z x17 l in let z18 := kx_reg_z x18 l in let z19 := kx_reg_z x19 l in let z20 := kx_reg_z x20 l in
    let z21 := kx_reg_z x21 l in let z22 := kx_reg_z x22 l in let z23 := kx_reg_z x23 l in let z24 := kx_reg_z x24 l in
    let z25 := kx_reg_z x25 l in let z26 := kx_reg_z x26 l in let z27 := kx_reg_z x27 l in let z28 := kx_reg_z x28 l in
    let z29 := kx_reg_z x29 l in let z30 := kx_reg_z x30 l in let z31 := kx_reg_z x31 l in
    let zks := kx_kz_reify KZS l in
    let zrs := kx_rr_reify RRS l in
    let zws := kx_rr_reify WWS l in
    change (evtF segs RNG Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                              x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m rom))
      with (kx_pendingF segs RNG Q F fc m rom pc STOPS FUEL
              [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
               x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] l
              [z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15; z16; z17; z18; z19; z20;
               z21; z22; z23; z24; z25; z26; z27; z28; z29; z30; z31] zks zrs zws)
  end.

Ltac kx_goFd DIRS :=
  lazymatch goal with
  | |- kx_pendingF ?segs ?RNG ?Q ?F ?fc ?m ?rom ?pc ?stops ?fuel ?xl ?zv ?zs ?zks ?zrs ?zws =>
    let na := eval vm_compute in (length zv) in
    let sr := constr:(ELit 0 :: map (fun z => lnorm (zx z)) zs) in
    let kn0 := constr:(map zk_ent zks) in
    let r0 := eval vm_compute in (kx_exec segs fuel stops (SCR DIRS [] []) (SS pc sr [] (kn0 ++ atom_ranges na) na)) in
    let reads0 := eval vm_compute in (kx_reads_of na (snd (fst (fst r0)))) in
    let ispec := eval vm_compute in (find_idx zks) in
    let ifs := lazymatch ispec with
               | Some (?ztl, ?zT) =>
                   let s0 := eval vm_compute in (zle (ZSub (ZL 64) ztl)) in
                   let Tx := eval vm_compute in (zle zT) in
                   eval vm_compute in (idx_facts Tx s0 (snd (fst (fst r0))))
               | None => constr:(@nil kentry)
               end in
    let kn1 := constr:((kn0 ++ atom_ranges na) ++ (read_ranges na reads0 ++ ifs)) in
    let tsv := eval vm_compute in (tabs_of zks) in
    let tfs := lazymatch tsv with
               | nil => constr:(@nil kentry)
               | _ => eval vm_compute in (tab_ranges kn1 (tabs_of zks) na reads0)
               end in
    (* [comment removed for export] *)
    let shv := eval vm_compute in (shz_of zks) in
    let sfs := lazymatch shv with
               | nil => constr:(@nil kentry)
               | _ => eval vm_compute in (shz_ranges kn1 (shz_of zks) na reads0)
               end in
    let kn := lazymatch constr:((tsv, shv)) with
              | (nil, nil) => kn1
              | _ => constr:((kn0 ++ atom_ranges na) ++ ((tfs ++ sfs) ++ (read_ranges na reads0 ++ ifs)))
              end in
    let r := eval vm_compute in (kx_exec segs fuel stops (SCR DIRS [] []) (SS pc sr [] kn na)) in
    lazymatch r with (?ss', ?scs, ?scr', ?accs) =>
      let reads := eval vm_compute in (kx_reads_of na scs) in
      let ws := constr:(map (Z_to_bv 64) zv) in
      let KXS := fresh "KXxs" in
      pose (KXS := kx_vals segs m ws reads);
      let xs := constr:(KXS) in
      let KXE := fresh "KXE" in
      pose (KXE := kx_env ws xs);
      let E := constr:(KXE) in
      let KXA := fresh "KXA" in
      assert (KXA : forall j, (j < length zv)%nat -> ev KXE j = Z_to_bv 64 (nth j zv 0)) by exact (kE_atom zv KXS);
      let rr := constr:(map zr_reg zrs) in
      let HK := fresh "HK" in let HRR := fresh "HRR" in let HK1 := fresh "HK1" in let HSH := fresh "HSH" in
      assert (HSH : Forall (shz_ok m E) (shz_of zks)) by (cbn [shz_of]; kx_forall; kx_shz1 segs zv xs m);
      assert (HK1 : know_ok segs E m kn1);
      [ unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [ | apply atom_ranges_ok] | apply Forall_app; split ];
        [ apply Forall_map_iff; kx_forall; kx_know1 segs zv xs m
        | apply (read_ranges_ok segs m ws reads); [ vm_compute; reflexivity | | vm_compute; lia ];
          intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth
        | lazymatch ispec with
          | Some (?ztl, ?zT) =>
              let s0 := eval vm_compute in (zle (ZSub (ZL 64) ztl)) in
              let Tx := eval vm_compute in (zle zT) in
              let tlz := eval cbv [zden nth] in (zden zv ztl) in
              apply (idx_facts_ok segs E m Tx s0 tlz (snd (fst (fst r0))));
              [ exact (zle_ok zv xs zT (eq_refl true)) | exact (zle_ok zv xs (ZSub (ZL 64) ztl) (eq_refl true)) | lia ]
          | None => constructor
          end ]
      | assert (HK : know_ok segs E m kn);
      [ lazymatch constr:((tsv, shv)) with
        | (nil, nil) => exact HK1
        | _ => let HKA := fresh "HKA" in let HKB := fresh "HKB" in
               pose proof (proj1 (Forall_app _ _ _) HK1) as [HKA HKB];
               unfold know_ok; apply Forall_app; split; [exact HKA|]; apply Forall_app; split; [| exact HKB];
               apply Forall_app; split;
               [ lazymatch tsv with
                 | nil => constructor
                 | _ => let TEQ := fresh "TEQ" in
                        assert (TEQ : tab_ranges kn1 (tabs_of zks) na reads0 = tfs) by (vm_compute; reflexivity);
                        rewrite <- TEQ; clear TEQ;
                        apply (tab_ranges_ok segs m ws reads kn1 (tabs_of zks));
                        [ vm_compute; reflexivity | exact HK1 | cbn [tabs_of]; kx_forall; kx_tab1 segs zv xs m
                        | intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth | vm_compute; lia ]
                 end
               | lazymatch shv with
                 | nil => constructor
                 | _ => let SEQ := fresh "SEQ" in
                        assert (SEQ : shz_ranges kn1 (shz_of zks) na reads0 = sfs) by (vm_compute; reflexivity);
                        rewrite <- SEQ; clear SEQ;
                        apply (shz_ranges_ok segs m ws reads kn1 (shz_of zks));
                        [ vm_compute; reflexivity | exact HK1 | exact HSH
                        | intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth | vm_compute; lia ]
                 end ]
        end
      | clear HK1;
        assert (HRR : Forall (region_ok segs m E) rr);
        [ apply Forall_map_iff; kx_forall; kx_region1 segs zv xs m
        | let KXR := fresh "KXR" in
          assert (KXR : regs_ok E sr (mkRl xl)) by kx_regs_ok zv;
          let ww := constr:(map zr_reg zws) in
          let HWW := fresh "HWW" in
          assert (HWW : Forall (win_ok RNG E) ww) by (apply Forall_map_iff; kx_forall; kx_win1 segs RNG zv xs);
          unfold kx_pendingF;
          refine (kx_run_evtF segs RNG fuel stops (SCR DIRS [] []) pc sr kn na ss' scs scr' accs E (mkRl xl) F fc m rom Q
                    (rfull_mkRl xl) _ KXR HK _ _ _);
          [ vm_cast_no_check (@eq_refl (sym_state * list sidecond * scripts * list (saddr * nat)) r)
          | apply (kx_scs_bulk2 segs m ws reads kn rr (shz_of zks) scs); [ vm_compute; reflexivity | exact HK | exact HRR | exact HSH | ];
            let rest := eval vm_compute in (List.filter (fun s => negb (sc_auto2 na reads kn rr (shz_of zks) s)) scs) in
            let REQ := fresh "REQ" in
            assert (REQ : List.filter (fun s => negb (sc_auto2 na reads kn rr (shz_of zks) s)) scs = rest) by (vm_compute; reflexivity);
            change (length ws) with na; rewrite REQ; clear REQ; change (scs_denot segs m E rest); unfold scs_denot; kx_forall;
            kx_sc_rest segs m ws reads na
          | let HSR := fresh "HSR" in
            assert (HSR : Forall (shz_racc RNG E) (shz_of zks)) by (cbn [shz_of]; kx_forall; kx_shr1 RNG zv xs);
            apply (kx_accs_ok_part2 segs RNG E m kn ww (shz_of zks) accs HK HWW HSR);
            let rest := eval vm_compute in (List.filter (fun an => negb (acc_auto2 kn ww (shz_of zks) an)) accs) in
            let AEQ := fresh "AEQ" in
            assert (AEQ : List.filter (fun an => negb (acc_auto2 kn ww (shz_of zks) an)) accs = rest) by (vm_compute; reflexivity);
            rewrite AEQ; clear AEQ HSR; change (Forall (accP RNG E) rest); kx_forall
          | clear HRR HWW HSH; intros KXLF; cbn [s_log s_regs s_pc] in KXLF |- * ] ] ] ]
    end
  end.


Ltac kx_goF := kx_goFd (@nil bool).

Tactic Notation "kx_runF" uconstr(STOPS) uconstr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
  kx_prepF S Fu K R W; kx_goF.

(* [comment removed for export] *)
Tactic Notation "kx_runFd" uconstr(STOPS) uconstr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in let D := constr:(DIRS : list bool) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
  kx_prepF S Fu K R W; kx_goFd D.

(* [comment removed for export] *)
Tactic Notation "kx_runFz" uconstr(STOPS) uconstr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in
  let D := eval vm_compute in (repeat false 4096) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
  kx_prepF S Fu K R W; kx_goFd D.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AsanZ.
Variable segs : list Segment.
Variable zv : list Z.
Variable xs : list word.
Local Notation E := (kE zv xs).

Lemma adenot_ez : forall a, 0 <= ez zv E (a_base a) + a_off a < 2^64 ->
  bv_unsigned (adenot E a) = ez zv E (a_base a) + a_off a.
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["AsanZ"] "p'0h01bh11zh21Rh31ah41ki006a_basei015a_offi021sp;2p;1p;3p;6p;4g01Ugj2KTg00?_j18Tg01\4j33Tg00>cj15Tg00Fnj20Tg00C_j2@Tg001Ij14Tg00F3j1>Tg00FQj2ETg00W\j2=Tg00D[j2<Tg001nj1CTg00[@j2;Tg00HHj22Tg00@\j2BTg002Lj1JTg00YMj27Tg00I2j29Tg01:=j2:Tg01\ij3ITg01]Lj3HTg00Zbj66Tg00Z3j2ATg00GKj2?Tg01^3j2DTg01^lj4FTg00IXj3GTg00c`R0f1R1f0R23Gp=1g00`hR3P3g00cBR3p,2zvR4p,2xsR5,K4R6%8233%52'0R7'@g00j:#4R8#>%48#4#4#4#4R8#>'ER9,=7'<%C8R81;61'2%819346%51'0'1[P2g00bE1B12R7#89346%57'0R7,@31=79'<%J8R7f2R39346R:,78R;1282/03,78,28f39346/03R<'1X07P0128;R;/01R7,98112<X10R=P0198:R>1023,98/1<X10P010:1R</:9P=AI<921::9/01/:9AH:19E610>1,98/1<eP;1A8:E61787,281A87E61?63P4P61D45P3CFE61B31R3#8R5,?6,28%53R7'0,78,28/1<e1;63,28R8/1<eA3465/07,18eW2X40W0P1P2O2n01102000121100101W3o"). Qed.

Lemma kx_acc_rng : forall RNG lo len a n, rng RNG lo len -> (1 <= n)%nat ->
  0 <= ez zv E (a_base a) + a_off a < 2^64 ->
  lo <= ez zv E (a_base a) + a_off a -> ez zv E (a_base a) + a_off a + Z.of_nat n <= lo + len ->
  accP RNG E (a, n).
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["AsanZ"] "h04__x1h14__x2h24__x3h31bh41jh52H0h63Hn0h77__arithh84__ffh98__varmaph:5__with;4__x4h<4__x5h=4cstrh>1Hh?2H1h@2H2hA2HnhB2L1hC2L2hD1RhE3RNGhF1ahG3lenhH2lohI1nhJ1zp;3p;2p;1p;4p;6p;<p;7p;8g01U4j3fTg00Fnj21Tg001Ij18Tg00F3j1DTg00FQj2[Tg00C_R0j20Tg00D;R1j15Tg00D[R2j2:Tg006Ij1QTg00<iR3j2;Tg01Ugj2NTg00?_j14Tg00>cj12Tg00W\j2CTg00:Qj3@Tg00J2j2ATg00JLj4WTg00K3j1VTg00MVj1UTg000ij1RTg00NVj2<Tg00^Bj4=Tg00ORj1PTg00P0j1OTg00Qcj29Tg00Q>j1FTg00Rhj3?Tg00Snj4ETg00RFj1MTg00U=j2LTg00U_j2STg00IXj3TTg00VKj3eTg00Vjj4dTg00O4j1cTg001nj1`Tg00[@j2KTg00HHj2ITg01_dj2^Tg00Zbj6]Tg007fj3\Tg0000j3ZTg01\4j3JTg00\=j4_Tg00]]l<YTg00^`j7aTg00_Dj8bTg00cBR4f0R5'0p=7f3R6f2R7f1R83J/15p=6%459J78p=>1185,07p=3g00`hR9g00afR:P8P5C_p=BP:g00c`R;P3P1P0g00d>f5R0f4R1P6P7P8P5M<Yp=XP8g00d`R3g00e?R<P<g00e_R=P5g00ffFap=GP6P3P<P<P=P7P8P5Gbp=Hg00hEAf167P2%711116g00j:R3#8R>#D%8>R?#8#8#8#8R@#D'[RA'0f6RB/08%58,17RCf7RD/1BRE'0f9RFP6P7O2[[^4:^3;':g00k^#QRG/;7p,2zvRHp,2xs,NHRI%41%21C6RJ#71CJA':A>HI0%2053DPHPI%4B%2BC6%50'1f8RJ/1DRK'0f:RL1BDB7@I[[[[P5%7B10EA10F811LFRE,0Cf<RDP6P7O2[[^4:^3;':P210KA10L8f;RK=3CLf=R2P6P7O2[[^4:^3;1;GBPHPI%4J%2JC6RJ#71CJA':A>HIF%2F53KPHPI%4L%2LC6%5F'1?3DKf>RJ1BKL7@I[[[[P510EA1028A3CJ2f@RCP6P7O2[[^4:^3;1;GFPHPI%4K%2KC6RK#71CKA':A>HID%2D53JPHPI%42%22C6%5D'1f?;3JP;PHPI%4J%2JC6RDfBRKP5PJO2XJ;P1PDP21;G2%D3RD%52RA'0RFPGPD1A;DP2PA1A;AEXP6CWRAPF%VJRD%5J#7RGg00lZRE#URL%REREP;1<;7P81<;6C=%P;RB%O;RMP;19;3RNg00f?RO19;>RP%F3,9;R35?;CE,GMRQ%M<R<PQCH1LM=R=P5P7g00_hRQg00`HRR'A1S57=TQRdAe;48CdR4b8b9b:X0;X1;X2;1187RR,05A3876[^0;^1;^2;P5fARQ#2RSA>HIQRHfCRTP1O4b7b=b6PAPFPDPGPLPEP;P;1<;1P7%c;REC=P8P;1<;0P6PEC=C=PBPMP;A?;NP=?;3PO19;?%F>,9;5?;CE,GMRMP<PMCHP=P4b8b9b:X0;X1;X2;X;;X<;1158/17?36111R6?310[^0;^1;^2;^;;^<;P5PKPT%5CPSPHP6O6b7b=b6O4%`@R@1KIJ'I1^J7E]PQ1BJ2RJ9\9:,KI,I@AZ9:JO2eA@QIJeWCWBWDWAW>W@P8P5O2n2001000000121000000W5W?P8P5O2n2001000000121000000W5XI:XF9XG;XH;WEo"). Qed.

Lemma kx_rd_known : forall (m : word -> option byte) a b s1 s2,
  (forall s, s1 <= s < s2 -> m (wa s) = Some b) ->
  0 <= ez zv E (a_base a) + a_off a < 2^64 -> s1 <= ez zv E (a_base a) + a_off a < s2 ->
  rdn segs m (adenot E a) 1 = Some [b].
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["AsanZ"] "p'0h01bi001bh12b1h22b2h31nh41zh51Hh62H0h72Hwh81Lh91Rh:1ah;1mh<1oh=1sh>2s1h?2s2i011xp;1p;2p;3p;6p;4g001Ij14Tg001nj1ATg002Lj13Tg002oR0j1CTg00C_j2>Tg00W\j2<Tg00D[R1j2=Tg01`_j1;Tg01aNj22Tg00IXj30Tg01Ugj2GTg00?_j17Tg01\4j36Tg00>cj19Tg00Fnj28Tg00F3j1DTg00FQj2RTg00HHj21Tg01b0j3QTg00[@j2@Tg00I2j2PTg00J2j2BTg00X8j1NTg00Xaj3MTg00Zbj65Tg00YMj2LTg00Z3j2KTg01_dj2ITg000ij1HTg01bTj2?Tg00MVj1JTg00N6j3:Tg00RFj1FTg006Ij1OTg01cMj4ETg00j:#4R2#4#4R3#4#4#4R4#AR5#3R6%A3#3R3#CR7[g00`hg00c`R8f2R9f0R:'>f1R;,<:'=f6R<%;;O1f4R=,23507[^=8g00cBR>p,2zvR?p,2xs,G?R@%7=36%9='8RA'>%D2%D4'R,<A'=f3RAf5R4#796?@%94'8R2'>1<29'=g01dBR2%3:RB%3;RCP1%39?0;:11A911A;508R1[119;119:508%3A?09;[RD%3=?0A9\1AQ9;:P:n2001000000120000000W2W1W3PD^2C^1B^32P:P5f7R2,@@RB%7296?@%92'8RC#;RDP8PCf8R1#796?@%91'8R=#;RE,15908:X48P81P5CRFA08=:X48R=P8PCP=1B8CPFP91>>C%N5,<C'=e9M5CE51L5C,151K5CE5115D908Ce115B1I29E5O4b61@@<R9%7<96?@%9<'8#;506P6PD%H3R@#CR?P0P3P?P0P3P7f9P:O1123:R5p,4segsR>/?:n10110100021010000%J3RF9:3:,2@R=%F@RGn10110100021010000A:32F,2@RH30X06P7123<P0P3P?P0P3P7P:P51?>En10110100021010000P=PGn10110100021010000=0?HX<7A:3<F,2@,B?P1PDO1PAPCP;O2E5PBP:E5b7P>P2P9g00k^#OCEA:34F,2@50?eW8W9W5X?8W>X03W:W;o"). Qed.

Lemma kx_rd_known_ex : forall (m : word -> option byte) a b s1 s2,
  (forall s, s1 <= s < s2 -> m (wa s) = Some b) ->
  0 <= ez zv E (a_base a) + a_off a < 2^64 -> s1 <= ez zv E (a_base a) + a_off a < s2 ->
  exists bs, rdn segs m (adenot E a) 1 = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["AsanZ"] "h01ah11bh22bsh31mh41sh52s1h62s2p;1p;2p;3p;4p;8g001Ij10Tg001nj1;Tg002Lj15Tg002oj14Tg00C_j23Tg00W\j22Tg00D[j21Tg01`_j1@Tg01aNj26Tg00IXj37Tg01Ugj2>Tg00?_j19Tg01\4j3:Tg00>cj1=Tg00Fnj2<Tg00F3j18Tg00FQj2HTg000ij1GTg00[@j2FTg006Ij1CTg01cMj4BTg00MVj1ATg00N6j3?Tg01d`j8DTg01e]j4ETg00j:#0R0#0#0R1#0#0#0R2#;#5%;1#5R1#4R3[g00`hg00c`R4f2R5f0R6'3f1R7,26'1f6R8%@7O1f4R9,61573[^44g00cBp,2zvR3p,2xs,>3R:%993:%=9'<R;'3%80%82'H,2;'1f3R;f5R2#99:3:%=2'<R3'31235'1%G1R3%43p,4segsf8f7R0,F:g00k^#CCB163637X23%A19?12P0P8P2P9P;P5P7P6GDCEUUUX64W5X11W0W3o"). Qed.

(* [comment removed for export] *)
Lemma kx_br_zero : forall (m : word -> option byte) a s1 s2 sx e,
  (forall s, s1 <= s < s2 -> m (wa s) = Some (Z_to_bv 8 0)) ->
  0 <= ez zv E (a_base a) + a_off a < 2^64 -> s1 <= ez zv E (a_base a) + a_off a < s2 ->
  edenot E e = rdval segs m (adenot E a) 1 sx ->
  branch_taken BC_NE (edenot E e) (edenot E (ELit 0)) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_KXGoF ()) ["AsanZ"] "p'0h02Heh11Hh21Lh31Rh41ah51bi001bh61eh71mh81oh91sh:2s1h;2s2h<2sxi012sxi022bsi031xp;1p;2p;3p;5p;4p;8p;6g001Ij10Tg001nj1FTg002Lj1ATg002oR0j1?Tg00C_j27Tg00W\j28Tg00D[j2;Tg01`_j1UTg00YMj22Tg01aNj2=Tg00IXj33Tg01Ugj2HTg00?_j1@Tg01\4j3ETg00>cj1CTg00Fnj2BTg00F3j1:Tg00FQj2WTg00GKj26Tg00[@j29Tg006Ij1VTg01f7j55Tg01g1j1TTg000ij1RTg00MVj1QTg00N6j3LTg01gnj1>Tg01hkj3<Tg01igj1KTg01jGj2JTg00HHj2ITg01jdj2MTg01kDj2NTg01kaj2OTg00J2j2PTg01cMj4GTg01d`j8STg00Zbj6DTg01lHj3XTg01m7f1R1f0R23Xp=4g00_hR3g01miR4732p=1g00j:#0R5#0#0R6#0#0#0R7#FR8#AR9%F6R:#AR;#?R<[g00`hg00c`R=g00bEf4R>/72f3R?,82';f7R@%U1O1g00cBRA,2:RB,=;53<[^9=p,2zvR<p,2xs,H<RCf5RD#@3E%CD'BRE,7A%:5%:7'W,8E';f6RE#@9E<C%CE'BR<,7D18<>';16C?p,4segsR<f8R719C@g00k^#VR5P>D5539P9P<f9RF19C7RGP5PDD5RH%TA,6CRI,42#1X59%R;RJ#?RK%Q;9L;BR;,=JP0PJP9P2%>29<@5,28128An10110300021010200/4I#1X8KP316CDP<f:19CFP5P2D5539P3P=P1%K5,J:1I:B%:6,MA'NRA'OPAn0110100020000,28/4I#1]0PD16C>RCP<PFPGP5g00`HD55391P34R>W0P<PFPGP5P4D5939CP>W0n0110000020000P2O1A<D5A,28/4I#1e%>;9<D5,28/4I#1eP<PFPGP5CGPFP7PBP@PEP?f2P1GSED14HI#1ePCP2EDW0W2W3W1W6X<3X;=W:W4W7o"). Qed.
End AsanZ.

Ltac kx_zfin := let na := lazymatch goal with |- context [kE ?zv _] => eval vm_compute in (length zv) end in idtac.

(* [comment removed for export] *)
Ltac kx_zsimp zv :=
  let na := eval vm_compute in (length zv) in
  cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
  rewrite ?Z.mod_small by (Z.div_mod_to_equations; lia).

Ltac kx_asan SHZ :=
  lazymatch goal with
  | |- accP ?RNG ?E (?a, ?n) =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        change E with (kE zv xs);
        match goal with H : rng RNG ?A ?N |- _ =>
          apply (kx_acc_rng zv xs RNG A N a n H ltac:(lia)); kx_zsimp zv; Z.div_mod_to_equations; lia end
      end
  | |- exists bs, rdn ?segs ?m (adenot ?E ?a) 1 = Some bs =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        change E with (kE zv xs);
        eapply (kx_rd_known_ex segs zv xs m a _ _ _ SHZ); kx_zsimp zv; Z.div_mod_to_equations; lia
      end
  | |- branch_taken BC_NE (edenot ?E (EVar ?j)) (edenot ?E (ELit 0)) = false =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        let H := fresh "RV" in kx_read_eq j H;
        lazymatch type of H with _ = rdval ?segs ?m (adenot _ ?a) 1 ?sx =>
          change E with (kE zv xs) in H |- *;
          eapply (kx_br_zero segs zv xs m a _ _ sx (EVar j) SHZ); [ kx_zsimp zv; Z.div_mod_to_equations; lia
                                                                  | kx_zsimp zv; Z.div_mod_to_equations; lia | exact H ]
        end
      end
  end.
