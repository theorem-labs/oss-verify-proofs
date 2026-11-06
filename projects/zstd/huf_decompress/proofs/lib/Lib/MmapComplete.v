(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MmapComplete () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib9Placement:vm_base_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib9Placement<vm_find_baseC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC46Stdlib6ZArith4Zdiv:Z_mod_multC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z8le_transC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib3Lib<MmapCompleteHvm_base_fold_max_ge_seedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List4findI47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega:ZMicromega;ZArithProof03C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic3iffc59OSSVerify5KrLib3Lib<MmapCompleteCvm_base_fold_max_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib<MmapCompleteKvm_base_fold_max_in_or_seedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib3Lib<MmapCompleteEvm_base_round_alignedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z;le_gt_casesc59OSSVerify5KrLib3Lib<MmapComplete@vm_base_round_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib<MmapCompleteFvm_base_fold_max_ge_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib<MmapComplete@vm_base_round_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z7le_reflC56Stdlib6ZArith6BinInt1Z;add_le_monoC4ELinuxProcessSemantics?LinuxProcessSem5StateAregion_free_introC59OSSVerify5KrLib3Lib9PlacementBvm_base_candidatesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c59OSSVerify5KrLib3Lib<MmapCompleteBvm_base_find_of_InC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List8map_consc59OSSVerify5KrLib3Lib<MmapCompleteEvm_find_base_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib<MmapCompleteJvm_find_base_gap_availableC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Hceil].
  apply andb_true_iff in H as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Hceil.
  repeat split; assumption.
Qed.

Lemma vm_find_base_gap_available : forall h nZ a,
  vm_find_base h nZ = Some a -> vm_gap_available h nZ = true.
Proof. intros h nZ a H. unfold vm_gap_available. now rewrite H. Qed.

(* [comment removed for export] *)
Lemma vm_base_round_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h01zp;2p;1p;3g004nj27Tg00HBj16Tg00H`j20Tg00I=j21Tg00IZj25Tg00J:j12Tg00?4j23Tg00<Bj34Tg00AjR0f0R1g00@TR2'7g00C?#6'0/12/52%21/32g00AL540eW0o"). Qed.

Lemma vm_base_round_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h02H0h17__arithh24__ffh38__varmaph45__with52H1h62H2h72H3h82H4h94__p1h:6__sat1h;4__x1h<4__x2h=4__x3h>1qh?1rh@1HhA2H5hB2H6hC6__sat0hD6__sat2hE1zp;1p;2p;4p;6p;3p;7p;8g000Gj1>Tg00HBj1ITg00K8j1jTg00KXj1\Tg00L8j1XTg00LVj1UTg00M4j1TTg00M_j2@Tg00NBj49Tg00Nmj6RTg00OQj2iTg00Egj2gTg00P3j2`Tg00<Bj3BTg00P_j3ZTg00Q>j4YTg00R0j3Vj2KTg00I=j24Tg00RQj25Tg00?4j22Tg004nj2:Tg00Rnj2GTg00S_j2FTg00TPj1STg00Tij2Ej3QTg00:mj23Tg003HR0j28Tg00UPj2DTg00;Ij27Tg00V7j2HTg00V]j2JTg00WCj1NTg00Wbj2CTg00XKj3PTg00Y4j2hTg00Y`j3fTg00Z@j2OTg00Z^j4eTg00[<j1_Tg00[^j6^Tg00\Bj1]Tg00\gj2?Tg00]Jj7[Tg00]nj3LTg00^Qj3aTg00_4j3MTg00J:j1bTg00H`j2cTg00_Wj7dTg00`;j8WTf0R1#>#>p=;f2R2f1R3':/c1p=1P3g00`_R4g00a>R5P5g00a^R6P1g00b>Fdp=<g00AjR7g00ALR87B1p=AAB731p=61781p=0f3R9P4P5P5P6P2P3P1GWp==g00C?R:#>R;#>#;#;#;#;#;#IR<%I:R=511R>g00b^R?#jR@%\?RA%X7RB%U7RC%T7RDP4P5P5P6P71@7<REg00cJRF1@78RGC9,<DERRH1iD6RIP1P2g00?TRJg00@4RK'g1`12=BJKdAZ783CYRKb2b3b4%A<RJg00d1[RLP1b17V<14><,5<12><':,6>A13<=R>1G><%0>%0<RMA19<=RN/2<#0[[A12<=RO/F<%0ORPf4RQ?1<=RR/4<RS#0\M[1KN<%SJRT15<S12R<RS':,6R[1ER<138<RUf5RV?1<=RW/2<RX#013X<'8[1DW<13<8RYf6RZ?1<=R[/2<R\,3<17\8'8[1H[<f7?1<=R]/4<#A\J1J]<f8?1<=R^/2</6^\J14^<R_P7f9R`?1<=Ra/2<RbP7P@PAPBPCP7PGg00dNRGPEC9,<DRBPIPKb2b3b4PUP1b1b?b>b8b7b6b5b0bCb:7Q<12><R>#013><'81GO<%0S\M\P1FN<%0N14W<RN#0\M[1KR<15<N/:X,6W\T1EW<%0\13\<'8\U1D[<12]<R[,3<17[8'8\Y1H]<%A_\J1J^<16ba\J14a<P7f:Ra?1<=/2<P7P0%01131<f<152<'7P`%02139<R`p-0R0g00e5RJ#NRb#N,C71C7b1C7J5P75P7g00eT'h=f?@PAP71O72P31O79CePCPDPDPB%_5RBPDP4P5P5P6PDP4P5P5P6PVE^P7%]:,?7R6PGPEC9,<DF[C=PBPDPDPHPBP71?7:R:=L7E1@7=5a7PF1?7;R;9M7E=L76C9,<DC=PBP7P:g00f@AM7;EC9,<DC=C=PIPKb2b3b4X;7X<7X=7W918Q`\U15<9/:Q,6O\L159<,72[[^;7^<7^=7^90P1%0VPVPZf@Paf;O6b1WBW0P3P1O2n2001000000121000000b?b>bAb8b7b6b5b:bDb0b@%b1,71eXE7o"). Qed.

(* [comment removed for export] *)
Lemma vm_base_round_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h01Hh12H0h22H1h32H2h42H3h57__arithh64__ffh76__sat0h88__varmaph95__with:4__x1h;4__x2h<1qh=1rh>6__sat1h?4__x3h@2H4hA2H5hB2H6hC2H7hD2H8hE6__sat2hF2q0hG2r0hH4__x4hI2HbhJ3HbmhK2HqhL3HzbhM1bhN1zp%0p;2p;1p;6p;3p;4p;5p;7p;8g00;Ij2:Tg00?4j20Tg000Gj1GTg00HBj1WTg00Rnj2STg00R0j2>j3ZTg00TPj1aTg00I=j21Tg00Tij2ATg00:mj23Tg003Hj25Tg00UPj2;Tg00V7j2<Tg00V]j2=Tg00K8j1fTg00KXj1eTg00L8j1dTg00LVj1cTg00M4j1bTg00M_j2QTg00Nmj6`Tg00OQj2_Tg00Egj2^Tg00P3j2]Tg00<Bj3HTg00P_j3\Tg00Q>j4[Tg004nj2ETg00S_j2PTg00WCj1UTg00Wbj2NTg00XKj3DTg00Y4j2YTg00Y`j3XTg00Z@j2TTg00Z^j4FTg00[<j1rTg00\Bj1qTg00\gj2MTg00_4j3JTg00]nj3ITg00^Qj3pTg00RQj2CTg00fgj5oTg00gSj5nTg00hAj1hTg00h_j2gTg00i@j3VTg00iij5iTg00J:j1jTg00NBj4RTg00_Wj7kTg00H`j2lTg00`;j8mTg00AjR0f0R1g00ALR23Hp=7%G1#Gp=B1:21p=4f3R3f2R4f1R5'C/E15H0p=81:12p=@AH051p=?P0P5g00cJP1CRp=KP5g00`_R6g00a>R7P7g00a^R8P1g00b>Fkp=61E45/l1p=2P0P5g00dNP1CRp=OP3P6P7P7P8P4P5P1Gmp=9P0P5g00f@P1CRp=L1:51g00@T,05#7g00C?R9#GR:#GR;#B#B#B#B#B#WR<1S4<%44%4<R=f4R>/0<R?#4[[1>3<%7<R@#aRAP>P<11><RBP?C8[1A><132<R?f5RC/0<RD#4RE13D<'5[1;C<13<2RDf6RF/0<RG,3<%@G'5[1<F<f7RH/1<RI#7\@1=H<f8RJ/0<RK/?J\@11J<S00P0f9RL/0<RMP0g00b^RN#fRO%eNRP%d0RQ%c0RR%b0RSP6P7P7P81Q0<R61Q02RT'K,6SE`RU1_S8R8P1P4g00?TRVg00@4RW'^1]14=HVWdA\025C[R2b6b8b9g00d1\@RWP1b5b=b<b4b3b2b1b0b75Z4P4P<114<104<C8%W9RV92><RXP<113</EVRY1S3<RZ%43PE\=[RE1P><R[%4>R\11F<R]#4\=[R^1>C<R_PFP<P]PGC8\AR]1AF<RF10H<R`#413`<'5\?R`1;H<Ra13<K%@K'5\DRb1<J<Rc11L<#7\@Rd1=L<Ref:Rf/0<Rg/?f\@Rh11f<RiP0f;Rj/0<RkP0POPPPQPR1OT6,6SP8P2b6b8b9P?P1b5b=b<b4b3b2b1b0b7b>PZPEP[P^P_P]PFP`PaPbPcPdPePhPiP0PkP0g00e5Rk#URi#URh#U,N01N0hRh1N0iRi1N0kRk5D05D05D0g00eTRe'Y=XNOPPP0P01T0>P4PQCFP51T03S01CFPRPSPSPU%r7R7%q9,M0Rd1M0:R:9J061M0;R;5I0'K,6SC9P7PS1K;T,6SS02P7PS1M09Rc/Ld,6SP7AI0c61Q0VRd5p0AI0:dRd9J06'O,6SC9C9C9P8P2b6b8b9X:0X;0X?0XH0P3P<P4P>C8\W%7>1:4>A23<V1E>V,C<'3[[[^:0^;0^?0^H0P1P5f=RbP4f>RaPHPjf<R`O7b5b=b<b4b3b2b1b0b7b>Do11X</3YA2C<V/1<RY/C<1CB<P>PYPBP<1S><R>%4G\=\\R\1PC<RG%4C%4I\=[RIA2H<VRC/P<RB%4CA2L<VRC/1<RY#4\=[RXA2J<V/><S03PCP<PY10C<C8\AS041AC<RCA2f<VRY/0<RF#413F<'5\?RF1;Y<RYA2j<VR]/0<R_,3<%@_'5\DR_1<]<R]A2`<VR^/1<#7\@R[1=^<R^A2b<VRE/0</?E\@RZ11E<REP0A2a<V/0<RlP01>a<Rmf?RnP<11n<10n<C8\ARo1An<Rpf@Rq/0<Rr#413r<'5\?Rr1;q<RsfARt/0<Ru,3<%@u'5\DRu1<t<RvfBRw/1<#7\@Rx1=w<RyfCRz/0</?z\@R{11z<R|P0fDR}/0<R~P0POPPPQPR1LT6,6SP8P2b6b8b9P=P1b5bGbFbDbCbBbAb@b=b<b4b3b2b1b0b7b>bEP>P\PGPIPBPXQ03Q04PCPFPYP_P]P[P^PZPEP0PlP0PmPoPpPrPsPuPvPxPyP{P|P0P~P0POPPP01T04P5PQCFPRPS1Ocd,6SP71Lc:,6SC9P8P2b6b8b9X:0X;01E5V,311:54[^:0^;0P1P4PLPwO3b5bGbFbDbCbBbAb@b=b<b4b3b2b1b0b7b>bEDnP>P\PGPIPBPX1>H<PJP<Q00PKC8\A1AJ<%4M13M<'5\?1;L<13<g%@g'5\D1<f<11j<#7\@1=j<10`</?`\@11`<P010b<P0A2n<V/><A2q<VRqP<11q<10q<C8\A1Aq<A2t<VRt/0<Rq#413q<'5\?1;t<A2w<VRw/0<Rt,3<%@t'5\D1<w<A2z<VRz/1<#7\@1=z<A2}<VRz/0</?z\@11z<P0fE?2<V/0<P0%h9,g0R9=V0hAV09i=D0k5D0/Ye=XNOPPP0P0Q01P4PQCFP5PQCFPRPSPSPUP7AJ06c=I0;,K:,6SC9P7PSQ02P7AJ0c6/L:,6SC9C9P8P2b6b8b9X:0X;0X?0P4P<P5P3C8\W%731C4</:3[[^:0^;0^?0P1PJfFPLPaP}O5b5bGbFbDbCbBbAb@b=b<b4b3b2b1b0b7b>bEDibKbJ%j3/:4eWIWLXM0XN0o"). Qed.

Lemma vm_base_fold_max_ge_seed : forall l s, (s <= fold_left Z.max l s)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h04__x1h11lh21sh37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94__x3h:4__x4h;1Hh<2H0h=2IHh>1xh?2z0p;1p;2p;3p;4p;6p;7p;5p;8g00KXj1FTg00;Ij20Tg00K8j1ATg00Z@j2=Tg00LVj1UTg00M4j1OTg00\gj27Tg00OQj2JTg00Egj2HTg00P3j2GTg00<Bj33Tg00P_j3XTg00Q>j4VTg00jKR0j2<Tg00jhj2TTg00:mj2BTg003Hj25Tg00kJj2@Tg00hAj1NTg00h_j2MTg00WCj1;Tg00Wbj24Tg00i@j3LTg00XKj38Tg00Y4j2?Tg00Y`j3:Tg00L8j1KTg00Z^j4>Tg000Gj1ETg00NBj46Tg00\Bj1ITg00[^j6PTg00kdj7QTg00[<j1RTg00lHj5STg00ljj5[Tg00_Wj7ZTg00]Jj7YTg00`;j8WTg00AjR1P1P0f1R0f0R2D[p=2P1P0g00f@P2C6p=9P0g00`_R3g00a>R4P4g00a^R5P2g00b>FZp=1f2R6P3P4P4P5P0P2FYp=Cf3R7P3P4P4P5P6P0P2GWp=D%F1R8P11202,02^21R9X18g00b^R:#AR;%F:R<1=10%U1R=%O1R>g00C?R?,71R@/9@'11J>5RAP2P6g00?TRBg00@4RC'H1G26=3BCdg00AL=X10CVRCb4b6b7X011022^01P2P0O1b3%A1/22,02eX21P01<27RBO1126B,0Bf4RB,T01B0B1<0BRD=31B'510B0A31D0'5'@f5,<6P1p-0RD%N?,M1g00e5RE#;RF#;RG,415L1141F141E581581REg00eTRF'?%;G,41=81E/?F=::;5::P<P1P11=1BP6%K1C>P01=17C>P=P>P>P3P4P4P5P1P@g00dN%E?R=#E,71R<C6,1>P1%I?,71R?g00cJR:P<C6,1>5C>P>P3P4P4P5f6R5EPP1P?P:P@C6,1>5C>FQ%R4R4P>171=R=,9?,1>P419@=,1>CDCDPAPCb4b6b7X01X81X91X:1W51B27A3167'5A3162,5B'@10761067[[^01^81^91^:1^5DP2f7RD/0BPDP01250PBP6P7O7b3b?b<b;A:176/22,02eX21X=9X18X>1P2DSW1o"). Qed.

Lemma vm_base_fold_max_ge_in : forall l s x,
  In x l -> (x <= fold_left Z.max l s)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h03Hinh11lh21sh31xh41Hh54__p1h64__x1h74__x2h84__x3h94__x4h:1yh;2H0h<2IHh=7__arithh>4__ffh?8__varmaph@5__withA2z0p;1p;3p;2p;4p;6p;7p;5p;8g00KXj1ETg00mHj34Tg00;Ij20Tg00K8j1DTg00m_j2XTg00Y`j32Tg00jKR0j29Tg00n>j2LTg00jhj2KTg00:mj2@Tg003Hj28Tg00kJR1j2GTg00WCj1=Tg00Wbj26Tg00hAj1WTg00h_j2VTg00i@j3UTg00XKj3<Tg00Y4j2CTg00Z@j2BTg00L8j1RTg00Z^j4ATg00LVj1QTg00M4j1OTg00[^j6NTg00\Bj1MTg00\gj27Tg00NBj4;Tg000Gj1?Tg00kdj7JTg00[<j1PTg00OQj2ITg00Egj2STg00P3j2TTg00<Bj3HTg00P_j3`Tg00Q>j4_Tg00FAj6^Tg00lHj5]Tg00ljj5\Tg00_Wj7YTg00]Jj7ZTg00`;j8[Tg00AjR2P2P0f1R0f0R3D\p=1AH203p=3P0g00`_R4g00a>R5P5g00a^R6P3g00b>FYp=5f2R7P4P5P5P6P0P3FZp=>P2P0g00f@P3C;p=:f3R8P4P5P5P6P7P0P3G[p=F%E2R9P2A42371187,00[^32^22R:X19%D2R;942311;7,00/X3W0X32X22f4R;=2289423P1f5R1/30A420;f6R<=221/18,07P313<7P2P8f7R=9223/11,0;X:219;8R>,L<11<>,0>1K1;1@1;191;R>/3;'810;113>1'8'G19<1P2p-0R>g00b^R?g00e5R@#=RA#=RB#=,62g00C?RC#W,V2162B5U2162A162@5<25<2R@5<2g00eTRA'C1C@A%D?52?32%E?P2P21B2;P7%R2CAP01B28CA%Q2%O2R?P?P4P5P5P6P?P4P5P5P6P<ENP2%MC,72R4g00cJRA172CR@C;,5?5>?%?CRC#?,72RB,:@,5?P2P4PAPBC;,5?5>?FJ%P5R5P?172CRC,:4,5?P51:@C,5?CFCF1I?6P3P7g00?TR?g00@4R6'S1T37=H?6dg00AL=`20C_b>b?b@X62X72X82X92W51373,8;10381378'8'G10871078[[^62^72^82^92^5>P3f8R>/@=P>P0f:/10P=P7P8O7b=bAb;b4A228</1;,08eP=P3E^W4P3O1A4271P119;=P8P3O3A22=</1;,08eW0P3O1n200100000021100010000W0X32X22X<:X19X:2P3D]W1o"). Qed.

Lemma vm_base_fold_max_le : forall l s b,
  (s <= b)%Z -> (forall x, In x l -> (x <= b)%Z) ->
  (fold_left Z.max l s <= b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h01xh11bh21lh31sh42Hlh52Hsh64__p1h74__p2h84__x1h94__x2h:4__x3h;4__x4h<1Hh=2H0h>2Hxh?2IHh@7__arithhA4__ffhB8__varmaphC5__withD1yhE2z0p;1p;2p;3p;4p;7p;5p;6p;8g00KXj1JTg00;Ij20Tg00K8j1DTg00Y`j3=Tg00jKR0j2<Tg00Egj2BTg00oLj3RTg00jhj2NTg00:mj2@Tg003Hj27Tg00kJj2ITg00WCj1>Tg00Wbj26Tg00XKj35Tg00Y4j2HTg00Z@j2GTg00L8j1WTg00Z^j4ETg00LVj1VTg00M4j1STg00\gj24Tg000Gj1FTg00NBj4:Tg00\Bj1QTg00kdj7PTg00[<j1MTg00OQj2LTg00P3j2OTg00<Bj3?Tg00P_j3KTg00Q>j4TTg00ofj3UTg00lHj5^Tg00mHj3]Tg00ljj5\Tg00[^j6[Tg00_Wj7ZTg00]Jj7YTg00`;j8XTg00AjR1f1R2f0R33]p=2P1P1P0P2P3D\p=8A?123p=1P2g00`_R0g00a>R4P4g00a^R5P3E[p=CP2P0P4P4P5P3g00b>FZp=3f2R6P0P4P4P5P2P3FYp=AP1P2g00f@P3C:p=;f3R7P0P4P4P5P6P2P3GXp=9%J1R8P11023R9f4R:,231027R;[^0118:7/06[[^11^31R<X28%D1R=,23P;[^01P218=7/06eW4X59X11X31f6R=f5R>5=1R?,23P;[^01P:1<7=P6P3P=11==12=>1B1=3RO210=6f7R;,N:1@:;1<:;R@/1;'710;:11@:'7'If8R@,<>P1p-0RAg00b^RBg00e5RC#>RD#>RE#>,61RF161D161CRC551551g00eTRD'H161E=51C951F/HD%DB5=B3=%JBP1P11G1:P6%W1CEP21G17CE%V1%S1RBPBP0P4P4P51CB=P1g00C?R0,41RDg00cJRF%F0RC#F,41REC:,3B5AB1CB;P1PDPF%Q0,41R0C:,3B5ABFP%M4R4PB141CRC,;E,3BP4PB1;0C,3BP41;DC,3BC9C9C91LB5P3P6g00?TRBg00@4R5'B1O36=?B5dg00AL=K12CTbAbBbCX81X91X:1X;1X6AW71137,7:1136,7>'I10:610:7107:[[[^81^91^:1^;1^6A^7AP3f:RA/0;1@;APAP;P=P2P6P7P>O9b@bEb=b<123=P6P211@2122;;U3O2W>X01O418?7/06eW4X59X11X31X?<X28XD1P3D^W2o"). Qed.

Lemma vm_base_fold_max_in_or_seed : forall l s,
  fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "h01Hh11lh21sh32_Hh41oh51zh63Heqh73Hinh82IHh91yp;1p;2p;3p;6p;5g00KXj1FTg00Egj2?Tg00oLj3:Tg00K8j1CTg00jKR0j21Tg00jhj2@Tg00:mj26Tg003HR1j25Tg00;Ij28Tg00kJR2j23Tg00ofj3>Tg00FAj6=Tg00Y`j3DTg00lHj5BTg00ljj5ATg00<Bj3<Tg00mHj3;Tg00AjR3P3P0f1R0f0R4DAp=4f3R5f2R65<3A;304'3p=2A<304p=0A;304p=9A<360/34p=7A;304,36p=E%F3R7P31404R8P4P8P0C2^23R8X171044g00d11?343:%C3R9/44R:P4P:P9C2eX23P01145R9O11469R:P9P:P6C2P2f4R:,10R9,45R;/0919;5f5R;,16R9,4:R<19<:R=97;<776P410<9P3f6R<,15R9f7R>P4P4P<C2974:X531@5<165<109<'518<51095'5'3P216:>11:>R2/0>'518>:102:'5f8R2,1;R:/0;R?P2P:P:P>C2'3P416;210:2'5P1f9R:,6<11<:R@/0:f:RA,1>RBPAPBPBP:C277>R>P4f;RB,62f<RC,1:RD/0CP3f=REf>P4P4PEC2974BX53RF10EARG10EERH19ECRI'31?3E9:HI3>11AEREP4E=W0W3P0P4O2n2001000000120000000W0P4O1182;/5?P118:<10@<P>P418B210D:P3PAPF10AAAEGAC1?3A3:PEP4E=W0W3P0P4O2n2001000000120000000W0P4O1n200100000021000010000b414;9R9P4E=W6P4O1109510<9R<199;R9'3A><943>X7=P4O1n200100000021100010000b4AD356R6/44R5P4P5P6C2eX23X88X17X93P4DBW1o"). Qed.

Lemma vm_base_find_of_In : forall {A} (f : A -> bool) l x,
  In x l -> f x = true -> exists y, List.find f l = Some y.
Proof.
ltac2:(KReplay.run1 (kr_t_MmapComplete ()) [] "p'0h01yh12Hyh21xh33Hinh41lh51Hh62Hxh71Ah83Heqh92IHh:1bi001bh;1eh<1fp;1p;3p;2p;4p;6p;7p;5p200R0g00mHR1p4p710p8P0g00FAR2p4p710p8P0g00lHR3p4p710p8P0g010@R4p4p710p8g00KXj18TP1j35Tg00Cdj12TP4j34Tg00EEj21Tg00<Bj30Tg010Yj23Tg00K8j1<Tg00m_j2;Tg00Y`j3:Tg00Egj29Tg0113j4=Tg011Mj4BTg011ij6ATg012Gj6@TP2j7?TP3j5>Tg00?TR3f0R2g00@4R430p=6g00GbR19032p=7P3\2f1R5#8f2R6%86f3R7f4R8?525P8P5O1#6f6R9f7R:#2A4:9811:230X09'3[[]2W4%<79572P7P5O1#6f5R;%29%<9949;119230X0;'3/;5W6W3X26%87A5;25P;P5O1#6f8R<#2A4<:811<230X0:,3:[[^28A:9769592P9P5O1#6P:P;O1P31932P<P9O1=032P3f:R7P<O1=032f<R=f=R>#2R?P3f>#2P611>7f9R@94>=RAn010000002000011>2RB30X0='3]1P5P@P:O1R5#6f;RC%2=11=@11=230X0CP<%2C11C<'9C=W1%75g00kJA0C<;A5C;:A0?ABX0=,3=P8A0=@9P>P:P>P2O1#7f?R8f@RB#2A4B8=11B230X08'3]1X0>P=P:O1#7P3P1P>P<O1R8P4P3P8P1P2CBP9EAA0314P3P1P3p-0P2g00d1R1g012cn0110000020000X;3g013?P4P2E@P1fAR1#2A41B>111230X0B,3B/;2b5b8W1P7P2P6F?W5P2O1A5=9<P<P:P2P;O3W3P2O1n200100000021000010000W1n0110000020000P2O1b1b:%2@A:@9;94@<11@230X0<,3<eW6W3X2;W9W4X06P2D>W4W<X70o"). Qed.

Lemma vm_find_base_complete : forall h nZ g,
  (0 <= nZ)%Z ->
  (bv_unsigned g mod page_size = 0)%Z ->
  (0 < bv_unsigned g)%Z ->
  (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 nZ) = true ->
  exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ g HnPos HgAl HgPos Hghi Hgfree.
  pose proof (alloc_top_lt h) as Htop.
  assert (Hmod : two_pow_64 = bv_modulus 64) by reflexivity.
  set (maps := vm_reserved h ++ vm_maps h) in *.
  set (G := bv_unsigned g) in *.
  assert (HG : (0 <= G < bv_modulus 64)%Z)
    by (subst G; rewrite <- Hmod; pose proof (bv_unsigned_in_range 64 g);
        unfold bv_modulus in *; unfold two_pow_64; lia).
  assert (HnW : bv_unsigned (Z_to_bv 64 nZ) = nZ)
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; rewrite <- Hmod; lia).
  assert (Hfloor : (page_size <= G)%Z).
  { unfold page_size in *.
    pose proof (Z.div_mod G 4096 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound G 4096 ltac:(lia)). nia. }
  set (cZ := page_size
             :: map (fun iv : word * word =>
                       page_round_up_Z (bv_unsigned (fst iv) + bv_unsigned (snd iv)))
                    maps).
  set (cs := List.filter (fun c => (c <=? G)%Z) cZ).
  set (g' := fold_left Z.max cs page_size).
  assert (Hcs : forall x, In x cs <-> In x cZ /\ (x <=? G)%Z = true)
    by (intro x0; unfold cs; exact (filter_In _ x0 _)).
  assert (Hlo : (page_size <= g')%Z) by (unfold g'; apply vm_base_fold_max_ge_seed).
  assert (Hhi : (g' <= G)%Z).
  { unfold g'. apply vm_base_fold_max_le; [exact Hfloor|]. intros x Hx.
    apply Hcs in Hx. destruct Hx as [_ Hx]. now apply Z.leb_le. }
  assert (Hcand : In g' cZ).
  { destruct (vm_base_fold_max_in_or_seed cs page_size) as [Heq|Hin].
    - assert (Heq' : g' = page_size) by exact Heq. rewrite Heq'. now left.
    - apply Hcs in Hin. exact (proj1 Hin). }
  assert (Hg'W : bv_unsigned (Z_to_bv 64 g') = g')
    by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold page_size in Hlo; lia).
  assert (Hg'Al : (g' mod page_size = 0)%Z).
  { destruct Hcand as [Heq|Hin].
    - rewrite <- Heq. reflexivity.
    - apply in_map_iff in Hin. destruct Hin as (p & Heq & _).
      rewrite <- Heq. apply vm_base_round_aligned. }
  assert (Hg'free : region_free maps (Z_to_bv 64 g') (Z_to_bv 64 nZ) = true).
  { apply region_free_intro. intros b s Hin.
    pose proof (region_free_In _ _ _ _ _ Hgfree Hin) as Hno.
    unfold iv_overlap in *. rewrite HnW in Hno. fold G in Hno.
    rewrite Hg'W, HnW.
    apply andb_false_iff in Hno.
    set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
    destruct (Z.le_gt_cases (B + S) G) as [Hend|Hend].
    -
      assert (Hc : In (page_round_up_Z (B + S)) cZ).
      { right. apply in_map_iff. exists (b, s).
        split; [reflexivity|assumption]. }
      assert (Hcle : (page_round_up_Z (B + S) <= G)%Z)
        by (apply vm_base_round_le; assumption).
      assert (Hcg' : (page_round_up_Z (B + S) <= g')%Z).
      { unfold g'. apply vm_base_fold_max_ge_in. apply Hcs. split; [assumption|].
        now apply Z.leb_le. }
      pose proof (vm_base_round_ge (B + S)) as Hround.
      apply andb_false_iff. left. apply Z.ltb_ge.
      exact (Z.le_trans _ _ _ Hround Hcg').
    -
      destruct Hno as [Hno|Hno].
      + apply Z.ltb_ge in Hno. lia.
      + apply Z.ltb_ge in Hno.
        apply andb_false_iff. right. apply Z.ltb_ge.
        exact (Z.le_trans _ _ _
                 (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hno). }
  unfold vm_find_base.
  apply (vm_base_find_of_In (vm_base_ok h nZ) _ (Z_to_bv 64 g')).
  - unfold vm_base_candidates. fold maps.
    destruct Hcand as [Heq|Hin].
    + left. now rewrite Heq.
    + right. apply in_map_iff in Hin. destruct Hin as (p & Heq & Hp).
      apply in_map_iff. exists p. split; [now rewrite Heq|exact Hp].
  - unfold vm_base_ok. fold maps. rewrite Hg'W, Hg'free.
    rewrite (proj2 (Z.eqb_eq _ _) Hg'Al).
    assert (Hg'base : (g' + nZ <= alloc_top h)%Z)
      by exact (Z.le_trans _ _ _ (Z.add_le_mono _ _ _ _ Hhi (Z.le_refl nZ)) Hghi).
    rewrite (proj2 (Z.leb_le _ _) Hg'base).
    assert (Hg'pos : (0 < g')%Z) by (unfold page_size in Hlo; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hg'pos).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vm_gap_available_complete : forall h nZ g,
  (0 <= nZ)%Z ->
  (bv_unsigned g mod page_size = 0)%Z ->
  (0 < bv_unsigned g)%Z ->
  (bv_unsigned g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) g (Z_to_bv 64 nZ) = true ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ g Hn Hal Hpos Hhi Hfree.
  destruct (vm_find_base_complete h nZ g Hn Hal Hpos Hhi Hfree) as [a Ha].
  exact (vm_find_base_gap_available _ _ _ Ha).
Qed.
