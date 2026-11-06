(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MState.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import MmapComplete.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Gap () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1N02C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizec59OSSVerify5KrLib4Spec3Gap4CEILC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib4Spec3Gap6sum_szC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib4Spec3Gap3gszC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib4Spec3Gap:gsz_nonnegC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List6filterC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib4Spec3Gap5aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap9in_band_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap3ghiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphc59OSSVerify5KrLib4Spec3Gap=above_mono_ptC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib5Lists4List2InC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib4Spec3GapAfilter_above_monoC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC47Corelib4Init9Datatypes3fstI47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib4Spec3Gap>page_size_4096C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multc59OSSVerify5KrLib4Spec3Gap5FLOORC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap9FLOOR_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List9find_noneC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib4Spec3Gap3potC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap=sum_sz_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib9Placement<vm_find_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap3gloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib<MmapCompleteEvm_find_base_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3GapEregion_free_false_invC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03c59OSSVerify5KrLib4Spec3Gap8CEIL_valC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00c59OSSVerify5KrLib4Spec3Gap9walk_stepC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9filter_Inc59OSSVerify5KrLib4Spec3GapFpage_round_up_Z_boundsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3GapAfilter_above_dropC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3GapHpage_round_up_Z_aligned'C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsc59OSSVerify5KrLib4Spec3GapAsum_sz_live_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap@sum_sz_filter_leC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib4Init5Peano2le01C56Stdlib6ZArith6BinInt1Z7le_reflc59OSSVerify5KrLib4Spec3Gap4walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec3Gap=FLOOR_alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lc59OSSVerify5KrLib4Spec3GapFvm_gap_available_introC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Definition FLOOR : Z := 0x2aaaaaaab000.
Definition CEIL : Z := 0x7fff7f800000.

Lemma FLOOR_val : FLOOR = 0x2aaaaaaab000.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p;1p;2g0000j13Tg000Uj14Tg0013j25Tg001Mj12Tf0R0#2#3#2#3p=0%20#2p=1g0022g002P#0#0#0#0#0#0#0#0#3#1#1#1#1#1#1#4'5o"). Qed.
Lemma CEIL_val : CEIL = 0x7fff7f800000.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p;1p;2g001Mj10Tg000Uj16Tg0013j25Tg0000j11Tf0R0#1#1p=7%10#1#1#1p=2%00#0p=4%00#0#0#0p=3g0022g002P#7#2#2#2#0#2#2#0#4#3#3#3#3#3#6'5o"). Qed.

(* [comment removed for export] *)
Lemma CEIL_le_alloc_top : forall h,
  sp_window_lo <= bv_unsigned (vm_init_sp h) -> CEIL <= alloc_top h.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h04__x1h12Hsh27__arithh34__ffh48__varmaph55__with61hp;1p;2p;4p;3p;8p;7g001Mj10Tg0035j1NTg003Sj18Tg004Lj2:Tg0056j24Tg005Rj1QTg0062j1MTg006Rj2DTg0070j1CTg007Nj1BTg0000j11Tg000Uj15Tg0089j26Tg008\j2RTg009?j4?Tg009jj1PTg00:Lj3=Tg00:oj3LTg00;Rj8KTg00<6j2ETg0013j2FTg00<Xj2GTg00=Dj3HTg00=^j3ITg00>=j4JTg00>oj2;Tg00?Lj2<Tg00?ij1ATg00@aj7OTf0R0#0#0p=7%10#1p=@%10#1#1#1p=3%00#0#0#0p=9%00#0#0#0#0#0#0#0p=2f1R1g00AER2g00AdR3P3g00BDR4P0g00BdFOp=>g00CDg00D;g002PR5#0#7R6#0#7R7#NR8%80':'4g0022R9g00E6R:#Q%M:1D91%C9%B9R:P2P3P3P4P9%@5#3#3#3R2#1#0#7#9#2#2#2#5R;,69g00EbR<1R95R5C?,>:%P3P9%02#3#3#0#7#9#2#2#5R2,69P<%56R6,69%97#5R7,69R<5=9==9<9L95C?,>:GK1E:4P0f2R:g00FIR4g00FiR5'F1G0:=H45dg00GI=I91CJb3b4b5W014;01;67/;7,<1,42[^09P0%8:,:8P1O2b2%81,:8g00Gg'<,42eg00Hd%A1'4eW1W6o"). Qed.

Lemma page_size_4096 : page_size = 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p;1p;2g000Uj13Tg0013j22Tg001Mj11Tf0#1#1p=0g0022g002P#0#0#0#0#0#0#3'2o"). Qed.

Definition glo (e : word * word) : Z := bv_unsigned (fst e).
Definition gsz (e : word * word) : Z := bv_unsigned (snd e).
Definition ghi (e : word * word) : Z := glo e + gsz e.

(* [comment removed for export] *)
Definition in_band_b (e : word * word) : bool := (glo e <? CEIL) && (FLOOR <? ghi e).

Fixpoint sum_sz (l : list (word * word)) : Z :=
  match l with [] => 0 | e :: r => gsz e + sum_sz r end.

Lemma sum_sz_live_bytes : forall l, sum_sz l = live_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h01lh12IHh21ah32a0h41nh51zi001bi011pp;1p;2p;3p;6p;4p;5g001Mj12Tg0035j1BTg00IVj1:Tg00J9R0j28Tg0062j1ATg00JYj14Tg00KMj11Tg0013j27Tg005Rj19Tg00LFj36Tg004Lj25Tg00Lfj23Tg00MCj6@Tg00Maj4?Tg00NAj3<Tg00N^j1;Tg00OOj5=Tg00=Dj3>Tg0022R1f1R2f0R33>p=0g002P#2#2#2#2#2#2#BR4#:R5/85R6#AR7P6%43%13'0R8X07g00GI,71%96R9#4%19'0eP0P5P5f2R0=662R9#4%19'0\8^07P3P1%12R9f3R:,54R;/33%10,3;'0X511540/39R9,71%42R1P3E@P5P5P:P0C?R09<55,54/31/09e%;0/31/09eA6602R0#4%10'0eX18X07X45X25P2P3O2n2001101000121100100X36P3D=W0o"). Qed.

Lemma sum_sz_app : forall l1 l2, sum_sz (l1 ++ l2) = sum_sz l1 + sum_sz l2.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h02l1h12l2h24__x1h34__x2h44__x3h52IHh67__arithh74__ffh88__varmaph95__with:1eh;1zp;1p;2p;3p;4p;7p;6p;5g001Mj12Tg0035j1KTg00IVj1?Tg00J9j2<Tg0062j1:Tg00P1j35Tg00JYj11Tg00Lfj20Tg00=Dj33Tg0013j29Tg005Rj17Tg00N^j1;Tg006Rj28Tg00PNj4JTg0070j1ITg007Nj1HTg008\j26Tg0000j1CTg00Plj34Tg009?j4@Tg00@aj7ATg00<6j2BTg00<Xj2>Tg00=^j3DTg00>=j4ETg00MCj6=Tg00LFj3FTg00OOj5GTg002PR0#2R1#2#2#2#2#2#K#?R2/<2R2#:R3P2g0022R4f1R5f0R6552#1%15R7%16R8'033^13R9X03g00GIR:/08,94%72R;=526#1%1;/08534eX13P4f2R;#1/08f4#;R</06f3R=#1R>,0</07534X;4g00E6R?#7%:?P4184;P5184=CJ%I4%H4R?g00AEg00AdR@P@g00BDR@P41640RA1641R1%C0,64R0544544g00QOA44A1=440C@g00BdFA1B?@P6P;g00FIR@g00FiR?'91>6;=3@?dAD4:5CEb7b8b9X24X34X44105;,061065/0;534^24^34^44P6P7P>P<O3b6A52;6#1P5P6O1E=AF2=;R==526#1%1=/08534eX13X59X03X:2P6DGW0o"). Qed.

Lemma gsz_nonneg : forall e, 0 <= gsz e.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h01bh11nh21Hh31ep;1p;2p;3g001Mj10Tg0035j1:Tg00IVj12Tg00J9j24Tg004Lj23Tg0056j21Tg00R6j19Tg00R_j25Tg00S;j26Tg00NAj37Tg00N^j18Tg002P#0#0#0#0#0#0#:R0#2R1/41g00SnR2f0R3#2R4g00TLg00GIR5f1R6/33R7'1R8%96,57f2/36,151663P6n2001000000120000000W0W1P8^04^12P3P0A7116O2b2%83,15eW3o"). Qed.

Lemma sum_sz_nonneg : forall l, 0 <= sum_sz l.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h01lh17__arithh24__ffh38__varmaph45__with54__x1h64__x2h71Hh82IHh91ep;1p;2p;3p;4p;5p;7p;8g001Mj11Tg0035j1VTg00IVj1ETg00J9j2BTg0062j1>Tg00JYj13Tg005Rj19Tg00Tgj1DTg0070j1CTg007Nj1ATg0089j2@Tg00<6j2UTg0013j2TTg00<Xj2RTg00=Dj3QTg00=^j3MTg00>=j4HTg0056j2;Tg00UEj1GTg00N^j18Tg00V=j1=Tg00V\j25Tg00WEj37Tg00Wnj2FTg00LFj3:Tg006Rj2ITg00PNj4JTg008\j26Tg009jj1KTg00Plj3LTg00Lfj2NTg00OOj5OTg009?j4PTg00@aj7?Tg00;Rj8STg00GIR0f0R1';p=0g0022R2f1R3g00EbP1CPp=2P3g00AER4g00AdR5P5g00BDR6P1g00BdF?p=4f3R7P4P5P5P6f2R4P3P1GSp=<g002PR8#1R9#1#1#1#1#1#V#ER:/B:R:#>R;P:%31#0R<X0;g00E6R=#9R>%>=R?%D2R@%C2RA%A2RB1@20RC/2C'41UB6R6P1P4g00FIRDg00FiRE'T1R14=QDEdAM203CHREb2b3b41;00P1b1%9:#3#0e%G4%84#0g00XZR0#=RD#=,52152D1520572572g00Y9'F=:=>P?P21I24P3P@CJPAPB1628R8,2C,4B%K5R5PB1629R9,2C,4BP5AL289,2C,4BC<C<P6PEb2b3b4X52X62%01%041N47#0[[^52^62P1%37f4#8P3P4O4b1b7A::43#3#0eX8<X0;X9:P1DOW0o"). Qed.

Lemma sum_sz_filter_le : forall f l, sum_sz (List.filter f l) <= sum_sz l.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with71lh81Hh92IHh:1bi001bh;1eh<1fp;1p;2p;3p;4p;5p;7p;8g001Mj13Tg0035j1WTg00IVj1HTg00J9j2ETg0062j1ATg00Yej34Tg00JYj11Tg0056j20Tg005Rj1@Tg00Tgj1FTg0070j1DTg007Nj1CTg0089j2BTg00<6j2VTg0013j2UTg00<Xj2TTg00=Dj3NTg00=^j3MTg00>=j4LTg00UEj1KTg00N^j19Tg00LFj37Tg00Lfj26Tg006Rj2=Tg00PNj4GTg008\j2:Tg0000j1ITg009jj1JTg00Plj38Tg00V=j1>Tg00V\j2<Tg00WEj3?Tg00Wnj2OTg00OOj5PTg009?j4QTg00@aj7RTg00;Rj8STg0022R0f1R1g00Ebf0R2CQp=5P1g00AER3g00AdR4P4g00BDR5P2g00BdFRp=2f3R6P3P4P4P5f2R3P1P2GSp=;g002PR7#3R8#3#3#3#3#3#W#HR9/E9R9g00FIR:[%A9R;P9A4932#1%12R<'0X7;g00E6R=#@R>%A=R?%F0%D0R@%C0RAg00GIRB,B0RC/5C'21VA5R5P2P3g00FiRD,U:1T23=N:DdAM0B1CLRDb4b5b610BBP2b3%@9RE9491#1%1E'0eA4962#1/0<%K3%93,0Bf5R<P6O1P:P:P:P;P2f7f4R:549RE979<PEn0100000020000#1%9<R<%1:RF'6'0P2P>P?P01=03P11=06CGRGP@PA1:08R8%I7,:0RH'5,2A%J4R41:07R7=808A807H'5,2AC;P5PDb4b5b6X00X10X20101316131616'0[^00^10^20P2PF%1EREP<P6O4b3f6=496RI979:#1%9:%16'6RJ'0eg00XZRK#>RL#>,<01<0L1<0K5?05?0g00Y9'O=7=>P?PGP@PA15C8,2AP4PA157H,2AP4A808H,57,2AC;C;P5PDb4b5b6X00X10X2010B11016166:,03[[^00^10^20P2PFP<PEP3P6O5b3%1I/0Jen0110000020101b:b8A7931R3949:#1%13'0eW9X7;X;9P2DPW7W<o"). Qed.

Lemma length_filter_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61lh71Ah83IH0h94cstrh:5cstr0h;1xh<2IHh=1bi001bh>1fp;1p;3p;2p;4p;5p;<p;7p;8p200R0g00OOR1p4p710p8P0g00Z@R2p4p710p8P0g00YeR3p4p710p8g0062j16TP3j33TP2j20Tg00Z`R2j21Tg0056R3j22Tg0013j27Tg005Rj1ATg00Tgj1OTg0070j1LTg007Nj1ITg0089j2DTg00<6j2WTg00<Xj2VTg00=Dj3UTg00=^j3TTg00>=j4RTg00[:j4;Tg00LFj3<Tg00V=R4j1=Tg00[eR5j14Tg000Uj1PTg00Lfj25Tg00\Ej4NTg00\lj1?Tg006Rj2KTg00PNj4JTg008\j2>Tg001Mj1HTg009jj1MTg00Plj3CTP1j5GTg00]Ql<ETg009?j4FTg00@aj7STg00^6l<YTg00;Rj8XTg00^[R1g0022R6P2P5P3g00_:R7g00XZR8g00GIR9f1R:P8P9f0R;M<Ep=QP6P:g00EbP;CFp=8P:g00AER<g00AdR=P=g00BDR>P;g00BdFSp=9P1P1P6P6P4P5P5f3R4g00_\f2R?P:P;M<Yp=@P1P6P2P5P3P7f5R7f4R3P4P?P:P;M<Ep=:P4P<P=P=P>P?P:P;GXp=Bg00FIR<\;%6:P?%6?A34?;,04104;'1W611881299R81769R5/Q5g00E6R5#AR2%65R5%O6R1%L6R@%I6RA1D69RB/8B'91WA>R>P;P?g00FiRB,7<1V;?=U<BdAT69:CRRBb3b4b5P8P;b2C;%A?R893?:,0?10?8'1e%64A334;,03103;'1P3P?O1P<P<f7R8P<f8R<#6P;f6RC=384RD9<83PDn0100000020000'01084#='1P;A3C7?RE,0CRF#=RG10C?RH#=RI'1%4FRJg002PRK#PRL'5RM%4HRN/5LRO'2PGPM15;LX;6RMPFPJ176JRGC@PIPOPMPHPN176NRMC@RPE:11FH12JNRQPFPJPGPHPNPME:P:CNRMPQ108DRD#?R8%4D,29RD10<3R<#?RN%4<,29R9P2P5P61K6?P:P1CJR1P@PA1>6KR<%HK,>6RK'8,9ARH%M=R=1D6LRR9C6<AC6KRRR'8,9ACBP>PBb3b4b5X06X1612;:RK15:L15?LRL'2[^06^16P;f:RS/0C#4f9=3SC,0S#4P4O3RSb2b:b9b8C;A<C4E,0C/1Ie11FIRC12JOPFPJPGPIPOPPE:PMPQP8PDPNP9P2P5P1P@PAPHP=18<R,9ACBP>PBb3b4b5X06X1612:L\K^06^16PSb2b:b9b8C;PCen0110000020101b=A<7?:R:9373,07107:'1eW<W6X;?P;DGW6W>X70P;O1X70o"). Qed.

(* [comment removed for export] *)
Definition above (c : Z) (e : word * word) : bool := in_band_b e && (c <? ghi e).
Definition pot (nZ c : Z) (maps : list (word * word)) : Z :=
  Z.of_nat (length (List.filter (above c) maps)) * (nZ + 4095) + sum_sz (List.filter (above c) maps).

Lemma above_mono_pt : forall c c' e, c <= c' -> above c' e = true -> above c e = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h01Hh11mh21nh32H2h44__x1h54__x2h64__x3h72H1h82Hch97__arithh:4__ffh;8__varmaph<5__with=1bh>1ch?2c'h@1ep;1p;2p;3p;4p;6p;7p;8g001Mj13Tg0035j1XTg00IVj1JTg00J9j2DTg0056j2@Tg00`@j2;Tg00a3j14Tg00ajj12Tg00b[j21Tg00c8j3CTg00TLR0j2BTg00c[j28Tg00R_j25Tg00d9j2VTg00V=j1?Tg00V\j29Tg00WEj3>Tg00Wnj2UTg005Rj1RTg00LFj3QTg0062j1KTg006Rj2<Tg00PNj4ITg0070j1HTg007Nj1FTg0000j1GTg008\j27Tg009?j4:Tg009jj1ETg00<6j2LTg0013j2MTg00<Xj2NTg00=^j3OTg00>=j4PTg00MCj6ATg00=Dj3STg00@aj7TTg00;Rj8WTg00FIR1f0R2g00FiR33Sp=0f1R4g00AER5g00AdR6P6g00BDR7P2g00BdFTp=6f3R8P5P6P6P7f2R5P4P2GWp==g0022R9g002PR:#3R;#3#3#3#3#3#X#JR</D<1@541;54#0%45R<%25,18R=;C2%0<%0='BP0%48#0f4R=%28'1#0%4=f6R<%2='1'8#0P2f5#4#0f7R>%2<'1#0P1P3f:R<f8#2R?'1,82#0X=1P01142#01554R@[RA15421154#0RB[RC1585\B1V42RBP4n2001000000120000000X19X29PA^19^29P2f9RDP?P4O315D?P0PAPC1185#0\@PBP2n2001000000120000000X19X29PC^19^29P2f<RC%2<g00E6RBg00XZRA#?R0#?,991990199A5>95>9g00Y9'U%RB3Q%KBP91<95P41<98CI%H9%F9RBP9%G:,79RAg00dYR0179;R;C:,6B%E6R6PBP9179:R:g00EbPAC:,6BP6P9P:P0P;C:,6BC=C=1LB7P2P51M131N25#0dg00GI=O94CPb:b;b<X49X59X691@481558[\@^49^59^69P2PCf;#2f=P5P<O5b9O3b0b3b0%2>,1D,83#0e%4>P4EAW3W7P4P2O2n2001000000121000000b01;=5#0eW0W8W@X?9W>o"). Qed.

Lemma filter_above_mono : forall c c' maps, c <= c' ->
  (length (List.filter (above c') maps) <= length (List.filter (above c) maps))%nat
  /\ sum_sz (List.filter (above c') maps) <= sum_sz (List.filter (above c) maps).
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h02E2h14__x1h24__x2h34__x3h44__x4h52E1h67__arithh74__ffh88__varmaph95__with:4__x5h;1bi001bh<3IH0h=4cstrh>5cstr0h?1Hh@4mapshA2H0hB2HchC3IH1hD3IH2hE1chF2c'hG1ehH2e0hI1lhJ1xp%0p;1p;2p;3p;4p;6p;5p;<p;7p;8g001Mj1ATg0035j1uTg00IVj1eTg00J9j2^Tg0062j1\Tg0056R0j20Tg00`@j1:j2<Tg00Yej32Tg00Z@j21Tg00JYj13Tg00Z`R1j2@Tg0013j2ETg005Rj1XTg00Tgj1mTg0070j1lTg007Nj1iTg0089j2STg00<6j2dTg00<Xj2bTg00=^j3aTg00>=j4`Tg00[:j4HTg00e@j4_Tg00LFj38Tg00UEj1]Tg00N^j1FTg00=Dj3>Tg00V=R2j1BTg00Lfj25Tg00TLR3j29Tg00[eR4j1?Tg000Uj1tTg00e[j1OTg00f9j6NTg00\Ej4sTg00\lj1YTg006Rj2ITg00PNj4GTg008\j2CTg009jj1nTg0000j1WTg00Plj3DTg00fbj5kTg00g]j6TTg00h9j2hTg00V\j2JTg00WEj3ZTg00Wnj2gTg00OOj5jTg00]Ql<VTg009?j4fTg00@aj7oTg00^6l<cTg00hXj7pTg00;Rj8qTf2R5f1R6#:f0R732p=7%36/07p=;1@56/97p=4g00^[R8g0022R9P1P4P0g00_:R:g00XZR;g00GIR<P6P;P<P7M<Vp=rP5g00AER=g00AdR>P>g00BDR?P9P6g00EbP7Cfg00BdFop=6g00FIR@g00FiRA7>7p=K%37,06p=R1156/@7p=QP8P8P9P9P2P4P4f3R2g00_\P5P6P7M<cp=[P8P9P1P4P0P:f5R:f4R0P2P5P6P7M<Vp=PP5P=P>P>P?P6P7Fpp=LP2P=P>P>P?P5P6P7Gqp==1067,95p=Ug00i<R=9>@7p=Mg002PR4#AR1#AR8#A#A#A#A#u#eRB/^BRB#\RC1056PB%:2RD=2B7RE,1BA7B07RF,1BRG%3FRF,;E34X@C1@;;RE10<<RHPEPH1E9<RE/rEg00E6RE#XRI%\ERJ%m9RK%l9RL%i9RM1S9<RN;6N1dM?R?P7P51E@A1b75#KdAa9<6C`ROb7b8b9PHP7b6RHCHPHC_%XBRH97B5RP,1BA2BDHRH,1B%3H,;P34e%::RP=2B7RH,1B1RFH54GP3A2BP6RPf6R3#:RG=2B6RH,1B5QB%3H,;PA8B25RP92BGRG,1Bf7RH#:RF=2BPRP,1B%3P,;G34P7A2BF2f8RF#:RG=2B2,1B5QBA2BG0f9RG#:RP=2B0#3';%]3%F3,0<f:RD/<HP@1E@7RQf;RR/<F=>@7P@f=RS/<D=>@7P@PCP6f>RT=7BDRU98BRPUn0100000020000RU,1BP@PCf?RV/<RRWA7BVDRX98BRPXn0100000020000RX,1B%3X,;U34]5P6f<RU/<GRG#K1<TDS00P@PQA>@W7S01P@fARW/<SS02=>@7RX%:WRY=2BSRZ98BTR[,1BP@PCP6fB#:R\=2BSR]98BTP]n0100000020000R],1BR^%3]R],;[34]0P6f@R[/<UR_#KR`A7B[URa,1BRb#BRcA2BYURY,1BRU#BRd'@Re%FSRf%3aRg'5%3YRh,5fRf'0Ri'9%?bRj%t4Rk'5Rl%?URm/5kRn'0Ro/9iPePiPoPiPcPl157kXJ9RlPbPj1E9jRcC[PdPnPlPUPm1E9mRlC[S03EP%OiEN1@bURi10jmRoPbPjPcPUPmPlEPS04PFCsRFPo11BZRl#YRm%?l,0<RefC=7BTRp,1BRq#YRr%?q,0<RsPIPJP9P91I90P5PKCGS05P6P91I9:P2PKCGCGS06PLPM1C94RK1C91Rt56MRu%n>R>PM1C98R8%W1,C9R156MP>1S9kRv9D9KAD9tvRv56M%W4,C9R4=D98AD94156M5LMC=C=P?POb7b8b9X19X29X39X49X:91076Rt100:Rw155k152k'0150:15033U[[^19^29^39^49^:9P7fE=7B[Rx#3RyfD=7B[Rz#3R{%FWR|11Bx#?Rx11Bz#?RzP2PRO7b6b>b=b<CHA8BSaRa,1BR}A8BSYRY,1BR~%3aRa%3YRY'034eW0%M_R_P@Q02%M7X;@P7PAPWP[PSPTP2DkETA>@A=P@PAP@p-0P7g00i\g00j8RAn0110000020000XH@g00jUP=P7ETPAA2B\TR\,1B#B%FV%3\'5/Rp74q/h7bAb010ah94}UeW0n0110001020101P7O1b0b;W5%MGQ00P@PQQ01P@1;Z]94l^^0XP61@bdRX10gfRf'910jnRl/9fPXPfPlPfPbPjPcPdPnQ03EP%OfENPFPoPmPePrPs%B;Rf#B,J91J9f1J9;5Z95Z9g00Y9'g=8EIPJQ06PLPMPuP>PMA6MN8P>PMA6M41P>A6MKvAD98196M45LMC=C=C=P?POb7b8b9X19X29X39X49X:910<01003150k,02153H7U:[[\t^19^29^39^49^:9P7PyP|P{PxPzP2PDPRO8b6b>b=b<CH10gY94b~eX0`10ghRh,9iRg19ohPiPhPoPhQ04%OhENPFPoPmPePrPsPIPJP9Q05P61I92CGPLPMPuP>PMA6M48R4P>ALMu4C=C=P?POb7b8b9X19X29X39X4910201052/9w[\t^19^29^39^49P7PyP{PxPzP2PRO6b6b>b=b<CHPgeX0_n0110001020101P7O1b0b;W5n0110001020101P7O1b5b;b?A8B3:R392BPRP,1BA7BD3R3,1B%33,;P34eWDWCP6P7O2n2001000010121000000W?XICXGBP6DjWBW@XF9XE9o"). Qed.

(* [comment removed for export] *)
Lemma filter_above_drop : forall c c' maps e, c <= c' -> In e maps -> above c e = true -> ghi e <= c' ->
  (length (List.filter (above c') maps) + 1 <= length (List.filter (above c) maps))%nat
  /\ sum_sz (List.filter (above c') maps) + gsz e <= sum_sz (List.filter (above c) maps).
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h04__x1h14__x2h22E2h34__x3h44__x4h54__x5h61bi001bh73Hinh87__arithh94__ffh:8__varmaph;5__with<1xh=2E1h>1Hh?4__x6h@4cstrhA5cstr0hB3IH0hC2HahD2IHhE4mapshF1yhG2H0hH2HbhI2HchJ3HhihK2HxhL3IH1hM3IH2hN2M0hO2M1hP2M2hQ2_HhR1chS2c'hT1ehU2e0hV1lp%0p&0p;1p;2p;3p;4p;6p;5p;7p;8p;Bp;<g001Mj1GTg0035k10;Tg00IVj1zTg00J9j2nTg0062j1iTg0056R0j21Tg00k1j3FTg00`@j27j15Tg00ajj1ETg00Yej30Tg00V=R1j1HTg00Z@j24Tg00N^j18Tg00JYj13Tg005Rj1fTg00kHj2DTg00LFj36Tg00=Dj3ATg00a3j1NTg00b[j2@Tg00c8j3tTg00TLR2j29Tg00c[j2^Tg00k_j2oTg006Rj2QTg00Tgj1mTg0070j1lTg007Nj1kTg008\j2KTg009jj1jTg00<6k20:Tg0013j2ITg00<Xk209Tg00=^k308Tg00>=k407Tg00MCj6VTg00l?k403Tg00LfR3j22Tg00Z`R4j2:Tg00[eR5j1;Tg000Uj1~Tg00e[j1OTg00f9j6TTg00\Ej4cTg00\lj1PTg0000j1_Tg0089j2`Tg00[:j4RTg00UEj1xTg00fbj5wTg00g]j6aTg00h9j2uTg00V\j2\Tg00WEj3eTg00Wnj2|Tg00OOj6}Tg00PNj4sTg009?k401Tg00@ak702Tg00;Rj8rTg00m>lBqTg00^6m<04Tg00]Ql<pTg00Plk305Tg00hXk706Tg00FIR6f0R7g00FiR83Ap==f6R9f5R:'4f4R;'Df3R<':f2R=#3f1R>'2/17'9p=gf7R?/49/D:14;<':%3=/2>%37'1'9p=B12=>%37'1p={14=>,:</97p=bg00i<R@9A67p=>g0022RAP=P>P7Csp=JP=g00AERBg00AdRCPCg00BDRDPAP>g00EbP7H01g00BdK02p=<P<PBPCPCPDP=P>P7Grp=?1:=>/97p=U14>7,:=p=h%37,1>p=]14=>/D7p=W1:;<12=>/17'9p=[%3=/2>/17p>00g00^[REPEPEPAPAPAg00mdP5P5P5P3g00nDP:P;P<P=P>P7MBqp=dPEPEPAPAP1P5P5P<g00_\P=P>P7N<04p=ZPEPAP4P5P0g00_:P:P;P<P=P>P7M<pp=Mg00GIR0/17p=LB05A>7p=CP=PBPCPCPDP>P7K06p=S11>7,9=p=Y%3=/2>%37'1p=y12=>/17p=X%3>/27p=vg002PRB#GR5#GR4#G#G#G#G$0;#zRE/nERE#iR111<=AFE>=17:=#=%E</1:PEAFE:7PEf8R3#5RF=0E>RGg00XZS00#HRHf9RI#5RJ=0E>RK,4ERLPG%89RG%3KRKFg]7XE1%fERM9FE;g00j8S01PEA0EFMRFPHPEA0EJMRMPFPGPMGBP7n010000100W7AFE971DLHPEf:RL#5S02=0E>RM%8?={KMCb]7A6E=>9FE?g00ngAAE<3AFE3=PEP6P1f;RM/7;%5MS03=0E<RK96E;PKn0100000020000RKPHPEP6P1f<RG/7;%5GRF=0E<RJ96E;PJn0100000020000RJPK%8IPJGBP7AAE;IPEPLPEP6P1f=RJ/77%5JRK=0E:RN96E7PNn0100000020000ROPHPEP6P1f>RP/77%5PRQ=0E:RR96E7PRn0100000020000RSPO%8MROPSGBX<EP6P8PEP6P117JMRSA6EMNPNn0100000020000RTPHPEP6P1P7A6EMRRUPRn0100000020000RVPTPOPVGBX66%NLRV%EL,@JRT;t?%=V%=T'9P2%NM#=%EM,@P#=%NG%EG,@P'^#>P7%NJ#=fART%EP'@#=P6P8fBRVf@RW#ERX'@,^7#>X66P21@>7#>11>=RY[117>RZ1@=>#>[R[1@<=#>\Y1o>7P7n2001000000120000000XFAX<AP[^FA^<AP7PVPXg00E6RX#fR[%iXR\1QA=%mAR]7J>%lAR^%kAR_1KABR`1KA5Ra5<_Rb%jCRCPbC?20:_DRDP7P=1I682097=#=dB08A0>H07Rcb9b:b;X0AX1APY\Z^0A^1AP7fCRY%ETPJO3b8O3b>f?Rd#E,@T,^8#>e%NdP>EVWQWHP>P7O2n2001000000120000000bC17GL#>ReePeP6P@PEP6P1P7A0EQ9RQ96EGPQn0100000020000RePHPE%5dRf=0E9Rg96EGRhPe%8GRePhGBX66PPPJP:PLH0314ENRh14ERRi%3NRN%3RRR'13UP214EQ?hEg%3Q/]gA0Ef?Rf=WEHRj%5WRk=0E?Rl,4ERm#H%3f%8JRf%3l,2fD[P7A0Ek3Rk,4E%5TRf=0E3Rl7hEA0EfI#3%5VRf=0EI']A0EfLRf,4ERn/DHRo%5YRp=0ELRq,4ERr#HRs':Rt%8WRu%3q,2u600fRf'9%;nRu%~BRq'2Rv%;rRw/2qRx'1Ry/9fPtPfPyPfPoPvPnPu1IAuRvPHPq1IAqRoEdPsPx127qS04X<ARxPrPw1IAwRsCZEM%OfET1:nr11uwRfPnPuPvPrPwPsEMP>CcPfA0EpM,4ERp#P%;p#LfERp#5=0EG,4ERf#P%;f#LP[P\1QA;Rf?J=]1QA:?J<]R]7J>S05P^P_PbPCP_%_BRB,KARb%_5,KAR55<_PC1`AqRs,C`R`1CasRw5<_S061KA4R4,CbRr1C45R45<_5S_C?C?PDPcb9b:b;X0AX1AX3AX4AX5A11<:12=qRv12<qRu'112;:Rn12:9S073Y[\Z^0A^1A^3A^4A^5AP7fGRZ#5=0EPRy#3fDRt#8RzfFR{#5=0EPR|#314Ey#;14E|#;P<P;O7b8bAb@bNCRWPWOP>P7O2n2001000000121000000b>1DhHRhPEPU12NORN/]UCbePSP7EVbK17JLP?EVP:P7EVW>P7O1AFEI<P<P7O1PEA0EF;RFPHPEA0EK;RKPF%8LRFPKGBP21:hi11NRPEP6P117P?A6E?QPQn0100000020000RQPHPEP6P117d?A6E?gPgn0100000020000RgPQPePgGBP71:jm%8P=ykl%xL%LF17VMP61I67RF17YG=A67P617pP=A67PEP6P1P>A6Ed|P|n0100000020000R|PHPEP6P117ZdRGA6EdyPyn0100000020000RyP|PzPyGB]=P>17tJRJ#=17{PS08P6PFAA6G7S09P6fIRG/7TS0:=A67RPPE%5GRy=0ETRz96EVR|PHP6P1P>fJRd#5Rl=0ETRk96EVPkn0100000020000Rk,4ES0;P|%8ZS0<%3kS0=Fg]2P>fHRk/7WRZ#=R|%5k=0EWRm,4ERj/DHRg#HReA0EyWRy,4ERW#HRQ':RN%8TRR%3mRh'2%8{R{%3yRi,2RRR3XR2'9%;jRK/2qRI/2qRS%;WRU/2qRO'1R}/92PNP2P}P2PePSPxPgPIPjPK1IAKPHPqPoEdRoCZPQPOPxPWPU1IAURxCZS0>EM%O2ET1:gWR211IURKPgPIPoPWPUPxEMS0?P3CcRxPK14EzRU#PRj%;U#LRSfK#5=0EVRe,4ER}#PRN%;}#LR~P[P\1QA99Jf=?J>]S0@P^P_A<_`aRaPCP_%GB,KARB9<_4PC1C`s=<_w1Cr51CbB5<_5S_C?C?PDPcb9b:b;X0AX1AX3AX4AX5AX?AQ04/1>Rb11n9RwAXvqu12n912;?3Y[[^0A^1A^3A^4A^5A^?AP7fM#5=0EtR9#3R`%8dRdfL#5=0EtRt#3Rs%8pR414E9#;R914Et#;RtP<PMO8b8bAb@bBCRA6ETmRm=WEHR]A6ETyRy,4ERf1vm{Rm%3yRy'13UeW2%>ZRZP6Q0:%>7X66P7P8PGPkPTPpP<DwEaAA68@P6P8P6p-0P7g00i\Q01n0110000020000XU6g00jUP@P7EaQ01A0ElVRl=WEH#HP}%8Y%3l'2%8k%3eD[/u7bGb211mi9U]WeW2n0110001020101P7O1b2b6W=%>JQ08P6PFQ09P61DUHQ0;%3zQ0<Q0=D[^2PP>1:gQRP12h{R{/1RRR'911IORh/9RPPPRPhPRPgPIPoPQPOQ0>EM%ORETPxPKPjPSPNP~%HH,\A1\AHQ00,\A5eA5eAg00Y9'|=6X[P\Q0@P^P_PaPCP_1`A0=<_5PCP_A<_rBPCQ061C5B9<_r5S_C?C?C?PDPcb9b:b;X0AX1AX3AX4AX5AX?A%L:11n?12;q,1uQ0712?33Y[[\b^0A^1A^3A^4A^5A^?AP7P`P4PdPsP9PtP<PLPMO9b8bAb@bBCR11{y9UgfeX2|11{iR{,92Ri19K{P2P{PKP{Q0?%O{ETPxPKPjPSPNP~P[P\Q05P^P_PaPCP_A<_r5RrPCAS_arC?C?PDPcb9b:b;X0AX1AX3AX4AX5AAX<;:11v</9w[\b^0A^1A^3A^4A^5AP7P`PdPsP9PtP<PMO7b8bAb@bBCRPieX2Zn0110001020101P7O1b2b6W=n0110001020101P7O1b=b6b>WMWLP>P7O2n2001000010121000000bDW7P7O1n200100001021100011000PEQ02A6E<=R<50ER7PHPEQ03=0E<R<P7%83P<GBeW7WDXV1X<EP:P=E}WJWCW7WIXTEWEXSAXRAo"). Qed.

Lemma region_free_false_inv : forall maps lo n,
  region_free maps lo n = false -> exists e, In e maps /\ iv_overlap lo n (fst e) (snd e) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h01eh11Hh21Eh32loh41nh52H0h61lh74mapsh82Heh93Hinh:2IHh;1ah<2a0h=1bi001bh>2szi011pi021xp;1p;2p;3p;6p;4p;5g001Mj19Tg0035j1NTg00IVj1HTg00J9R0j2DTg0062j1MTg00oAj38Tg010;j3;Tg00NAj3:Tg010XR1j25Tg005Rj1CTg00g]j6LTg00h9j2KTg00LFj32Tg00Maj43Tg0112j4<Tg0013j2@Tg00=Dj36Tg011kj1>Tg00c[j2=Tg00k1j37Tg012Ij3FTg00e@j4ATg012cj4BTg013=j3ETg00OOj5ITg00TLR2j2JTg00FIR3f0R4g00i<R536p=4f3R6f2R7f1R8P4C<g00FiR9563p=0A7678/J4p=1A6349p=Gf4R:A2784776p=?g002P#9#9#9#9#9#9#N#HR;/D;R<#MR=P<A8784#4P<P4P:P6P7A;;;4R>A:;;4R?C0R@C1X0<,5<[^4;^3;RAX7=%C<RB?884#4P3P9P3p-0P4g00i\g00j8RCn0110000020000X03g00jUP5P4ELPCP<P4PBP:P6P>P?C0C1X0<,5</K4b5W1X4;X3;P0P;P;A2<:6?884#4P<P4f6R0f5RB52<P@C1X0<,5<[^4;^3;\A^6=P4P;P;PBP:C3=2<6?884#4P7P8P0PBC<P31@34P6P7f7R@P0C<=634P3PBP:f9RCf8RDC<=634%>8A8D0B'=#4P<P4P;P;f<R3f;REC3f:RF52<PDP@P>P?C0RGC1X0<,5<]1]2P8P:P6PDP@C<RH#G%>9A8@B:R9'=#4P<P<P4P;P;PEPFC3=2<CP@P0P>P?C0RIC1X0<P;P;PFPCC3RJP<PJP<PJPDD?P0PBA;;;JA:;;JC0A6<JJA7<JD1@<J3FP8CACBW1W2%4H%>5/=9#4P@P0PBP4O3P<P4PCPIC1X0<,5<P1P<P<P4PFPGC1X0<P<P4P;P;f=RGP3C3=2<EPCPDP>P?C0C1X0<,5<P4P<P4P3PFPCP>P?C0C1P2A7<8GPEPFA;;;8A:;;8C0P<P4P;P;fARFf@REC3f?R252<PGP3P>P?C0C1X0<,5<P4A7<62f>R6PGA;;;:A:;;:C0P<P<P4P;P;fDfCR:C3fBRG52<PEP2P>P?C0C1X0<PBP<PBP<P;P;P:PGC3RGPFD?P2P6A;;;BA:;;BC0A6<GBA7<BF;E8P4CACBW8W9P8P4O2n2001000000121000000W5X0<P8P4O2n2001000000121102000b0W1W2n0110001020101P4P7O2b2b=W1X4;X3;X:AX6=X>;X;;P8P4O2n2001101010121100100X<<P4DIW7o"). Qed.

Lemma page_round_up_Z_bounds : forall z, z <= page_round_up_Z z <= z + 4095.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71zh81Hh92H0p;1p;2p;4p;6p;3p;7p;8g001Mj1<Tg000Uj1BTg00Lfj20Tg00?Lj29Tg013Wj2ATg00>oj2;Tg0056j21Tg0000j1@Tg00TLj23Tg005Rj1OTg0062j1MTg00Tgj1dTg0070j1cTg007Nj1`Tg0089j28Tg009?j44Tg0144j6ZTg00<6j2YTg0013j2XTg00<Xj2WTg00=Dj3=Tg00=^j3VTg00>=j4UTg014Xj3TTg0159j2DTg00R_j2?Tg015Yj3RTg00V=j1>Tg00V\j2:Tg00WEj37Tg00Wnj2GTg016@j1NTg016^j2PTg017?j3QTg00LFj3HTg006Rj2ITg00PNj4STg008\j2FTg009jj1bTg00Plj3ETg00:oj3aTg00:Lj3KTg00MCj6_Tg017hj1]Tg00@aj7\Tg00hXj7^Tg00;Rj8[Tf0R0#<#<p=5%@0#@p=6f1R1g00AER2g00AdR3P3g00BDR4P0g00BdF\p=2g0022R5P1g00EbP0C4p=Cf2R6P2P3P3P4P1P0F^p=Lf3R7P2P3P3P4P6P1P0G[p=JP5g002PR8#<R9#<#5#5#5#5#5#BR:1010%B8R;'9/A0/;0R<,11%@8R=#6#6#6#6#6#BR>,01,1<'3X75100:/9;R<g00E6R?#OR@%M?RA%d5RB%c5RC%`5RDP2P3P3P4P5185:R2g00QOREg00GIRF,85RGC4,2DEZ1YD4R4P0P6g00FIRHg00FiRI'X1W06==HIdAV5F1CURIb1b2b3A=5:Fg00j8[P0b07T:1A<:,;:1D<:'09=5<101:/9;R<P@PAPBPCP5PGg00dYRBP2C4,2DP4PIb1b2b31?F:P0b07R:1D<:RH,1F1?H:'3g00XZRH#>RJ#>RK,:51:5JRJ1:5HRH575575g00Y9RL'G%>K,:5%N8,P5=Q5J=75H575/GL=H?@5H?PAP51I56P11I57CSPCPD1F5=R=,CG,2DP5P=PBP2C4,2D5LD%b3R3PDP51F58R8=E52185;5a5PE1F59R99K52=E5=C4,2DP3AK592R9,C8,2D185>9E58,C9,2D5LDCJCJP4PIb1b2b3X45X55X6511F61?6:'31;:6/079=5<1;7:R<,16106>,1<'3[[^45^55^65P0107:/9;R;/D:1A;:P7P1P6O5b0b9b8g018fg019^E_%]0R6,10100>,16'3eX75o"). Qed.

Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod 4096 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h01zp;1p;2p;3p;6g000Uj16Tg00Lfj25Tg00?Lj24Tg013Wj27Tg00>oj2;Tg0159j23Tg00=Dj32Tg01:Zj2:Tg00MCj69Tg017hj18Tg001Mj11Tf0R0#1#1p=0g0022R1P1g002PR2#0#0#0#0#0#0#6R3f1/50%62R2'4/70/;0/33g00GIR4521X011503/42/73/:3g018fg019^E9%80/33=214eW0o"). Qed.

Lemma FLOOR_aligned : FLOOR mod 4096 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "h01zp;1p;2p;3p;6g001Mj10Tg0000j12Tg000Uj14Tg0159j28Tg00=Dj37Tg0013j26Tg00MCj65Tf0R0#0#2p=9%00#2#0#2p=1%00#0#0#0p=3%00#0p=:g0022R1g002P#0R2#2#9#1#1#1#1#1#1#1#2#3#3#3#4%02#:#3#3#4,80g00GIR0571X011610g01;:g01;mE5o"). Qed.

Lemma find_some_of_In {A} : forall (f : A -> bool) l x, In x l -> f x = true -> exists y, List.find f l = Some y.
Proof.
ltac2:(KReplay.run1 (kr_t_Gap ()) [] "p'0h01Eh11yh21Ah31Hh42H0h53Heqh62Hfh73Hinh81eh91fh:1lh;1oi001oh<1xi011ai021bp;1p;3p;2p;4p;6p200R0g00k1R1p4p710p8P0g01<dR2p4p710p8g0062j1>TP1j3=Tg00=Dj30TP2j32Tg01==R2j11Tg0013j26Tg01=_j23Tg010Xj25Tg012cj4;Tg009jj14Tg01>Aj68Tg01>_j49Tg01?;j6:Tg00g]j6<Tg00h9j27Tf0R1g00FIR3[f1R4#>f2R5f3R6?=14P6P4O1g00FiR7503f5R8f4R9;26%18f6R6#1R:/61A2689=0:1P2f7R2f8R:#1A2:26;01f9R;f:R<#1R=13<1705X1;'5]0P4%1;R>A2;:213;1R?30P<f;R@#113@513@130X1<P413<4,6=C;W0X1:P1O1%12A2268%4230%4;=0>?X1:,5:P:P2P6P1P8P9E8P2P8O1g00i<R8503P3P8P:P6O1R6P7P3P6P8P1C9P9E:A0387P3P8P3p-0P1g00j8R8g00i\n0110200020000X83g00jUP7P1E<P81781b4b5b3'7W0n10110000021010100P1O1b0b;W6W7W<W:W9X20P1O1X20o"). Qed.

Section Walk.
Variable h : VmMaps.
Variable nZ : Z.
Let maps := vm_reserved h ++ vm_maps h.
Hypothesis HnZ : 0 < nZ.
Hypothesis Htop : CEIL <= alloc_top h.

(* [comment removed for export] *)
Lemma walk_step : forall c,
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  (exists a, vm_find_base h nZ = Some a)
  \/ (exists e, In e maps /\ above c e = true /\ glo e < c + nZ).
Proof.
  intros c Hal Hfl Hinv. pose proof FLOOR_val as FV. pose proof CEIL_val as CV.
  assert (Hpot : 0 <= pot nZ c maps) by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia).
  assert (Hc64 : 0 <= c < 2^64) by (unfold FLOOR, CEIL in *; lia).
  assert (HnZ64 : 0 <= nZ < 2^64) by (unfold FLOOR, CEIL in *; lia).
  destruct (region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
  - left. apply (MmapComplete.vm_find_base_complete h nZ (Z_to_bv 64 c)); rewrite ?unsigned_lit by exact Hc64.
    + lia.
    + rewrite page_size_4096. exact Hal.
    + lia.
    + unfold CEIL in *. lia.
    + exact Hfree.
  - right. destruct (region_free_false_inv _ _ _ Hfree) as (e & Hin & Hov). exists e.
    unfold iv_overlap in Hov. rewrite !unsigned_lit in Hov by assumption. apply andb_prop in Hov as [O1 O2].
    apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
    split; [exact Hin|]. split; [| unfold glo; lia].
    unfold above, in_band_b, ghi, glo, gsz. unfold CEIL, FLOOR in *.
    rewrite (proj2 (Z.ltb_lt (bv_unsigned (fst e)) _)) by lia.
    rewrite (proj2 (Z.ltb_lt 0x2aaaaaaab000 _)) by lia.
    rewrite (proj2 (Z.ltb_lt c _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma walk : forall k c,
  (length (List.filter (above c) maps) <= k)%nat ->
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  exists a, vm_find_base h nZ = Some a.
Proof.
  induction k as [|k IH]; intros c Hk Hal Hfl Hinv.
  - destruct (walk_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exact Hok|].
    exfalso. assert (HinF : In e (List.filter (above c) maps)) by (apply filter_In; auto).
    destruct (List.filter (above c) maps); [destruct HinF| cbn in Hk; lia].
  - destruct (walk_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exact Hok|].
    set (c' := page_round_up_Z (ghi e)).
    pose proof (page_round_up_Z_bounds (ghi e)) as [R1 R2]. fold c' in R1, R2.
    assert (Hhi : c < ghi e). { unfold above in Hab. apply andb_prop in Hab as [_ Hab]. apply Z.ltb_lt in Hab. exact Hab. }
    assert (Hcc : c <= c') by lia.
    destruct (filter_above_drop c c' maps e Hcc Hin Hab R1) as [D1 D2].
    apply (IH c').
    + lia.
    + apply page_round_up_Z_aligned'.
    + lia.
    + unfold pot in *. unfold ghi in *. pose proof (gsz_nonneg e).
      pose proof (sum_sz_nonneg (List.filter (above c') maps)). nia.
Qed.
End Walk.

(* [comment removed for export] *)
Theorem vm_gap_available_intro : forall h nZ,
  0 < nZ -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  (Z.of_nat (length (List.filter in_band_b maps)) + 1) * (nZ + 4095) + live_bytes maps <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ HnZ Htop maps Hb. unfold vm_gap_available.
  assert (Hinv : FLOOR + nZ + pot nZ FLOOR maps <= CEIL).
  { unfold pot. rewrite <- sum_sz_live_bytes in Hb.
    assert (L1 : (length (List.filter (above FLOOR) maps) <= length (List.filter in_band_b maps))%nat).
    { unfold above. clear. induction maps as [|e l IH]; cbn; [lia|]. destruct (in_band_b e); cbn; [destruct (_ <? _); cbn; lia| lia]. }
    pose proof (sum_sz_filter_le (above FLOOR) maps). pose proof (sum_sz_nonneg maps).
    assert (M : Z.of_nat (length (List.filter (above FLOOR) maps)) * (nZ + 4095)
                <= Z.of_nat (length (List.filter in_band_b maps)) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  destruct (walk h nZ HnZ Htop (length (List.filter (above FLOOR) maps)) FLOOR (le_n _) FLOOR_aligned (Z.le_refl _) Hinv) as [a ->].
  reflexivity.
Qed.

(* [comment removed for export] *)
Corollary vm_gap_available_intro_N : forall h nZ N R T,
  0 < nZ <= R -> CEIL <= alloc_top h ->
  let maps := vm_reserved h ++ vm_maps h in
  Z.of_nat (length (List.filter in_band_b maps)) <= N ->
  live_bytes maps <= T ->
  (N + 1) * (R + 4095) + T <= CEIL - FLOOR ->
  vm_gap_available h nZ = true.
Proof.
  intros h nZ N R T HnZ Htop maps HN HT HB. apply vm_gap_available_intro; [lia| exact Htop|]. fold maps.
  set (L := Z.of_nat (length (List.filter in_band_b maps))) in *.
  assert (M1 : (L + 1) * (nZ + 4095) <= (N + 1) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (M2 : (N + 1) * (nZ + 4095) <= (N + 1) * (R + 4095)) by (apply Z.mul_le_mono_nonneg_l; subst L; lia).
  lia.
Qed.
