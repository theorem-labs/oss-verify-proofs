(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Exec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ExecF () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1c59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses7rew_iffK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic8eq_ind_rC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Peano2le00I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4prod01c59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib4LibA5ExecF;rng_acc_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4LibA5ExecF;rng_acc_varC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalc59OSSVerify5KrLib4LibA5ExecF6mstepFC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF7mstepsF01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF7mstepsF02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00i59OSSVerify5KrLib4LibA5ExecF7mstepsF00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF;mstepsF_indC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I47Corelib4Init9Datatypes4prod00I47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib4LibA5ExecF9evtF_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessc59OSSVerify5KrLib4LibA5ExecF=mstepsF_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implc59OSSVerify5KrLib4LibA5ExecF=mstepF_weakenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF>mstepsF_weakenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_step_accessesC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib4LibA5ExecF;mstepF_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib3Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib4Exec6msteps01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF<mstepF_mstepC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib4Exec6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF>mstepsF_mstepsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib4LibA5ExecF5cstepC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF6csteps01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib4LibA5ExecF6csteps02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00i59OSSVerify5KrLib4LibA5ExecF6csteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF:csteps_indC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C4ELinuxProcessSemantics?LinuxProcessSem3RunHmi_account_step_projectsc59OSSVerify5KrLib4LibA5ExecF4evtCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF<csteps_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9evtC_doneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF8evtC_cutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF<footprint_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesC46Stdlib5Lists4List2InC59OSSVerify5KrLib4LibA8AcctCoreAaccesses_pages_inC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib4LibA8AcctCore7page_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC59OSSVerify5KrLib4LibA8AcctCore;accesses_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofI47Corelib4Init5Logic5False00I59OSSVerify5KrLib4LibA8AcctCore4ainv00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecFHaccesses_ok_of_footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreBmi_account_step_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCore<same_but_matC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreAsame_but_mat_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF;mstepF_liftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreCsame_but_mat_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreBsame_but_mat_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9evtF_liftC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesK47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib3Lib4Exec5mstepC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyC59OSSVerify5KrLib3Lib4Exec:msteps_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib4LibA5ExecF=lazy_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecFBpage_base_of_rangeC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4BoolBnot_true_iff_falseC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC46Stdlib5Lists4List>existsb_existsC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega5Tauto8GFormula06C47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc59OSSVerify5KrLib4LibA5ExecFPpage_in_ranges_false_of_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA5ExecF9rng_fp_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition footprint := Z -> nat -> Prop.   (* [comment removed for export] *)

Definition acc_in (RNG : footprint) (acc : word * nat) : Prop :=
  RNG (bv_unsigned (fst acc)) (snd acc).

(* [comment removed for export] *)
Definition rng (RNG : footprint) (lo : Z) (len : Z) : Prop :=
  0 <= lo /\ lo + len <= 2^64 /\
  forall b (j : nat), lo <= b -> b + Z.of_nat j <= lo + len -> RNG b j.

Lemma rng_sub : forall RNG lo len lo' len',
  rng RNG lo len -> lo <= lo' -> lo' + len' <= lo + len -> rng RNG lo' len'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h14__x2h24__x3h31bh41jh57__arithh64__ffh78__varmaph85__with94__x4h:2H0h;4__x5h<4__x6h=4cstrh>1Ah?1Bh@1HhA2HbhB3HhihC2HjhD3HlohE3RNGhF3lenhG4len'hH2lohI3lo'p;3p;2p;1p;4p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002Pj3<Tg003Cj20Tg003_j21Tg004<j15Tg004aj1BTg005?j2UTg005\j19Tg006<R0j28Tg006Wj1>Tg0076j2;Tg007_j3@Tg008Hj2DTg0094j1CTg009Tj3XTg00:4j1VTg00:Tj27Tg00;2j1TTg00;Pj1PTg00;nj1MTg00<Yj26Tg00=<j1JTg00=^j2?Tg00>Aj2ITg00>cj2HTg00?=j2GTg00?ij3FTg00@Cj3KTg00@bj4LTg00ATj3:Tg00B7j1=Tg00B\j1ETg00C:j3NTg00C]j1OTg00DBj4ATg00D]j4QTg00E;j4RTg00Efj7STg00FJj8WTg00FnR1f2R2f1R3f0R4CQp=4P2g00GLR5g00GkR6P6g00HKR7P1P3g00HkP4CRg00IRFSp=2f3R8P5P6P6P7P2P3P4GWp=3g00J2f4R5?<82P0g00JkR9/051158R:g00KIR;#5R<#BR=%5<R>#5#5#5#5R?#B'UR@'0g00KnRAf6RB/03%93,12RCf7RD/1BRE'0f9RFP8P2O2[[]4^31'8f5RG/0811BG,0:f8R:?<G5[[P4109B10E@10F3f:RE/1FRH,0Cf<RIP8P2O2[[^4A^31'8P011:DR0/0@10E3f;RJ/1ERK,0Cf=RLP8P2O2[[^4A^3110FD100HA<IF:[[P410H@10L3f>RH/1L,0Cf@P8P2O2[[^4A^3110IE11LI,0K109I11IJ/0@RJ10H3RKf?RE/1H,0CRCfCRFP8P2O2[[^4A^31R0'8g00LMRMg00M9RN#>RO#>,;11;1O1;1N5@15@1g00MX'D%CM3XRN%VMRM1712%T1RO743%P1RP%M1RQ161<RR161;RS52Q%J6R6PQ1?19RT=2QRP6A2QTSC3C31IQ7R7P4P2g00NDRTg00NdRU'H1G42=FTUdAK193CLRUb6b7b8X01X1110341092RTPT[[^01^11P4PEPLP2P:O4b5PJP0PNPM1715R0?42O1718RJ743PPPQA:1SRR:%=;R;,61161>R>5:1RT52QRVP6PQ1?1=%E?5N1R?92QTP6A2Q:?C3C3P7PUb6b7b8X01X11X21X911143R?1128R='01185RW/0@10=@[[^01^11^21^91P4PHPEPIPLP3P5O6b5PBP8P2%O2RL%92,09R9PNPMA4J2O?43OPPPQA2Q>RP6PQA2QS>P6A2QSRC3C3P7PUb6b7b8X01X11X21102310381028[[^01^11^21P4fBRSPGfDRRP8PDO5b5b=PLP9PNPM171B9402171G?48O743PPPQ%=<,61%5;,615:1R;92Q:P6PQA2Q;TP6PVC3C3P7PUb6b7b8X01X11X21X91X;1X<1115GRU,0?11GB/0W10=U[[^01^11^21^91^;1^<1P4fAPSPFPR%95PGP2PBO8b5b=O4XCCXAKX4AX31CACAWBWDW@W?P3P4O2n2001000000121000000W:W>P3P4O2n2001000000121000000W:XG1XI1XF1XH1WEo"). Qed.

(* [comment removed for export] *)
Lemma rng_sub' : forall RNG lo len lo' len',
  rng RNG lo len -> (lo <= lo' /\ lo' + len' <= lo + len) -> rng RNG lo' len'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h01Ah11Bh21Hh32H0h43RNGh53lenh64len'h72loh83lo'p;3p;2p;8g002Pj32Tg003Cj21Tg003_j20Tg006<R0j23Tg00ODj84Tg00J2g00FnR1f4R2f3R3f2R4321124f1R5,041023'1'3P0f5R0/1310341002'1f7R4?223f0R31140f6R2/00f8R6/04'1f:f9P6P4P2P0P5P3G4W1W0P5P3O2n2001000000120000000W3W2X61X81X51W7W4o"). Qed.

Lemma rng_bounds : forall RNG lo len, rng RNG lo len -> 0 <= lo /\ lo + len <= 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h01bh11jh21Hh34__x1h44__x2h51Ah61Bh73RNGh82_Hh97__arithh:4__ffh;8__varmaph<5__with=3lenh>2lop;3p;2p;1p;4p;7p;8g002Pj3PTg003Cj20Tg003_j21Tg004<j12Tg004aj19Tg005?j2LTg005\j1CTg006<R0j23Tg0094j1?Tg00:4j1>Tg00:Tj2=Tg00;2j1;Tg00D]j4:Tg00;Pj1OTg00;nj1NTg00<Yj28Tg00ATj3KTg00=^j24Tg00B\j1DTg00C:j3BTg00E;j45Tg00=<j1ATg00P;j7@Tg00>Aj2ETg00>cj2FTg00?=j2GTg00?ij3HTg00@Cj3ITg00@bj4JTg00Efj7<Tg00FJj8MTf1R1g00GLR2g00GkR3P3g00HKR4f0R5g00IRF<p=6f3R6P2P3P3P4f2R7P1P5GMp=7g00J2g00FnR8AP715P0g00JkR9/07R:1171g00KIR;#2R<#9R=%2<#2#2#2#2R>#9'LR?'0g00KnR@f4RA/01%C1,17RBf5RC/1ARD'0f7REP6P7O2[[]1^08'310961167/0?'3P5109A10D?10E1f8RD/1ERA,0Bf:RFP6P7O2[[^1@^08'3P0f6R0/1C/0?10D1f9/1D,0Bf;RDP6P7O2[[^1@^08109E11E0/0?'3P510A?10D1f</1D,0Bf>P6P7O2[[^1@^08g00LMR@#?%>@P81=87P1%;8C:%O8%N8R@P8188;R;188<5K8g00HkR<148=%D>5B8C5,6@R>%A3R=P@P81489P<P;C5,6@R;P=P@P2P3P3P4P;P>F@C7C71E@4P5P7g00NDR@g00NdR4'F1G57=H@4dAI891CJb:b;b<X38X481151/0?10911176/0?,3:[[^38^48P5PFPDP7P0O4b9W8W6P1P5O2n2001000000121000000W2W5P1P5O2n2001000000121000000W2X=8W>W7o"). Qed.

Lemma rng_nil : forall RNG lo, 0 <= lo <= 2^64 -> (forall j : nat, RNG lo 0%nat) -> rng RNG lo 0.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h12Hjh27__arithh34__ffh44__p1h58__varmaph65__with74__x2h84__x3h91jh:2Hbh;1bh<2H0h=4cstrh>1xh?1Hh@2H1hA2H2hB3RNGhC2lohD2x0hE1yp;1p;2p;6p;3p;4p;8p;7p;<g004<j19Tg004aj1GTg005?j2RTg003Cj20Tg006<j2<Tg005\R0j15Tg003_j22Tg0094j1UTg00:4j1QTg00:Tj2@Tg00;Pj1NTg00;nj1iTg00=^j2KTg00<Yj2CTg00P_j6[Tg00=<j1ZTg00>Aj2YTg00>cj2;Tg00?=j2XTg00?ij34j1ETg00@Cj3WTg00@bj4VTg00B\j1TTg00C:j3STg00ATj3?Tg00QCj2PTg00Qfj3OTg00C]j1FTg006Wj1ATg0076j2=Tg007_j3>Tg008Hj2MTg009Tj3LTg00D]j4hTg00B7j1gTg00RCj4fTg00Rnj4bTg00SUj1aTg00T3j2`Tg00TTj3^Tg00U=j8]j7_Tg00DBj4ITg00E;j4JTg00Efj7\Tg00P;j7cTg00FJj8dTg00U[l<eTg00JkR1f0R2'0p=81221p=7g00FnR3f1R4g00HkP2CJp=6P4g00GLR5g00GkR6P6g00HKR7P2g00IRF\p=1f2R8P5P6P6P7P4P2Fcp=Hf3R9P5P6P6P7P8P4P2Gdp=3A4321p=:g00KnR:P3f6R;P0f5R0f4R<P9P8P4g00M9R=P1P2M<ep=DP3P4g00V@P2CJp=Bp-0R>^D:^>3%82R?g00KIR@#9RA#GRB%9A#9#9#9#9RC#G'RRD,02RE'<P9P8P=O2^9:%88%78RF/0DRG10<4RH%54RI,28%70'0RJf7RKP9P8O2[[^9:^;3RL'<g00LMRM#URN%QMRO1@34RP%N3RQ%i3RR1K31RS1C3@RT'6,1RRUPRP5P6P6P7P9E[R55HR%Z6R6PUC31YR7R7P2P8g00NDRVg00NdRW';1X28=4VWdAW314CVRWb3b5b6X03X4>1<?4%84[^03^4>P2109DP9P8O3b2PGPLPNPOPPPQPR1K3B%TC5S3RC,6T,1R9HR5P6A?3TS/6C,1RC3P7PWb3b5b6X03X4>1<4E%74/0D[^03^4>P2%89P9P8O3b2A4:8=R>%58RD#:%E:RE%E3RC%52R5943IA4:421P423OXE:X>:RIP8PD1;3D1;31R1FD%F8%8D%A=RD#ARB,=3RP1=3D1=3=RD5>35>3g00MXRL'M=LMNPOP31@38P41@39ChRGPQPRPUP6PR%g@,C3RU=?3T1C3ARA=?3SRV'6,1RP6PR16AU,1RP61BTS,1RC3C3C3P7PWb3b5b6X03X73X831294/0F109<%:9[[\?^03^73^83P2P0f8R?%5<RXP4P8P9O6b2b=CfP>A4:9=%59R>#:RYPEPCPIP9P>1;3>P1FDP2CbPY%F<%8X%a@,`3%AB,=35^3A>3PD5>3/ML=LMNPOPGPQPR1BUS,1RP6PRA?3TU/6V,1RP6PR16AT,1RP61BTA,1RC3C3C3P7PWb3b5b6X03X73X83%:81249/0F1098A439<[[[^03^73^83P2%5;f:R9PKP8P<P0O6b2b=b<A43<KP:P=12;5f9R5#7'0f;RFPKP4O2]1X9:%5=RK,20%7?'0P3P51092124K%7F'0f=P8P=O2]1]:X;31055129K%79'0P5P=O1W1W:P;P4P<P2G]W1P<P4P8F_bAb@X1JX:HX9:X;3CICIW<W?XC3WBo"). Qed.

(* [comment removed for export] *)
Lemma rng_acc_lit : forall RNG lo len E (n : nat),
  rng RNG lo len -> (1 <= n)%nat -> (lo <= E /\ E + Z.of_nat n <= lo + len) ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h14__x2h24__x3h34__x4h41bh51jh62H0h73Hn0h87__arithh94__ffh:8__varmaph;5__with<4cstrh=1xh>1nh?1Ah@1BhA1EhB1HhC3HE1hD3HE2hE2HnhF3RNGhG3lenhH2lohI1mhJ1yhK1zp;3p;2p;1p;4p;<p;6p;7p;8p;Bg002Pj3uTg003CR0j20Tg004<j19Tg004aj1DTg005?R1j2HTg005\R2j14Tg003_j22Tg006<R3j23Tg006Wj1;Tg00VgR4j2BTg00B\j1WTg00WAj1QTg00Wdj2@Tg00XJj4ATg00Xjj2?Tg00Y`j2jTg00Rnj4cTg00C]j1aTg0094j1`Tg00:4j1_Tg00:Tj2FTg00;2j1\Tg00D]j4ETg00;Pj1[Tg00;nj1ZTg00<Yj2>Tg00=<j1YTg00>Aj2XTg00>cj2CTg00?=j2VTg00?ij3UTg00@Cj3TTg00@bj4RTg00ATj3=Tg00B7j1STg00ZFR5j1PTg00ZdR6j2<Tg00[@j3tTg00[fj1sTg00\Dj4rTg00U[l<NTg00\gj6nTg0076j28Tg007_j3:Tg008Hj2MTg009Tj3LTg00=^j2GTg00C:j3iTg00E;j4KTg00P;j7dTg00RCj4bTg00]Pj1gTg00^9j3hTg00U=j6OTg00^ej2ITg00_Oj2kTg00`>j3lTg00`[j3mTg00Efj7JTg00FJj8^Tg00a8l<]Tg00a]lBpTf2R7f1R8'2f0R9'0p=1g00FnR:/C9p=7g00KnR;P:P4P2P0g00bCf5R0f4R2f3R4P7P8P9M<Np=fP7g00GLR<g00GkR=P=g00HKR>P:P8g00HkP9CKg00IRR?FJp=5P4P<P=P=P>P7P8P9G^p=6g00beR@P:P:P:P5P5P0P2P4P7P8P9M<]p=qP:P:P:P:P:P:P1P9P8P7P1P4P2P0f6R1f7R5f8RAf9RBMBpp=oP8P<P=P=P>P9P?FJp=eg00J2Au247P3g00JkR?/02g00KIRC#9RD#DRE%9DRF#9#9#9#9RG#DRH'HRI91241018%48,27RJ1251RK'0PBP4P7O2[[^5;^4:'3g00M9RL#;RM/B71012%441210512'3%WGRG#QRNP;1@G0P2CA,?A[[P910?110KI10B8f:RK/2BRO,0Jf<RPP4P7O2[[^5;^4:'3P3A1A5I10K8f;RQ/2K,0Jf=RRP4P7O2[[^5;^4:1BM110KA%45=1AO'3PNP;1@GBPACA,?P[[P910OI10R8f>RO/2RRA,0Jf@RJP4P7O2[[^5;^4:1BMB10RQ%4K12RP51Q'3P310OP%4Q=1PAPNP;1@GRPPCA,?JP910JOf?RP%4OfA/2J31P:1jGJRRfDRAP9PJO2XK:RQP:PJPQP1PJPP1BMP%DCR1%4PRQ'0R3PMP1%71PPPQ%7QEfP0CcRQP3%aJRB%4J,0?R5g00LMRS#`RT%_SRUP:1F:7P8%\:RVCE%[:RW%Z:RX1>:CRY1>:DRD55XRZ%Y=R[PZC61XX>RZP9P7g00NDR\g00NdR]'C1V97=U\]dAT:?8CRR]b9b:b;X0:X1:10981087[^0:^1:P9fCR\fER^P2O3b8b<b7PQP3PBP5PTPUP:P:1F:2P7PVCEP81F:4CERVPWPXA=:YD%SC,>:RC1>:FRF5=:55XR_P[P_C6PZP]b9b:b;X0:X1:X2:X3:1274R_919812429187[^0:^1:^2:^3:P9PAP^fB#4R`P\P4O5b8b<b7O4PR10?JRR%PGRa,HERb,<JRc'31<JIRd,3RPRPcPRPdp-0/CR9tRRP:P:P6P9X=:RdP61<89#sXJ:X=:PJPJ%7JPbPIPdPdPdP:P:g00cC1H89Cr#7XI:X>:PEPE%7EPaPHPdPd%P9#7X=@PGPH%7HEqM:oM<NEnPQP3PBP5%;MR5#;RB#;R3#;,8:18:318:518:LRL5::5::5::g00MXR5'M18:B18:M=::L5::/M5=LST5LSPUPVPWPX1G:1=5XFP[PXA=:YFA=:DCRC55XP[PXA5XDYP[PX1G:E=i:GRE95XCP[PX1G:?RC=5XDP[PXP<P=P=P>A5XCYP:PYg00cgPECK,eXFdC6C6C6C6C6PZP]b9b:b;X0:X1:X2:X3:1014A182_1047A120I10?0R?1<0I,3?[[[[[^0:^1:^2:^3:P9P`PAP^P\P7P4P2PKPOO9b8b<b7Cb%gG,<J,3Re9hGJEO1@GJRR,IG1kGJEOP\PNP;PRPPCARP9lN;,IGAmN;PO2e1?\PeWDWCP8P9O2n2001000000121000000W6WEWBW@P8P9O2n2001000000121000000W6W?P8P9O2n2001000000121000000W6X>;XA:XG:XH:WFo"). Qed.

Lemma rng_acc_var : forall RNG lo len (x : word) (n : nat),
  rng RNG lo len -> (lo <= bv_unsigned x /\ bv_unsigned x + Z.of_nat n <= lo + len) ->
  acc_in RNG (x, n).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h14__x2h21bh31jh42H0h57__arithh64__ffh78__varmaph85__with94__x3h:4__x4h;4cstrh<1Ah=1Bh>1Hh?2H1h@2H2hA3RNGhB3lenhC2lohD1nhE1xp;1p;3p;2p;4p;7p;8g004<j15Tg00B\j1WTg00WAj1ITg002Pj3ETg003Cj20Tg004aj1?Tg005?j2PTg005\j14Tg003_j21Tg006<R0j26Tg00^ej22Tg00XJj48Tg00Xjj29Tg00C]j1VTg0094j1UTg00:4j1TTg00:Tj2;Tg00;2j1OTg00D]j4:Tg00;Pj1NTg00;nj1HTg00<Yj27Tg00E;j4=Tg00=<j1GTg00>Aj2FTg00>cj2JTg00?=j2KTg00?ij3DTg00@Cj3LTg00@bj4MTg00ATj3>Tg00B7j1CTg00`>j3QTg00`[j3BTg00Efj7RTg00FJj8STf2R1f1R2'1f0R3'0p=31123,01p=AP2g00GLR4g00GkR5P5g00HKR6P3g00IRFRp=<f3R7P4P5P5P6P1P2P3GSp=@g00J2g00FnR4g00KIR8#5R9#5R:#5#5#5#5R;#WR<#IR=g00KnR>f4R??E71P0g00JkR@/0?%?9%?;'PR;93?7f6RA/02%42,11RBf7RC/1ARD'0f9REP7P1O2[[^3>^24'6f5RF12<7RG'0%4111F?53G'6P=P>P?P7C8,9C[P310@A10D;10E2f:RD/1ERG,0Bf<RHP7P1O2[[^3>^24'6P0f8RI?3C;10D2f;RJ=ABDf=RKP7P1O2[[^3>^2412<CRL,0E%4A11EI53L'6P=P>PIPCC8,9J[P310G;10K2f>RG=ABKf@RBP7P1O2[[^3>^2412<DR;,0H%4E11HJ53;'6P012<JR0,0K%4D11KH530f?R0P=P>PHPJC8'9P312<K,0012<G%4K11B033PF12<0PG%VGRF%4G,0@RKg00LMRJ#URH%TJRJP41;41P2%O4RDC:%N4R;%H4REP41748RCg00HkRI1749R9C=,<ERL%G5R5PLC@1FE6R6P3P1g00NDRLg00NdRA'J1K31=DLAdAL4@2CMR@b6b7b8X04X1410321021[^04^14P3fA,2<RAfCRLP7O3b5b;PFPKPHPJP4P41;4?P1PDC:P21;47C:P;PEP4A>4C9PI%C8,74174:5>4C=,<EREP5PEC@P6P@b6b7b8X04X14X94X:411179332117?9321[^04^14^94^:4P3fBR?PL%4BPAP1O5b5b;O4P?P=P>P0PGC8RG9Q=>,2<AB=>GO2e19?GeW@W?P2P3O2n2001000000121000000W4W>W=P2P3O2n2001000000121000000W4W<P2P3O2n2001000000121000000W4WDWEXB4WCWAo"). Qed.

(* [comment removed for export] *)
Lemma rng_acc_litZ : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> 1 <= nz -> (lo <= E /\ E + nz <= lo + len) ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h12nzh21Eh31Hh42H0h52HEh62Hnh73RNGh87__arithh94__ffh:8__varmaph;5__with<4cstrh=3lenh>2loh?1np;3p;1p;2p;4p;7p;8p;6p;<g002Pj3TTg005\R0j12Tg00?ij36Tg004aj17Tg003CR1j20Tg003_j23Tg006<j25Tg004<j11Tg00B\j1<Tg00WAj1;Tg00Wdj28Tg00XJj49Tg00Xjj2:Tg006Wj1STg00VgR2j2RTg00>cj24Tg00C]j1CTg0094j1BTg00:4j1?Tg00:Tj2@Tg00;Pj1ATg00;nj1>Tg00=^j2=Tg00<Yj2ETg00E;j4FTg00Efj7GTg00=<j1HTg00FJj8ITg00>Aj2JTg00?=j2KTg00@Cj3LTg00@bj4MTg00RCj4NTg00dNj8OTg00eIj6PTg00U[l<QTg00KnR3g00FnR4P2P0P1g00bCf5R1f4R0f3R2f2R5f1R6f0R7M<Qp=Dg00J2AT102%25=646P4%22R8g00KIR9#7R:/07R;f8R<f6R='013=6f7R>,3<'0'5f:%19#1#1#1#1#1#<R?#;P318?>P=C9':[[X1410:810>1%20,3113>='0'5f9P<P>P=P1P2g00M9#SR=/R1%21R<,0:P=P:144:P1P<144<ED%C1g00JkR1/0<g00LMR<#B%?<1@46%A4%>4R<g00GLR=g00GkR0P0g00HKR8P<P=P0P0P8P41=4:g00Hk1E49CFg00IRFGR9%H0P9GI1J<8P7P5g00NDR8g00NdR<'41K75=68<dAL416CMb9b:b;X0410:6\;^04P7%2>P2O2b8b<CNP7GOW5W6P5P7EPW4W3X14X?3X24X=4X>4W7o"). Qed.

Lemma rng_acc_varZ : forall RNG lo len (x : word) (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (lo <= bv_unsigned x /\ bv_unsigned x + nz <= lo + len) ->
  acc_in RNG (x, n).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h02nzh11Hh22H0h32HEh43RNGh53lenh62loh71nh81xp;1p;3p;2p;4p;7p;6g004<j10Tg00B\j1=Tg00WAj17Tg002Pj36Tg005\j15Tg00?ij3;Tg00^ej23Tg003Cj22Tg003_j21Tg006<j24Tg00XJj48Tg00Xjj29Tg00eej7:Tg00eIj6<Tg00J2g00FnR0g00KI#0#0#0#0#0#0#=R1#7R2g00KnR3f5R4f4R5f3R636f2R7#5f15;0P0%56R6f7R81314R9'2f0R:,19f6R9,18'2'4f9P2P3P9P4C8'9[X001315R1,2911161194'2'4f8P8P9P4P5P7P:F:W3P7P:E<W2W1X00W7W8X50W6W4o"). Qed.

(* [comment removed for export] *)
Lemma rng_acc_wrapZ : forall RNG lo len E (n : nat) (nz : Z),
  rng RNG lo len -> Z.of_nat n = nz -> (lo <= E mod 2^64 /\ E mod 2^64 + nz <= lo + len) ->
  acc_in RNG (Z_to_bv 64 E, n).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h02H0h14__x1h24__x2h31bh41jh57__arithh64__ffh78__varmaph85__with94__x3h:4__x4h;4cstrh<2nzh=1Ah>1Bh?1Eh@1HhA2H1hB2H2hC3RNGhD3lenhE2lohF1nhG1zp;3p;2p;1p;4p;6p;7p;8g002Pj3\Tg003Cj20Tg004<j16Tg004aj1BTg005?j2[Tg005\j13Tg003_j21Tg006<R0j25Tg00?ij39Tg00f`j24Tg00B\j1ETg00WAj1DTg00Wdj2;Tg00XJj4:Tg00Xjj28Tg00Y`j2UTg00C]j1TTg0094j1QTg00:4j1MTg00:Tj2=Tg00;2j1LTg00D]j4<Tg00;Pj1JTg00;nj1ITg00<Yj27Tg00E;j4>Tg00=<j1HTg00>Aj2KTg00>cj2GTg00?=j2FTg00@Cj3NTg00@bj4OTg00ATj3ATg00B7j1PTg00^ej2CTg00_Oj2RTg00U=j6STg00`>j3ZTg00`[j3YTg00eIj6XTg00Efj7VTg00FJj8WTf2R1f1R2'1f0R3'0p=2P2g00GLR4g00GkR5P5g00HKR6P3g00IRFVp=?f3R7P4P5P5P6P1P2P3GWp=@g00J2g00FnR4g00KnR8f5R9f4R:;\7P0g00JkR;/09g00KIR<#6R=#B%6=R>#6#6#6#6R?#B'[R@929:f7RA/02%32,11RBf8RC/1ARD'0f:REP7P1O2[[^48^34'5%37=941149@RF,0Af6RG,1A92F7'5f9RF%E?R?#DRHP81;?GP9C:'8[[P310;A10D@10E2f;RD/1ER9,0Bf=RIP7P1O2[[^48^34'5P0A2FC@10D2f<RC/1D,0Bf>RJP7P1O2[[^48^34%3A=94G14F@RK,0DA2KA9'5PHP81;?EPFC:,8I[[P3109@10J2f?R9/1JRK,0BfARBP7P1O2[[^48^34%3E=94FP4%3DRD14I@RF,09RAA2F3K'5PHP81;?JPIC:,8BRL[X<414C@RM,0J11JI92MD'5P0PA%3C=2FKPLP3149@,0Bf@RL/4@%39fBR9/1B32P41U?BfERFP3PBO2XG4PG14B@PL%TLRG%3L,0;RKg00LMRC#QRA%MCRCP41=41P2%L4R0C<%J4RM%I4RDP4174<RJg00HkRI174=R=C>,?DRN%H5R5PNC@1KD6R6P3P1g00NDRNg00NdRO'G1F31=9NOdAN4;2COR;b6b7b8X14X2410321021[^14^24P3fC/4@R@PFP7O3b5b;PGPKPAPCP4P41=4:P1P0C<P21=47C<PMPDP4AA4J=PI%P<,74174>5A4C>,?DRDP5PDC@P6P;b6b7b8X14X24X94X:411179232117:9221[^14^24^94^:4P3fDR:PF%39P@P1O5b5b;O41;?BR1,C?1R?BESP:PHP8P1PLC:RL9ZH8,C?AYH8LO2e18:LeWBWAP2P3O2n2001000000121000000W0PEP3EXW0W@W>P2P3O2n2001000000121000000W0W=P2P3O2n2001000000121000000W0X<4WFX?4XD4WEWCo"). Qed.

(* [comment removed for export] *)
Definition fp_union (R1 R2 : footprint) : footprint := fun b j => R1 b j \/ R2 b j.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mstepF (RNG : footprint) (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\
  exists accs, RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' accs)
          /\ Forall (acc_in RNG) accs.

Inductive mstepsF (RNG : footprint) : machine_state -> machine_state -> Prop :=
| mstepsF_refl : forall ms, mstepsF RNG ms ms
| mstepsF_cons : forall ms ms1 ms2, mstepF RNG ms ms1 -> mstepsF RNG ms1 ms2 -> mstepsF RNG ms ms2.

Definition evtF (RNG : footprint) (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', mstepsF RNG ms ms' /\ Q ms'.

Lemma mstepsF_one : forall RNG ms ms', mstepF RNG ms ms' -> mstepsF RNG ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h03RNGh12msh23ms'p;3p;2p;6p100g@p4p7210R0p100?ip4p710p8P0p100eIp4p710p8P0p100glp4p710p8P0p100hJp4p7210p8P0p100U=p4p710p8P0p100`>p4p710p8g00hgj32Tg00i]j21Tg00jVj60Tg00J2g00kOR0f2R1f1R2f0R332f3R4P1P2P2P31142E0UX20W1W0o"). Qed.

Lemma mstepsF_trans : forall RNG a b c, mstepsF RNG a b -> mstepsF RNG b c -> mstepsF RNG a c.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh11ah21bh32msh42H0h59IHmstepsFh63RNGh71ch83ms1h93ms2p;3p;6p;7g00lVj30Tg00hgj33Tg00jVj62Tg00mOj71Tg00J2g00kOR0f3R1f2R2f1R330f4R4f6R5f0R6;01f7R7?024[X20X10f5R8?062P6UX30A3723f8R9?023f9?025f:R:?047[A0:17f;P5P8P9P1P3P6O1E2UW5W4W0X90X80X30P1P2P6F1W0X70X20W1W6o"). Qed.

Lemma evtF_done : forall RNG (Q : machine_state -> Prop) ms, Q ms -> evtF RNG Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh11Qh23RNGh32msh43ms'p;3p;2p;4g00lVj30Tg006<j24Tg00i]j22Tg00DBj41Tg00nJj43Tg00J2g00kOR0p-0[f1R1f0R2O1P0f4f2R3;02f3R4P2O1'4X40P1A0411P3P1O11241P2C1C3W0X30W1W2o"). Qed.

Lemma evtF_step : forall RNG Q ms ms1, mstepF RNG ms ms1 -> evtF RNG Q ms1 -> evtF RNG Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h03ms'h12H0h21Hh32HQh42Hsh51Qh63RNGh72msh83ms1i001xp;3p;2p;6p;4g00hgj36Tg00ndj32Tg00lVj30Tg006<R0j21Tg00jVj65Tg00DBj44Tg00nJj43Tg00J2g00kOR1p-0[f3R2f1R3f0R436f4R5?223g00oXP1f6R6?024f5R7P4O1'1X01A2675P4f8R8?074f7P4O1'1P0f9R0?063P8P3O1f:R6?208P4f;R9?082P9P5O1P1f>f<R5;04f=R8P4O1'1X01P7A0897P5P7O1P8P9P6P7P0P3E5P4C4C3W3W4P3P4O2n2001000000120000000W1X01P3P4O2n2001000000120100000W1W2X81X71W5W6o"). Qed.

(* [comment removed for export] *)
Lemma evtF_step_acc : forall RNG Q ms ms1 accs,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms1 accs) ->
  Forall (acc_in RNG) accs ->
  evtF RNG Q ms1 -> evtF RNG Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h04accsh11Eh21Fh32Hsh41Kh51Qh63RNGh72msh83ms1p;1p;3p;2p;4p;6g00:4j1ETg004<j10Tg00B\j1<Tg00WAj19Tg0102j1DTg010Tj17Tg00=<j1=Tg00?ij31Tg011Zj1;Tg012aj1:Tg013ij22Tg014nj35Tg0165j23Tg017=j2CTg00Xjj16Tg017]j34Tg00ndj3@Tg006<j2?Tg00oXj2>Tg00DBj48Tg00nJj4ATg018>j6BTg00J2g00kOR0p-0[g0197#ER1g00KI#0#0#0#0#0#0#<#9R2#DR3f2R4#7%=2R531%;0R6#:R7p,4segsR8f3R9'2f1R:9504,3631g00Kn,C2R2f6R;#6;44f7R<f4R=7@;f8R>P<P;f5R?%7;=135128<f0R<950;,36517f9#6=42<'?X01R5,>1P9P1P5P=128;A50?=,36517%6>=42=P4P:C8CAC8P<EBW4W2W1W3W0X80X70W5W6o"). Qed.

(* [comment removed for export] *)
Lemma evtF_cut : forall RNG (P Q : machine_state -> Prop) ms,
  evtF RNG P ms -> (forall ms', P ms' -> evtF RNG Q ms') -> evtF RNG Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h03ms'h11Hh22H1h32H2h42HPh52HQh61Kh71Ph81Qh93RNGh:1eh;2msh<3ms1h=3ms2i001xp;3p;2p;6p;4g00ndj31Tg00lVj30Tg006<R0j22Tg00oXR1j23Tg01:<j66Tg00DBj45Tg00nJj44Tg00J2g00kOR2p-0[R3f3R4f2R5f0R631P1P2f5R7?056f4R5P6O1'2X02P7P6O1f7R8f1R9717[^02f6R:?154[P6A0856P:P6O1'2P0f8R;?079P8P9O1f9R<P6O1f;R=?1<9[^02f:R<?1;8[P6A0<84P<P5O1f<R>P6O1R?f>R@?1>9[^02P6P:P9O2A0@86/2?X02,32P1P2f?R1?0;6f=R;P6O1'2X02A11;>P6fAR>?0<6P1P6O1'2P0fB?0=9f@R0P9O1fCR<?1>0P6fDR0?0;4P<P5O1P2fG?006fEP6O1'2X02P7fFR5?0<7P0P7O1P5P<P1P7P=P9E6P6C5C4W5W3P9P6O2n2001000000120000000W1X=2P9P6O2n2001000000120100000b:W6W4W2P9P6O2n2001000000120000000W1X<2P9P6O2n2001000000120100000W1X;2X83W7W9o"). Qed.

Lemma evtF_mono : forall RNG (P Q : machine_state -> Prop) ms,
  evtF RNG P ms -> (forall ms', P ms' -> Q ms') -> evtF RNG Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h03ms'h11Hh22HPh31Kh41Ph51Qh63RNGh72msp;3p;4p;6g00ndj32Tg01;9j41Tg01<2j60Tg00J2g00kOR0p-0[R1f3R2f2R3f0R432f4R5P4O1P5f1R6O1[^00f5R7P5P2P3P6P7P4O1f7P7P6P3P6P4O2C1W2X00E0W3W1X70X51W4W6o"). Qed.

(* [comment removed for export] *)
Lemma evtF_eq : forall RNG Q ms ms', ms = ms' -> evtF RNG Q ms' -> evtF RNG Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h02msh11Qh23RNGh33ms'p;3p;6g00?ij32Tg00ndj30Tg00U=j61Tg00J2g00kOR0p-0[f1R1f0R2520f4f3R3;01P0f2f6f5;02X00P2P3P1E1UUX30X00W1W2o"). Qed.

(* [comment removed for export] *)
Lemma mstepF_weaken : forall (R R' : footprint) ms ms',
  (forall b j, R b j -> R' b j) -> mstepF R ms ms' -> mstepF R' ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h04accsh11Hh21bi001bh31jh41Eh51Fh62Hsh71Rh82R'h91Wh:1ah;2msh<3ms'i011ni021pi031xp;3p;1p;2p;4p;6g00hgj36Tg004<j13Tg00B\j1ETg00WAj1ATg0102j1KTg010Tj1:Tg00=<j1JTg00?ij38Tg00:4j1CTg011Zj1BTg012aj1@Tg017=R0j2?Tg00Xjj12j27Tg017]j30Tg006<R1j24Tg00oXR2j29Tg00^ej25Tg00XJj4>Tg00`>j3=Tg00`[j3<Tg01<jj6DTg00DBj4;Tg00nJj4FTg013ij2GTg014nj3HTg0165j2ITf5R3f4R4f3R5'Gf2R6g00kOR7f1R8f0R93H'I38p=1g00J2R:g00Fng00KnR;P3P8P9O2P3P6P8O2[]3]2A6468P1g00KI#3#3#3#3#3#3#ER<#AR=#KR>%:5%J=R?38g0197#CR@%B7RA#@RBp,4segsRCP4PAP5P9E11?=;RDf6RE#2;09'4X0@'9A6345P9%:3=8>?PBPCf7RFPAPEP9E1f9RE#2=0D9'4X0@,9@P2P@PBPCf8R2PAPFP9E1f:RG#2=0D9'4X0@A6E2FP9PBPCPGPAPEP9E1f<R2#2=0D9'4P1PBPCf;R1PAPGP8E1f=RG#2=0D8A6G21P9PBPCPGPAP2P5E1f@R5#2R2=0D4f?R4#:=8>?PBPCP5PAP4P9E1fA#2R5=0D9'4X0@R?,9@PEP@P?P3PBPCP4PAf>P3E1A0D23P8PDP5P2P0P=P;fCR0/791708[P9fFR215<8P9O2P015<6P8P9O3W1P2P=P;P8P9C>R09==;,5<A<=;0O2P2P=P;P6P8C>R69==;,5<A<=;6O2[e17201726[eX3;X2=P8P9O2n2001102000121100101X:DP3P9EDC;CFC;W5W4P8P9O2n2001000000121000000W1X0@P8P9O2n2001000000121103000W1W6P8P9O2n2001000000121000000W1W9X<7X;7X8:W7o"). Qed.

Lemma mstepsF_weaken : forall (R R' : footprint) ms ms',
  (forall b j, R b j -> R' b j) -> mstepsF R ms ms' -> mstepsF R' ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h02msh12Hsh23ms'h31Hh44IHHsh51Rh62R'h71Wh81bh91jh:3ms1h;3ms2p;3p;2p;6p;7g00lVj30Tg00i]j25Tg00hgj32Tg01=Jj61Tg00jVj64Tg00mOj73Tg00J2R0g00kOR1g00Fng00Knf5R2f1R3f0R4O2P2f2R5P3O2[]9]8f4R6?053P2f6?034X21X011524X01f8?253f9R7?053f3R3=075f:R7P2P6P3f;P7P2P6f7P5E1P4E4W4W1W3X;1X:1X01P3P5P4F3W1W7X21W0X60W5o"). Qed.

Lemma evtF_weaken : forall (R R' : footprint) Q ms,
  (forall b j, R b j -> R' b j) -> evtF R Q ms -> evtF R' Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h03ms'h11Hh22HQh32Hsh41Qh51Rh62R'h71Wh81bh91jh:2msi001xp;3p;2p;6p;4g00ndj32Tg00lVj30Tg006<R0j21Tg01>Gj63Tg00DBj45Tg00nJj44Tg00J2R1g00kOR2p-0[g00Fng00Knf5R3f1R4f0R5O2P3f2R6P4O2[]9]8f4R7?264g00oXP2f6R6f3R8;05P7P5O1'1X02A2378P5f8R9?035P6P5O1'1P0f9R0?064f7R6P4O1A2096P5f;R6?098f:R9P7O1P2f=R7?065f<R8P5O1'1X02P3A0893P6P3O1P7P8P9P3P0P4E3P5C5C4W2W3P4P5O2n2001000000120000000W1X02P4P5O2n2001000000120100000W1W7X:2W4X61W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mstepF_step : forall RNG ms ms', mstepF RNG ms ms' -> RiscvSemantics.step segs ms = MachineOk ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h04accsh11Hh21mh31Eh43RNGh52_Hh63_H0h72msh83ms'i001xp;3p;1p;2p;6g00hgj3JTg004<j15Tg00B\j1BTg00WAj1>Tg0102j1ITg010Tj1=Tg00=<j1CTg00?ij36Tg00:4j1@Tg011Zj1?Tg012aj1:Tg013ij21Tg017=j2HTg00Xjj13Tg017]j34Tg006<R0j27Tg00oXR1j2<Tg01?Ej29Tg01@Aj2;Tg0165j28Tg00>cj2ATg00U=j6DTg01AKj2ETg00eIj6FTg014nj3GTg00kOR2f1R3f0R43Gp=2f3R5f2R6183436p=0g00J2AJ634P0g00KI#5#5#5#5#5#5#B#>R7#IR8%=6%C7R936g0197#@R:%?2R;#:R<p,4segsR=/15P;1264C0g00Kn,H7R7f4R>#3;44'7X0:'<%:2R?19=5P2P6C0P4%=>=689P<f6R9,1=P;f5R8/24C0f7R6#3=474'7X0:,<:P1P:P<11=6P;1294C0f8R1#3=474'7X0:P?19=6P2P9C0P4P<f9R9,1=P;1214C0f:R1#3=474'7P0P<11=1P;1293C0f;R9#3=473P?19=9P2P1C0P4P<f<,1=P;1295C0f>R9#3=47>P?11=9R>,;21829R796?4X2?P<f=R5/28,8;1;24=6?7X2<1825,A?P>P3ED19=91E=9EFW6W3P3P4O2n2001000000120000000W1X0:P3P4O2n2001000000120100000W1W5P3P4O2n2001000000121000000W1X82X72W4o"). Qed.

Lemma mstepF_mstep : forall RNG ms ms', mstepF RNG ms ms' -> mstep segs ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh13RNGh24accsh32msh43ms'p;3p;1p;2p;4g00hgj3FTg004<j10Tg00B\j16Tg00WAj14Tg0102j1ETg010Tj1;Tg00=<j1:Tg00?ij31Tg012aj12Tg01?Ej27Tg0165j23Tg00:4j18Tg011Zj19Tg013ij2DTg014nj3CTg017=j2BTg00Xjj1<Tg017]j3=Tg006<j2>Tg00oXj2?Tg01BUj3@Tg01C0j4ATg00DBj45Tg00J2g00kOR0f2R1f1R2f0R33Fg00KI#0#0#0#0#0#0#6#4R4#E%;1%:431R5%20p,4segsR6/71130231g0197#8R7%90R8#2f3R9,D6AC013,3831g00Kn,B4f4#<;=3'>X27'?=@53P9P1P2P3CAC5W0X40W3W1o"). Qed.

Lemma mstepsF_msteps : forall RNG ms ms', mstepsF RNG ms ms' -> msteps segs ms ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h02msh11Hh23ms'h32H0h49IHmstepsFh53RNGh63ms1h73ms2p;3p;2p;4p;6p;7p101Ckp4p70R0p100?ip4p710R1p8P0p100glp4p710R2p8P0p100hJp4p7210R3p8P0p100U=p4p710R4p8P0p100`>p4p7210R0p8p101D[p4p70R5P1p8P5P2p8P5P3p8P5P4p8P5P0p8p101EIp4p70R5P1p8P5P2p8P5P3p8P5P4p8P5P0p8g00lVj30Tg01F?j31Tg01G5j23Tg00hgj32Tg01Gkj46Tg01Hgj65Tg00mOj74Tg00J2g00kOR0f2R5f1R4f0R330f3R2p,4segsR1?143X20X001313X00f6?254f7?054A1125P1f5R1f4R6P2f9P1P6P5C6P3E5W4W3W1X70X60X00P5P4P3F4W1X20W0W5o"). Qed.

Lemma evtF_evt : forall RNG Q ms, evtF RNG Q ms -> evt segs Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h03ms'h12H0h21Hh32HQh41Qh53RNGh62msi001xp;3p;2p;4g00ndj37Tg00lVj30Tg006<R0j21Tg01I]j32Tg01F?j33Tg01JNj46Tg00DBj45Tg00nJj44Tg00J2g00kOR1p-0[f2R2f1R3f0R437g00oXP1f4R5?024f3R6P4O1'1X01p,4segsR7?262P4f6R2?054f5R8P4O1'1P0f7R0?083P2P3O1A2702P4f9R2?006P2P5O1P1f:R5=374f;R0P4O1'1X01P8A3728P5P8O1P0P2P8P3C6P4C5C4W3W2P3P4O2n2001000000120000000W1X01P3P4O2n2001000000120100000W1X61W4W5o"). Qed.

(* [comment removed for export] *)
Lemma mstepF_det : forall R R' ms a b, mstepF R ms a -> mstepF R' ms b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h02Hah12Hbh21Rh32R'h41ah51bh62msh71ti001mi016resultp;3p;4p;1p;2p;6g00hgj34Tg01C0j42Tg012aR0j17Tg01?Ej20Tg0165j21Tg00?ij33Tg01KLj48Tg00glj66Tg00hJj65Tg00J2R1g00kOR2f4R3f2f1R434f3R5=434f6R6P3P5P4C2%72R7p,4segsR8/031125R933P6f5R:P5P4C2108:=379P7P2P0P2P2f0R0P0P6P6n1011000003101010000X77112:R:1123R3P7P:1086R8P3P7P8P:P4C8P0E6E5b1b0W1W0X52X42W6X31W2o"). Qed.

Lemma mstepF_not_svc : forall R ms ms', mstepF R ms ms' -> ms_svc_pending ms = None.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h04accsh11Hh22H0h31Rh42_Hh52msh63ms'p;3p;1p;2g00hgj3BTg004<j10Tg00B\j1>Tg00WAj1;Tg0102j1ATg010Tj12Tg00=<j1?Tg00?ij31Tg00:4j1=Tg011Zj1<Tg012aj1:Tg013ij27Tg014nj33Tg0165j29Tg017=j2@Tg00Xjj14Tg017]j36Tg006<R0j25Tg00oXj28Tg00J2g00kOR1f2R2f1R3f0R43BP0g00KI#0#0#0#0#0#0#>#;R0#AR5%22%?0R631g0197#=R7%<1R8#:R9p,4segsR:f3R;'7A3124,9831g00Kn,@0R0f4R2#4;64'5X07'8%2;=156P4%22=156f6,7:f5=314,98519f7#4=604'5X07,87P3W4W1P3P4O2n2001000000120000000W2X61W5W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cstep (c c' : machine_state * Model) : Prop :=
  m_halted (snd c) = None /\ ms_svc_pending (fst c) = None /\
  mi_account_step segs (fst c) (snd c) = MachineOk c'.

Inductive csteps : machine_state * Model -> machine_state * Model -> Prop :=
| csteps_refl : forall c, csteps c c
| csteps_cons : forall c c1 c2, cstep c c1 -> csteps c1 c2 -> csteps c c2.

Lemma csteps_one : forall c c', cstep c c' -> csteps c c'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01ch12c'p;2p;1p;5g017=j23Tg01Khj22Tg01L]j10Tg01MUj51Tg00kOg01NM'3R0f1R1f0R2'2f2P1P1P2%01D1UX10W0o"). Qed.

Lemma csteps_trans : forall a b c, csteps a b -> csteps b c -> csteps a c.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh11ah21bh32c0h42H0h58IHcstepsh61ch72c1h82c2p;2p;5p;6g017=j24Tg01OCj20Tg01Khj22Tg01MUj51Tg01P;j63Tg00kOg01NM'4R0f2R1f1R2'0R3f0R4f3R5'0f4R6,01[X20X101041P4UX301212f6R7,01f7R8,06[1058P7f5f8P5P2P4O1D1UW5X43W0X80X70X30P5P1P4E3W0X60X20W1o"). Qed.

Lemma cstep_det : forall c a b, cstep c a -> cstep c b -> a = b.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h01Hh12Hah22Hbh32_Hh43_H0h53_H1h63_H2h71ah81bh91ch:1ti001mi016resultp;2p;1p;3p;4p;6g017=j2FTg01Khj26Tg004<j15Tg00B\j1<Tg00WAj1ETg0102j1DTg01Q5j18Tg00=<j1=Tg00?ij32Tg012aR0j1;Tg006<R1j27Tg0165j29Tg01Qlj3:Tg01KLj4CTg00glj6BTg00hJj6?Tg00`[j3@Tg00`>j3ATg010Tj1>Tg00kOR2g01NMR3f0R43@p=0AA234p=1f2R5f1R6#>;24p=3f5R7f4R8f3R9;:5196432p=41F23R31656P1g00KI#5#5#5#5#5#5#<#ER2#DR:%09R;#8%=2R232%19R<=3:2%;3R=p,4segsR>P<P;P3P5E4'71685A2389[P4%07#8=2:2f6R9#1R8=3:2P=P>P8%09P3P7E4'7P1f7R7#1R8=3:2P=P>P8%07P3P9E4f8R8/69A2387[P4f9R8#1=3:2P=P>f:R7#1%07P3P8E4f;R9/68P1f<R5#0R;#8=2:2%15R<=3:2P=P>P<P;P3P7E4'7A2359P4f>R5#0#8=2:2f?R9#1R7=3:2P=P>P7%09P3f=E4'7P1f@R1#1R7=3:2P=P>P7%01P3P5E4A2319P4fBR1#1=3:2P=P>fCR2#1%02P3fAE4P=P3P0P3P3P4P4fDR0P0n1011000003101010000X:=1932R21931R1P=P2%10%005:>R>P1P=P>P2P8CCP4EBE?W2W6P6P4O2n2001000000120000000W0W5P6P4O2n2001000000121000000W0W1W4P6P4O2n2001000000121000000W0W3P6P4O2n2001000000121000000W0X83X73W9o"). Qed.

Lemma cstep_sstep : forall ms mo ms' mo',
  cstep (ms, mo) (ms', mo') -> sstep segs (mkCfg ms mo) [] (SNext (mkCfg ms' mo')).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh12Hah22Hhh32Hsh42moh53mo'h62msh73ms'p;2p;1p;3p;4p;8g01Khj2HTg004<j13Tg00B\j1>Tg00WAj1GTg0102j1DTg01Q5j1;Tg00=<j1?Tg00?ij31Tg010Tj16Tg017=j2=Tg012aj1FTg01Qlj38Tg0165j27Tg006<R0j2<Tg01Rhj22Tg0094j1CTg01S]j1:Tg01TSj49Tg01UGj8BTg00XJj4ATg00`[j3@Tg00`>j3ETg00kOR1g01NMR2f1R3f0R4CAp=0A@124p=5AE124p=4f3R5f2R6'01034'HP0g00KI#3#3#3#3#3#3#>#GR7#DR8f4R9/05R:#5R;#;%?7R731%4:R:#6=1871=12R<#FR=p,4segsR>?8:;1063,7<31'<P>f5R:/29g01V;#CR;1256#:C9P4f6R6/0:R5#5#;=187f7R?/06R@#4RA#6=187%5@98>A10:9,7<51='<P0f8R0/0?R9#4RA#6=187%5998>A17<551=P>f9R5/20P;12?6#:C9P4f:R?/05#4#6=187f;R7/0?R8#4%5858>1050,7<51=P>f<R=P7P?P5P:P3P4GBP>12=7P;12?5#:C9eW1W3P3P4O2n2001000000120000000W0W2P3P4O2n2001000000121000000W0X52X71X42X61o"). Qed.

(* [comment removed for export] *)
Lemma cstep_step : forall ms mo ms' mo',
  cstep (ms, mo) (ms', mo') -> RiscvSemantics.step segs ms = MachineOk ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh12Hah22_Hh33_H0h42moh53mo'h62msh73ms'p;2p;1p;3p;6p;4g01Khj2ETg004<j13Tg00B\j1=Tg00WAj1DTg0102j1CTg01Q5j18Tg00=<j1>Tg00?ij30Tg010Tj16Tg017=j2<Tg012aj1;Tg01Qlj37Tg0165j22Tg006<R0j2:Tg01?Ej29Tg01W1j6BTg00XJj4?Tg00`[j3@Tg00`>j3ATg00kOR1g01NMR2f1R3f0R4C?p=1A@124p=4AA124p=5f3R5f2R6'11134'EP0g00KI#3#3#3#3#3#3#=#DR7#CR8f4R9/15R:#4R;#8%>7R730%5:R:#6=0871<12R<#;R=p,4segsR>?7:;1163,2<30':%;1R6f5R:,9>121530P4f6R5/1:R;#4#8=087f7R?/15R5#5R@#6=087%4597>@11:9,2<50=':P0f8R0/1?R:#5R9#6=087%4:97>912<;50=f9R;,9>121?506P4f:R6/1;#5#6=087f;R7/16R8#5%4857>11;0,2<50=P>f<P7P6P;P4EBW1W3P3P4O2n2001000000120000000W0W2P3P4O2n2001000000121000000W0X52X71X42X61o"). Qed.

(* [comment removed for export] *)
Definition evtC (Q : machine_state * Model -> Prop) (c : machine_state * Model) : Prop :=
  exists c', csteps c c' /\ Q c'.

Lemma evtC_done : forall (Q : _ -> Prop) c, Q c -> evtC Q c.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01Hh11Qh21ch32c'p;2p;1p;4g017=j25Tg01OCj20Tg006<j22Tg01L]j11Tg00DBj44Tg00nJj43Tg00kOg01NM'5R0p-0[f1R1f0R2O1P0f2R3/02f3P2O1'2X30P11011P3P1O1%11P2C4C3W0X20W1o"). Qed.

Lemma evtC_cut : forall (P Q : _ -> Prop) c,
  evtC P c -> (forall c', P c' -> evtC Q c') -> evtC Q c.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h02c'h11Hh22H1h32H2h42HPh52HQh61Kh71Ph81Qh91ch:2c1h;2c2h<1ei001xp;2p;5p;4g017=j27Tg01X6j21Tg01OCj20Tg006<R0j22Tg00oXR1j26Tg01Xjj55Tg00DBj44Tg00nJj43Tg00kOg01NM'7R2p-0[R3f2R4f0R5'1P1P21045f4R4P5O1'2X02f5R6P5O1f1R7,16[^02f3R8,14[P51045f6R9P5O1'2P01067f7R:P7O1f9R;P5O111;7[^02f8R;/1:[P510:8f:R<P4O1f<R=P5O1R>11=7[^02P5P9P7O210:5/2>X02,62P1P210;5f=R;P5O1'2X0211;=P510<5f?R<P5O1'2P0f;R0/07f@R=P7O1fA/1=P510;8fCR;P4O1P2fDR4/05fEP5O1'2X02P610;6P4P6O1P;P<P6P0P7D5P5C4C3W5W3P7P5O2n2001000000120000000W1X;2P7P5O2n2001000000120100000b<W6W4W2P7P5O2n2001000000120000000W1X:2P7P5O2n2001000000120100000W1X92X83W7o"). Qed.

Lemma evtC_mono : forall (P Q : _ -> Prop) c, evtC P c -> (forall c', P c' -> Q c') -> evtC Q c.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h02c'h11Hh22HPh31Kh41Ph51Qh61cp;2p;3p;5g017=j23Tg01X6j22Tg01Yfj30Tg01Z_j51Tg00kOg01NM'3R0p-0[R1f2R2f0R3'2f4R4P3O1P4f1R5O1[^00P4f3P2P5f5R4P3O1P2P5P3O29045W2X00D1W3W1X60X51W4o"). Qed.

(* [comment removed for export] *)
Definition footprint_ok (lz : list (word * word)) (AL : word -> Prop) (RNG : footprint) : Prop :=
  forall b (j k : nat), RNG b j -> (k < j)%nat -> 0 <= b < 2^64 -> page_ok lz AL (page_base_of (b + Z.of_nat k)).

Lemma footprint_ok_weaken : forall lz AL (R R' : footprint),
  footprint_ok lz AL R' -> (forall b j, R b j -> R' b j) -> footprint_ok lz AL R.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h01bh11jh22ALh31Hh42Hbh52Hkh62Hrh71Rh82R'h91Wh:1kh;2lzp;1p;2p;3g004<j10Tg00B\j1;Tg00WAj14Tg017=j23Tg00:4j1:Tg01[Wj32Tg01\Sj29Tg003Cj25Tg004aj11Tg005?j26Tg00Zdj27Tg006<j28Tg00KI#0R0#0#0#0#0#0R1#;#4R2/32#:p-0\2g00J2R2f3R3f2R4f0R532g00FnR6g00KnR7f4R8f1R9P5O2P8P4P9O2[]1]0f6R:P4P9O21994g00Jk/58%10%11'6,78'8f7f5R1P8P3P:P1P8P4O3P9P5O6W6W5W4X:7X17X06A2183eW9W3X82W7W2W;o"). Qed.

Lemma accesses_ok_of_footprint : forall lz AL RNG accs,
  footprint_ok lz AL RNG -> Forall (acc_in RNG) accs -> accesses_ok lz AL accs.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h01kh11Hh21nh31ah42Hph54__x1h61ph71xi001xh82ALh91Fh:3FOKh;3Hinh<2Hkh=3RNGh>7__arithh?4__ffh@8__varmaphA5__withB4accshC2lzp;1p;2p;3p;4p;6p;7p;8g004<j19Tg00B\j1iTg00WAj1XTg017=j2BTg00:4j1ATg01[Wj3]Tg00Xjj1?j2DTg017]j3>Tg0094j1FTg01\kj2UTg01]hj33Tg01^?j4QTg01\Sj27Tg00^ej21Tg005\j1:Tg00oXR0j2;Tg01_CR1j2YTg01_]j36Tg01`Wj3WTg01BUj6VTg01a9j2TTg003Cj2@Tg00]Pj1STg00Zdj2=Tg006<R2j28Tg00:Tj2RTg00;Pj1PTg00;nj1OTg00=^j2GTg00<Yj2NTg00E;j4KTg004aj1MTg00C:j3hTg00P;j7gTg00=<j1fTg00FJj8eTg00>Aj2dTg00>cj2cTg00?=j2bTg00?ij3<Tg00@Cj3\Tg00@bj4^Tg005?j2_Tg00U=j6[Tg01alj3`Tg00XJj4aTg003_j2JTg01bjj1LTg00Efj7ZTf2R3g00KnR4f1R5f0R6Cap=51J56#Lp=4f6R7f5R8f4R933f3R:A<356'8'8p=21;46p=0A<356,8:p=I1135/J6p=H%L69<35p=EP5g00GLR;g00GkR<P<g00HKR=P6g00IRFZp=Cg00KIR>#9R?#9#9#9#9#9R@#iRA#XRB/BB#Ap-0\Bg00J21BB4RC#AA]:35%?3=>C5%FBRD,U:93B6P9PDP5P6CQA3B5DPCA5B35REf7RF1765RGPBP911A3%:6RH'4RIF2X04#0X24#0X3B,;B'YP1A3B3DPCPEf8R1PGPBP8PIF2X04#0X24#0X3B,;Bf9RJ?61:P6A3B:Dg01cef;RDf:RK;68RLP6n010000000W1P6O1PCPEPJPGPBP7PIF2X04#0X24#0X3B,;BP0PBPCPEPKPGPBPFPIF2X04#0X24#0X3BPLP6PCPEf<REPGPBPJPIF2X04#0X24#0P0P4PCA5B:5f=RIPGPBPK11A:/4HF2X04#0X24f?R:f>;6JP6PCA5B85P:PGPBPE11A8/4HF2X04#0P0P4PCA5B73f@R01763PBPI11A7/4HF2X04fCR7fBRG;6IP6PCA5B19PG1769PBP:11A1/4HF2P2A5BJ8=3C71758PBP011AJ%:5'4CIfGRHfFfAR:36P6A5BDFfERG53C1791PBP711AE%:9'4CIP2178JfD%:89HAI5EBfKR2fJRE;6GP617FD%:19HA09EBHPB11A:RH%:J'4fOR0fNR1;66X6BPEPHPIPJfLRJ#?RE=>C2fMRD93C61D05[^7C[A3C6J1D15[^7C%?D=>CJ[AWCE2fIA5B:IP8EVP51TA:g00JkR:/@H%SA,=H'8g00FnRHg00LMRI#F%AI1RH5%PH%OHRIP;P<P<P=PIP;P<P<P=PH1GH:g00Hk1NH>R>CK,CIPHP>g00cg%M?R?,GH=hHACK,CIFgR>%f<P>Ge1dI=P6P3g00NDRIg00NdR='c1b63=<I=dA\H:5C^b?b@bAW51@:6%M@,_?R?,=6'81@:51=5?'8[^5HP611A7P5O2b>b1O6fHP6E[W1W<P5P6O2n2001000000121000000W1W;P5P6O2n2001000000121000000W1X04P5P6O2n2001000000121100000W1X24P5P6O2n2001000000121100000W1X3BP5P6O2n2001000000121100000W1P6O1n200100000021000011000b4W4X6BA`893eW9W:WBW=W8WCo"). Qed.

(* [comment removed for export] *)
Lemma mstepF_lift : forall lz AL N RNG ms ms' mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  mstepF RNG ms ms' ->
  exists mo', cstep (ms, mo) (ms', mo') /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h03mo'h11Hh24accsh32ALh41Eh51Fh63FOKh72Hah82Hhh92Hsh:3INVh;4INV'h<1Nh=3RNGh>2SBh?1eh@2lzhA2mohB2mshC3ms'i001xp;1p;2p;3p;4p;6p;;g004<j1>Tg00B\j1UTg00WAj1OTg017=j2@Tg00:4j1FTg01[Wj3STg01dBj48Tg0102j1NTg01Q5j1DTg00=<j1KTg00?ij36Tg00hgj3HTg010Tj1BTg011Zj1TTg012aj1ETg013ij2<Tg00Xjj1=Tg017]j3:Tg006<R0j23Tg00oXR1j2ATg01Khj24Tg01e;j6MTg01fCl;LTg01Qlj37Tg01gHj29Tg00`[j3JTg00`>j3ITg00DBj4?Tg00nJj4PTg014nj3QTg0165j2RTg00XJj4GTg00kOR2f1R3f0R43Qp=;f3R5f2R61R3436p=1P2g01NMR7P3P4CGp=0f6R8f5R9f4R:P5P6C81934'3'3p=21A74p=5P:P5P6P3C8/34p=Cg00KI#>#>#>#>#>#>#U#OR;/@;#Fp-0\;g00KnR<g00J2AS895f7R=P8P9P3C8%N;R>%D6%K;R636AH89:P0%B8=6>6g0197#FR?%T2R@#ERAp,4segsRB/<=P@1;84C11@;<R<f8R;#=;:4'3X2?'A10;810=4'4f<RCf;RDf:REP4P8P4F2X07#5P4%B;=6>6PA1<BEP@f9R8/;4C1%=D=:<4'3X2?,A?P1P?PA1<BDP@1;E4C1%=C=:<4'3X2?10CE10D4'4f@RDf?RFf>RGP4PEP4F2X07#5P4PAf=RE,<BP@1;C4C1%=G=:<4'3P0PA1<BGP@1;E3C1%=F=:<310DG10F4'4fDREfCRCfBRHP4PGP4F2X07#5P4PA1<BDP@1;F5C1%=H=:<:PBfFR<fER@PEPHPDfARDP9P3PGP<P@PCP9PFP4EMM;L1@27RF#ERGA7BCDPF10H4C1fGRAP<P@P4PDP4F2X07#5P1P7PGA7BEHPF10C4C1fHR1PAP<P4PHP4F2X0710@C10E4'4fIRHP1PAP4PCP4F2X07#5P4PGA7B<EPF10@4C1fJRCPHP1P4PEP4F2P0PGA7BA@PF10<3C1fKREPCPHP319@3DC10HA1014'4fMR@fLRDPEP4PAP4F2X07#5P4PGA7BHAPF1015C1fNR5P@PDP:191:DCP0fOR0P5P@P9C819H910@E10D4'4fQRHfPR1P0P4PEP4F2X07#5P4PHP1P0P=C819D;P710151004'4fTfSR1fRRDP4P5P4F2X07P8100@R01058R5'4P1PDPHP8C8RH19@8R@'3AJ270R8#D=6>6AI270R0#B=6>6R6PGA7B08PFP5C1R5'3PCP6P5P<P9C?C?PHP@P3P4C?C?CPW>W;P3P4O2n2001000000121000000W1W7P3P4O2n2001000000121000000W1X07P3P4O2n2001000000121100000b?W5W4P3P4O2n2001000000121000000W1X2?P3P4O2n2001000000121100000W1W9P3P4O2n2001000000121000000W1W8W:W6XA7XC2XB2W=W<W3W@o"). Qed.

(* [comment removed for export] *)
Theorem evtF_lift : forall lz AL N RNG Q ms mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  evtF RNG Q ms ->
  exists ms' mo', csteps (ms, mo) (ms', mo') /\ Q ms' /\ ainv lz AL N mo' /\ same_but_mat mo mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h03mo'h13ms'h21Hh32HQh42Hhh53INVh62moh73RUNh81eh92msh:3ms0h;3msfh<2ALh=2C1h>2CSh?3FOKh@3HQ'hA2IHhB4INV'hC4INV1hD1NhE1QhF3RNGhG3SB'hH3SB1hI2SThJ2lzhK3mo1hL3ms1hM3ms2hN1oi001xp;1p;2p;3p;4p;;p;6p;5g004<j1:Tg00B\j1XTg00WAj1UTg017=j2JTg00:4j1WTg01[Wj3VTg01dBj45Tg0102j1TTg01Q5j1@Tg00=<j1LTg00?ij3BTg00ndj3HTg00lVj3>Tg006<R0j22Tg01gHj24Tg01OCj2=Tg01L]j1STg01hGj1QTg00DBj48Tg00nJj4?Tg00hgj3OTg01iKl;KTg01Khj2;Tg01jFj3MTg00U=j6NTg01MUj5PTg01kLj5GTg00mOl;RTg00XJj4CTg00oXR1j2FTg00kOR2g01NMR3f1R4f0R5CCp=0f6R6f5R7f4R8f3R9f2R:C51445'2'2p=7P2P3P9P:CC/=4/25p=11F35p=31F25p=6P8P9P:P4C5/25,27p=91245,2:p=AP8P9P:P4C5/25p=<1=:4/25p=I1445,2:,29p=DP2P3P:P4CC/=5p=Eg00KI#:#:#:#:#:#:#X#UR;/J;#Wp-0R<\;g00Kng00J2P<\2AV679f7R<P6P7P4C5%T;R=%@:%L;R;3BAH678P1P2f8R>?>65P<P5O1'2X12P>P<1045R?f9R@P4O1f=RAf<RBf;RCP5P<P5F7C1X03#3X12#6P5f:RD?>>5P@P5O1'2P0A>C@4PDP4O1PBPCP?PAP4O1fAREf@RFf?RGP514C5RHE9C1X03#3X12#6P5A>AC9PAP8O1PGPFP5O1fFRIfERJfDRKP5C5%@4=B=;RLP<P8P?PIP4O1fJRMfIRNfHROP5C5RP1485RQ3AC1X03#3X12#6]4]5^63]3X;2X92PGP5O1PJPKfCRRP5C5P2P6P8P?PJP4O1PNPOfGRSP5C5RT;AQC1X03#3X12P8P3P7P91075PKP7O1POPSPIP51495RUE9C1X03P:108:RV/=VPRP8O1RWPSPIPJP:C5RX14::RY'2RZ'2%SVPWPZP9PXPYP4%Q:C8C8C8C?C?X4LW5X63W3X:2fBRY?O:4A>R:4PRP:O1P@P8P?PNP4O1fMRXfLRZfKRWP5C5RV;AQC1X03#3X12#6^4L^5T^63]3PKP9O1PZPWPMPNP@P>P:PJP4P5P6M;K10D910@5';?AVUX03#3P1P310C810D5';fNRVPXPZP5PQE9X0310A6RQPZP4O1fPRZfORUPVP51465D<R6'27I?X03#3X12#6P510B5,;Q/26P0f>R6/0<10A4';fQPZPUP414<4D<PEPDP?PZP4O1fTRQfSRTfRR[P5PDP5F7C1X03#3X12#6P510F@10G9';PQPTP[P814D8D<P0fUR\PQPTP7C514C7PJP6P?PQP4O1fXR]fWR^fVR_P51465R`E9C1X03#3X12#6P5P^P_P\P<C5146>PEPFP@P4P=%@GAB=5;XN=PA%@@AMG@5ENO4PSPCP?P^P4O1f[R^fZR=fYR;P5PHE9C1X03#3X12#6P1P2POPBP?P]P4O1f\R]P^P=P5PBP5F7C1X03#3X12PMPRP?P;P4O1f]R;P]P^P5PRP5F7C1X03#3X12#6P5PMP6P?P=P4O1f^R6P;P]P5P`E9C1X03#3P1P3PWPG10:5P^P:O1f_R:P6P;P5PGP5F7C1X03PVPSP?P;P4O1faRGf`R1P:P5C5R:PSP5CDC1X03#3X12#6P5PXPE1085P;P8O1P:PEP5CDC1P010749EVYP6P7O1fbR6PGP1P4PYP4F7P[PWP?PGP4O1feR[fdR1fcR:P5PWP5F7C1X03#3X12#6P510<99EZKPGP>O1P[P1P:P8PJP8F7P0P6P@O1ffP[P1P714I7D<P_PUP?P[P4O1fiR[fhRIfgR6P5PUP5F7C1X03#3X12#6P5P1PCO1P[PIP6P>14N>D<P0fjR0P[PIP@C514M@P=PTP?P[P4O1fmR[flRIfkRNP5PTP5F7C1X03#3X12#6P5PIPNP0PCC514XBP2P;P_P?PIP4O1fpfoR?fnR;P5P_P5F7C1X03#3X12PEP3P]P\10Y5PNPYO1P?P;P[P5P\P5F7C1X03PA10^QR^10EAR\'=P0PEO1REP;P[PIPAC5RI14QAR['2R;'2P^10=VP\PMP@DPPEP;P7PIP[P4PQPVPAPJP5DGC8C8C8C?C?WGWBP4P5O2n2001000000120000000W2W@P4P5O2n2001000000120000000W2W>P4P5O2n2001000000121000000W2X03P4P5O2n2001000000121100000W2X12P4P5O2n2001000000121100000b8WHWCP4P5O2n2001000000121000000W2W=P4P5O2n2001000000121000000W2XK3P4P5O2n2001000000121100000b8X4LX5PX63W3WAW7WIXM2XL2X:2PAP7P4P5PBPDP@M;RW3W7P4P5O2n2001000000121000000W2X;2P4P5O2n2001000000121100000W2W4W5W?X63X92WEWFWDW<WJo"). Qed.

(* [comment removed for export] *)
Corollary evtF_lift_evtC : forall lz AL N RNG Q ms mo,
  footprint_ok lz AL RNG -> ainv lz AL N mo -> m_halted mo = None ->
  evtF RNG Q ms ->
  evtC (fun c' => Q (fst c') /\ ainv lz AL N (snd c') /\ same_but_mat mo (snd c')) (ms, mo).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h02c'h13mo'h21Hh33ms'h42ALh52CSh62EVh73FOKh82HQh92Hhh:3INVh;4INV'h<1Nh=1Qh>3RNGh?2SBh@1ehA2lzhB2mohC2msi001xp;1p;2p;3p;4p;;g004<j17Tg00B\j1JTg00WAj1ETg017=j2<Tg00:4j1ITg01[Wj3HTg01dBj45Tg0102j1DTg01Q5j1CTg00=<j1BTg00?ij3ATg00ndj3@Tg01lQl;?Tg01OCj21Tg00oXR0j2:Tg00`>j3>Tg00`[j3=Tg01X6j28Tg01gHj29Tg006<R1j26Tg00DBj4;Tg00nJj4FTg00XJj4GTg00kOR2g01NMR3f1R4f0R5CGp=0f5R6f4R7f3R8f2R9C51945'6p=31645,69p=4f6R:P6P7P8P9C51945'6'6p=2g00KI#7#7#7#7#7#7#J#ER;/<;#Ip-0R<\;g00Kng00J2P<\2AH:68f7R<P:P6P4C5%D;%C9%B;3AA@:67f:R;f9R=f8R>P<P:P6P7P8P9P4P5M;?10<:R?1045R@'1P>P4O1f<RAf;RBP;P5P:P5E334X13,:3X32,:2P0P210></1@P=P4O1f=R:PAPBP5P<P5E334X13,:3X321<23RCP=A>235RDO1P:PAPBA=235REP<PEF2W0/8?P510;=/1@PBP4O1f?R@f>R?P:P5P=P5E334X13,:3P0P310B;R01095'1PAP9O1f@R9P@P?P5P;P5E334X13P:PDO1fAR;P9P@PEPBPEF2X0C/80P510:A1075'1P?P7O1fBR0P;P9P5PAP5E334P110?:1064'1P@P6O1fCRFP0P;P4P:P4F2P;PDO1fERGfDRHPFPEP@PEF2X0C10@?'8P5109@10<8'1P0P>O1fFR<PGPHP7P9P7F2P1PFP=O1fGR7P<PGP6P;P6E3PGPDO1fIR9fHR8P7PEPFPEF2X0C10F0'8P5PGPBO1fJRFP9P8P>PHP>E3P1fKR1PFP9P=C519G=P9PDO1fMRGfLR>P1PEP7PEF2X0C107<'8P5PGP>P1PBC5198APC101F/15P>PDO1fPfORDfNR>PEPFPEE334X0C10;:RC10F9/1CP1A>23CO1PDP>PGA=23CRCP9PCF2RCP=P1P;O1PDP>PGP:C5RG199:R9'6P6PGP9P4P5C;C;PCeC;CFW?W;P4P5O2n2001000000120000000W2W8P4P5O2n2001000000120000000W2W5P4P5O2n2001000000121000000W2X13P4P5O2n2001000000121100000W2X32P4P5O2n2001000000121100000b@W6W9W:W7XB3XC2W=W>W<W4WAo"). Qed.

(* [comment removed for export] *)
Lemma footprint_ok_nolazy : forall AL RNG, footprint_ok [] AL RNG.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "h02ALh13RNGh22_Hh33_H0h43_H1h51bh61jh71kp;1p;2p;3g004<j10Tg00B\j1BTg00WAj13Tg01\Sj22Tg003Cj2ATg004aj11Tg005?j2:Tg00Zdj24Tg006<j25Tg005\j16Tg003_j27Tg01bjj18Tg017=j29Tg0094j1@Tg01mJj2?Tg00?ij3<Tg00>cj2;Tg01nGj3=Tg01[Wj3>Tg00KI#0R0#0#0#0#0#0R1#B#3R2p-0[g00J2g00Fng00KnR3f3R4f2R5f1R6O21265g00Jkf4R5'A%10%11':,45'5g00NDR5f5%64'7#8R41922#@R2'?g01naR13<f7P4O11;513=W4W3W2X73W6W5f09>26eW1W0o"). Qed.

Lemma evt_lift_nolazy : forall Q ms mo,
  m_vm_lazy mo = [] -> m_halted mo = None -> evt segs Q ms ->
  exists ms', csteps (ms, mo) (ms', mo) /\ Q ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) ["WithSegs"] "p'0h02HQh13ms'i003ms'h21Hh33RUNh41mh52msh63ms0h72Hhh82Hlh92Hsh:2IHh;1Qh<2STh=2moh>3ms1h?3ms2i011xp;1p;2p;3p;6p;4p;5p;8g004<j14Tg00B\j1TTg00WAj1JTg017=j2>Tg00:4j1STg01oAj1RTg0094j1LTg00?ij30Tg0102j1ETg01Q5j1?Tg00=<j1CTg01I]j3ATg01F?j35Tg006<R0j26Tg00oXR1j2@Tg01L]j1QTg0209j3OTg010Tj19Tg012aR2j1=Tg01?Ej28Tg0165j22Tg00`[j3ITg00`>j3HTg01Qlj3<Tg020lj1FTg0224j1GTg00>cj2DTg00U=j6;Tg023<j4KTg00DBj47Tg01MUj5BTg024@j8MTg00nJj4NTg00XJj4:Tg01OCj2PTg00kOR3g01NMR4f3R5f2R6C:P3P4f1R7f0R8C:'Pp=1P3P4P7P8C:p=3p-0\3g00KI#4#4#4#4#4#4#T#JR9/>9R:#S%R8%L:30%E9R:%?7%C9R930p,4segsR;f4R<;A5P1P3f5R1=5;8f6R=P8O1'6X13P=P1P8P1C1f7R>P8O1'6X13,@3P8A5;>8f8R?P8O1'6P0A5;?7f9R@P7O1f:RAP@P8P@C1f;RBP8O1'6X13,@3P8A5;A5f<RCP<O1P3f=RDPCP8PCC1f>REP8O1RF'6X13P1PCPBP1PBC1PDP1O1P;f?P8O1P6PEP7PEC1]0X13X53137D#QX0FX63AO;67P0%95=0:9%=3R018;5123630A5;56fCR6P5O1P1fBRFP<PFC1]0fDRFP<O1P>P6P1P6C1]0[[P8%91=0:918;=1231500A5;=1fFR6P=O1P?fER=P>P=C1]0fGRDP>O113A6R>13@6RE13?6AI34>R?#?=0:9AH34>R>#9=0:9R91>34R:#=RBA<;>?12:ERE30R>'6PFP9P>P<PBP2P3PB18;AR<138D,2:%F:R9%G:RFn101101000310100000013AD,2:RD90B8X4BP0123@P2P3PBP8fH,38,2:P9PFn1011010003101000000=0BDX401DBEP<P5E;A<;A6P;PAP6P=CKE;P>eC7C7P7P8O1DBW0W:W3W<W9P7P8O2n2001000000121000000W2X?3X>3X63PCP1P7P8GMP8C7CNW0W3P7P8O2n2001000000121000000W2X13P7P8O2n2001000000121101000W2W7W8X=4X53W;o"). Qed.

End WithSegs.

Arguments mstepF segs RNG ms ms' /.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_ok (lz : list (word * word)) (AL : word -> Prop) : footprint :=
  fun b j => forall k : nat, (k < j)%nat -> 0 <= b < 2^64 -> page_ok lz AL (page_base_of (b + Z.of_nat k)).

Lemma footprint_ok_fp_ok : forall lz AL, footprint_ok lz AL (fp_ok lz AL).
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h02ALh11Hh22Hbh32Hkh41bh51jh61kh72lzp;1p;2p;4p;3g004<j10Tg00B\j1=Tg00WAj13Tg017=j22Tg00:4j1<Tg0258j4:j29Tg01\Sj25Tg003Cj24Tg004aj11Tg005?j26Tg00Zdj27Tg006<j28Tg01[Wj3;Tg00KI#0R0#0#0#0#0#0R1#=#3R2/22#<p-0\2g00Fng00KnR2f4R3f3R4f2R5f1R6C:1565g00Jk/43%10%11'6,73'8P5P4P6f0R4O3W2W3W1X62W5W419649;64eW0W7o"). Qed.

Lemma fp_ok_largest : forall lz AL RNG, footprint_ok lz AL RNG -> forall b j, RNG b j -> fp_ok lz AL b j.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h02ALh11Hh22Hbh32Hkh42Hrh53RNGh61bh71jh81kh92lzp;1p;2p;3p;4g004<j10Tg00B\j1<Tg00WAj13Tg017=j22Tg00:4j1;Tg01[Wj3:Tg01\Sj25Tg003Cj24Tg004aj11Tg005?j26Tg00Zdj27Tg006<j28Tg0258j49Tg00KI#0R0#0#0#0#0#0R1#<#3R2/22#;p-0\2g00J2f2R2f1R3f0R43:g00Fng00KnR5f3R6P3P4O21542g00Jkf4R7'4%10%11'6,77'8f6R1f5R0P7P2P6P3P4O6W2W3X85P1P0P2P3C9eW4W7W6W1W5W0W9o"). Qed.

(* [comment removed for export] *)
Lemma rng_fp_ok : forall lz AL lo len,
  0 <= lo -> lo + len <= 2^64 ->
  (forall z, lo <= z < lo + len -> page_ok lz AL (page_base_of z)) ->
  rng (fp_ok lz AL) lo len.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with64__x3h74__x4h84__x5h91bh:1jh;2ALh<1Hh=2Hbh>3Hhih?2Hjh@2HkhA3Hk0hB3HlohC2_HhD4cstrhE5cstr0hF1khG3lenhH2lohI2lzhJ1zp;1p;2p;3p;4p;7p;8p;<g004<j16Tg00B\j1cTg00WAj1YTg017=j2PTg00:4j1KTg003_j21Tg004aj1ETg005?j2WTg003Cj20Tg00ZdR0j28Tg006<j2;Tg01bjj1LTg01_]j3bTg005\R1j17Tg0258j4aTg0094j1]Tg00:Tj2?Tg00;Pj1[Tg00;nj1ZTg00=^j2GTg00<Yj29Tg00=<j1XTg00>Aj2VTg00>cj2ATg00?=j2UTg00?ij3TTg00@Cj3STg00@bj4OTg00;2j1NTg00D]j4<Tg00ATj3>Tg00C:j3MTg01\SR2j2CTg00Rnj4RTg00C]j1DTg006Wj1@Tg0076j2:Tg007_j3=Tg008Hj2JTg009Tj3FTg00B7j1HTg00E;j4BTg00P;j7`Tg00DBj4ITg00Efj7\Tg00FJj8^Tg00U[l<_Tg00JkR3f0R4'0p=3g00FnR5f1R6g00HkP4CBp=5P6g00GLR7g00GkR8P8g00HKR9P4g00IRF\p=2f3R:P7P8P8P9f2R;P6P4G^p=4g00KnR<P5P2P1P0g025mf5R0f4R1P:P;P6P4M<_p=Qg00KIR2#6R=#6R>#6#6#6#6R?#cR@#YRA/PA#Kp-0\A%36RA11;6%E=RB%E?'WR?'01014111:RC,84';f7RDf6RE%L63b[^J5%3110C?RC10E6RF%76,1;11DE'0RGf:RHf9RIP:P;CaRJ[[^:<^95RK';g00LMRL#]RM%KLRN1?56%[5RO%Z5RP1G53RQ1952RR'5,2PRS%X8RTPSC41VP9RSP4P;g00NDRUg00NdRV'A1U4;=TUVdAS536COR3b3b4b5X05%34PA[^05P4P0P:O2b2PCPKPMPNP51?5;P6%N5RKC<POPP195=RC9>5R1G5B=M5@'5,2PR@PTP@C4PSP3b3b4b5X05X151146/0?116;/0?[^05^15P4P1P0P;O3b21C4:%30180?';PD%7;R?,1E1C;0%70R@,8?RBP;P?1A5?P0P@1A5@EQP6CRPB%DE%7ERB#3%D1%71#3g00M9R@#@R?#@RA#@RV#@,:51:5?1:5@R@5=55=5g00MXR?'J1:5V1:5A==5@5=5/J?=FLM5FLPNP5P51?51P;PKC<P6P51?50P:PKC<C<POPP%H2,95R2,5Q,2PPTPPP5P2g00cgRQ%H=,95R=CB,2PPTPPA>5C=195>9>5RR>'5,2PPTPP15RC,2PPTPPP7P8P8P9A>5C2R2,5R,2PP5P2PQP>CB,2PF`C4C4C4C4PSP3b3b4b5X05X15X65X75X85%3;18:011:E11;0'010:1110ERE,01111D,8E';[[[[^05^15^65^75^85P4%7If>PBPHf?P6P:PDf8O9b2bEbDbAO2WCW@XF<PJeX?GX=FX:<X95CICIW<W>WBXG5XH5W;WIo"). Qed.

(* [comment removed for export] *)
Lemma page_base_of_range : forall z, 0 <= z < 2^64 ->
  bv_unsigned (page_base_of z) <= z < bv_unsigned (page_base_of z) + page_size.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h02H0h16__sat5h24__x1h34__x2h44__x3h51xh61Hh72H1h82H2h92H3h:2Hah;7__arithh<4__ffh=6__sat4h>8__varmaph?5__with@1qhA1rhB1zhC2HzhD1mhE1nhF1yp&0p;1p;2p;3p;4p;6p;<p;7p;8p;Bg004<j1GTg004aj1ITg005?R0j2KTg00B\j1qTg026Oj2CTg026lj2;Tg00Y`j2\Tg003Cj2:Tg003_j2=Tg027Ij2WTg00?ij37Tg027jk102Tg00f`j2>Tg028Ck200Tg00ZdR1j23Tg028jj2vTg006<j2DTg029Qj2gTg02:7j2fTg02:]j2OTg00>cj24Tg02;>j2aTg02;fj3`Tg006Wj19Tg0076j26Tg00SUj1[Tg00T3j2ZTg00TTj3MTg008Hj2@Tg0094j1YTg009Tj3ETg00:4j1XTg00:Tj2LTg00D]j4VTg00;Pj1UTg00;nj1TTg00=^j2JTg00B7k103Tg00<Yj2HTg00=<k101Tg00E;j4BTg02<Jj6~Tg02<nj3STg00ATj3RTg00>Aj2{Tg00?=j2zTg00@Cj3uTg00@bj4sTg00ZFR2j1NTg00[@j3pTg00[fj1oTg00\Dj4nTg00U[l<jTg00\gj6kTg02=Qj2lTg02>:j3mTg02>cj2eTg00C:j3dTg00RCj4cTg00]Pj1bTg00^9j3rTg00U=j6PTg00Wdj2tTg00^ej2QTg00_Oj2wTg01bjj1_Tg007_j3xTg00Efj7yTg00P;j7^Tg00FJj8|Tg00a8l<}Tg00a]lB]Tg00JkR3f0R4':p=2%G4#Gp=<f2R5f1R6/34'Dp=1g00FnR7?x64p=5P7P6g00HkP4CBp=?P6g00GLR8g00GkR9P9g00HKR:P4g00IRFyp=0P7P6g00cgP4CBp=AP5P8P9P9P:P6P4F^p=Ff3R;P8P9P9P:P5P6P4G|p=8g00beR<P7P7P7P2P2f5R2f4R=P;P5P6P4M<}p=hP7P7P7P7P7P7P0P4P6P5P0P;P=P2f6R0f7R>f8f9MB]p=i%24R?g00KIR@#GRA#IRB%GA#<#<RC#IRD'KRE714P7%qCRF%<C#<#<#IRC,C6/;CRG'\RH1:451=4C715XB7RIP7PGPI1W6CRIA77C3RJ$021C5C,;C1>5C'=9775[RK2005CRL133CRM1>;CRN#2?1NC[RN1v;CRO13C31>=CRP,3C1:P3'D[RP1g=CRQ1C2C=773\JRR1f2CRS1>0C=770\JRT1C0CRUP71>>CR>P7P2g02?ORV1O3C'4PMeO1RMA1?4CR?1aBDRW133BRX%2D133E[RY[RZ%2BR[g02@5R\A`BD6UW:R]%2E\\^:[R[P61O3B,4VPXeO1RXPYg00LMRVg00M9R\#9R^#9R_#9R`,67Ra%[@,Z7Rb167^R^5M7167\R\'5'5g00MXRc'@167_15^\R^'5/@c%YVR_5EV3E%XVRdP71L75P61L7;CVRe%U7Rf%T7Rg1J73Rh&03@,H7Ri'?,0g1J7CRj,Ai,0g5FgRk&019RlPgPgPgP8P9P9P:P7Pjg00V@R9PhCB,0gE~PlP71H7ARAP91H7@R@9S7j=R7iCB,0gC8RiPlAS7@jR@/?A,0gAR7@j,AA,0g5FgC8C81{g:R:P4P5g00NDRjg00NdR9'41z45=7j9dAu736CsR3b<b>b?X27X37X47%25?15CR9g01ce\J1;C5/==977;[RJ1;5CR5/:;1=5C71;[[^27^37^47P4P2f=RjP0P=f;R8O5b;b1b=b1b0bAb@b9b8b7b0b6PHPIPKPLPNPOPPPQPRPSPTPUP7P>P7PMP?%25R?%NFRM,KBR>,35RU'D135ERT,D?P?PUP?PTp-0/4?9p??P7P7P1P4X57R?P11364#oXF7X57P5P51475P>PEP?P?P?P7P7g00cC1K64Cn,47XD7XE7PBPB147BPMPDP?P?%N4,47X5<PFPD147DEhM:iM<jEkPWPZP]P[PXPY%9`R`#9,67RYAM7ba/5^'5/@c1l7C=m7\167`/5a,5Y'5/@c,e\=EV_5EVPdPePfPgPkPlPgPiPlPg1?hA,0g1J7B=d7FRB,AA,0g5FgPl1?h@,0g1A@B,0g5FgC8C8C8P:P3b<b>b?X27X37X47%2;?1;E1;;CRC#2?1CE[\J\9^27^37^47P4P2PjP0P=P8f<O6b;b1b=b1Ccb0bAb@b9b8b7b0b6%2G%bF71Ge9rFGEP1tFG,QF1wFGEP%_6,QFRF/:6g02@Q,=F716eWCXB7o"). Qed.

(* [comment removed for export] *)
Definition lazy_disjoint (lz : list (word * word)) (lo len : Z) : Prop :=
  Forall (fun r : word * word => lo + len <= bv_unsigned (fst r) \/ bv_unsigned (fst r) + bv_unsigned (snd r) <= lo) lz.

Lemma page_in_ranges_false_of_disjoint : forall lz lo len z,
  lazy_disjoint lz lo len -> lo <= z < lo + len -> 0 <= lo -> lo + len <= 2^64 ->
  page_in_ranges (page_base_of z) lz = false.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "p'0h01xi001xh11Hh21rh34__x1h44__x2h54__x3h62H1h72H2h82Hah92Hbh:3Hinh;7__arithh<4__ffh=4__p1h>6__sat4h?8__varmaph@5__withA4__x4hB4__x5hC4__x6hD1bi011bhE1mhF1nhG1AhH1DhI3HhihJ3HlohK2HzhL1PhM6__sat3hN1ahO1lhP5lemmahQ3lenhR2lohS2lzhT1yhU1zi021pp&0p;1p;2p;3p;4p;8p;:p;6p;7g004<j1GTg00B\j1rTg00WAj1fTg017=R0k209Tg00:4j1`Tg02AIk303Tg003Cj21Tg003_j26Tg00Zdj2<Tg006<R1j25Tg004aj1STg005?k208Tg006Wj1ETg0076j2_Tg008Hj2MTg0094k101Tg009Tj3NTg00:Tj2HTg00D]j4OTg00;Pj1nTg00;nj1mTg00<Yj2ATg00B7j1[Tg00ATj3QTg00=^j2VTg00C:j3gTg00=<j1eTg00>Aj2dTg00>cj2WTg00?=j2cTg00@Ck307Tg00@bk406Tg02BFk205Tg027jR2j1UTg02CHk104Tg00`>j3DTg00^ej22Tg02Cnj24Tg00`[j3@Tg02DKj2>Tg02Dij3^Tg01]hj3;Tg00oXR3j2TTg02EER4k202Tg02E^j4]Tg000Sk400Tg02FEj2}Tg02G2R5j2|Tg02GPj4xTg02H2j8wTg02Hel:sTg02ITj3qTg00XJj4ITg02J7j3pTg02JZj2oTg01_Cj2BTg017]j3ZTg01`Wj3tTg01BUj6uTg02;>j2vTg02;fj3lTg02:]j2yTg00;2j1zTg02K:j7kTg00P_j6{Tg01bjj1YTg01mJj2jTg007_j3~Tg00E;j4\Tg00Efj7aTg00P;j7iTg00FJj8hTg00?ij3XTf0R6#G#Gp=Jg00JkR7/16p=Cf2R8f1R9'6/16p=:g00FnR:/_6p=FA~:96p=7P8g00GLR;g00GkR<P<g00HKR=P:P9g00HkP6C\g00IRR>Fap=8P:P9g00cgP6C\p=LP9P;P<P<P=P6P>Fap=KP8P;P<P<P=P9P6Fip=Pf3R?P;P<P<P=P8P9P6Ghp==g00NDR@g00NdRA7X6p=0%Y6,29p=3g02@QRB,66p=bg01na9X@6p=R1296,68p=?169B/46p=9g00KIRB#GRC#GRD#J#JRE#rRF#fRG009GRH#`B03?8911?916?8,<9'5f4RI#Cf5RJ%SCRK%SERL+08RM7:Ig00LMRNg00M9RO#ERP#ERQ#ERR#ERS#FRT%FPRP1_:ORO'7'7g00MXRU'M%FRRR%FQRQ/7O'7/MU&01NRV5NN3N%`NRWP:1H:8P91H:?CO%n:RX%m:RY1A:CRZ%[BR[,A:R\5Q:R]1V:K=g:FR^58Y%e<R_PY1V:7R`=8YZP_PY1A:BRB98YZ1LB],KY5PYP_A8Y`B1LB^,KY5PYC=C=C=1dY=R^P6P81W@A1c68#0dB07:79H06RAb<b?b@X3:X4:X5:A:98M%C811?8R`16?I,<8'5%C?1<?M'5[[[^3:^4:^5:P6f6R]f7RaPJP9P8P?O6b;-05I13FIRb/1I%bb,<I'5P1%06#U%R9[Rb%R6%09#URc[%R8\c&046P9n2001000000120000000XD@Pb^D@P6ADGG6,2FR@13FaRb'4A@GG69?@FRc,9b'>RbX2HRdf9Re5^HRf%0ff:Rf9;H6Rgf8Rh,3FRi,4@19ic'>RiX2HRjP6O1#0'5X0H,TH+02p-0RkPk]GPkPkP4P4C]P2g02K^PkPkP4PkPkPkP5H00R5C]P>PkPkP4P41}k4P4P5PkP41|69XTkX0kg02LPCxGwA^Hjf#0f;Rj9;H6R413FeR5,4@195c'>X2HP6O1#0'5X0H,THP6M:sWPAqHde%0b,5gX0H,THRgP3PH%0i,54X0Hg01ceR4P6P0PGPGf>R09;H613FjRi,4@19ic'>#0'5P4[P6PGPGP9P6CIRifA5;HADGGi,2FR313F0Rb'4A@GGi9?3F,9b'>#0'5P1PGPGP8P9CIRbfBR35;HADGGb,2FRif?Rd,3FR5'4A@GGb9?iF,95'>#0P4P6PGPGPIP?CIfDR55;HPGPGPJPICIRi9DGG,2FRb13F3R3'4A@GGi9?bF,93'>#012F]R3fCRb,3FRi'4R>A?3FJ,9iRi;p6%0>%0i'5P112FaRi13F5R>'4#016i3,9>#0P4P612FeRefF,3F'4#0fG,3F12Ff/6e'9#0P11496#01189[R111961489#0Re[P`\e1o96P9n2001000000120000000XE:XF:ReP1^E:^F:R1P6f<,2FR`fI,3FR>P8O311`>PeP1P6fKR1,3F#bRe12F0f=7?FR>P?O311e>fOR>fNRe;:@11c>'BX2HR`=ZH>fQRi9;H6fPR3ADGG9,2FR25:iA@GG99?2FRl/1i'B[^0H[A;H63163>Rm/1211l3'B[^0H11m@11c3'BX2H=ZH3[AtH`>P1PGPGPdP0CIR0PfEufMADGG0,2FRf5:eA@GG0,2F=:fe'B1vKL1<7KRf%CL1<7M[Re[%CKR0g02@5RdAlKL9UW8%CM\d^80P9g02?O1y7K'WPfeO1Pe%ESRS#E#F17QP,7T'7/MU%FS17RO,7T'7/MU=NNV5NNPWP:P:1H:IP81H:]COP9P:1H:JP?%z:COCOPXPY1A:DRD%JE#J#J#SRE,V:5Q:RX%[C,A:RC%G[,A:5Q:R[58YP_PYA8YCDP_PYPYP;P<P<P=AQ:B\R\=8YCA8Y[BFkP_PYA8YDZ1LZX,KY5PYP_PYA8YBZ1LZ\,KY5PYP_PYP;P<P<P=PhE{C=C=C=C=C=P^PAb<b?b@X3:X4:X5:XA:XB:XC:X=k16IJ9:?E11JIA:8I]A:]a8'B11]I16]E,<I'511IJ16I],<J'5Pj[[[[[^3:^4:^5:^A:^B:^C:^=kP6P412Fb12F513FifRPifSPJPaPIfLP>O<b;b>bMb>P4eb:b7b1b6b1W7W6P9P6O2n2001000000121000000b9W9W:P9P6O2n2011000000121000000W1XOGXNGP9P6O2n2001102000121101101X0HP9P6O2n2001000000121100000W1%UgeO2O2b1%YJ/jh#RebLWIWJWKWHXU:XQ:XR:WSo"). Qed.

Lemma rng_fp_ok_disjoint : forall lz AL lo len,
  0 <= lo -> lo + len <= 2^64 -> lazy_disjoint lz lo len -> rng (fp_ok lz AL) lo len.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h62ALh71Dh83Hhih93Hloh:2Hzh;3lenh<2loh=2lzh>1zp;1p;2p;3p;4p;8p;7g004<j11Tg00B\j1VTg00WAj1CTg017=j2?Tg00:4j1;Tg003Cj20Tg003_j22Tg004aj14Tg005?j2ATg02AIj3@Tg0094j1>Tg00:Tj23Tg00;Pj1<Tg00;nj1UTg00=^j2:Tg00<Yj28Tg00E;j47Tg00=<j1TTg00>Aj2OTg00>cj2NTg00?=j2BTg00?ij39Tg00@Cj3DTg00@bj4ETg00;2j1FTg00D]j4GTg00ATj3HTg00C:j3ITg00Zdj2JTg006<j2KTg01bjj1LTg01mJj2MTg02MFj8=Tg01nGj3PTg02NVj7QTg00Efj7RTg00FJj8STf1R0g00GLR1g00GkR2P2g00HKR3f0R4g00IRFRp=5f3R5P1P2P2P3f2R1P0P4GSp=6g00KIR6#1R7#1#1#1#1#1R8#VR9#CR:/?:#;p-0\:g00FnR:g00JkR;/00R<1210%47R=%48'AR8'0f5R>?@51f6R?P>f4R@P5g00LMRA#>RB%;ARA13:0%<:RC%U:RDP:1::;g00HkRE18:6R6C7,5DRF%T2R2PFC61OD3R3P4P1g00NDRFg00NdRG'N1B41=9FGdAD:;0CERGb2b3b4X0:10;4P<[^0:P4P>P5O2b1PBPAP:13:1P0%F:CGPCPDP:18:79H:6PE1::==I:9C7,5DRDP2PDC6P3PGb2b3b4X0:X5:1240/081201/08[^0:^5:P4P@P>P1O3b110>412>@,J4'K%L0R8f8RG'Mg01na59Ff7P8O1PGP?P>P0P1P4P@P5G=3PW:X>:FQW7W8W9X;:W<W6W=o"). Qed.

(* [comment removed for export] *)
Lemma rng_fp_ok_allowed : forall lz AL lo len,
  0 <= lo -> lo + len <= 2^64 ->
  (forall p : word, (exists z, lo <= z < lo + len /\ p = page_base_of z) -> AL p) ->
  rng (fp_ok lz AL) lo len.
Proof.
ltac2:(KReplay.run1 (kr_t_ExecF ()) [] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with64__x2h72ALh81Hh93Hhih:3Hloh;2Hzh<3lenh=2loh>2lzh?1ph@1xp;1p;2p;3p;4p;7p;8g004<j12Tg00B\j1WTg00WAj1JTg017=j2CTg00:4j1?Tg003Cj20Tg003_j21Tg004aj1;Tg005?j2ETg00Zdj26Tg006<j23Tg01bjj15Tg00?ij34Tg00oXj2VTg0094j1UTg00:Tj2>Tg00;Pj1RTg00;nj1QTg00=^j2=Tg00<Yj2<Tg00E;j47Tg00=<j1ITg00>Aj2HTg00>cj28Tg00?=j2FTg00@Cj3GTg00@bj4DTg00;2j1KTg00D]j4LTg00ATj3BTg00C:j3MTg01mJj2NTg00DBj4ATg00nJj4OTg02OOj3PTg02NVj7@Tg00Efj7STg00FJj8TTf1R0g00GLR1g00GkR2P2g00HKR3f0R4g00IRFSp=:f3R5P1P2P2P3f2R1P0P4GTp=9g00KIR6#2R7#2#2#2#2#2R8#WR9#JR:/C:#?p-0^@:g00FnR;g00JkR</00R=1110%;7R>%;8'ER8'0f5R?/04f4R@,1?,64'3RA%54RB94:0'3X1;,V;f6RCP0O1[^?:PCP?P@P5g00LMRD#URE%?DRD1>;0%R;RF%Q;RGP;1=;<g00HkRH1<;6R6C7,:GRI%I2R2PIC91HG3R3P4P1g00NDRIg00NdRJ'81F41=4IJdAG;<0CDRJb3b4b5X0;10<4P=[^0;P4P?P5O2b2PEPDP;1>;1P0%K;CLPFPGP;1<;79B;6PH1=;>=M;9C7,:GRGP2PGC9P3PJb3b4b5X0;X6;1140/081101/08[^0;^6;P4P@P?P1O3b2%50R@f8'Ng01na54If7RIP@O1P1P@P;10I411IC,64'3%51=4:B'3X1;P010C011C?,60'3A4:@@P418:@CACOO23PX;AX1;F@W8W9W:X<;W=W7W>o"). Qed.
