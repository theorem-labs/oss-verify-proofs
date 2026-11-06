(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel TopLevelSB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prog ProgA EquivPA AsanProgDeps AsanInv AsanOK ImgFacts AsanHandoff ModelOK.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanMain () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA;TopLevelGenAtfam_no_kill_treeC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z2leI59OSSVerify5KrLib2AS9MainEntry7amodelL00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib2AS9MainEntry9amL_limitC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMain7amodelHC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib4Spec7AsanInv7LIMIT34C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS9MainEntry6amodel00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib2AS9MainEntry>amodel_amodelLC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMainBamodelH_of_amodelLC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC59OSSVerify5KrLib4Spec7AsanInv5LIMITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv@LIMIT34_le_LIMITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8LIMIT_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry9amain_atLC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib2AS9MainEntry@asan_mem_facts_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8pfact_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntryAasan_pure_facts_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry:hidden_argC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib2AS9MainEntry8ashadow0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c49OSSVerify5KrLib8AsanMain:amain_openC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsK47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib2AS9MainEntry4WblkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib2AS:MainExport8mfact_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5mfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan>asan_mem_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5pfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan?asan_pure_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg7a_phdrsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C59OSSVerify5KrLib2AS9MainEntry3ARAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry3AGPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry5AMAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry8amain_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntryBamain_at_amain_atLC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMain>amain_atL_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA;TopLevelGenBside_ok_of_tree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg9p_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nsafeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ModelX2MXC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib4Spec;AsanHandoff7atop_ofC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMain2TAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA<nodesA_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoffDequiv_PA_asan_toP_LLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7EquivPA3toPC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel;tree_tracesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC47Corelib4Init5Logic3notC59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA7ptracesC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses8symmetryC47Corelib4Init5Logic3iffK59OSSVerify5KrLib2AS7SpinAlg9srealizes03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoff<a_space_beg0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoff<a_ptr_array0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanHandoff7resv_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps8aps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5ProgA:progA_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA8tree_atAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA?implF_srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps:AAllocAsanC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nstepAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA5minvAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nexitAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg9a_init_pcC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA3alwC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib7Classes?RelationClasses=iff_SymmetricC59OSSVerify5KrLib4Spec7EquivPA9toP_validC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMain=plain_side_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesc49OSSVerify5KrLib8AsanMain2TPC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC4ELinuxProcessSemantics?LinuxProcessSem3RunAreaches_error_cfgI4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_cfg00C4ELinuxProcessSemantics?LinuxProcessSem3RunEreaches_unmodeled_cfgK4ELinuxProcessSemantics?LinuxProcessSem3Run8behavior01C59OSSVerify5KrLib3Lib3CfgAobs_trace_cfg_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA;TopLevelGen?run_init_configC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMain=amain_at_openC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib8AsanMainCasan_main_srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry<asan_side_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run8behavior00c49OSSVerify5KrLib8AsanMain9asan_sideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7EquivPA:equiv_PP_LC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:TopLevelSB@side_ok_equiv_sbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceFsanitizer_source_limitC59OSSVerify5KrLib4Spec8ImgFacts6lim_sbC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition plain_tree_ok_stmt : Prop :=
  forall L, 2^31 <= L ->
  tree_ok psegs p_init_pc p_phdrs L
          (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).

(* [comment removed for export] *)
Definition TA (L : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp (toP en)) (mo0 psegs L (toP en) inp).

(* [comment removed for export] *)
Definition TP (L : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs L en inp).

Lemma plain_no_kill : forall L, tfam_no_kill (TP L).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMain ()) [] "h01Lp;1p;2p;4p-1R0p10000p4p710p9P0p1000\p4p710R0p9p1001:p4p70P0p8g001hj12Tg002`j21Tg003Sj40Tg004Zg0058#2g005XR0f0g006M,10C0W0o"). Qed.

(* [comment removed for export] *)
Definition amodelH (V : nat -> Z) (sp : word) fs (mo : Model) : Prop :=
  LIMIT34 <= vm_limit (m_vmmaps mo) /\ amodelL (vm_limit (m_vmmaps mo)) V sp fs mo.

Lemma amodelH_of_amodelL : forall lim V sp fs mo, LIMIT34 <= lim -> amodelL lim V sp fs mo -> amodelH V sp fs mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMain ()) [] "h02HLh12HMh21Vh32fsh43limh52moh62sph71zp;1p;2p;5p;4p;6g007Hj10Tg007mj1;Tg008Kj14Tg008nj21Tg009Jj52Tg00:Ej2:Tg00:`j49Tg00;;j15Tg00<2j16Tg00<ij67Tg000\j63Tg00=dj48Tg004ZR0g00>YP0[g00?8#0#0#0#0#0#0#;#4g001:g00?]g00@SR1f4R2'1f5R3P2f3R4f2R5f1R6D2P0f6R7f0R8,11P8P7P3P2P4D2':X701117P7P3P2P4P5D2P6P8C9%55#6P7P3P2P4P5P8E7E3P3P2P4P5C8eW1W0W5W3W6W2W4o"). Qed.

Lemma amodelH_of_amodel : forall V sp fs mo, amodel V sp fs mo -> amodelH V sp fs mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMain ()) [] "h02HMh11Vh22fsh32moh42sph51zp;1p;4p;2p;6p;5p;7g007Hj10Tg007mj17Tg008Kj12Tg00ALj41Tg008nj26Tg00BFj65Tg00Bbj53Tg00Cbj74Tg00>Yg004ZR0[g00?8#0#0#0#0#0#0#7#2g001:g00?]f3R1f2R2f1R3f0R4C1g00DbR5f4R6P1P2P3P0g00Ecg00@S/64X50g00FZP5g00G\E5P6P1P2P3P4D3F4W0W3W2W4W1o"). Qed.

(* [comment removed for export] *)
Definition amain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 696%nat)) (Z_to_bv 64 (V 697%nat)) (Z_to_bv 64 (V 698%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 699%nat)) (Z_to_bv 64 (V 700%nat)) (Z_to_bv 64 (V 701%nat)) (Z_to_bv 64 (V 702%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 703%nat)) (Z_to_bv 64 (V 704%nat)) (Z_to_bv 64 (V 705%nat)) (Z_to_bv 64 (V 706%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom asegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv asegs m
    /\ stk asegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodelH V (en_sp en) (in_fs inp) mo.

Lemma amain_atL_open : forall lim en inp ms mo, LIMIT34 <= lim ->
  amain_atL lim en inp ms mo -> exists w V m, amain_open en inp w V m ms mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMain ()) [] "p'0h01ah11mh21Vh31wh41Hh51nh62H1h73H10h82H2h92H3h:2H4h;2H5h<2H6h=2H7h>2H8h?2H9h@2HLhA2enhB3inphC3limhD2mohE2msi001xp%0p&0p;2p;5p;1p;Op;3p;7p;4p;8g008nk20:Tg00HVk50QTg007Hj1:Tg007mj1qTg008Kk109Tg00IQk10ITg00J3j20Tg00JYj16Tg00KKj25Tg00L5k106Tg00LZj1DTg00M8j11Tg00MWk10HTg00N7j1;Tg00NmlOPTg00O_k20FTg00PQk10ETg00Q3k10CTg00Qlk20ATg00RIj2^Tg00Rfj1=Tg00S\k10;Tg00T<j1pTg00U>j1nTg00V9j1fTg00W<j37Tg00X8k10KTg00Xgj1NTg00Y\j1LTg00ZSj33Tg00Zmj2ZTg00[gS00j24Tg00\Aj7>Tg00]9j2JTg00]Vj1bTg00^Jj1jTg00=dk40BTg00:ER0j22Tg00Cbk70@Tg00:`j4uTg00_>j4tTg00_Xj2eTg00`5j2_Tg00`Rj2\Tg00a2j1]Tg00aRk70>Tg00bDk20=Tg00b`k20DTg00cVk10<Tg00dIj4}Tg00dek207Tg00eEj3|Tg00f@j3MTg00f]j3KTg00g>j2sTg00h2j4oTg00hdj8lTg009Jj5rTf0R1#:#:p=v%:1#:#:#:p=~f2R2f1R3/e1'0p=R%11#1p>0N%11#1#1#1p>0L%11#1#1#1#1#1#1#1p>0J%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=81_31,02p=Q1\31#]p=Cf4R4f3R51^23'_/_1'0p=E%:1#:#:#:#:#:#:#:p=Ug00i^S01f7R6f6R7f5R8P4P5P2P3P1K0>33p=Fg00jeR900:220=31'2p=S1^52/_3/_1p>0?g004ZR:%N5,54738%L1,5393:2'2p=H20D7893:6&0<2,55/J393:4/21'2p=AP4P5P2P3C},\8#]93:7/21p=@P5g00kCR;P2P3C},\4#]93:8/21p=IA3:67A3:841\23#]93:5/21'2'2p=[20752/J393:4/21p=9g00kbR<?|31p>0Pg00lWR=g00mQR>=M=17K3p>0Og00nUR?g00oOR@=M?17K3p>0M1s<1p=mP<P51e23P1Cop=Og010TRAP7P8P4P5P2%b3P1Glp=kP4P5P2%j3P1Dr,28,27p>081231,22,25,24p=`1J5293:4/23/21p=X1231,22p=Yg011KRB/41p=BA3:45153193:2'2p=iPA%67%;8%=4%N5%L2%b3P1Glp=<P4P5P2%j3P1Drp=W%f39M?@9K?2/21p>05%p39M=>9K=2/21p>04%=1,\3#]p={P2P;P3P1C}p=h1^671^84'_1^52'_=3:3/21p=GA|<84%p59M=>5K=%n2%f39M?@5K?/21'2p=V20723/J1p=cA3:45A3:23/21'2p=aPAP7P8%=4P5P2P3P1Glp>0G1Z78P4P5P2%j3P1Dr'2,26p=?1s<8P<P41e52P3Co/21'2p=T1\84#]93:71\23#]93:5/21'2p=d%p19M=>p=yA|<23=K=1p=w%n6%f79M?@5K?1s<8P<P41e52P3Co/21'2'2p>03%f19M?@p=x%n3=K?1p=zP<P41e52P3Co/21p>02PAP7%;8P4P5P2P3P1Glp>011Z23/21p>00P7P8P4P5P2P3P1CuCup=gg011kg012cQ01g00?]g00@S00:4P8P4P5P2P3I0QQ00PBg00>YRAP:[R?g00?8R@#:R=#vR>#:RC#:RD#:RE#qRF$09RG%q>$09RH$0IRI[RJP7g013],0FRKf8RL#6RM,5FRN&06@#~R@#DRO5RFg014R,0FRPg015G,0FRQP3%1;RR#1RS#1RT#1RU#1RV#1RW#1RX#1RY#1RZ#1R[$0N$0L$0J#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8#8R\O1,0FS02P3%1\R]O1,0FS03P3%1]R^O1,0FS04%D>R>9QFNR_&0HHR`%;6Ra'CRb,0FRcPcP_PFPNP>Pb%DCRCDER_%:@#U#U#U#U#U#U#U#D,0FR@P3%1^RcO1,0FS05P3%1cRdO1,0FS06P3%1dReO1,0FS07P3%1eRfO1,0FS08g016<,0FRgP_10F9R_P_P_P_P_P_P_P_P3%1fRhO1,0FS09P3%1hRiO1,0FS0:P3%1iRjO1,0FS0;P3%1jRkO1,0FS0<MOP&06=#q00FGRlPg%qD/09R9&0EGRGP1&0C<R<GFP2P1O1RD%D=%DE+0AR=7SD^5ARDP3P;O1RmPN%vE#~RE#:#vRn#DRoP3PWO1RpPN%DEREPCP3P[O1RqPNPoPEPoPm1^Eq1^CpH0?S0=PNP3PRO1S0>PbP3PSO1S0?P`%=6P3PTO1S0@PHP`Pa&0;HRbP3PXO1S0APHP`PRPaPbP3PUO1S0BPLP6P3PVO1S0CPFPLPEP3PYO1RaPFP6P3PZO1RrPFP6EHGAF@EIG[D9D920P31Rs%p2+0OS0D%n3Rt%f2+0MS0E%m1RuP1PN%Un#DRnPNCOf9RN?7L1P2&0K3RvO1Rwf:Rx#6Ry%;NRz%=NS0F%NNR{%LNS0GPxPvFk53I[^0:1Z31R|PNP3PMP6P8K08D`DX3YX1J'4X2?'4X3BPNPLP2P3P1P6P7F>X1J,4JX2?,4?X3B#BP1PLPK15FyRM=RFOPPPQQ02Q03Q04AQFM>S0H1C`zR},0FR~P~Q0HPFPMP>P}PCDER~P@Q05Q06Q07Q08PgP~P_P_P_P_P_P_P_P_Q09Q0:Q0;Q0<MOPPlPgP9PGP1P<GFPmPMPoPpPMPEPCPqPMPoPEQ0=PMQ0>P}Q0?P`Q0FQ0@PHP`PzPbQ0APHP`PRPzPbQ0BPxPNQ0CPFPxPEPa15F{PrPFQ0GDiGAF@EIG[D9D9Q0DQ0EPuP1PMPnPMCOf;RM?7x1f<R{PMPMPMPMP{PvF<93Iw[^0:P|PMP3PyPNP6K08D`DX7YDX1J,4JX2?,4?Q00P?PNPK%6MS0E,5FRy=RFOPPPQQ02Q03Q04AQFy>S0D%;xRz,C`R},0FR~P~Q0DPFPyP>P}PCDER~P@Q05Q06Q07Q08PgP~P_P_P_P_P_P_P_P_Q09Q0:Q0;Q0<MOPPlPgP9PGP1P<GFPmPyPoPpPyPEPCPqPyPoPEQ0=PyQ0>P}Q0?P`%=xQ0@PHP`PzPbQ0APHP`PRPzPbQ0BPMPxQ0CPFPMPEPaPFPxPrPFPxEHGAF@EIG[D9D9PuP1PyPnPyCOA7{M1f=Ry#6Rz%;{R}%={S0D%N{S0G%L{S0FPyPvFk93Iw[^0:P|P{P3Q0EPxPLDWD`:05t5:04s5DX7YDX1J,4JX2?PyP{P2P3P1PMPxF>X1J,4JX2?,4?X3B#BP1PMPK15FzR~=RFOPPPQQ02Q03Q04AQF~>S041C`}S03,0FS02Q02Q04PFP~P>Q03PCDES04P@Q05Q06Q07Q08PgQ04P_P_P_P_P_P_P_P_Q09Q0:Q0;Q0<MOPPlPgP9PGP1P<GFPmP~PoPpP~PEPCPqP~PoPEQ0=P~Q0>Q03Q0?P`Q0DQ0@PHP`P}PbQ0APHP`PRP}PbQ0BPyP{Q0CPFPyPEPaQ0G,5FPrPFQ0FDiGAF@EIG[D9D9PuP1P~PnP~COf>R~?7y1f?RrP~P~P~P~PrPvF<93Iw[^0:P|P~P3PzP{PxDWD`:05t8:04s8DX7YDX1J,4JQ00PJP{PK%6~RD,5FRs=RFOPPPQP2P\O1,0FP2P]O1,0FP2P^O1,0FAQFs>Rt%;yRz,C`R|,0FRaPaPtPFPsP>P|PCDERtP@P2PcO1,0FP2PdO1,0FP2PeO1,0FP2PfO1,0FPgPtP_P_P_P_P_P_P_P_P2PhO1,0FP2PiO1,0FP2PjO1,0FP2PkO1,0FMOPPlPgP9PGP1P<GFP5P1O1Rt?St=^5AP2P;O1RtPsPoP2PWO1RaPsPEPCP2P[O1R}PsPoPEPoPtPEP}PCPaPsP2PRO1P|P2PSO11{`yP2PTO1PHAh`zbP2PXO1PHP`PRPzPbP2PUO1P~PyP2PVO1PFP~PEP2PYO1PFPyP2PZO1PFPyEHGAF@G[GGD9D9P2P1P7P2P7PuP1PsPnPsCOA7r~1f@Rs#6Rz%;rR|%=rRa%NrR}%LrS00PsPvFk93Iw[^0:1Z21PrP2PDPyPMDWD`EVDX3YX1JfARDPsP2P3P1PrP~F>X1J,4JX2?,4?X3B#BP1P~PK15FzRt=RFOPPPQP4P\O1,0FP4P]O1,0FP4P^O1,0FAQFt>Rq1C`|Rp,0FRmPmPqPFPtP>PpPCDERqP@P4PcO1,0FP4PdO1,0FP4PeO1,0FP4PfO1,0FPgPqP_P_P_P_P_P_P_P_P4PhO1,0FP4PiO1,0FP4PjO1,0FP4PkO1,0FMOPPlPgP9PGP1P<GFP8P1O1Rq?Sq=^5AP4P;O1S0FPtPoP4PWO1RqPtPEPCP4P[O1RmPtPoPEPoQ0FPEPmPCPqPtP4PRO1PpP4PSO11C`aP4PTO1PHAh`|bP4PXO1PHP`PRP|PbP4PUO1PsPrP4PVO1PFPsPEP4PYO115F}P4PZO1PFQ00DiGAF@G[GGD9D9P4P1PLP4PLPuP1PtPnPtCOA7Ds1fBRtPDPDPDPDPtPvF<93Iw[^0:1Z41PDP4PzPrPyDWD`EVDX3YP0PrPK%6DRz,5FRw=RFOPPPQP8P\O1,0FP8P]O1,0FP8P^O1,0FAQFw>Ru%;sR},C`R|,0FRaPaPuPFPwP>P|PCDERuP@P8PcO1,0FP8PdO1,0FP8PeO1,0FP8PfO1,0FPgPuP_P_P_P_P_P_P_P_P8PhO1,0FP8PiO1,0FP8PjO1,0FP8PkO1,0FMOPPlPgP9PGP3P<GFP7P1O1Ru?Su=^5AP8P;O1Ru1JwoP8PWO1RaAcwECP8P[O1RpPwPoPEPoPuPEPpPCPaPwP8PRO1P|P8PSO11{`sP8PTO1PHAh`}bP8PXO1PHP`PRP}PbP8PUO1PDPsP8PVO1PFPDPEP8PYO1PFPsP8PZO1PFPsEHGAF@G[GGD9DaP8P3PNP8PNP3P3PwPnPwA7tD1P5PvO1fCRw#6R}%;tR|Pt%Nt%Lt%bwPvK0G53I[^0:P8P3PtP8PzPsP~G?ETEV3YfERzfDRaP2P3P1PwPtF>X1J,4JX2?,4?X3B#BP1PDPK15F}R}=RFOPPPQP6P\O1,0FP6P]O1,0FP6P^O1,0FAQF}>Rp1C`|R|,0FRuPuPpPFP}P>P|PCDER|P@P6PcO1,0FP6PdO1,0FP6PeO1,0FP6PfO1,0FPgP|P_P_P_P_P_P_P_P_P6PhO1,0FP6PiO1,0FP6PjO1,0FP6PkO1,0FMOPPlPgP9PGP5P<GFPNP1O1R5?S5=^5APLP;O1R5%6aR|,5FR}/JoPLPWO1RpAc}ECPLP[O1RuP}PoPEPoP5PEPuPCPpP}PLPRO1P`%;wRpPLPSO1P`%=wPLPTO1PHP`PpPbPLPXO1PHP`PRPpPbPLPUO1PaPwPLPVO1PFPaPEPLPYO1PFPwPLPZO1PFPwEHGAF@EIFdGGD9DaPLP4P{PLP{P4P4P}PnP}A7za1P7PvO1fFR7PzPzPzPzP7PvF<53I[^0:PLP4PzPLP|PwPDG?ETEV3YP0PxP1O1R|?S|=^5APNP;O1R|%6zR4,5FR}PoPNPWO1RpP}PEPCPNP[O1RuP}PoPEPoP|PEPuPCPpP}PNPRO1P`%;aRpPNPSO1P`%=aPNPTO1PHP`PpPbPNPXO1PHP`PRPpPbPNPUO1PzPaPNPVO1PFPzPEPNPYO1PFPaPNPZO1PFPaEHGAF@EIFdGGD9D9PNP8PyPNPyP8P8P}PnP}A77z1P6PvO1fGR6P7P7P7P7P6PvF<53I[^0:PNP8P7PNP4PaPtG?ETEVDXfIR4fHR}P2P3P1P6P7F>X1J,4JX2?,4?X3B#BP1P{P1O1Rp?Sp=^5AP{P;O1Rp%6}Ru,5FR|PoP{PWO1R5P|PEPCP{P[O1RqP|PoPEPoPpPEPqPCP5P|P{PRO1P`%;6R5P{PSO1P`%=6P{PTO1PHP`P5PbP{PXO1PHP`PRP5PbP{PUO1P}P6P{PVO1PFP}PEP{PYO1PFP6P{PZO1PFP6EHGAF@EIFdGGD9D9P{PLPsP{PsPLPLP|PnP|A74}1PxPvO1fJRxP4P4P4P4PxPvF<53I[^0:P{PLP4P{PuP6PzG?ETEVDXP0PyP;O1Ru%64RL,5FR|/JoPyPWO1R5Ac|ECPyP[O1RqP|PoPEPoPuPEPqPCP5P|PyPRO1P`%;}R5PyPSO1P`%=}PyPTO1PHP`P5PbPyPXO1PHP`PRP5PbPyPUO1P4P}PyPVO1PFP4PEPyPYO1PFP}PyPZO1PFP}EHGAF@EIFdGGD9DaPyPNPDPyPDPNPNP|PnP|A7x41PMPvO1fKRM#6R|%;xR5%=xS00%NxRq%LxS0FPMPvFk53I[^0:PyPNPxPyPLP}P7G?ETEVfMRLfLRuP2P3P1PMPxF>X1J,4JX2?,4?X3B#BP1PrP;O1S0G15F|R|/JoPrPWO1RpAc|ECPrP[O1RmP|PoPEPoQ0GPEPmPCPpP|PrPRO1P`P5PrPSO1P`Q00PrPTO1PHP`P5PbPrPXO1PHP`PRP5PbPrPUO1PMPxPrPVO1PFPMPEPrPYO115FqPrPZO1PFQ0FDiGAF@EIFdGGD9DaPsP{PaPsPaP{P{%6uRq,5FR5PnP5A7Lu1P~PvO1fNR~PLPLPLPLP~PvF<53I[^0:PsP{PLPsPqPMP4G?ETEVP0%yz9wDyPDPzPyPy%6LRq,5FR{PnP{A7~L1PrPvO1fOR{P~P~P~P~P{PvF<53I[^0:PDPyP~PDPqPuPxG?L03fQRqfPR5P2P3P1P{P~F>X1J,4JX2?,4?X3B#BP1%y69wwrPaP}PsPs%65Rr,5FR|PnP|A7q51PtPvO1fRRtPqPqPqPqPtPvF<53I[^0:PaPsPqPaPrP{PLG?L03P0%x4,zzPDPD%6qRr,5FRsPnPsA7tq1PwPvO1fSRwPtPtPtPtPwPvF<53I[^0:PzPDPtPzPrP5P~G?ETfURrfTRsP2P3P1PwPtF>X1J,4JX2?,4?X3B#BP1%xM,z6PaPa%6sR|,5FRpPnPpA7rs1P7PvO1fVR7PrPrPrPrP7PvF<53I[^0:P}PaPrP}P|PwPqG?ETP0%mzPz%6rR|,5FRaPnPaA77r1P6PvO1fWRaP7P7P7P7PaPvF<53I[^0:P4PzP7P4P|PsPtG?I02fYRtfXR|P2P3P1PaP7F>X1J,4JX2?,4?X3B#BP1%m6P}%6|R6,5FRpPnPpA7t|1PxPvO1fZRxPtPtPtPtPxPvF<53I[^0:PuP}PtPuP6PaPrG?I02P0P4%6tR6,5FR}PnP}COA7xt1PMPvO1f[R}#6RpPx%=x%Nx%Lx%b}PvK0153I[^0:PLP4PxPLP6P|P7G?f]R7f\R6P2P3P1P}PxF>X1J,4JX2?,4?X3B#BP1PM15FpRpPnPpCOA7761P~PvO1f^R~P7P7P7P7P~PvF<53I[^0:P5PuP7P5%66P}PtG?P0A7~71P{PvO1f_R{P~P~P~P~P{PvF<53I[^0:P~Pq%67P6PxDW:00qLfaR6f`R}P2P3P1P{P~F>X1J,4JX2?,4?X3B#BP1A7}{1PqPvO1%66RuP}%=}%N}%L}%b6PvK0153I[^0:P6Ps%6}P{P7DW:00s5P01ZrqfbR0PrPuP}P~DWfeR}fdRuP2P3P1fcRsP0F>X1J,4JX2?,4?X3B#BP11ZawP}P|%6uPsP6DWPBfhfgR|P2P3P1ffR2P}F>X1J,4JX2?,4?X3BP7P?P|P2P{P3P1P}PuF>X1J,4JX2?PtPJP2P}P~PxP1PuPsF>X1JPrPsPK%6}RK,5FRs=RFOPPPQPtP\O1,0FPtP]O1,0FPtP^O1,0FAQFs>R^%;uR],C`R\,0FRQPQP^PFPsP>P\PCDER>P@PtPcO1,0FPtPdO1,0FPtPeO1,0FPtPfO1,0FPgP>P_P_P_P_P_P_P_P_PtPhO1,0FPtPiO1,0FPtPjO1,0FPtPkO1,0FMOPPlPgP9PGPrP<GFPxP1O1Rx?Sx=^5ARAPtP;O1R;1JsoPtPWO1RWAcsECPtP[O1R[PsPoPEPoP;PEP[PCPWPsPtPRO1P\PtPSO11{`uPtPTO1PHAh`]bPtPXO1PHP`PRP]PbPtPUO1P}PuPtPVO1PFP}PEPtPYO1PFPuPtPZO1PFPuEHGAF@G[GGD9DaRF%y79wtrRZ%x7,ztR7%mrRYPrPsPnPsCORsA72}1PaPvO1P|P2P2P2P2P|PvF<53I[^0:RI1ZtrRrPtPK%juRuP0H0BRv'2R|'2Ra'2R}'2Rn'2RE'2RV'2RU'2PqPAPUPLPFPVP4PZPEPzP7PnPDPYP}PyPsPaPNPIP|P8PrPvP3P2PtPKPuP0P6P1K0@CuFgFgFgFgCtCtCtW7W?P3P1O2n2001000000121000000W4W>P3P1O2n2001000000121000000W4W=P3P1O2n2001000000121000000W4W<P3P1O2n2001000000121000000W4W;P3P1O2n2001000000121000000W4W:P3P1O2n2001000000121000000W4W9P3P1O2n2101000000121000000W4W8P3P1O2n2011000000121000000W4W6P3P1O2n2111000000121000000W4X1JP3P1O2n2011000000121100000W4X2?P3P1O2n2011000000121100000W4X3BP3P1O2n2011000000121100000W4W@WDWEWBWAXC:o"). Qed.

Lemma amain_at_open : forall en inp ms mo,
  amain_at en inp ms mo -> exists w V m, amain_open en inp w V m ms mo.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMain ()) [] "h02HMh12enh23inph32moh42msh51zp;4p;2p;6p;5p;7g0173j44Tg008nj23Tg00BFj60Tg017mj51Tg0191j72Tg011kg012cg00i^g00?]f3R0f2R1f1R2f0R3C4g00DbR4f4R5P0P1P2g004ZR6g00Ecg00@S/33X56g00FZP4g00G\E0P5P0P1P2P3D1F2W0W3W4W2W1o"). Qed.

(* [comment removed for export] *)
Definition asan_impl_stmt (rsA : Z) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
    amain_open en inp w V m ms mo ->
    exists NMAX RNG A Q,
      tree_atA asegs (at_nodeA asegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
        (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
        Q ms (MX mo []) mo.

Section Assembly.
  Variable rsA : Z.
  Hypothesis plain_ok : plain_tree_ok_stmt.   (* [comment removed for export] *)
  Hypothesis asan_impl : asan_impl_stmt rsA.

  Lemma plain_side_ok : forall L, 2^31 <= L -> side_ok psegs p_init_pc p_phdrs L (TP L).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMain ()) ["Assembly"] "h02HLh11Lp;1p;2p;8g007Hj18Tg00LZj11Tg00L5j10Tg00Qlj22Tg008nj27Tg001hj16Tg002`j24Tg019mj23Tg01:aj85Tg004Zg00?8R0#8#1%00#0#0#0#1'2f0R0'7g0058R1#6g005XR2g01;ig01<bf1R3g006M,42g00i^g01=YUV1,31p,8plain_okP3P0O2G5W0W1o"). Qed.

  (* [comment removed for export] *)
  Lemma asan_main_srealizes : forall L, 2^31 <= L -> forall en inp,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
    forall ms mo, (exists w V m, amain_open en inp w V m ms mo) -> SpinAlg.srealizes asegs (mkCfg ms mo) (TA L inp en).
Proof.
    intros L HL en inp Hv Hi ms mo (w & V & m & HM).
    pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & [HLIM HMOD]).
    apply Forall_app in HP as [HP _].
    destruct (asan_impl en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT).
    eapply SpinAlg.srz_conseq.
    + exact (implF_srealizes asegs (at_nodeA asegs) nstepA nexitA minvA (nsafeA NMAX) fstepS NMAX (nodesA_sound asegs NMAX) _ RNG A Q ms (MX mo []) mo HT).
    +
      destruct (equiv_PA_asan_toP_LL (vm_limit (m_vmmaps mo)) HLIM L HL PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
      intros tr. unfold TA. symmetry. apply HEQ.
  Qed.

  Lemma asan_side : forall L, 2^31 <= L -> side_ok asegs a_init_pc a_phdrs target_alloc_limit (TA L).
Proof.
    intros L HL. apply asan_side_ok. intros en inp Hv Hi. split.
    -
      destruct (plain_side_ok L HL (toP en) inp (toP_valid _ _ _ en inp Hv) Hi) as [Htr _].
      apply Htr. rewrite run_init_config. cbn [bh_traces]. apply obs_trace_cfg_nil.
    - intros ms mo HM. apply amain_at_open in HM. exact (asan_main_srealizes L HL en inp Hv Hi ms mo HM).
  Qed.

  (* [comment removed for export] *)
  Theorem base_asan :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage asegs a_init_pc a_phdrs).
  (* [comment removed for export] *)
  Proof.
    eapply (side_ok_equiv_sb _ _ _ _ _ _ (TP sanitizer_source_limit) (TA sanitizer_source_limit));
      [exact (plain_side_ok _ lim_sb) | exact (asan_side _ lim_sb) |].
    intros enS enT inp HvS HvT Hi. unfold TP, TA.
    apply (equiv_PP_L _ lim_sb); [exact HvS | exact (toP_valid _ _ _ enT inp HvT) | exact Hi].
  Qed.
End Assembly.
