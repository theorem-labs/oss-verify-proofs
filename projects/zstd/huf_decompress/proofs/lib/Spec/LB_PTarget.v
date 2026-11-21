(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (22 recorded proofs replaced by written proofs (malok_amb0, Q_fds, malloc_Q and 19 more); Q_fds and Qamb_fds take a new premise that the kernel build is unchanged (m_kernel mo' = m_kernel mo); Qamb_Qrun, malloc_Qamb and run_Q bound Pamb by Pcap with Pamb_le_Pcap, zstd_frame_info's proofs). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe Malloc KStep MI_Inv MI_Cnt Stdio Harness Adapter Driver PState Prog StepB TargetSafe
  LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PCaps LB_Hist LB_PAmb LB_PStdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Keeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_LB_PTarget () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Adapter9run_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness;fuzz_mallocC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Driver7IOStyle00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic9etwl_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5MSafe4assnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic6mspecLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib4Spec8LB_Logic:mspecL_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic9mspecL_ifC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_pureC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List6Exists00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec7LB_Hist4AMBZC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec7LB_Hist:amb_countsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw3LRXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw4n63XC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw4R63XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget5malokC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Inv3PHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_PAmb8PHI_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib4Spec5KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw;bigb_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_StmtA4bigbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw5ROOMXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_PAmb:validc_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_PAmb6validcC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8LB_PCaps8PHI_PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4RBIGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw7LBUDGETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec8LB_StmtA4NREQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_PCaps4AMBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_PAmb9validc_63C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6SMALLXC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List6filterC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:fold_rightC46Stdlib5Lists4List?Forall_cons_iffC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib4Spec7LB_Hist8LRX_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Hist9n63X_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw9R63X_consC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec:LB_PTarget<small_countsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Hist7LRX_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Hist8n63X_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Hist8R63X_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib4Spec8LB_PCaps;PHI_Pcap_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw7QI_minvC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib4Spec6LB_Raw6QI_fdsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw7QI_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw9QI_set_soC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw7QI_permC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6LB_Raw2QIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Alloc=raw_malloc_LQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget1QC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Alloc;raw_free_LQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8raw_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic;mspecL_munrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes9Empty_set00C59OSSVerify5KrLib4Spec4Prog;new_handlerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6Q_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget4Q_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9LB_PStdio8s_emit_LC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver7io_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog2ioC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib4Spec:LB_PTarget8malloc_QC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget=new_handler_QC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6olistQC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6free_QC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness8free_optC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Hist9AMBZ_consC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkappK47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=dt_size_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness?dbuf_size_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget=fuzz_malloc_QC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib4Spec:LB_PTarget9malok_hufC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget=SMALLX_olistQC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib4Spec:LB_PTarget:free_opt_QC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationHPermutation_app_swap_appc59OSSVerify5KrLib4Spec:LB_PTarget6Q_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog8fuzz_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic:mspecL_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=PRODUCER_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9WKSP_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=WKSP_SIZE_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Driver9MAX_INPUTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness8BUFF_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness<BUFF_MAX_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget:fuzz_one_QC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6emit_QC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib4Spec:LB_PTarget:malok_amb0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget;run_calls_QC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog3runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_Hist8AMBZ_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget4QambC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_PAmb4PambC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec7LB_PAmb<Pamb_le_PcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7LB_PAmb8Pamb_ambC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget4QrunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib4Spec8LB_Logic4liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState9set_so_psC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6malokAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8LB_Logic4etwlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget6run_QPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:LB_PTarget9Qamb_QrunC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TARGETP.
Variable P : Z -> Z.
Hypothesis HPc : forall c, P c <= Pcap c.
Hypothesis HP8 : forall c, validc c = true -> AMBC <= P c.

(* [comment removed for export] *)
Definition malok (X : list (bptr * Z)) (n : Z) : Prop := ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET /\ n <= NREQ.

(* [comment removed for export] *)
Lemma malok_amb0 : forall n A, AMBZ A -> (length A <= 3)%nat -> 0 <= n <= 24 * 2^24 + 12 -> malok A n.
Proof.
  intros n A HA HL Hn.
  destruct (amb_counts A HA) as (A1 & A2 & A3). pose proof PHI_Pcap as HPh. unfold RBIG, W in HPh. pose proof (PHI_mono P Pcap HPc) as PM.
  assert (Hbb : bigb n <= 24 * 2^24 + 8192).
  { unfold bigb. destruct (_ <=? _); [|pose proof (bigb_nonneg n); lia]. rewrite round_up_pg_eq. unfold page_round_up_Z, page_size, IB, UNIT.
    pose proof (Z.div_mod (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 4 + 16 + 4096 - 1) 4096 ltac:(lia)). nia. }
  split; [| split; [unfold LBUDGET in *; lia| unfold NREQ; lia]].   (* [comment removed for export] *)
  split.
  - intros Hsmall. pose proof (validc_cls n ltac:(lia)) as Vc. specialize (A1 (size_to_class n)). specialize (HP8 _ Vc). unfold AMBC in *. lia.
  - intros Hbig. specialize (HP8 63 validc_63). unfold AMBC in *. lia.
Qed.

(* [comment removed for export] *)
Definition SMALLX (S : list (bptr * Z)) : Prop := Forall (fun b => 0 <= snd b < MMAP_THRESHOLD) S.

Lemma small_counts : forall S, SMALLX S -> (forall c, LRX S c <= Z.of_nat (length S)) /\ n63X S = 0 /\ R63X S = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "p'0h01ch14__x1h27__arithh34__ffh48__varmaph55__with64__x2h72HSh81ah91bi001bh:1Hh;1Sh<1lh=2xbh>1zi011zh?1Ah@2A1hA1PhB4__p1hC4cstrhD1xhE1yhF2A2hG2A3hH2HnhI2IHhJ2NBhK1nhL1pi021pp&0p;2p;1p;3p;4p;5p;6p;7p;8g00C9R0k205Tg00CYj1UTg01KNj1FTg00UIj1\Tg00R7j1ATg00Hgj21Tg00ZPj34Tg00ICR1j20Tg00Uij1fTg00VGj1bTg00Vek104Tg00WPj2`Tg00YBk201Tg00RWj2~Tg00Ydj2vTg00Zjj3tTg00[Ij4qTg012dj4GTg00O`j27Tg01LIj1NTg0102j1STg01Lgj2OTg01MDj2MTg01Mbj3WTg00HJR2j22Tg00P=j1VTg01N=j4eTg01NYj5dTg00hAj3;Tg0000j38Tg01O8k403Tg00_bj2>Tg00KNj1=Tg00A_j2JTg01O\j1ETg00JZj2BTg00LCj1CTg01P:k200Tg00haj2[Tg015Nj4}Tg015lj6zTg00iaj2ZTg00FMj1uTg00X3j4PTg016Pj7sTg00i?j1rTg00G2j1pTg00SXj1oTg017Xj3RTg01PZj4nTg008lj6@Tg00eAj1mTg00e_j2lTg00Doj1XTg00cFj2YTg00f@j3kTg014ej3wTg00fij2xTg01QTj3jTg00nEj1iTg01ROj3yTg01SIj1hTg00A=j5{Tg014Aj7|Tg01Smj3gTg01TJj4_Tg0174k802Tf3R3f2R4'Bf1R5f0R6'J#A'1p=6g0198R7%=5g018;R834%C6=478'0,04p=:A4768p=3P7P5g01<7P6CPp=LP5g01:8R9g01:WR:P:g01;7R;P6g01;WF|p=9P7P5g01ERP6CPp=Qg00:;R<?g76p=D1J56#Ap=<1056,04p=c1B45/16p=aP<P7P4P5C_=;36p=51186p=?P<P7P5P6C_p=T%C6=478p=KA4758/06p=^%=6=478p=]g01BBR=g01TjR>746p=IP3P9P:P:P;P4P5P6L02p=H205<7R?#UR@P?%F6P4P6P?P4C6^07?:55[RAX;@%\?RB#Fg01<^RC#ARD/1D^07%3DRDA4788RE'0g01DfRF#\RG%UFRH%f7RI%b7RJ&047RK1`78RL/LL'9201K;RMP6P4g01F9RN,~=1v64=4=NdAt785CqRNb3b4b51188P6b2X07PDPEPGPHPIPJ1QLL,9KPMPNb3b4b5PEP6b2REPECGCGg01ACRE%D6RD'7RO#N%SD/O5'MX=?=W?B,<?1<?BRP'1^07POX=?=W?B,<?#3P7P7P2P8P?P7P=P7POg01BbRO,2Dg01CUR2'2#VP8n0100000020000X=?PBCeDd#33ceAaB6P^07?:BBeW7P0P<P7A;?45#Ff4R0=;?3RBP6P?PBC6^07A;?34RB;:B[\A^<@P6P?P3P4P5C5#Fg00B\p4p710RBp-0RP\6RQ%U4RRP1A;3569834P3P4O1A8035'0[RSP4P5O1A8346'0A;0459803RT[P0P3O1f5RU?804'0\TP3P4P5P6H03P5n2001000000120000000W<X85WAW?PS^<R^85^AQ^?BP6P?%?D1>DE'0X9?RD1TU0RBP3P5O5%DBRB#?1>BE'0A8?D3'0P1f6RB/TU#DRQ#?1>QE'0A8?D0f8RQf7RR'TRS=;?BRTP6P?PTC6^07P?PRPBPUC5RU;:UP6%DSRS#?1>SE'0A8?DRPRP6O1RRf9RDP6P?PDC6^07?:QQP1f:RQP6P?PQC6^07%=D%KD'^P?f=RDf<RSf;RUC5RBP6P?PBC6^07P?PSPUPQC5RQ;:QP6PSP6P?PSC6^07%=S%KS'^P1%]D%KDP?fARDf@RQf?RUC5RBP6P?PBC6^07P?PQPUf>C5RB;:BP6%]U%KQP71J?DRQ#A#EP?fERUfDRBfCRTC5/B6RV/15^07P?PBPTfBRWC5RX#=RY#3RZ%CXR[#3R\'0R]'0X>7P11756#I1>54R1[1>65R^1745#I[R_1734#I\120056P6n2001000000120000000XE7XD7P_^E7^D7P6PEPTPGPHP71[74P5PIC}RIPJPKPKP9P:P:P;PKP9P:P:P;P0EzP7g01==R;,Z7R9g01G6%u;,Z7R_CP,9KR`Fs%r:R:P`CHPMPNb3b4b5X17X67XBP104^P1[^17^67^BPP6%?BPEPBPSO4b2O3b:17EW#I1<?TRS#E,1V^07P]P7P=P717EB#N%SB/O6'M%p;R]P8n01000000200001BT6RP'21<?B#E,16X>7PR11PS17EU#N%SU/O5'MP=P=P=P7P6P]P8n0100000020000RPfFRS/B3'21<?S#E'1P61J?URS#oRR%AS#?RSPGPHPIPJPK1L9_,9KR1P:1`7]R^=R79AR7_^R^'L,9KCHPMPNb3b4b5X17X671165R_12]5124]R`'1[^17^67P6fGRa,<?1Ba0P3O3Rab2bCPRPSPGPHPIPJPKP1P:AR7L9R1/L^,9KCHPMPNb3b4b5X17X671285R^/1`\_^17^67Pab2bCn0110000020000b9b@PVPUPBPTP6CnE@X07PZP\P7P=P717ETREP]P8n0100000020000%=W'2%36R]X>7R\P=P>%=TRZ,2P#3X9=%m;,l7%XC,Y75k71Y7C5w7g01H9'x=;FGPH1[75PJPK1Q9L,9KP:1Q1L,9KCHPMPNb3b4b5X17RN%3^\]^17R]P6PZP3O2b2PEP6E@PYAjBTWE@P7%iT%CW'2RYP\P=P>P=P7P612BO/22#VP8n0100000020000%CTR8'2#3X9=PNP]P6P8P4O2b2PEP6E@%3YeP[AyBTWE@CGCGbJ%XQ#A%hQE@PXP6P?PXC6^07P?PTPWPDC5RD;:DeWGWFP5P6O2n2001000000121000000W:W@P5P6O2n2001000000121000000b8W7WHP5P6O2n2001000000121000000b7b:W7XIAX;@XK7XL<P5P6O2n2001102000121100101X8?P6D{W;o"). Qed.

Lemma malok_huf : forall n A S, AMBZ A -> (length A <= 2)%nat -> SMALLX S -> (length S <= 3)%nat -> 0 <= n <= NREQ ->
  malok (S ++ A) n.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "p'0h02Hah14__x1h24__x2h33HL0h44HLS0h57__arithh64__ffh77__sat10h87__sat11h97__sat12h:6__sat9h;8__varmaph<5__with=4__x3h>4cstrh?5cstr0h@4__x4hA1chB1zhC1HhD4__p1hE7__sat13hF7__sat14hG2A1hH3HP8hI2PMhJ2S1hK7__sat15hL7__sat16hM1ahN1AhO2A2hP2A3hQ2H0hR2H1hS2H2hT2H3hU2H4hV2H5hW2H6hX2HAhY2HLhZ3HLSh[3HPhh\2HSh]3Hbbh^4Hbigh_2Hnh`6Hsmallha1Shb2S2hc2S3hd2Vche7__sat17hf7__sat18hg1bi001bhh1np%0p&0p;2p;1p;3p;6p;4p;<p;7p;8g00C9k20WTg00CYj1wTg00D9k10CTg00A_j25Tg00Doj1cTg00ENR0j2lTg01KNk10ITg00HgR1j20Tg00ICR2j24Tg00I^k204Tg00Ehj18Tg00G2j19Tg00KNj17Tg00LCj1<Tg00FMj13Tg00GPj2WTg00HJj22Tg00Gmj2STg00B?j3JTg00M8j2^Tg01UJk20?Tg00R7R3j1;Tg00N2j1qTg00Nfk307Tg00O`k206Tg00P=j1mTg00Q9k102Tg00SXj1ITg00T=j2YTg00Tej3ZTg00UIk10VTg00Uik10UTg00VGk10TTg00Vek10STg00WPj2vTg00X^k60QTg00YBk20PTg00RWj2uTg00Ydk20OTg00ZPj3LTg00Zjk30NTg00[Ik40MTg00\;k30Lk20GTg00\\j2OTg00]9j2ETg00]Yj2sTg00^Jj2rTg00X3j4VTg00_;k30Hk20ETg00_bj2GTg00`>k10FTg00`Wk20BTg00a>k20ATg00adk20@Tg00bJk20>Tg00cFj2XTg00eAk10<Tg00e_k20;Tg00f@k30:Tg00fij2hTg00hAj3dTg00haj2eTg00i?k109Tg00iaj2TTg00jDj3nTg00jgj3fTg00lKk108Tg008lj6\Tg00mIk105Tg00nEj1UTg00kJj1bTg00khj3]Tg008Pk603Tg00o<k30=Tg0102j1PTg00JZj2MTg0110k201Tg011lk10DTg01VKk300Tg01WDj2~Tg012dj4jTg013?j2tTg01X>j2}Tg01Y8j3|Tg013\m<0JTg00S1k40KTg014Aj7kTg014ej3{Tg015Nj4zTg015lj6yTg016Pk70RTg0174j8aTg017Xj3xTg018;R4f0R5'0p=1f2R6f1R7'M/05p=K%35#3p=Ag0198R8?L54p=:1267/05p=>1267/25p=if4R9f3R:'2/26/27/t5p=61u85p=Bg018YP8P0P3P1g019Vf5R1P9P:P6P7P5N<0Jp=@1l9:P6P7P5H0Kp=C1G45p=Q1v85p=FP8P7g01ERP5CVp=`P7g01:8R3g01:WR0P0g01;7R;P5g01;WR<Fkp=_A{875p=RP8P6P7P5Czp=?P6P3P0P0P;P8P7g01<7R=P5CVP<Fkp=HP7P3P0P0P;P5Eyp=oP6P3P0P0P;P7P5K0Rp=[P:P3P0P0P;P6P7P5Gap=gAx875p==f6R>P3P0P0P;P1P9P:P3P0P0P;P6P7P5GaGap=pP8P7P=P5CVp=NP9P3P0P0P;P:P3P0P0P;P6P<FkP7P5Gap=Dg00:;00W8R<#wS00Q00&0C715<6g01<^S01#cS02#cR='l&0I615<:%c=R?'l%1>g01HeR@,0>'4204>9f7RAg01==RB#8RC#9RD7K5^A8%7>/0D%<>%3BRE#9RF%3CRG#8S03#3S04#9RH'WRI%3ES05#3S06#3RJ#A#A#A#ARK#3#9RL'2,SDRM'0'4'4P2f8S07?K5D^A8%7A/0D%<A/0M'4Q079J<Af9S08'^P5f:RN?K5D^A8%7N/0D%<N/0M'4P2f;RO#7/0D%<O/0Mf<S099J<Of=RP'^P5%7P/0Df>RP#<RQ/0M20?POf?RR15<R#;7K5^A8%7P#:%:Q'4'4P2f@RQ15<Q#;7K5^A8%7R#:%<R#:'4fA9J<QfBRP'^P515<P#;9KP5^A8%7P#:%<P#:'4P2fCS0:#7#:Q0:#<#:fDS0;fER25J<fFRP'^P5%72#:%<P#:g01=bg01>]R2#qS0<g01?Tg01@KRS3>p,1PRTp,3HPc8072%qTR2Q0<'0g01ACRUfKRV+06g01BBRWPWPWP8P5fMRXg01BbRYg01CURZ3i#mP4n010000002000012@LR['0P5P8fLR\?iYZRZ$02S0=105[XB8P\Q05#9RY%9JRJ%9KRK%9BR]D6R^fJR_,5<R`P?%;`Ra/0DRbP`Pa%BaP?PD%BDS0>E@PPDCPb15<\RbP=%;bRa/0FR`PbPa%BaS0?P=PF%BFS0@E@fIS0ADCP`%Ib%1afNR`,5<Rc#IS0B%;cRd#1S0C%3GS0D#3#9RG,YFRe%QFRf%1G1WFGRg#Q[[Rh%1FRig01DJRjAZFG7UW0RG%1g\j^0iRg1YFHRk%1H%QI[\fRlAZFH7VjX0iRH%1I\j^0iRmg01DfRn$0VRo%wnRp&0U8Rq&0T8Rr&0S8RsP3P0P0P;%FKR31v84Rt'`,_sJ0QS0E20Ps;R;P5P6g01F9S0F,uW20O56Q0F5LWdB0N847H0MRub6b;b<%:KRvg01FY[S0GP5b5b:b7b8b9b?b>b3b480LK1O^K,SK1E^K'29L8^PXPYPJPKP]D6R^15<VRwP?%;wRx/0DS0HPwPx%BxP?PDQ0>E@fGDCS0IQ0H15<XRxP=%;xRw/0FS0JPxPw%BwS0KP=PFQ0@E@P_DCS0LQ0J%IxS0M%1wS0NfOS0O,5<S0P#IS0QQ0P#;R_#1S0RfQRyPYPJPKP]D6Rz/sK%1z%1KRzfSS0SPYPJPKP]D6R{/EK#1[[fRR|PYPJPKP]D6R}/rK%1}S0TfTS0UPYPJPKP]D6S0V/OK#1\z[PePhPGPgPkPlPHPmPoPpPqPrP8Ptg01G6S0WP3CV,_sS0XP;Pub6b;b<%QKR~P5b5b:b7b8b9bEbFb?b>b3b480HK1E^KR^#11G^K'4PbP?10aDS0YPbPaQ0?P?PDQ0>E@fHDCS0?Q0YPcP=10dFS0ZPcPd%BdP=PFQ0@E@PVDCS0[Q0ZQ0BQ0CfPRc,5<Ra#IS0\%;aRb#1S0]1s}KQ0TQ0V/EK#1\z[1r{K%1{fUPYPJPKP]D6/OK#1\z[PePhPGPgPkPlPHPmfXS0TPYPJPKP]D600GK&0FvfYRzPYPJPKP]D6R{1O{K,SK1E{K'25L8[20E{KfZS0VPYPJPKP]D6R{/EKR}#11G}K'4\~20B{K1GK4f[S0^PYPJPKP]D6R{/EKR},GK10}4'4[20A{Kf\S0_PYPJPKP]D6R{/OK#:\v20@{Kf]PYPJPKP]D6R{/EK=L8{\vg01G]20>{KR{eP{p-0R{%c?,X8S0`&0<B-0;81X8?S0a60:8Q02,X8Q01,X8'RS01'R'Rg01H9Rv'h=dnoPp1e89S029?q9??6q1e8:R}7?7PrPsPsQ0X&090R0Q0D,T8R49Hst1os>5[sCgP0PsPsQ0EP01T8CR^%FY'=%FJ'=/=3%F]S0E5n81T8BRB9f83/=4'`,_sCgP0PsAHst^1T8ER49Hs^5[sP0Af8B3%FLR3,=45HsCgFpP;Pub6b;b<X18X28X=8X@8WD%19S0D/41\~Q0GP9PYPJPKP]D61SK6/215L8[Q0D109:'41S:K129L'0[[[^18^28^=8^@8^D{P5f_S0DPYPJPKP]D6R~/EKS0G/GKQ0GQ0DP@1O~KP1P>Q0TO8b5f^PYPJPKP]D6/OK/SK/0[ebWbVbUbTbSbRb:b7b8b9bEbFb?b>b3b4bQbCQ0=/0[e%mZ&08ZE\&05\%U\#1Q0IQ0HQ0LQ0JQ0MQ0NQ0QQ0R%8E#3RE#9RZ,YFS0=%1Z1WFZRK#Q[\fS0TAZFZ7VjX0iS0D%1K\j^0iS0G%8CRC#3#8RZ#9RJ,YFS0X%1J1WFJRY#Q[\fS0bAZFJ7VjX0iS0c%1Y\j^0iS0dPePhPGPgPkPlPHPmPoPpPqPr%FFRJ%bZ5]8%bE9]8J'=/=3S0e9HstP;Pub6b;b<AiYKLS0f#1P5b5b:b7b8b9bEbFbKbLb?b>b3b4%1[ebCn0110000020101bg%UV/0[R[eP[P8Q0<1025XB8P7Q03#8#8#3#A#8#3#8#8#3#8#3#8#3#A#A#A#A#A#9R[g01YSJ03102[AJ<V\RY@0=TX%<YS03,22%UXS0<;>SS0g10X@RY'41GXURKAJ<\XRL%P`RE'MPTPEO17>][10UXS0h%7LPT%8C#8RC#8#9S0iO1RL7>][Q0?Q0YQ0[Q0ZQ0BQ0CQ0\Q0]PePhPGPgPkPlPHPmPoPp1e86S0]??7qPrPsP8PBQ0WP4CV,_sRZP0PsAHstBR~1os95[sP0A[s~ZFpP;Pub6b;b<X18X28XD{1G57%17/4:%161G6:'4[[^18^28^D{P5fWR{/0@PUP{Q08PcO5b5b:b7b8b9b?b>b3b4-01`&0DEQ0F5LWQ0;Q0O#PRWO1AK`WDQ09%PcRWO1AK`Wdp,3HP8RW%PyRdP6O2g01I\REPTPdO1'0P8%P|Rd,Mc1Myd'2RU125]R@PTQ0S#PO1'0XB8PaP?10bDR~PaPb%BbP?PDQ0>E@P\DCP~15<|R|P=%;|R~/0FRbP|P~%B~P=PFQ0@E@Q0ODCPb%I|%1~Q0U,5<R~#I%;~#1PePhPGPgPkPlPHPmQ0`Q0a1X8=Q01'R'RR~'R/hv=dnoS0`PpQ02??9q??6q??7}PrPsPsQ06,T8R|%FDRb'NP0PsPs1NB|P0PsPs1N4bP0PsPsQ06#9R|#F/N^P01=B4Q0E'==Hs^DDDDRaDDDDP;Pub6b;b<X18X28X=8X@810:DRZ107910|11291?>]>[\Z[[^18^28^=8^@8P515<z#;PTQ0^#PRZO1Q0V/MZ1MzZQ07PNPOQ08O8b5b:b7b8b9b?b>b3b4PTPdO19>U]eAJ<cy/MdB00cydE\bHbJbGbdX`KQ0hPWQ0ig01JSO210ELP8%7X%7`'2RE10@LXB8PxP?10wDR@PxPwQ0KP?PDQ0>E@Q0ADCP@Q0PP=10_FR@Q0PP_%B_P=PFQ0@E@P\DCP@Q0QQ0R15<yRy#I%;y#1PePhPGPgPkPlPHPm1h~v=dnoPpQ0]??7}PrPsPs1`BtP0PaDDP;Pub6b;b<X18X28X=8%:5106D10|912:9?>]1[[[^18^28^=8P5PL%7{fV#7PQQ0AQ08O6b5b:b7b8b9b?b>b3b4A>E]LeAJ<X`#71~X`E\bHW^CjQ0gPYP8%<V%<\'2R<1225%U`;>SXB8Q0IQ0HQ0LQ0JQ0MQ0NQ0QQ0RQ0=Q0TQ0DQ0GQ0XQ0bQ0cQ0d%9CR`,YF%1`1WF`RE#Q[\fAZF`7VjX0i%1E\j^0iPePhPGPgPkPlPHPmQ0`PpQ02??6q??7}PrPsPsQ05,T8RrQ0e'NP0PsPs%F[,NBP0PsPs1`4tP0PsPsQ04#b9]8JRt/=39f8b,N^P01=4^,=B/=r%bC9]8J=n8t5HsDDDDDDDDP;Pub6b;b<X18X28X=8X@8Q0f,0:107[%::101M121>,291tEI7>A[[[[^18^28^=8^@8P5Q0_#UQ0^#<Q0V#<P2PQPRQ0:P\O8b5b:b7b8b9bEbFbKbLbebfb?b>b3b4122<Q0<;>SeQ031}V\E\%1X?|YPCjCjbIb]bIb[WcWbP7P5O2n2001000000121000000WCWJP7P5O2n2001000000121000000bMWPWOP7P5O2n2001000000121000000WCWGP7P5O2n2001000000121000000bMW_WZW\WYWXWaWNXh8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bp0 : bptr := ((0%N, 0), 0).
Definition Q (X : list (bptr * Z)) : assn PState := QI X P.
Local Notation mspecL := (mspecL LBUDGET).

Lemma Q_minv X s mo : Q X s mo -> minv mo /\ m_halted mo = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "h01Xh12moh21sp;2p;1p;4g00C9j22Tg00CYj11Tg01ZQj40Tg00:;g0198'2#1R0g01[IR1g01\BR2f2R3p,1Pf1R4f0R5C0X12X21X00P3P4P5O3W1W2W0o"). Qed.
Lemma Q_fds X s mo mo' : Q X s mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> Q X s mo'. Proof. apply QI_fds. Qed.
Lemma Q_live X s mo : Q X s mo -> live mo <= LBUDGET.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "h01Xh12moh21sp;2p;1p;4g00C9j22Tg00CYj11Tg01]oj40Tg00:;g0198'2#1R0g01[IR1g01\BR2f2R3p,1Pf1R4f0R5C0X12X21X00P3P4P5O3W1W2W0o"). Qed.
Lemma Q_so X s mo v : Q X s mo -> Q X (set_so_ps v s) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "h01Xh12moh21sh31vp;2p;1p;5g00C9j22Tg00CYj11Tg01^gj50Tg00:;g0198'2#1R0g01[IR1g01\BR2g01_aR3f3R4p,1Pf2R5f1R6f0R7D0X33X12X21X00P4P5P6P7O4W3W1W2W0o"). Qed.
Lemma Q_perm X Y s mo : Permutation X Y -> Q X s mo -> Q Y s mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "h01Xh11Yh22moh31sp;2p;1p;5g00C9j22Tg00CYj11Tg01`\j50Tg00:;g0198'2#1R0g01[IR1g01\BR2f3R3f2R4p,1Pf1R5f0R6D0X22X31X10X00P3P4P5P6O4W2W3X10W0o"). Qed.

Lemma malloc_Q : forall X n, 0 <= n ->
  mspecL (fun s mo => Q X s mo /\ malok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Q ((p, n) :: X) s mo /\ n < 2^63 | None => Q X s mo end).
Proof. intros X n Hn. unfold Q, malok. eapply mspecL_pre; [apply raw_malloc_LQ; exact Hn|]. intros s mo [H1 (H2 & H3 & H4)]. auto. Qed.

Lemma free_Q : forall X p n, mspecL (Q ((p, n) :: X)) (raw_free p) (fun _ => Q X).
Proof. intros X p n. unfold Q. apply raw_free_LQ. Qed.

Lemma new_handler_Q : forall X (R : Empty_set -> assn PState), mspecL (Q X) new_handler R.
Proof. intros X R. unfold new_handler. apply mspecL_munr. Qed.

Lemma emit_Q : forall X v, mspecL (Q X) (io_emit io v) (fun _ => Q X).
Proof. intros X v. cbn [io io_emit io_S]. apply (s_emit_L LBUDGET (Q X) (Q_live X) (Q_so X)). Qed.

Local Ltac ret_Q := apply mspecL_ret; intros ? ? HH; exact HH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition olistQ (o : option bptr) (n : Z) : list (bptr * Z) := match o with Some p => [(p, n)] | None => [] end.

Lemma fuzz_malloc_Q : forall X n,
  mspecL (fun s mo => Q X s mo /\ (0 < n -> malok X n)) (fuzz_malloc raw_malloc new_handler n)
         (fun r => Q (olistQ r n ++ X)).
Proof.
  intros X n. unfold fuzz_malloc.
  apply mspecL_if; intros C.
  - apply Z.ltb_lt in C.
    eapply mspecL_bind.
    + eapply mspecL_pre; [apply malloc_Q; lia|]. intros s mo [HQ HM]. split; [exact HQ| exact (HM C)].
    + intros [p|]; cbn beta iota.
      * apply mspecL_pure. intros _. ret_Q.
      * eapply mspecL_bind; [apply (new_handler_Q X (fun _ _ _ => False))|]. intros [].
  - apply mspecL_ret. intros s mo [HQ _]. exact HQ.
Qed.

Lemma free_opt_Q : forall X o n,
  mspecL (Q (olistQ o n ++ X)) (free_opt raw_free o) (fun _ => Q X).
Proof. intros X [p|] n; cbn [free_opt olistQ app]; [apply free_Q| ret_Q]. Qed.

Lemma AMBZ_olistQ : forall o n A, AMBZ A -> (length A <= 2)%nat -> 0 <= n <= 2^26 + 64 -> AMBZ (olistQ o n ++ A).
Proof. intros [p|] n A HA HL Hn; cbn [olistQ app]; [apply AMBZ_cons; assumption| exact HA]. Qed.

Lemma length_olistQ : forall o n (A : list (bptr * Z)), (length (olistQ o n ++ A) <= S (length A))%nat.
Proof. intros [p|] n A; cbn [olistQ app length]; lia. Qed.

Lemma SMALLX_olistQ : forall o n S, SMALLX S -> 0 <= n < MMAP_THRESHOLD -> SMALLX (olistQ o n ++ S).
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) ["TARGETP"] "p'0h01Sh11nh22HSh32Hnh41bi001bh51oi011oh61pp;1p;2p;3p;4p;6g01aTR0j1=Tg00C9j2<Tg00CYj18Tg01KNj10Tg00Hgj25Tg00_bj24Tg00ICj23Tg023Vj22Tg00B?j31Tg01Smj37Tg01TJj46Tg028Qj69Tg01nlj2:Tg00i?j1;Tg00:;R1#=P0P1g0198R01<10R2#8R3f0R4#0R5g018;R6f2R7'5g01ACR8,47'3R9f4R:f3R;'2=127#0[[]0]1P4P2A7104R<,5614<8'3X42P1P0P:P;C6P7P4f1R<E91:1:/2;=127#0eX39X25X03X10X61P4O1P<%;1/2;=127#0eX39X25X03X10n10110100021010000W5o"). Qed.

Lemma fuzz_one_Q : forall A data, AMBZ A -> (length A <= 2)%nat -> zlength data <= MAX_INPUT ->
  mspecL (Q A) (Prog.fuzz_one data) (fun _ => Q A).
Proof.
  intros A data HA HL Hlen. unfold Prog.fuzz_one, Harness.fuzz_one.
  pose proof (dt_size_range data ltac:(unfold MAX_INPUT in Hlen; exact Hlen)) as Hdt.
  pose proof (dbuf_size_range data ltac:(unfold MAX_INPUT in Hlen; exact Hlen)) as Hdb. rewrite BUFF_MAX_val in Hdb.
  pose proof WKSP_SIZE_val as Hws.
  assert (S0 : SMALLX []) by (unfold SMALLX; constructor).
  (* the small requests (producer, dt, wksp) form the SMALLX prefix of the frame; dBuf is the big one *)
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    apply (malok_huf PRODUCER_SIZE A [] HA HL S0 ltac:(cbn; lia)). unfold PRODUCER_SIZE, NREQ. lia. }
  intros producer.
  assert (S1 : SMALLX (olistQ producer PRODUCER_SIZE)).
  { pose proof (SMALLX_olistQ producer PRODUCER_SIZE [] S0 ltac:(unfold PRODUCER_SIZE, MMAP_THRESHOLD; lia)) as H.
    rewrite app_nil_r in H. exact H. }
  assert (L1 : (length (olistQ producer PRODUCER_SIZE) <= 1)%nat) by (destruct producer; cbn; lia).
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    apply (malok_huf (dt_size data) A _ HA HL S1 ltac:(lia)). unfold NREQ. lia. }
  intros dt.
  assert (S2 : SMALLX (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE)).
  { apply SMALLX_olistQ; [exact S1| unfold MMAP_THRESHOLD; lia]. }
  assert (L2 : (length (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE) <= 2)%nat).
  { pose proof (length_olistQ dt (dt_size data) (olistQ producer PRODUCER_SIZE)). lia. }
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    rewrite (app_assoc (olistQ dt (dt_size data)) (olistQ producer PRODUCER_SIZE) A).
    apply (malok_huf WKSP_SIZE A _ HA HL S2 ltac:(lia)). unfold NREQ. lia. }
  intros wksp.
  assert (S3 : SMALLX (olistQ wksp WKSP_SIZE ++ (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE))).
  { apply SMALLX_olistQ; [exact S2| unfold MMAP_THRESHOLD; lia]. }
  assert (L3 : (length (olistQ wksp WKSP_SIZE ++ (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE)) <= 3)%nat).
  { pose proof (length_olistQ wksp WKSP_SIZE (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE)). lia. }
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply fuzz_malloc_Q|]. intros s mo HQ. split; [exact HQ|]. intros _.
    rewrite (app_assoc (olistQ dt (dt_size data)) (olistQ producer PRODUCER_SIZE) A).
    rewrite (app_assoc (olistQ wksp WKSP_SIZE) (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE) A).
    apply (malok_huf (dbuf_size data) A _ HA HL S3 L3). unfold NREQ. lia. }
  intros dBuf.
  (* the frees run dt, wksp, dBuf, producer; each frame is the one before, permuted *)
  eapply mspecL_seq.
  { eapply mspecL_pre; [apply (free_opt_Q ((olistQ producer PRODUCER_SIZE ++ A) ++ (olistQ dBuf (dbuf_size data) ++ olistQ wksp WKSP_SIZE)) dt (dt_size data))|].
    intros s mo H. eapply Q_perm; [|exact H].
    rewrite (app_assoc (olistQ dBuf (dbuf_size data)) (olistQ wksp WKSP_SIZE) (olistQ dt (dt_size data) ++ olistQ producer PRODUCER_SIZE ++ A)).
    rewrite (app_assoc (olistQ dt (dt_size data)) (olistQ producer PRODUCER_SIZE ++ A) (olistQ dBuf (dbuf_size data) ++ olistQ wksp WKSP_SIZE)).
    apply Permutation_app_comm. }
  intros _.
  eapply mspecL_seq.
  { eapply mspecL_pre; [apply (free_opt_Q ((olistQ producer PRODUCER_SIZE ++ A) ++ olistQ dBuf (dbuf_size data)) wksp WKSP_SIZE)|].
    intros s mo H. eapply Q_perm; [|exact H].
    rewrite (app_assoc (olistQ producer PRODUCER_SIZE ++ A) (olistQ dBuf (dbuf_size data)) (olistQ wksp WKSP_SIZE)).
    apply Permutation_app_comm. }
  intros _.
  eapply mspecL_seq.
  { eapply mspecL_pre; [apply (free_opt_Q (olistQ producer PRODUCER_SIZE ++ A) dBuf (dbuf_size data))|].
    intros s mo H. eapply Q_perm; [|exact H]. apply Permutation_app_comm. }
  intros _.
  eapply mspecL_seq; [apply free_opt_Q|]. intros _.
  ret_Q.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_calls_Q : forall A n payload rc, AMBZ A -> (length A <= 2)%nat -> zlength payload <= MAX_INPUT ->
  mspecL (Q A) (run_calls Prog.fuzz_one (io_emit io) n payload rc) (fun _ => Q A).
Proof.
  intros A n. induction n as [|n IH]; intros payload rc HA HL Hp; cbn [run_calls]; [ret_Q|].
  eapply mspecL_seq; [apply fuzz_one_Q; assumption|]. intros rc'.
  eapply mspecL_seq; [apply emit_Q|]. intros _. apply IH; assumption.
Qed.

Lemma run_QP : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL (Q [(b, cap)]) (run cfg payload) (fun _ => Q [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp. unfold run, target_run.
  assert (HA1 : AMBZ [(b, cap)]) by (apply AMBZ_cons; [apply AMBZ_nil| cbn; lia| unfold MAX_INPUT in *; lia]).
  eapply mspecL_bind with (Q1 := fun a s mo => match a with
                                               | None => Q [(b, cap)] s mo
                                               | Some None => Q [(b, cap)] s mo
                                               | Some (Some p) => Q [(p, zlength payload); (b, cap)] s mo
                                               end).
  { apply mspecL_if; intros _; [ret_Q|].
    eapply mspecL_bind.
    - eapply mspecL_pre; [apply malloc_Q; unfold zlength; lia|]. intros s mo HQ. split; [exact HQ|].
      apply (malok_amb0 (zlength payload) [(b, cap)] HA1 ltac:(cbn; lia)). unfold MAX_INPUT, zlength in *. lia.
    - intros [p|]; apply mspecL_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
  intros [[p|]|]; cbn beta iota.
  - eapply mspecL_seq; [apply run_calls_Q; [apply AMBZ_cons; [exact HA1| cbn; lia| unfold MAX_INPUT, zlength in *; lia]| cbn; lia| exact Hp]|]. intros rc.
    eapply mspecL_seq; [apply free_Q|]. intros _. ret_Q.
  - eapply mspecL_seq; [apply run_calls_Q; [exact HA1| cbn; lia| exact Hp]|]. intros rc. eapply mspecL_seq; [ret_Q|]. intros _. ret_Q.
  - ret_Q.
Qed.
End TARGETP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Qamb (X : list (bptr * Z)) : assn PState := QI X Pamb.
Definition Qrun (X : list (bptr * Z)) : assn PState := fun s mo =>
  exists P, (forall c, P c <= Pcap c) /\ (forall c, validc c = true -> AMBC <= P c) /\ QI X P s mo.

Lemma Qamb_Qrun X s mo : Qamb X s mo -> Qrun X s mo.
Proof. intros H. exists Pamb. split; [exact Pamb_le_Pcap|]. split; [exact Pamb_amb| exact H]. Qed.

Lemma Qamb_minv X s mo : Qamb X s mo -> minv mo /\ m_halted mo = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) [] "h01Xh12moh21sp;2p;1p;4g00C9j22Tg00CYj11Tg01ZQj40Tg00:;g0198'2#1R0g01[IR1g01\BR2f2R3g02TIf1R4f0R5C0X12X21X00P3P4P5O3W1W2W0o"). Qed.
Lemma Qamb_fds X s mo mo' : Qamb X s mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> Qamb X s mo'. Proof. apply QI_fds. Qed.
Lemma Qamb_live X s mo : Qamb X s mo -> live mo <= LBUDGET.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) [] "h01Xh12moh21sp;2p;1p;4g00C9j22Tg00CYj11Tg01]oj40Tg00:;g0198'2#1R0g01[IR1g01\BR2f2R3g02TIf1R4f0R5C0X12X21X00P3P4P5O3W1W2W0o"). Qed.
Lemma Qamb_so X s mo v : Qamb X s mo -> Qamb X (set_so_ps v s) mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) [] "h01Xh12moh21sh31vp;2p;1p;5g00C9j22Tg00CYj11Tg01^gj50Tg00:;g0198'2#1R0g01[IR1g01\BR2g01_aR3f3R4g02TIf2R5f1R6f0R7D0X33X12X21X00P4P5P6P7O4W3W1W2W0o"). Qed.
Lemma Qamb_perm X Y s mo : Permutation X Y -> Qamb X s mo -> Qamb Y s mo.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) [] "h01Xh11Yh22moh31sp;2p;1p;5g00C9j22Tg00CYj11Tg01`\j50Tg00:;g0198'2#1R0g01[IR1g01\BR2f3R3f2R4g02TIf1R5f0R6D0X22X31X10X00P3P4P5P6O4W2W3X10W0o"). Qed.
Lemma Qrun_minv X s mo : Qrun X s mo -> minv mo /\ m_halted mo = None.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) [] "p'0h01ch12H0h21Ph31Xh42moh51sh61Hh72_Hh83_H0h91xi001xp;2p;1p;3p;4p;5g00C9j2@Tg00CYj1?Tg02WQj38Tg01>]j17Tg00Hgj21Tg011lj1;Tg00ZPj34Tg01c5j42Tg00ICR0j20Tg02XJj15Tg00FMj13Tg00kJj19Tg02Y=j1:Tg01aTj1>Tg02Y`j16Tg00i?j1=Tg01ZQj5<Tg00:;g0198R1'@#?R2g01[IR3g01\BR4f2R5f1R6f0R738g02ZWP1^91R8P6P7O1%77R9'1^01R:g01BB%;7g01F934R;g01I\R<P5P6O1'1[^01R=f4R>P7f3R?P5C2'0'0X28%55g01==#3#3#3#3#3#3#9#:R@#>RA%65%=@R@34'0P7f6RBP7f5RCP>C2,0=,0:P0P5P7O1/19^01P?P6O1,1<\;^01f7R?P6PBPCC2'0%5B%6B=4A@'0P7P>P7O1/19^01PBP6O1,1<\;^01f:RBP>f9R>f8R9C2'0P0P?P6O1,1<\;^01f;PCPBP>C2%5B%6B=4A@'0P7P>P6O1,1<\;^01f>R1P9f=R9f<C2f?P>P1P9P7D<W6W8P6P7O2n2001000000120000000W1W7P6P7O2n2001000000120000000W1X28P6P7O2n2001000000120100000W1X44X53X32P5P6P7O3W4W5W3o"). Qed.
Lemma Qrun_fds X s mo mo' : Qrun X s mo -> m_vmmaps mo' = m_vmmaps mo -> m_kernel mo' = m_kernel mo -> minv mo' -> m_halted mo' = None -> Qrun X s mo'.
Proof. intros (P & H1 & H2 & H) E K M N. exists P. split; [exact H1|]. split; [exact H2|]. eapply QI_fds; eauto. Qed.
Lemma Qrun_live X s mo : Qrun X s mo -> live mo <= LBUDGET.
Proof.
ltac2:(KReplay.run1 (kr_t_LB_PTarget ()) [] "p'0h01ch12H0h21Ph31Xh42moh51sh61Hh72_Hh83_H0h91xi001xp;2p;1p;3p;4p;5g00C9j2:Tg00CYj19Tg02WQj35Tg01>]j14Tg00Hgj20Tg011lj18Tg00ZPj36Tg01c5j41Tg00ICR0j22Tg02\_j13Tg01]oj57Tg00:;g0198R1':#9R2g01[IR3g01\BR4f2R5f1R6f0R735g02ZWP1^91R8P6P7O1%47R9'0^01R:g01BB%87g01F936R;g01I\R<P5P6O1'0[^01R=f4R>P7f3R?P5C1'2'2X28%35g01@KR@'0P7f6RAP7f5RBP>C1,2=,2:P0P5P7O1/09^01P?P6O1,0<\;^01f7R?P6PAPBC1'2%3A/0@P7P>P7O1/09^01PAP6O1,0<\;^01f:RAP>f9R>f8R9C1'2P0P?P6O1,0<\;^01f;PBPAP>C1%3A/0@P7P>P6O1,0<\;^01f>R1P9f=R9f<C1f?P>P1P9P7D7W6W8P6P7O2n2001000000120000000W1W7P6P7O2n2001000000120000000W1X28P6P7O2n2001000000120100000W1X44X53X32P5P6P7O3W4W5W3o"). Qed.
Lemma Qrun_so X s mo v : Qrun X s mo -> Qrun X (set_so_ps v s) mo.
Proof. intros (P & H1 & H2 & H). exists P. split; [exact H1|]. split; [exact H2|]. apply QI_set_so. exact H. Qed.

(* [comment removed for export] *)
Definition malokA (X : list (bptr * Z)) (n : Z) : Prop :=
  forall P, (forall c, P c <= Pcap c) -> (forall c, validc c = true -> AMBC <= P c) -> malok P X n.

Lemma malokA_amb0 : forall n A, AMBZ A -> (length A <= 3)%nat -> 0 <= n <= 24 * 2^24 + 12 -> malokA A n.
Proof. intros n A HA HL Hn P HPc HP8. apply (malok_amb0 P HPc HP8 n A HA HL Hn). Qed.

Lemma malloc_Qamb : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => Qamb X s mo /\ malokA X n) (raw_malloc n)
         (fun r s mo => match r with Some p => Qamb ((p, n) :: X) s mo /\ n < 2^63 | None => Qamb X s mo end).
Proof. intros X n Hn. eapply mspecL_pre; [apply (malloc_Q Pamb n X Hn) || apply (malloc_Q Pamb X n Hn)|]. intros s mo [HQ HM]. split; [exact HQ|]. apply HM; [exact Pamb_le_Pcap| exact Pamb_amb]. Qed.

Lemma free_Qamb : forall X p n, mspecL LBUDGET (Qamb ((p, n) :: X)) (raw_free p) (fun _ => Qamb X).
Proof. intros. unfold Qamb. apply raw_free_LQ. Qed.

Lemma free_Qrun : forall X p n, mspecL LBUDGET (Qrun ((p, n) :: X)) (raw_free p) (fun _ => Qrun X).
Proof.
  intros X p n s mo (P & H1 & H2 & H). eapply etwl_mono; [apply (raw_free_LQ X P p n s mo H)|].
  intros [u s'] mo' HQ. cbn in HQ |- *. exists P. auto.
Qed.

(* [comment removed for export] *)
Theorem run_Q : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL LBUDGET (Qamb [(b, cap)]) (run cfg payload) (fun _ => Qrun [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hp s mo HQ.
  eapply etwl_mono; [apply (run_QP Pamb Pamb_le_Pcap Pamb_amb b cap cfg payload Hcap Hp s mo HQ)|].
  intros [u s'] mo' H. cbn in H |- *. apply Qamb_Qrun. exact H.
Qed.
