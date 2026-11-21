(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput; the m_channel_reader premise; the recorded proofs of ref_realizes_spec, ref_realizes_spec_pins replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim ShapeAlg Nodes Hoare ShapeLaws AllocIface PureModel VmLedger.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23Startup O23StartupDefs O23StartupFacts O23MainEntry O23Open O23Malloc65536 O23Usage O23OpenFail O23OpenFailBranch O23MainDir O23FuzzIface O23MainFile.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import RefLayout ArgvEnv.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Main () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib6Common9CliDriver4Spec=list_byte_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC47Corelib4Init5Logic3iffC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC56Stdlib6ZArith6BinInt1Z2leC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC69OSSVerify5KrLib6Common9CliDriver4Spec4specC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib6Common9CliDriver3Amb6amb_ofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3O23:O23Startup:main_entry00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinC69OSSVerify5KrLib6Common9CliDriver3Amb<mkProcInputCC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3O238O23Usage;ref_usage_wC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat9leb_spec0I47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3lebI47Corelib4Init9Datatypes7reflect00C69OSSVerify5KrLib6Common9CliDriver4Spec<t_opened_dirC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC69OSSVerify5KrLib6Common9CliDriver4Spec8t_openedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23OpenFailGref_open_fail_toolong_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23Main@list_byte_eqb_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23OpenFailEref_open_fail_empty_wC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Common5Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23MainDir<ref_dir_pathC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3O23;O23MainFile=ref_file_pathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23OpenFailFref_open_fail_absent_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib6Common9CliDriver3Amb?init_model_C_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23Startup;ref_startupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common9CliDriver4Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver4Spec5t_dieC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib6Common9CliDriver4Spec8dot_pathC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib6Common9CliDriver3Amb3Amb00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I69OSSVerify5KrLib6Common8Mallocng9AllocSure9AllocSure00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib3O237O23Main4pins00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23<O23FuzzIfaceBfuzz_call_contractC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_malloc_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_free_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface9al_ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIfaceAal_mmap_thresholdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23>O23Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_envC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O237O23MainAref_realizes_specC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common:AllocIface;AllocLayout00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng;AllocCalloc<CallocLayout00C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M7init_pcC1@~~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsUSrc_leptonica_pix_orient_fuzzer_repro1M5phdrsC1@~~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00".
Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fx0.

Abbreviation rsegs := Plain.M.loaded_segments.
Abbreviation rpc := Plain.M.init_pc.
Abbreviation rph := Plain.M.phdrs.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Main ()) [] "p'0h01Hh12H0h21qh32IHh41eh51ph63Heqh75lemmah81ah91bi001bh:2b1h;2b2h<1nh=1Bh>2H1i011lp;1p;3p;2p;4p;6p;;p;8p;7p;5p;9p-1R0g0000R1p4p710p9P0p1000\R2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0g001:R0p4p710p9p10024p4p70g002dR2p4p710R3p8p1003Bp4p70P3p8p10040p4p70P3p8g004fj1>Tg005Kj1WTg005ij16Tg006LR3j1KTg006lj30Tg007Fj1UTg007fj27Tg008@j49Tg008[j31j2Aj1JTg009;j6;Tg009Wj2<Tg00:6j3ETg00:cj2?Tg00;kj2HTg00<IR4j23TP1j2VTg00<dj2TTg00=ER1j2:Tg00=^j4QTg00>Ej3PTg00?;j4CTg00?nl;OTg00@ij22Tg00ASj2BTg00B0R5j6MTg00Bbj2LTg00CBj3NTg00Cfj8@TP2j7Gj8ITg00DCj6DTg00D`j5RTP0l9STg00EBR0f2R2f1R6'?g00EbR730f0R8':p=5A0087p=8A0067/:8p=Fp-0R9P1g00FBf5R:f4R;f3R<P2P6P8M9Sp==g00G3R=?068p=4g00GQ#>#>#>#WR>#6R?#KR@P?A0@689568^2@RAX5@P3P?%U?RBA0@B8758P8A0077RCA0@BBRD[PC\D17@BX0C1707X0DC9A5BBDeg00H6RD=007RCA1?26RE90@BRF[A1?68RG90@BRHPC[P8PCP0PDP0P9P8g00HVRDg00I3RIn0110000020000X40g00IOR0P7P8E;R7PDA1?;<RJ90@B/<8b1b6X0CP8PFP@PBP3P?P9P8PIPDn10110100020020000000X4@P0A1?<2RFP8E;PD1<C8RKb1b6X0HC9A5BGHeX2@X9?P6P8O2n10110100020021100101X2@P3P?A0@J895J8P8A0@JBRJ\CA0@FBRHPC[P8PCP7PDf6R7=1?:RL=0@B/<8b1b6X0CP8PJP@A1?:;P3P?P9P8PDPIn10110100020020000000X4@P0PBP8E;PDPKb1b6X0HC9A5FBHef7RH=E>6RB1?78RK'H%8BRD%8KR0'3'Ff8RI=E>2RJ1?H6RC'H#8%8JRJ%8CRC'3RMP8A1?IHRN=0@EROPO1V9ORPE=W71TBKA0@78RK,:0R0PMA0@H6RM,3JP9P9^=9P1P9P9P1P1CQP4P5PJP9P1g00Ik9P91R5PJCCPCPMP8M;OPOPOPPE=W7P:P8O112>HRC12>6RJ'B14CJRB'F12>IRQ12>2RR'B#8RS/3M14QRRR/3MRQPSPRP8PMPMP9P1P5PMCCEMPOPOPPE=W71LCJ13BKRBPO[A1?H7RO=0@GRCPQ[P4PRPMf9RM=1?IRR=0@FP8f:RQ,2>RP12>;'4A0@Q;P@P:f>R5=1?6=0@N^3AX5@P0^2@P@P@f=R0,A?1A?HP7P7P?P@\@R1%J?R9P9P0PHP1\?/79g00J[R9%68R1%66RSP4%62?06812<212<6'4R4[12261228'4%6<?026[RT%6;?0<2\4AN268P8n2001000000120000000W;W:W<PT^;S^:1^<9P8P>P5PIP<O4b0G@17@7G@W3f;P8PQFGW0W>P6P8O2n2001000000121000000X0BP@P?P3P?P?P8PMP6n10110100020020100101X4@PNPEP8EDA0?I2P@P@P3P?P@P8PMP8n10110100020020100101X4@PRPFP6EDA0@I2A0@M<P@P;A1?06=0@OA0?5If?,2>12>MR>'4A0@<I'3[]0^3AX5@A0@:895:8^2@f<=1?:=0@LA0?0HP?PIA1?8I=0@R14JPA0@MM'3]0X8?A0@NN14>>A0@II17=>17@IC9W0P5P8P6FGW1W0W3PQP8PMP<GIW1P8O1b1P8O1b1X0CC9O213DK/:CeO2O2A5OGCeX2@X9?P6P8O2n10110100020121100101X2@X3AX5@X8?P8DRW5o"). Qed.

Section Main.
  Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.

  (* [comment removed for export] *)
  Hypothesis AL_segs : al_segs = rsegs.
  Hypothesis AL_rom : al_rom = seg_rom rsegs.
  Hypothesis AL_malloc : al_malloc_pc = Z_to_bv 64 0xfa4b4.
  Hypothesis AL_free : al_free_pc = Z_to_bv 64 0xfa374.
  Hypothesis AL_tp : al_gp = Z_to_bv 64 0x123d20.
  Hypothesis AL_glob : forall a, al_globals a -> (0x144020 <= bv_unsigned a < 0x1443d0)%Z.
  Hypothesis AL_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_errno : forall a, al_errno_slot a -> (0x123c7c <= bv_unsigned a < 0x123c80)%Z.
  Hypothesis AL_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x145000)%Z.
  Hypothesis AL_hi : (al_image_hi <= 0x145000)%Z.
  Hypothesis AL_ret : forall k, ret_ok k -> al_ret_ok k.
  Hypothesis AL_env : forall (AMB : Amb) sp0 a0s path envv tid regs0 mem0,
      valid_sp sp0 -> valid_argv [a0s; path] -> valid_envp envv ->
      @main_entry AMB sp0 [a0s; path] envv tid regs0 mem0 ->
      forall M, O23Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M.
  (* [comment removed for export] *)
  Hypothesis FZ : fuzz_call_contract.

  Theorem ref_realizes_spec :
    forall sp brk mbase draw lim (inp : ProcInput),
      valid_sp sp -> valid_brk rsegs brk -> (lim <= lim)%Z ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      in_channel_reader inp = true -> valid_launch inp ->
      entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
      realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase draw lim inp Hsp Hbrk Hlim Hva Hve Hfits Hrd Hvl Hlau.
    apply (ref_startup sp brk mbase draw lim inp _ Hrd Hsp Hva Hve Hvl Hlau).
    intros tid regs mem Htid ME.
    rewrite (init_model_C_of inp draw mbase Hrd (segments_reserved rsegs) brk mbase sp lim).
    set (AMB := amb_of inp draw mbase Hrd) in *.
    remember (in_argv inp) as argv eqn:Eargv. remember (in_envp inp) as envp eqn:Eenvp.
    remember (in_fs inp) as fs0 eqn:Efs0. remember (in_stdin inp) as stdin0 eqn:Estdin0.
    clear Eargv Eenvp Efs0 Estdin0.
    destruct argv as [|a0s [|path [|x l]]].
    - apply (ref_usage_w sp [] envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits). cbn; lia.
    - apply (ref_usage_w sp [a0s] envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits). cbn; lia.
    - cbn [spec].
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (ref_open_fail_toolong_w sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply list_byte_eqb_eq in Hemp.
          apply (ref_open_fail_empty_w sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hemp).
        * assert (Hne : path <> []) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply list_byte_eqb_eq in Hdot.
             replace (0x62b1c : word) with (Z_to_bv 64 0x62b1c) by (apply bv_eq; reflexivity).
             apply (ref_dir_path sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hbrk
                      AL_segs AL_rom AL_malloc AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi); [| | exact Hdot].
             ++ intros z Hz. apply AL_ret. apply ret_ok_even. destruct Hz as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
             ++ apply (AL_env AMB sp a0s path envp tid regs mem Hsp Hva Hve ME).
          -- assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
             ++ replace (0x62b1c : word) with (Z_to_bv 64 0x62b1c) by (apply bv_eq; reflexivity).
                apply (ref_file_path sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits Hbrk
                         AL_segs AL_rom AL_malloc AL_free AL_tp AL_glob AL_grant AL_errno AL_ro AL_rw AL_hi AL_ret
                         (AL_env AMB sp a0s path envp tid regs mem Hsp Hva Hve ME) FZ data Hlk Hne Hnd ltac:(lia)).
             ++ apply (ref_open_fail_absent_w sp a0s path envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits
                         ltac:(lia) Hne Hnd Hlk).
    - apply (ref_usage_w sp (a0s :: path :: x :: l) envp tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Htid ME Hfits). cbn; lia.
  Qed.
End Main.

(* [comment removed for export] *)
Record pins {AL : AllocLayout} : Prop := Pins {
  p_segs : al_segs = rsegs;
  p_rom : al_rom = seg_rom rsegs;
  p_malloc : al_malloc_pc = Z_to_bv 64 0xfa4b4;
  p_free : al_free_pc = Z_to_bv 64 0xfa374;
  p_tp : al_gp = Z_to_bv 64 0x123d20;
  p_glob : forall a, al_globals a -> (0x144020 <= bv_unsigned a < 0x1443d0)%Z;
  p_grant : forall a, al_grantable a -> (0x1000 <= bv_unsigned a)%Z /\ ~ (0x10000 <= bv_unsigned a < 0x145000)%Z;
  p_errno : forall a, al_errno_slot a -> (0x123c7c <= bv_unsigned a < 0x123c80)%Z;
  p_ro : forall a, al_in_ro a -> (bv_unsigned a < 0x145000)%Z;
  p_rw : forall a, al_in_rw a -> (bv_unsigned a < 0x145000)%Z;
  p_hi : (al_image_hi <= 0x145000)%Z;
  p_ret : forall k, ret_ok k -> al_ret_ok k;
  p_thr : (al_mmap_threshold <= 131072)%Z;
  p_env : forall (AMB : Amb) sp0 a0s path envv tid regs0 mem0,
      valid_sp sp0 -> valid_argv [a0s; path] -> valid_envp envv ->
      @main_entry AMB sp0 [a0s; path] envv tid regs0 mem0 ->
      forall M, O23Malloc65536.env_ok sp0 mem0 M -> al_env sp0 [a0s; path] envv M }.

Theorem ref_realizes_spec_pins {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure} :
  pins -> fuzz_call_contract ->
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk -> (lim <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    in_channel_reader inp = true -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) (spec (in_argv inp) (in_fs inp)).
Proof.
  intros [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14] FZ.
  exact (ref_realizes_spec P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P14 FZ).
Qed.
