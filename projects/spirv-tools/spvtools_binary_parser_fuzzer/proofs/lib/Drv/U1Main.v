(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's mmap base; the model's channel reader as a premise of the writes; recorded proofs re-encoded or written as text where the change reaches them). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom Amb PropExec ShapeAlg ArgvEnv SRealizes LibIface LibBudget U1Layout FPSteps MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1Statics DrvLibContract DrvMallocTU1 S1Spec U1Start U1BootDefs U1Usage U1OpenFail
  U1RFront U1RTop U1RDirTop U1UsageTop U1TargetIface U1TargetTop.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require U1TargetConsts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1Main () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3iffK47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib3Drv6S1Spec=list_byte_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init9Datatypes?andb_true_introC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC49OSSVerify5KrLib3Amb5a_uidC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib3Amb7a_hwcapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Drv7U1Start:main_entry00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC49OSSVerify5KrLib9AllocCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC49OSSVerify5KrLib9RunRandom9rr_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:U1BootDefs6canaryC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib9RunRandom9rr_secretC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC49OSSVerify5KrLib9RunRandom<rr_secret_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat8leb_specI47Corelib4Init5Peano2le00C47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat3lebI47Corelib4Init9Datatypes8BoolSpec00K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC59OSSVerify5KrLib3Drv8U1RFront3LIMC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib3Amb<mkProcInputCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Spec<t_opened_dirC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC59OSSVerify5KrLib3Drv6S1Spec8t_openedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:U1OpenFailGref_open_fail_toolong_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv6U1Main@list_byte_eqb_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:U1OpenFailEref_open_fail_empty_wC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Drv9U1RDirTop8dir_bodyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Drv;U1TargetTop?u1_target_phaseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6U1RTop9file_bodyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:U1OpenFailFref_open_fail_absent_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Spec4specC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC59OSSVerify5KrLib3Drv6S1Spec?msg_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Spec5t_dieC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I49OSSVerify5KrLib9SRealizes9srealizes00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04C49OSSVerify5KrLib8PropExec3fx0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Spec8dot_pathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C49OSSVerify5KrLib8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203C49OSSVerify5KrLib7FPSteps?fp_frm_zero_fx0C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
ltac2:(KReplay.run1 (kr_t_U1Main ()) [] "p'0h01Hh11qh22H0h31eh41nh51bi001bh61ph72H1h82H2h92b1h:2b2h;1mh<2q0h=2IHh>1ai011lp;1p;3p;2p;4p;6p;8p;5g0000j1?Tg000Uj1NTg0013j18Tg001VR0j1DTg0026j30Tg002Pj25Tg002ij1HTg003Ij2;Tg003cj4<Tg004>j33j2Cj1ITg004^j67Tg005:j2>Tg005Yj36Tg006Fj2:Tg007Cj2=Tg007aj3MTg008DR1j2LTg008_j2@Tg009<j2GTg009\j24Tg00:Fj3FTg00:jj8ATg00;Gj6BTg00;dj1ETg00<Fj3JTg00<oj5KTg00=QR2f1R3f0R4':g00>1R530p=2A0245p=1g00>QR6?034p=9g00>o#?#?#?#NR7#8R8#DR9P81234A0934'5^19R:X69P0P8%H8R;/24A09;4'5P4A0255R<A09;;R=[P<\=1;9;X0<1;25X0=C<12;;/5=eg00?TR==025R<f2R>=383R?909;[A3834R@909;RAP<[P2P=P2p-0R=P4g00@4RBg00@QRCn0110000020000X32g00@mR2P5P4E7R5PBf3RD=38>RE909;/>4b2X0<P9P;P0P8P=P4PCPBn10110100020020000000X39P2P?P4E7PB1><4RFb2X0AC<12;@/5AeX19X58P3P4O2n10110100020021100101X<9P0P8f4RA=38DRG/24A09G4'5P4A09G;\<A09E;RHP<[P5PBf5R5=38A=09;/>4b2X0<P9PGP0P8P=P4PBPCn10110100020020000000X39P2P;P4E7PBPFb2X0HC<12E;/5Hef7RH=673f6R;/:4'=#1RFf8RB=38HR2=09?[A38H;RC=09@R=A67B>R<1:H3RI'=#1[AM<I4%1<%1I'LP1f9RI=67D#112B>f:R<=38I=09GP4f;RG=675#112G5P1f=RJ/24f>RK=093[RLA09J412K3RM[f?RN=09>\Mf<RMP4O1P3n2001000000120000000X19PL^19P4PHP3O2A09JHP9PKf@RL=38NA38<4509X19P9P91C8N1C8IPKPKP8P9\9RO%I8RPPPPNPIPO\8/;PP11@34#119>3[RP19341@>3#1RO[19D>\O1G34P3n2001000000120000000X;6X46PP^;6^46P4147LRL147<R6PAO319L6g00AIR6%84RL%83RPP1%8>?03414D>14D3'9RO[14>314>4'9%8D?0>3[RN%8A?0D>\OAF>34P4n2001000000120000000W:W9W4PN^:P^9L^46P4P7fBPMP3O4b0b7b0GA1;9KGAPBP4E7b8b0W8W7P3P4O2n2001000000121000000b0X0FP9P9P0P8P9P4PBP4n10110100020020100101X39P2P?P4EBA09H3P9P8P0P8P8P4P<P3n10110100020020100101X39A38IBPEP3EBA08IDA08<AP8PGA09G5A67J31:M;'=#1[X58A09<AP9PGA67JJ1:M4R<'=#1X19A67MMRA1:GGR;%1ARA%1;147M#EPAeP1%1<A09J3R<[A09M412J3[RJ12K>\<PGP4O1P4n2001000000120000000X19PJ^19P4PM1;9MO2b0C<3JP5P4E7W0P5P4E7W0P4O1b2P4O1b2X0=C<12C@/5=eX19X58P3P4O2n10110100020121100101X<9X=:X69X>8P4DKW6o"). Qed.

Section Main.
  Context {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb} {UL : ULim}.
  Variable MI : MallocIface SEGS L.
  Variable AINV0 : AS MI -> LibIface.mem -> Model -> Prop.
  Variables (TIGHT FRESH44 : AS MI -> Prop).
  Hypothesis DM : drv_mallocT MI AINV0 TIGHT FRESH44.
  Hypothesis LIB : lib_call_stmt SEGS L MI U1ST U1TargetConsts.LLVM_ENTRY U1TargetConsts.EMPTY_OBJ LIB_STACK lib_caps LIB_BIGCAP
                     U1TargetConsts.TD_LOCALE U1TargetConsts.GLOBAL_LOCALE.

  Theorem main_body : forall (sp : word) (a0s path : list byte) (envv : list (list byte)) (tid : word) (rdraw : EntryDraw)
                             (regs : bvmap 5 word) (mem : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    (* LPS 75d69e00: [U1Start.main_entry] takes the run's whole ProcInput and the mmap
       base in place of (argv, envp, uid, hwcap).  The input named here is the one this
       theorem's OWN conclusion already runs, two lines below -- [in_argv]/[in_envp]/
       [in_uid]/[in_hwcap] of it reduce to exactly the four the old spelling named -- and
       [mbase] is this theorem's own binder, so this is the same premise, not a narrower
       one. *)
    main_entry sp rdraw (mkProcInputC [a0s; path] envv fs0 stdin0) mbase tid regs mem ->
    (* LPS 727298f3: the launch's channel reader; every path writes to fd 2 or fd 1 *)
    a_channel_reader = true -> valid_brk RSEGS brk ->
    alloc_ceiling = bv_unsigned sp - 8388608 -> rr_canary = bv_unsigned (canary rdraw) -> rr_secret = rr_secret_of (ed_random rdraw) ->
    srealizes RSEGS (mkCfg (@mkst fx0 regs (0x6583c%bv : word) mem (seg_rom RSEGS))
                           (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved RSEGS) brk mbase sp LIM (mkProcInputC [a0s; path] envv fs0 stdin0)))))
              (spec [a0s; path] fs0).
Proof.
  (* The four cases of [spec]; each is the tail lemma of its Section, applied at this
     theorem's binders.  (LPS 727298f3: text in place of the recorded proof, whose
     callees gained the launch draw, the vDSO model and the channel reader.) *)
  intros sp a0s path envv tid rdraw regs mem brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hrdr Hbrk HAC HRR HRS.
  assert (EPC : (0x6583c%bv : word) = Z_to_bv 64 0x6583c) by (apply bv_eq; reflexivity).
  unfold spec.
  destruct (Nat.leb_spec 4096 (length path)) as [Hlong|Hshort].
  { exact (ref_open_fail_toolong_w sp a0s path envv tid rdraw regs mem brk mbase fs0 stdin0 LIM
             Hva Hve Hvsp Htid ME Hrdr Hlong). }
  destruct (list_byte_eqb path []) eqn:E0.
  { apply list_byte_eqb_eq in E0.
    exact (ref_open_fail_empty_w sp a0s path envv tid rdraw regs mem brk mbase fs0 stdin0 LIM
             Hva Hve Hvsp Htid ME Hrdr E0). }
  assert (Hpne : path <> []) by (intros E; subst path; discriminate E0).
  assert (Hplen : (length path <= 4095)%nat) by lia.
  destruct (list_byte_eqb path dot_path) eqn:E1.
  { apply list_byte_eqb_eq in E1. subst path. rewrite EPC.
    exact (dir_body MI AINV0 TIGHT FRESH44 DM sp a0s envv tid rdraw regs mem brk mbase fs0 stdin0
             Hva Hve Hvsp Htid ME Hrdr Hbrk HAC HRR HRS). }
  assert (Hpnd : path <> dot_path) by (intros E; subst path; discriminate E1).
  destruct (fs_lookup fs0 path) as [content|] eqn:HF.
  { rewrite EPC.
    exact (file_body MI AINV0 TIGHT FRESH44 DM LIB (u1_target_phase MI AINV0 TIGHT FRESH44)
             sp a0s path envv tid rdraw regs mem brk mbase fs0 stdin0 content
             Hva Hve Hvsp Htid ME Hrdr Hbrk HF Hpne Hpnd Hplen fp_frm_zero_fx0 HAC HRR HRS). }
  exact (ref_open_fail_absent_w sp a0s path envv tid rdraw regs mem brk mbase fs0 stdin0 LIM
           Hva Hve Hvsp Htid ME Hrdr Hplen Hpne Hpnd HF).
Qed.
End Main.
