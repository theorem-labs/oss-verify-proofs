(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: some recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the vDSO; the run over the run's segments; new lemmas; taken in part from projects/jsoncons/fuzz_bson_parser_max/proofs/lib/HaltsKit.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, 99 lines within its lines 21-260. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg Spec BigintSpec KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_HaltsKit () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem3Run<in_is_prefixC46Stdlib5Lists4List8map_consI46Stdlib5Lists4List6Exists00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4t_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit=exit_codes_inC13~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic3and00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree9kill_freeC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes001C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_altC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffC46Stdlib5Lists4List:Forall_appC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree;ev_not_killC13~~~K47Corelib4Init9Datatypes4list01C46Stdlib5Lists4List9app_nil_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic5False00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec1WC13~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffC45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics?LinuxProcessSem5State5event02C47Corelib4Init5Logic9False_indI47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_alt2C13~~~K47Corelib7Numbers7BinNums1Z02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9exit_codeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitDexit_codes_in_t_exitC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitIexit_codes_in_emit_writesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec5t_dieC13~~~K47Corelib4Init5Logic2or01K47Corelib7Numbers7BinNums1Z01C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3lebK47Corelib4Init9Datatypes3nat02C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec:zero_linesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitAexit_codes_in_dieC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:BigintSpec6t_bodyC13~~~C47Corelib5Lists7ListDef3nthC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9MAX_INPUTC13~~~I47Corelib4Init9Datatypes4bool00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit7codes02C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;msg_refusedC13~~~K47Corelib4Init9Datatypes3nat01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9msg_shortC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;msg_overrunC13~~~I47Corelib4Init9Datatypes3nat00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit6in02_2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit6in02_0C13~~~C56Stdlib5Arith8PeanoNat3Nat3lebC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec?msg_cannot_openC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec=list_byte_eqbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec>msg_read_errorC13~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitBexit_codes_in_alt2C13~~~I47Corelib4Init9Datatypes6option00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitDexit_codes_in_t_bodyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:BigintSpec4specC13~~~C46Stdlib5Lists4List2hdC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9msg_usageC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec8dot_pathC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State=procst_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelK47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00C4ELinuxProcessSemantics?LinuxProcessSem3RunKmi_account_step_model_frameC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit@m_halted_of_procC13~~~C47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StatePmaterialize_model_accesses_frameC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event04K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg00K4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg01C4ELinuxProcessSemantics?LinuxProcessSem3Run?forced_only_cfgK4ELinuxProcessSemantics?LinuxProcessSem3Run8star_cfg02C46Stdlib5Lists4List9app_assocC4ELinuxProcessSemantics?LinuxProcessSem3Run<star_cfg_indc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit8reach_foC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit=star_cfg_snocC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC46Stdlib5Logic>Classical_Prop7classicC4ELinuxProcessSemantics?LinuxProcessSem3Run?refusal_decidedK47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitGrefusal_decided_classicC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=sstep_cfg_subC4ELinuxProcessSemantics?LinuxProcessSem3RunBsstep_cfg_progressI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes000C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg7node_okC13~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitDsstep_cfg_not_haltedc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit;fo_progressC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunEforced_only_cfg_leastC4ELinuxProcessSemantics?LinuxProcessSem3Run>sstep_cfg_monoc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit=reach_fo_stepC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitDexit_codes_in_branchC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit@kill_free_branchC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgCsrealizes0_nonemptyC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit>node_evs_traceC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitEsstep_cfg_into_haltedC13~~~K4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitCmust_exit_in_at_cfg02K4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitCmust_exit_in_at_cfg01C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:DivergeSim7to_spin00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5bm_onC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8t_eq_symC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitBexit_codes_in_t_eqC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit>kill_free_t_eqC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAbudget_refused_atC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg>srealizes0_indC13~~~I4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitCmust_exit_in_at_cfg00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_nilC13~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3RunGrun_scfg_budget_refusedC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitFnoref_of_within_budgetC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKit=reach_fo_reflC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5StateCm_halted_init_modelc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8HaltsKitFsrealizes_must_exit_foC13~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitAmust_exit_in_scfg".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition exit_codes_in (S : list word) (T : TSet) : Prop :=
  forall tr, T tr -> forall code fs, In (ExitEv code fs) tr -> In code S.

Lemma exit_codes_in_t_eq : forall S T T', t_eq T T' -> exit_codes_in S T -> exit_codes_in S T'.
Proof. intros S T T' Heq H tr Htr code fs Hin. refine (H tr _ code fs Hin). apply Heq; exact Htr. Qed.

Lemma kill_free_t_eq : forall T T', t_eq T T' -> kill_free T -> kill_free T'.
Proof. intros T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.

Lemma exit_codes_in_branch : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exit_codes_in S (t_alt (fun i => t_emit (evs i) (T i))) -> exit_codes_in S (T i).
Proof.
  intros S I evs T i H tr Htr code fs Hin.
  refine (H (evs i ++ tr) _ code fs _); [| apply in_app_iff; right; exact Hin].
  exists i. right. exists tr. split; [reflexivity | exact Htr].
Qed.

Lemma kill_free_branch : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kill_free (t_alt (fun i => t_emit (evs i) (T i))) -> kill_free (T i).
Proof.
  intros I evs T i H tr Htr.
  assert (HF : Forall ev_not_kill (evs i ++ tr)).
  { apply H. exists i. right. exists tr. split; [reflexivity | exact Htr]. }
  apply Forall_app in HF as [_ HF]. exact HF.
Qed.

(* [comment removed for export] *)
Lemma node_evs_trace : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  T i [] -> t_alt (fun i => t_emit (evs i) (T i)) (evs i).
Proof.
  intros I evs T i H0. exists i. right. exists []. split; [rewrite app_nil_r; reflexivity | exact H0].
Qed.

Lemma exit_codes_in_t_exit : forall S code fs, In code S -> exit_codes_in S (t_exit code fs).
Proof.
  intros S code fs Hin tr Htr c' fs' Hc.
  unfold t_exit, t_emit, t_nil in Htr.
  assert (Hc' : In (ExitEv c' fs') [ExitEv code fs]).
  { destruct Htr as [Hp | (tr' & -> & ->)].
    - exact (in_is_prefix _ _ _ Hp Hc).
    - rewrite app_nil_r in Hc. exact Hc. }
  destruct Hc' as [Hc' | []]. injection Hc' as -> _. exact Hin.
Qed.

Lemma exit_codes_in_emit_writes : forall S ch s T,
  exit_codes_in S T -> exit_codes_in S (t_emit (Spec.W ch s) T).
Proof.
  intros S ch s T H tr Htr code fs Hin.
  destruct Htr as [Hp | (tr' & -> & HT)].
  - exfalso. assert (Hin' : In (ExitEv code fs) (Spec.W ch s)) by exact (in_is_prefix _ _ _ Hp Hin).
    unfold Spec.W in Hin'. apply in_map_iff in Hin' as (b & Hb & _). discriminate Hb.
  - apply in_app_iff in Hin as [Hin | Hin].
    + exfalso. unfold Spec.W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb.
    + exact (H tr' HT code fs Hin).
Qed.

Lemma exit_codes_in_alt2 : forall S A B, exit_codes_in S A -> exit_codes_in S B -> exit_codes_in S (t_alt2 A B).
Proof. intros S A B HA HB tr [Htr | Htr]; [exact (HA tr Htr) | exact (HB tr Htr)]. Qed.

Lemma exit_codes_in_die : forall S msg fs, In (Spec.exit_code 2) S -> exit_codes_in S (Spec.t_die msg fs).
Proof. intros S msg fs H2. unfold Spec.t_die. apply exit_codes_in_emit_writes. apply exit_codes_in_t_exit. exact H2. Qed.

(* [comment removed for export] *)
Section SpecCodes.
Context {fx : PropExec.FPState} {bmK : BMode}.
Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in02_0 : In (Spec.exit_code 0) codes02.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsKit ()) ["SpecCodes"] "p;1p;2p;3g009@j10Tg009ej1;Tg00:Cj13Tg00PGj21Tg00U@j1:Tg00FBj39Tg00Tbj17Tg00KFj14Tg00MNj35Tg003`j36Tg00G6j22Tg00ZCj38Tg00>U#0R0#0#0#0#0#0#;R1#3R2g00Z]R3,11%:3R339%70,11%425529623122338o"). Qed.
Lemma in02_2 : In (Spec.exit_code 2) codes02.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsKit ()) ["SpecCodes"] "p;1p;2p;3g009@j10Tg009ej1<Tg00:Cj17Tg00PGj23Tg00Tbj1;Tg00U@j1:Tg00FBj32Tg00KFj16Tg00MNj35Tg003`j31Tg00G6j24Tg00ZCj38Tg00HEj39Tg00>U#0R0#0#0#0#0#0#<R1#7R2g00Z],31%;0R0#:R3321310R0%62R15529123A2203A123114233839o"). Qed.

Lemma exit_codes_in_t_body : forall data fs, exit_codes_in codes02 (BigintSpec.t_body data fs).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsKit ()) ["SpecCodes"] "p'0h01bi001bh14datah22fsi01:config_leni021np;1p;2p;4p;5g009@j16Tg009ej1HTg00:Cj1DTg00:fj1NTg00[;j29Tg00[[j1MTg00\;j2GTg00Y>j23Tg00\Xj10Tg00]7j27Tg00PGj2CTg00Tbj1:Tg00]Wj2ATg00^4j2@Tg00^Qj22Tg00_1j14Tg00_Qj2BTg00_hj1?Tg00NKj2;Tg00U@j1LTg00LDj2>Tg00E8j2<Tg00<Nj28Tg00a2j4=Tg00VIj4FTg00Waj5ITg00bGj2ETg00cSj4JTg00coj2KTf0R0#6#6p=5f4R1f3R2f2R3f1R4P0CJ'Kp=1g00>UR5#5R6#6R7#HR8#DR9#Ng0032g00dY1994#M'Gg00ebR:P:g00fBR;P:g00?:R<P0g00gMR=/33P:P<1992R>g00hXR?#0R@#0RA#0#0#0#0RB'7g00i7RC/33P:P<P8P9P?P2g00Z]RD,C8RED1%67#5#5R7#:RFP8P9P@P2PED1'A'@%67#5#5#5#:R7'2#4RG,BB,7>R>g00j@RH/33%:5R5g00kKRIPIPGP@P8P9PAP1PED1%:6R6'2#4#0n0110100020010102#?';%LDRD/>3'<n0100000020000n0100000020001n0100000020001'8P0P;P=P4g00kjR=C=1993/7BP:P:P:P<P013C2P:P<1991P8P9P?P1PED1P8P9P@P1PED1,AF'@/27#4RG,BB'713H2PIPIPGP@P8P9PAf5RGPED1/26#4#0n0110100020010102#?RB,;51>D2RJ'<n0100000020000n0100000020001,8;P0P;PCP3P=C=P>P:P:P:P<P013H1PIPIP8P9P?PGPED1P8P9P@PGPED1,AF'@/27#4P@P8P9PAf6PED1/26#4#0n0110100020010102#?,;51>D1'<n0100000020000,8;P0P;PHP2P=C=P;P5PBPJP;PDP2g00m4CFDIn0110000020000b0n0110001020001b0n0110001020001b01E40,8;eW2W1o"). Qed.

Lemma exit_codes_in_spec : forall argv fs, exit_codes_in codes02 (BigintSpec.spec argv fs).
Proof.
  intros argv fs. unfold BigintSpec.spec.
  repeat first [ apply exit_codes_in_die; apply in02_2
               | apply exit_codes_in_t_body
               | apply exit_codes_in_alt2
               | apply exit_codes_in_t_exit; apply in02_0
               | match goal with |- exit_codes_in _ (if ?c then _ else _) => destruct c end
               | match goal with |- exit_codes_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.
End SpecCodes.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Lemma m_halted_of_proc : forall m m', m_proc m' = m_proc m -> m_halted m' = m_halted m.
Proof. intros m m' H. unfold m_halted. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_into_halted : forall cfg c evs c' code,
  sstep_cfg segs cfg c evs (SNext c') ->
  m_halted (cfg_model c') = Some code ->
  (m_killed (cfg_model c') = None /\ exists evs0 fs, evs = evs0 ++ [ExitEv code fs])
  \/ (exists evs0 sig fs, evs = evs0 ++ [KillEv sig fs]).
Proof.
  intros cfg c evs c' code Hss Hh.
  inversion Hss; subst; cbn [cfg_model] in Hh.
  -   exfalso.
    match goal with [ H : mi_account_step _ _ _ = MachineOk _ |- _ ] =>
      pose proof (mi_account_step_model_frame _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  - (* the vDSO call arm, new at LPS ca39bcd5: the post-model is
       [with_vdso_bump model''], so the halt flag has to come back through the
       bump before the materialization frame applies.  Both keep [m_proc]. *)
    exfalso.
    rewrite (m_halted_of_proc _ _ (m_proc_with_vdso_bump _)) in Hh.
    match goal with [ H : materialize_model_accesses _ _ = Some _ |- _ ] =>
      pose proof (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  -   exfalso.
    match goal with [ H : materialize_model_accesses _ _ = Some _ |- _ ] =>
      pose proof (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _) end.
    rewrite (m_halted_of_proc _ _ Hp) in Hh. congruence.
  -   left. split; [assumption |].
    match goal with [ H : m_halted ?m = Some ?c0 |- _ ] => idtac end.
    assert (code0 = code) by congruence. subst. eexists _, _. reflexivity.
  -   right. eexists _, _, _. reflexivity.
Qed.

(* [comment removed for export] *)
Definition reach_fo (c0 c : config) : Prop := exists tr, star_cfg segs forced_only_cfg c0 tr c.

Lemma reach_fo_refl : forall c0, reach_fo c0 c0.
Proof. intros c0. exists []. apply star_cfg_refl. Qed.

Lemma star_cfg_snoc : forall cfg c0 tr c evs c',
  star_cfg segs cfg c0 tr c -> sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c0 (tr ++ evs) c'.
Proof.
  intros cfg c0 tr c evs c' Hstar Hss. induction Hstar as [c1 | c1 evs1 c2 tr2 c3 Hs Hst IH].
  - cbn. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact Hss | apply star_cfg_refl].
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | exact (IH Hss)].
Qed.

Lemma reach_fo_step : forall c0 c evs c',
  reach_fo c0 c -> sstep_cfg segs forced_only_cfg c evs (SNext c') -> reach_fo c0 c'.
Proof. intros c0 c evs c' (tr & Hstar) Hss. exists (tr ++ evs). eapply star_cfg_snoc; eassumption. Qed.

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m Hoff.
  destruct (classic (exists eff' m' evs', syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false)) as [H | H].
  - left. exact H.
  - right. intros eff' m' evs' Hspec.
    destruct (refusal_b i m (eff_ret eff')) eqn:Hr; [reflexivity |].
    exfalso. apply H. eexists _, _, _. split; [exact Hspec | exact Hr].
Qed.

Lemma fo_progress : forall cfg c evs st,
  sstep_cfg segs cfg c evs st -> exists evs' st', sstep_cfg segs forced_only_cfg c evs' st'.
Proof.
  intros cfg [ms model] evs st Hss.
  eapply sstep_cfg_progress; [| eapply sstep_cfg_sub; exact Hss].
  intros x8 _. apply refusal_decided_classic.
Qed.

(* [comment removed for export] *)
Section Master.
Variable scfgD : SpuriousCfg.          (* [comment removed for export] *)
Context {fx : PropExec.FPState} {bmK : BMode}.
Hypothesis BMON : bm_on = true.        (* [comment removed for export] *)
Variable S : list word.
Variable c0 : config.
Hypothesis NOREFUSE : forall c, reach_fo c0 c -> ~ budget_refused_at segs c.

Theorem srealizes_must_exit_fo : forall c T,
  srealizes0 segs scfgD c T ->
  reach_fo c0 c ->
  exit_codes_in S T ->
  kill_free T ->
  (forall code, m_halted (cfg_model c) = Some code -> In code S /\ m_killed (cfg_model c) = None) ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c Hspin Hh Hmode | c T T' H IH Heq | c T Hon Hbr Hbrob HT0];
    intros Hreach HE HK Hhalt.
  -
    destruct Hnode as [Hcomp Hsound].
    assert (Hnh : m_halted (cfg_model c) = None).
    { exact (sstep_cfg_not_halted _ _ _ _ _ (Hcomp i0)). }
    apply must_exit_in_at_cfg_running.
    + exact Hnh.
    + destruct (fo_progress _ _ _ _ (Hcomp i0)) as (evs' & st' & Hfo). eexists _, _. exact Hfo.
    + intros evs' Herr.
      destruct (Hsound evs' SError (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Herr)) as (i & _ & Habs).
      discriminate Habs.
    + intros evs' c' Hfo.
      destruct (Hsound evs' (SNext c') (sstep_cfg_mono _ _ _ _ _ _ (forced_only_cfg_least scfgD) Hfo)) as (i & -> & Hc').
      injection Hc' as Ec. subst c'.
      apply (IH i).
      * eapply reach_fo_step; eassumption.
      * eapply exit_codes_in_branch; exact HE.
      * eapply kill_free_branch; exact HK.
      * intros code Hcode.
        pose proof (srealizes0_nonempty _ _ _ _ (Hcont i)) as H0.
        pose proof (node_evs_trace I evs T i H0) as Htr.
        destruct (sstep_cfg_into_halted _ _ _ _ _ Hfo Hcode) as [(Hk & evs0 & fs & Hevs) | (evs0 & sig & fs & Hevs)].
        { split; [| exact Hk]. apply (HE (evs i) Htr code fs). rewrite Hevs. apply in_app_iff. right. left. reflexivity. }
        { exfalso. pose proof (HK (evs i) Htr) as HF. rewrite Hevs in HF.
          apply Forall_app in HF as [_ HF]. inversion HF as [| x l Hx _]; subst. exact Hx. }
  -
    destruct (m_halted (cfg_model c)) as [code |] eqn:Hc; [| congruence].
    destruct (Hhalt code eq_refl) as [Hin Hk].
    eapply must_exit_in_at_cfg_halted; eassumption.
  -
    exfalso. rewrite BMON in Hmode. discriminate Hmode.
  -
    apply IH; [exact Hreach | eapply exit_codes_in_t_eq; [apply t_eq_sym; exact Heq | exact HE]
              | eapply kill_free_t_eq; [apply t_eq_sym; exact Heq | exact HK] | exact Hhalt].
  -
    exfalso. exact (NOREFUSE c Hreach Hbr).
Qed.
End Master.
End WithSegs.

(* [comment removed for export] *)
Section Top.
Context {fx : PropExec.FPState} {bmK : BMode}.
Hypothesis BMON : bm_on = true.

(* Native budget refusal uses the complete launch segment mapping. *)
Lemma noref_of_within_budget : forall segs pc ph sp brk0 mb rnd lim inp,
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  forall c, reach_fo (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) c ->
    ~ budget_refused_at (run_segments segs inp sp mb) c.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp Hnb c (tr & Hstar) Hbr.
  apply Hnb. cbn [run_scfg_budget_refused]. exists tr, c. split; [exact Hstar | exact Hbr].
Qed.

(* [Run.init_config] wraps [init_model] in [with_vdso] at LPS 727298f3; [with_vdso]
   passes [m_proc] through, so the halt flag is unchanged (as the fuzz_bson_parser_max port). *)
Lemma m_halted_with_vdso : forall v m, m_halted (with_vdso v m) = m_halted m.
Proof. reflexivity. Qed.

Theorem srealizes_init_must_exit : forall scfgD segs pc ph sp brk0 mb rnd lim inp S T,
  srealizes0 (run_segments segs inp sp mb) scfgD
    (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  exit_codes_in S T -> kill_free T ->
  ~ run_scfg_budget_refused forced_only_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros scfgD segs pc ph sp brk0 mb rnd lim inp S T Hs HE HK Hnb.
  cbn [must_exit_in_scfg].
  eapply (srealizes_must_exit_fo (run_segments segs inp sp mb) scfgD BMON S _ (noref_of_within_budget _ _ _ _ _ _ _ _ _ Hnb)).
  - exact Hs.
  - apply reach_fo_refl.
  - exact HE.
  - exact HK.
  - intros code Hh. exfalso. unfold init_config in Hh. cbn [cfg_model] in Hh.
    rewrite m_halted_with_vdso, m_halted_init_model in Hh. discriminate Hh.
Qed.
End Top.
