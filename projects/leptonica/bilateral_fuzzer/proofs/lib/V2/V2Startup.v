(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO and vvar pages; the start-up for each CONFIG_RSEQ value; writev's channel-reader flag; the model's launch and its stack image; recorded (KReplay) proofs re-proved by tactics; addresses and constants). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import ShapeAlg PureModel RefNodesMF StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require StartupBase StartupDefs Startup.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2StartupDefs V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocMusl V2RelocStart.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require CatExec PropExec StepTac MuslStrlen.
Ltac2 kr_t_V2Startup () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:StartupTac3bwdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI69OSSVerify5KrLib6Common4Musl7Startup:main_entry00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2V29V2Startup:main_entry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Common7ArgvEnv5argcNC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common8MemSplit3wfJC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl7Startup6J_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb5a_uidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb7a_hwcapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs6D_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit4cmemC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00k59OSSVerify5KrLib2V29V2Startup:main_entry01C1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic4True01I69OSSVerify5KrLib6Common9CliDriver3Amb3Amb00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V27V2Reloc8v2_relocC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib6Common4Musl:RelocStart4RPH0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib6Common9CliDriver3Amb<mkProcInputCC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z4of_NK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib2V29V2Startup<main_entry_LC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib6Common4Musl7Startup?ref_startup_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2RelocCode7v2_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2<V2RelocSites8v2_sitesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2RelocImg6v2_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2:V2RelocImg7v2_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2;V2RelocMusl5v2_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2<V2RelocStart8v2_startC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M7init_pcC1@~~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC69OSSVerify5KrLib6Common9CliDriver3Amb6amb_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinc59OSSVerify5KrLib2V29V2Startup?ref_startup_secC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c59OSSVerify5KrLib2V29V2Startup6me_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2V29V2Startup6J_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2V2=V2StartupDefs6D_mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit>rdn_cmem_aboveC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgJTgt_bilateral_fuzzer_ubsan1M5phdrsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=cmem_at_aboveC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib6Common8MemSplit6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit;cmem_at_winC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib6Common8MemSplit6win_loC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib6Common8MemSplitAstore_ok_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit<cmem_at_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=rdn_cmem_dataC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* the input the AMB world launches with: [mkProcInputC] over an empty file system and stdin,
   which neither the entry image nor any entry register reads *)
Definition inpA {AMB : Amb} (av ev : list (list byte)) : ProcInput := mkProcInputC av ev [] IEof.

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x3b9fc;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x56270;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN (inpA av ev);
  me_a0  : getr regs 10 = argcN (inpA av ev);
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x17868;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  (* the stack frames below sp0 are only ever used through [wfJ] *)
  me_mem : exists (J : word -> option byte),
             wfJ sp0 J
             /\ mem = cmem sp0 (wrap_mem (inpA av ev) a_mbase RPH (Z_to_bv 64 (Z.of_N rpc)) sp0 a_draw) J
                          (D_main sp0 (inpA av ev) a_draw tid);
  (* the launch facts the stack-image layout lemmas read *)
  me_vl  : valid_launch (inpA av ev);
  me_lau : exists brk : word, entry_launch_ok_va Sv48 (mkEntry sp0 brk a_mbase a_draw) (inpA av ev)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall sp0 brk inp mbase rdraw tid regs mem (Hrd : in_channel_reader inp = true),
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp ->
  @Startup.main_entry v2_reloc sp0 inp mbase rdraw tid regs mem ->
  @main_entry (amb_of inp rdraw mbase Hrd) sp0 (in_argv inp) (in_envp inp) tid regs mem.
Proof.
  intros sp0 brk inp mbase rdraw tid regs mem Hrd Hvl Hlau [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13].
  split; [exact f1|exact f2|exact f3|exact f4|exact f5|exact f6|exact f7|exact f8|exact f9|exact f10|exact f11|exact f12| | |].
  - destruct f13 as (J & HJ & ->). exists J. split; [exact HJ|].
    destruct inp. reflexivity.
  - destruct inp. exact Hvl.
  - exists brk. destruct inp. exact Hlau.
Qed.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase draw lim inp K (Hrd : in_channel_reader inp = true),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw mbase Hrd) sp (in_argv inp) (in_envp inp) tid regs mem ->
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x17868 : word) mem (seg_rom rsegs))
                           (with_tid tid (with_vdso (vdso_run_init (ed_vdso draw))
                                            (init_model (segments_reserved rsegs) brk mbase sp lim inp)))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hrd Hsp Hva Hve Hvl Hlau HK.
  refine (@Startup.ref_startup v2_reloc v2_code v2_sites v2_img v2_data v2_rw v2_start
            rpc _ sp brk mbase draw lim inp K Hsp Hva Hve Hvl Hlau _).
  - apply bv_eq; reflexivity.
  - intros tid regs mem Htid ME.
    pose proof (HK tid regs mem Htid (main_entry_L _ _ _ _ _ _ _ _ Hrd Hvl Hlau ME)) as R.
    bvlit64_to_Z_in R. exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.
  Local Notation IMG := (wrap_mem (inpA av ev) a_mbase RPH (Z_to_bv 64 (Z.of_N rpc)) sp0 a_draw) (only parsing).

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs IMG a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = IMG a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (wok_lo sp0 <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & HJ & ->).
    rewrite cmem_at_win by (unfold in_win; lia). apply HJ. unfold in_win. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (wok_lo sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply store_ok_cmem_win; [exact HJ | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 (inpA av ev) a_draw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 (inpA av ev) a_draw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & HJ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.

(* The entry stack image's layout facts, read through [main_entry]: the strings, argv and argc
   above sp0, via the shared ArgvEnv/RefLayout/CatExec lemmas at [inpA av ev]. *)
Section Layout.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Local Notation ENT := (Z_to_bv 64 (Z.of_N rpc)) (only parsing).
  Local Notation STK := (stack_to_mem sp0 (entry_stack_image (inpA av ev) a_mbase RPH ENT sp0 a_draw)) (only parsing).

  Lemma me_vl' : valid_launch (inpA av ev).
  Proof using ME. exact (me_vl _ _ _ _ _ _ ME). Qed.
  Lemma ly_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma ly_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma ly_len_av : (1 <= length av <= 1024)%nat. Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  Ltac lyctx Hl := first [ exact Hva | exact Hve | exact me_vl' | exact Hl | exact ly_lo | exact ly_hi
                         | exact (proj2 (proj2 Hvsp)) ].

  Lemma me_rdn_stack : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs STK a n.
  Proof using ME Hva Hve Hvsp.
    intros segs a n Ha Hn. rewrite (main_entry_rdn_above _ _ _ _ _ _ ME) by assumption.
    apply PropExec.rdn_wrap_stack_above; assumption.
  Qed.

  Lemma me_argc : forall segs, rdn segs mem sp0 8%nat = Some (word_le8 (argcN (inpA av ev))).
  Proof using ME Hva Hve Hvsp.
    intros segs. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl]. pose proof ly_hi.
    rewrite (main_entry_rdn_above _ _ _ _ _ _ ME) by lia.
    eapply read_argc_w; lyctx Hl.
  Qed.

  Lemma me_argv_ptr : forall segs k, (k < length av)%nat ->
    rdn segs mem (sp0 + nat_to_word (8 + 8 * k)) 8%nat
    = Some (word_le8 (cat_argv_ptr (ed_top a_draw) av ev a_execfn k)).
  Proof using ME Hva Hve Hvsp.
    intros segs k Hk. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl]. pose proof ly_hi. pose proof ly_lo.
    pose proof ly_len_av. pose proof (PropExec.u64_range sp0).
    rewrite (main_entry_rdn_above _ _ _ _ _ _ ME) by (rewrite StepTac.word_add_nat, StepTac.u_Z2bv by lia; lia).
    eapply read_argv_ptr_w; first [lyctx Hl | exact Hk].
  Qed.

  Lemma me_argv_null : forall segs,
    rdn segs mem (sp0 + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
  Proof using ME Hva Hve Hvsp.
    intros segs. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl]. pose proof ly_hi. pose proof ly_lo.
    pose proof ly_len_av. pose proof (PropExec.u64_range sp0).
    rewrite me_rdn_stack by (rewrite StepTac.word_add_nat, StepTac.u_Z2bv by lia; lia).
    eapply read_argv_null; lyctx Hl.
  Qed.

  Lemma me_argv_bounds : forall k, (k < length av)%nat ->
    (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k))%Z /\
    (bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k) + Z.of_nat (length (nth k av [])) + 1 < 2^64)%Z.
  Proof using ME Hva Hve Hvsp.
    intros k Hk. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl].
    exact (OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.SeqExec.argv_ptr_bounds
             Sv48 (inpA av ev) a_mbase sp0 brk a_draw k Hl Hk).
  Qed.

  Lemma me_argv_byte : forall segs k j, (k < length av)%nat -> (j <= length (nth k av []))%nat ->
    rdn segs mem (cat_argv_ptr (ed_top a_draw) av ev a_execfn k + nat_to_word j) 1%nat
    = Some [nth j (nth k av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
  Proof using ME Hva Hve Hvsp.
    intros segs k j Hk Hj. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl].
    destruct (me_argv_bounds k Hk) as [B1 B2].
    pose proof (PropExec.u64_range (cat_argv_ptr (ed_top a_draw) av ev a_execfn k)).
    pose proof (PropExec.u64_range sp0).
    rewrite me_rdn_stack by (rewrite StepTac.word_add_nat, StepTac.u_Z2bv by lia; lia).
    exact (CatExec.read_argv_byte_k Sv48 segs (inpA av ev) a_mbase RPH ENT sp0 brk a_draw k j Hl Hk Hj).
  Qed.

  Lemma me_argv_str : forall segs k, (k < length av)%nat ->
    rdn segs mem (cat_argv_ptr (ed_top a_draw) av ev a_execfn k) (length (nth k av []))
    = Some (nth k av []).
  Proof using ME Hva Hve Hvsp.
    intros segs k Hk. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl].
    destruct (me_argv_bounds k Hk) as [B1 B2].
    rewrite me_rdn_stack by lia.
    exact (CatExec.read_argv_str_k Sv48 segs (inpA av ev) a_mbase RPH ENT sp0 brk a_draw k Hl Hk).
  Qed.

  Lemma tab_firstn_S : forall k (l : list (list byte)), (k < length l)%nat ->
    (PropExec.total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= PropExec.total_arg_bytes_nat l)%nat.
  Proof.
    induction k as [|k IH]; intros l Hk.
    - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth]. rewrite CatExec.total_arg_bytes_cons. cbn. lia.
    - destruct l as [|s0 l']; [cbn in Hk; lia|]. cbn [firstn nth length] in *. rewrite !CatExec.total_arg_bytes_cons.
      specialize (IH l' ltac:(lia)). lia.
  Qed.

  (* each argv string ends below the stack top, so below the user address limit *)
  Lemma me_argv_fits : forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k) + Z.of_nat (length (nth k av [])) + 1
     <= 0x800000000000)%Z.
  Proof using ME Hva Hve Hvsp.
    intros k Hk. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl].
    pose proof ly_hi. pose proof ly_lo.
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k)
                 = (bv_unsigned sp0
                    + Z.of_nat (CatExec.cat_string_off (kb_rseq a_kernel) sp0 (ed_top a_draw) av ev a_execfn
                                + PropExec.total_arg_bytes_nat (firstn k av)))%Z).
    { eapply u_cat_argv_ptr with (inp := inpA av ev); first [lyctx Hl | exact Hk | exact RPH | exact ENT | exact rsegs]. }
    assert (Hsb : (CatExec.cat_string_off (kb_rseq a_kernel) sp0 (ed_top a_draw) av ev a_execfn
                   + PropExec.total_arg_bytes_nat av + PropExec.total_arg_bytes_nat ev
                   <= length (entry_stack_image (inpA av ev) a_mbase RPH ENT sp0 a_draw))%nat).
    { unshelve eapply struct_av_bound with (inp := inpA av ev);
        first [lyctx Hl | exact rsegs | exact Sv48 | exact brk]. }
    pose proof (PropExec.length_entry_stack_image_launch Sv48 (inpA av ev) a_mbase RPH ENT sp0 brk a_draw Hl) as Hlen.
    pose proof (PropExec.entry_page_top_within_window Sv48 (inpA av ev) a_mbase sp0 brk a_draw Hl) as Htop.
    unfold entry_page_top, va_stack_top in Htop. cbv [sp_window_hi] in Htop.
    pose proof (tab_firstn_S k av Hk). lia.
  Qed.

  (* each argv string starts within the entry image, which is at most 2101782 bytes long *)
  Lemma me_argv_near : forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k) + Z.of_nat (length (nth k av [])) + 1
     <= bv_unsigned sp0 + 2101782)%Z.
  Proof using ME Hva Hve Hvsp.
    intros k Hk. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl].
    pose proof ly_hi. pose proof ly_lo.
    assert (Hu : bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k)
                 = (bv_unsigned sp0
                    + Z.of_nat (CatExec.cat_string_off (kb_rseq a_kernel) sp0 (ed_top a_draw) av ev a_execfn
                                + PropExec.total_arg_bytes_nat (firstn k av)))%Z).
    { eapply u_cat_argv_ptr with (inp := inpA av ev); first [lyctx Hl | exact Hk | exact RPH | exact ENT | exact rsegs]. }
    assert (Hsb : (CatExec.cat_string_off (kb_rseq a_kernel) sp0 (ed_top a_draw) av ev a_execfn
                   + PropExec.total_arg_bytes_nat av + PropExec.total_arg_bytes_nat ev
                   <= length (entry_stack_image (inpA av ev) a_mbase RPH ENT sp0 a_draw))%nat).
    { unshelve eapply struct_av_bound with (inp := inpA av ev);
        first [lyctx Hl | exact rsegs | exact Sv48 | exact brk]. }
    assert (Hbl : (Z.of_nat (length (entry_stack_image (inpA av ev) a_mbase RPH ENT sp0 a_draw)) <= 2101782)%Z).
    { unshelve eapply lay_bsb_len with (inp := inpA av ev);
        first [lyctx Hl | exact rsegs | exact Sv48 | exact brk]. }
    pose proof (tab_firstn_S k av Hk). lia.
  Qed.

  (* the 8 bytes after an argv string's last character are mapped (the terminator and what follows
     it in the entry image) *)
  Lemma me_word_after : forall segs k, (k < length av)%nat ->
    exists t8, rdn segs mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top a_draw) av ev a_execfn k)
                                         + Z.of_nat (length (nth k av [])))) 8 = Some t8.
  Proof using ME Hva Hve Hvsp.
    intros segs k Hk. destruct (me_lau _ _ _ _ _ _ ME) as [brk Hl].
    destruct (me_argv_bounds k Hk) as [B1 B2]. pose proof (me_argv_fits k Hk) as Bf. pose proof ly_lo.
    destruct (MuslStrlen.read_word_stack Sv48 segs (inpA av ev) a_mbase RPH ENT sp0 brk a_draw k
                (length (nth k av [])) Hl Hk (le_n _)
                (PropExec.entry_stack_image_no_wrap Sv48 (inpA av ev) a_mbase RPH ENT sp0 brk a_draw Hl))
      as (t8 & _ & Hr).
    exists t8. rewrite StepTac.word_add_nat in Hr.
    rewrite me_rdn_stack; [exact Hr | rewrite StepTac.u_Z2bv by lia; lia | rewrite StepTac.u_Z2bv by lia; lia].
  Qed.
End Layout.
