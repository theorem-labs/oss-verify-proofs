(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the pins record re-proved by tactics in place of its recorded (KReplay) proof, for the start-up data image over the launch input and the auxv lemma over the launch's stack image). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymDrive SymDriveX.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec Hoare AllocIface MemSplit RefLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocInv_auxv AllocBase AllocCalloc MallocAllocLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2Startup O2StartupDefs O2StartupFacts O2MainEntry O2Open O2Malloc65536 O2Main.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Pins () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC69OSSVerify5KrLib6Common8Mallocng<MallocLayout9PC_MALLOCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_malloc_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7PC_FREEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface:al_free_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayout@mallocng_globalsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C59OSSVerify5KrLib6Common:AllocIface:al_globalsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutBmallocng_grantableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface<al_grantableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutCmallocng_errno_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface=al_errno_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayout>mallocng_in_roC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Common:AllocIface8al_in_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayout>mallocng_in_rwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface8al_in_rwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface;al_image_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface9al_ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIfaceAal_mmap_thresholdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpI59OSSVerify5KrLib2O29O2Startup:main_entry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2Malloc655366env_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Open9above_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayout<mallocng_envC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2or00C69OSSVerify5KrLib6Common9CliDriver3Amb7a_hwcapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2=O2StartupDefs6D_mainC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3subC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib2O29O2StartupCmain_entry_mem_dataC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib6Common9CliDriver9SymDriveX9rdn_agreeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC69OSSVerify5KrLib6Common8Mallocng>MallocInv_auxv7aux_envC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2StartupFacts<D_main_missbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry;D_main_noneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2O2>O2StartupFacts?D_main_pagesizeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib6Common9CliDriver3Amb5a_uidC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC59OSSVerify5KrLib6Common8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec=wrap_above_spC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O29O2StartupDmain_entry_mem_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9RefLayout8auxv_offC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8C59OSSVerify5KrLib2O2;O2MainEntry5auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry8auxvp_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2MainEntry<D_main_auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec>n_to_le_8_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout7ml_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6A_LIBCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng>MallocInv_auxv=aux_env_introC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common8Mallocng<MallocLayout<A_NEED_LOCKSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout;A_PAGE_SIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout6IMG_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout5RW_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng<MallocLayout9A_GOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_envC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2O26O2Main4pins01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib2O2>O2MallocLayout4LS16C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib6Common8Mallocng<MallocLayout8CTX_SIZEC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutGmallocng_mmap_thresholdC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9CliDriver3Amb3Amb00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeK46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_valI47Corelib4Init5Logic5False00C79OSSVerify5KrLib2O2>O2MallocLayout6ImgS161M?loaded_segmentsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O26O2Pins>need_locks_imgC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M5phdrsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x69acb) 1 = Some [Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_O2Pins ()) [] "p;1p;2p;3p;4g0000j10Tg000Uj16Tg0013j13Tg001Vj17Tg0026j1ATg002Xj2<Tg003Kj3;Tg003nj1:Tg004Nj32Tg004nj24Tg005Pj28Tg005jj19Tg006Lj11Tg0071j1@Tg007Oj25Tg0085j1?Tg008Tj4=Tg009Lj3>Tg009fR0#0#0#0R1#6R2#3R3#7R4#AR5g00:KR61<265;2%:3R7523,44'8g00:i%01#0#0#6R1#3%93U%10#0#1#0#0#1#1#0#1#0#1#1#0#0#1#0#1#1#@,51g00<O#?C=1526=237,445>5do"). Qed.

Theorem s16_pins : @O2Main.pins (@mallocng_alloc_layout LS16).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LS16] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    pose proof Hvsp as (Hlo & Hhi & Hal).
    assert (Hlo' : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact Hlo.
    assert (Hhi' : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact Hhi.
    (* the libc globals window agrees with the start-up data image [D_main] *)
    assert (LIBC : forall segs (a : Z) n, (0x69aa0 <= a)%Z -> (a + Z.of_nat n <= 0x69b38)%Z ->
              rdn segs M (Z_to_bv 64 a) n = rdn segs (D_main sp0 (inpA [a0s; path] envv) a_draw tid) (Z_to_bv 64 a) n).
    { intros segs a n H1 H2. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME).
      rewrite u_small by lia. rewrite stack_max_size_val. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16].
    split; [| split; [| split; [| split]]].
    + rewrite LIBC by lia. etransitivity; [| exact need_locks_img]. apply rdn_agree. intros j Hj.
      assert (j = 0%nat) by lia. subst j. rewrite u_small by lia.
      replace (0x69acb + Z.of_nat 0)%Z with 0x69acb%Z by lia. cbv beta.
      apply D_main_none; [exact Hva | exact Hlo' | exact Hhi' | reflexivity].
    + rewrite LIBC by lia. etransitivity; [eapply D_main_pagesize; eassumption |]. reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + destruct (me_lau _ _ _ _ _ _ ME) as (brk & Hlau).
      eapply (aux_env_intro (ML := LS16) (inpA [a0s; path] envv) a_mbase _ _ sp0 brk a_draw M).
      * exact Hva.
      * exact Hve.
      * exact (me_vl _ _ _ _ _ _ ME).
      * exact Hlau.
      * exact Hlo.
      * exact Hhi.
      * exact Hal.
      * intros a Ha. rewrite (HEa a Ha). rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha).
        apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS16]. rewrite u_small by lia. replace (0x69ac8 + 8)%Z with 0x69ad0%Z by lia.
        rewrite LIBC by lia.
        etransitivity; [eapply D_main_auxvp; eassumption |].
        f_equal. f_equal. eapply auxvp_eq; eassumption.
    + intros a Ha. apply HEr. right. rewrite !u_small in Ha by lia. rewrite u_small by lia. lia.
Qed.
