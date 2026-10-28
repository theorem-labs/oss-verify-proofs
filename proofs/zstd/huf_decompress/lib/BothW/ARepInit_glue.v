(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA ModelX.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA BothHandoff.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth BothEntry.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init
     ADepot_iface ADepot ADepot_init F_adepot ARepFrame ARepInit_kit ARepInit_A ARepInit_D ARepInit AMain_asm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepInit_glue () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes6lengthK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC4ARocqVerifyHarness?AgentSubmission8BothMain:amain_openC4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7atop_ofC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_space_beg0C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_ptr_array0C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5ainitC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyK47Corelib4Init9Datatypes6option02C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry:hidden_argC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC5ARocqVerifyHarness?AgentSubmission5BothW8F_adepot<adepot_ifaceC5ARocqVerifyHarness?AgentSubmission5BothW<ADepot_iface6ADEPOTC5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface5AFAKEK5ARocqVerifyHarness?AgentSubmission5BothW4ARep6aholes01C5ARocqVerifyHarness?AgentSubmission5BothW9AMain_asm4RNG0C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pfact_okC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry8ashadow0C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic3and00C46Stdlib5Lists4List:Forall_appC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry@asan_mem_facts_wC5ARocqVerifyHarness?AgentSubmission2AS9BothEntryAasan_pure_facts_wC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry4WblkC47Corelib4Init5Logic8eq_ind_rC5ARocqVerifyHarness?AgentSubmission4LibA6ModelX2MXC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8allow_ofC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8aallowedC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Peano2le00K47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_VC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_D8sb_factsC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadI47Corelib4Init5Logic2or00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6divideC56Stdlib6ZArith6BinInt1Z:mod_divideC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z7mod_mulK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission5BothW8ARepInit@AHEAP_P_init_qdfC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_A3ST0C5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP7AHEAP_PC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit2LVK5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout01C4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8mfact_okC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8wrap_memC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ARocqVerifyHarness?AgentSubmission8BothMain7amodelHC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7resv_ofC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_initC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps5aps_mC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth>asan_mem_factsI5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth?asan_pure_factsC5ARocqVerifyHarness?AgentSubmission5BothW4BImg7b_phdrsI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7K_ALIGNI4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg9b_init_pcC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_A2X0C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry3ARAC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry3AGPC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry3ATPC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry5AMAINC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5AQUARI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00I46Stdlib5Lists4List6Exists00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth8asan_visI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<K_SPACE_SIZEC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_SPACE_EXTRAI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega3Op203".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Glue.
  Variable A0 : (nat -> Z) -> alw.
  Hypothesis A0I : A0_init_stmt A0.
  (* [comment removed for export] *)
  Hypothesis ASH : forall V (p : word) (c k : Z), 0 <= a_space_beg0 V -> a_space_beg0 V mod 4096 = 0 ->
    bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
    (bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c - 4096
     \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c + 32768 * k)) -> A0 V p.
  Variable U : list (list Z).
  Hypothesis HU : (length U <= 4096)%nat.
  Hypothesis HU' : Forall (fun u => (length u <= 254)%nat) U.
  Variable ASEC : alayout -> astate -> aconc -> amem -> Prop.

  Theorem aheapP_at_main : forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
    ASEC (mkALayout (LV V) w U) (ainit (a_space_beg0 V) (a_ptr_array0 V)) X0 m ->
    AHEAP_P (mkAHoles AQUAR ASEC (ADEPOT adepot_iface) AFAKE) (mkALayout (LV V) w U) (RNG0 A0 V mo)
            (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) [] m.
Proof.
    intros en inp w V m ms mo _ _ HM HA HS.
    pose proof HM as (_ & _ & PIN & HMF & HPF & _ & _ & _ & SH0 & _).
    apply Forall_app in HMF as [HMF HMW]. apply Forall_app in HPF as [HPF _].
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
    { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    change (aps_m (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP)) with (ST0 V).
    unfold RNG0. apply AHEAP_P_init_qdf; try assumption.
    - intros p Hp Ha. apply A0I; assumption.
    - assert (E : al_space_beg (mkALayout (LV V) w U) = a_space_beg0 V) by (unfold al_space_beg, a_space_beg0; cbn [al_V LV Nat.eqb]; lia).
      pose proof (ARepInit_D.sb_facts V w U HPF HU HAT) as (S1 & _ & S3 & S4). rewrite ?E in S1. rewrite ?E in S3. rewrite ?E in S4.
      assert (SAL : a_space_beg0 V mod 4096 = 0).
      { unfold K_ALIGN in S3. apply (Z.mod_divide _ 65536) in S3; [|lia]. destruct S3 as [q Hq]. rewrite Hq.
        replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia. }
      rewrite E. intros p c k Hp Hc Hr. exact (ASH V p c k ltac:(lia) SAL Hp Hc Hr).
  Qed.
End Glue.
End CANSEC1.
