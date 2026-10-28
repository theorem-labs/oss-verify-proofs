(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed BothHandoff.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth BothEntry PrimaryShadowB.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ALayout ARep ARepFrame AHeapP APoisonR_iface ASec ARepInit_kit ARepInit_A ARepInit_D.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepInit_S () := "I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeC35stdpp4base;RelDecisionI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_mapsAmap_to_list_emptyC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldK5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp01K47Corelib7Numbers7BinNums8positive02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp02K5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp04K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact01K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission2AS:MainExport9mfact_eqbC5ARocqVerifyHarness?AgentSubmission2AS:MainExport:mfact_findC5ARocqVerifyHarness?AgentSubmission2AS:MainExport8mfact_okK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z3lebC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem:rw_bytes_bC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit9img_chunkI45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef6repeatK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact02C5ARocqVerifyHarness?AgentSubmission2AS:MainExport5zerosC45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kitEbytes_eq_of_unsigned'C5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_ptr_arrayK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW4ARep7junk_atK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5BothW4ASec9asec_instK47Corelib4Init9Datatypes3nat02C46Stdlib5Lists4List7existsbK47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsI5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth>asan_mem_factsI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit2LVK5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout01C5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_A?alayout_ok_initC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout6ao_ptrC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout4aobjC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_A3ST0C5ARocqVerifyHarness?AgentSubmission5BothW4ASec8asec_arrI46Stdlib7Sorting;Permutation;Permutation00C5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP6sec_mbC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nsecC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nresC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init9Datatypes6option00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission5BothW4ASec8sec_liveC47Corelib4Init5Logic3iffC5ARocqVerifyHarness?AgentSubmission5BothW4ASec:asec_chunkC46Stdlib7Sorting;Permutation@Permutation_reflK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit:u64arr_nilC5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit<rw_cells_CB0C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00I5ARocqVerifyHarness?AgentSubmission5BothW7ALayout:alayout_ok00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_ptr_arrayC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP7sec_wf1I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission5BothW4ASec<sec_disjointC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_ptr_array0K47Corelib5Lists7ListDef6Forall01C5ARocqVerifyHarness?AgentSubmission5BothW4ASec7asec_wfC5ARocqVerifyHarness?AgentSubmission5BothW4ASec@sec_disjoint_nilC5ARocqVerifyHarness?AgentSubmission2AS>PrimaryShadowB?primary_shadow0C5ARocqVerifyHarness?AgentSubmission2AS>PrimaryShadowB:aspace_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5azeroC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_D6sb_eq'C56Stdlib6ZArith6BinInt1Z3divC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame9shlen_divC5ARocqVerifyHarness?AgentSubmission5BothW4ASec6aprim0C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl8K_REGIONK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW4ASec>astartup_hullsC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP6sec_msC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry8ashadow0K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact01C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit:pfact_eqb'C5ARocqVerifyHarness?AgentSubmission5BothW<ARepInit_kit;pfact_find'C5ARocqVerifyHarness?AgentSubmission2AS:MainExport8pfact_okC46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission2AS9BothEntry7ashadowC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry;ashadow_visC46Stdlib5Lists4List2InK5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp03K46Stdlib9micromega:ZMicromega;ZArithProof03K5ARocqVerifyHarness?AgentSubmission2AS:MainExport5mfact08C5ARocqVerifyHarness?AgentSubmission5BothW4ASec4ashzK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission2AS:MainExport2zvK46Stdlib9micromega7EnvRing5PExpr04I5ARocqVerifyHarness?AgentSubmission2AS:MainExport5pfact00C5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth?asan_pure_factsC5ARocqVerifyHarness?AgentSubmission2AS9BothEntry6ASHOFFK46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission2AS:MainExport4zexp00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:K_HIGH_MEMC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission2AS=MainFactsBoth<asan_vis_appc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_S<asec_wf_initc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_S=asec_arr_initc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_S>asec_inst_initc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_S;aprim0_initc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_S9ashz_initC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List6filterC35stdpp4base5emptyC35stdpp8fin_maps;map_to_listC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_space_beg0C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_qlocC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_qglobC46Stdlib5Lists4List8flat_mapC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP=sec_chunks_ofK5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate01K47Corelib7Numbers7BinNums1N01I47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP6is_secC45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6aclass00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl8b_chunksC5ARocqVerifyHarness?AgentSubmission5BothW4ASec5ASECcC5ARocqVerifyHarness?AgentSubmission5BothW4ASec7ASEC_ofC5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_A2X0c5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_S:ASECc_initc5ARocqVerifyHarness?AgentSubmission5BothW:ARepInit_SAsec_chunks_of_ST0".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Let L := mkALayout (LV V) w U.

(* [comment removed for export] *)

  Lemma asec_inst_init : asec_inst L m.
Proof.
    unfold asec_inst.
    mf V m HM (MCell (ZLit 748776) 8 (ZMul (ZLit 4096) (ZV 226))) F1.
    aimg V m HM 0xb6d18 [C1 (Z_to_bv 8 0)] I2.
    aimg V m HM 0xb6d20 [CB 32 (repeat (Z_to_bv 8 0) 32)] I3.
    aimg V m HM 0xb6d40 [CB 512 (repeat (Z_to_bv 8 0) 512)] I4.
    mf V m HM (MZeroC (ZLit 749377) 3) F5.
    assert (F5' : rw_cells bsegs m 749377 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F5.
    aimg V m HM 0xb6f58 [CB 16 (repeat (Z_to_bv 8 0) 16)] I6.
    split; [exact F1|]. split; [exists (Z_to_bv 8 0); exact I2|]. split; [exists (repeat (Z_to_bv 8 0) 32); exact I3|].
    split; [exists (repeat (Z_to_bv 8 0) 512); exact I4|]. split; [exact F5'|]. exists (repeat (Z_to_bv 8 0) 16); exact I6.
  Qed.

  Lemma asec_arr_init : asec_arr L (ST0 V) [] m.
Proof.
    pose proof (ao_ptr _ (alayout_ok_init V w U HP HU HAT)) as (_ & P1 & P2). atop_facts. change (mkALayout (LV V) w U) with L in P1, P2.
    exists []. split; [apply Permutation_refl|]. cbn [map a_nsec a_nres ST0 ainit].
    split; [apply u64arr_nil; lia|]. split; [| intros i ch Hi; destruct i; discriminate].
    exists []. rewrite Z.add_0_r. change (Z.to_nat (8 * (0 - 0))) with 0%nat. apply rw_cells_CB0; lia.
  Qed.

  Lemma asec_wf_init : asec_wf L (ST0 V) [].
Proof.
    unfold asec_wf. split; [exact (alayout_ok_init V w U HP HU HAT)|]. cbn. split; [reflexivity|]. split; [split; [reflexivity| lia]|]. split; [reflexivity|]. split; [lia|].
    split; [constructor| exact sec_disjoint_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma aprim0_init : aprim0 L m.
Proof.
    unfold aprim0. destruct (primary_shadow0 V m SH0 HP) as [Z0 W0]. rewrite (sb_eq' V w U HU) in Z0, W0. change (mkALayout (LV V) w U) with L in Z0, W0.
    unfold K_REGION. rewrite ARepFrame.shlen_div. change (2 ^ 32 / 8) with 536870912. change (2^34) with 17179869184 in Z0, W0.
    split; [intros i Hi; apply Z0; lia|].
    destruct W0 as (W1 & W2 & W3). split; [exact W1|]. split; [lia|]. intros i Hi. apply W3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ashz_init : ashz L [] m.
Proof.
    intros x Hx HF _. pose proof SH0 as SZ. unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.
    pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
    pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 6 0 255) P6.
    unfold astartup_hulls in HF. cbv [al_V L LV Nat.eqb] in HF.
    unfold al_store, al_nodes, al_fake, al_dtls, al_ctx, al_t, al_res, al_ptr_array in HF. cbv [al_V L LV Nat.eqb] in HF.
    repeat lazymatch type of HF with
           | Forall _ (_ :: _) => let H1 := fresh "NH" in pose proof (Forall_inv HF) as H1; cbn [fst snd] in H1; apply Forall_inv_tail in HF
           | _ => clear HF
           end.
    assert (SX : shad x = ASHOFF + x / 8) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; reflexivity). unfold ASHOFF in SX.
    destruct (Z.lt_ge_cases x (32768 * V 0%nat + 4096 * V 10%nat - 8388608)) as [LOW|WIN].
    - apply SZ.
      + unfold ashadow. rewrite SX. clear -Hx HAT P0 P6 P10. atop_facts. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
      + intros (bn & Hin & Hr). rewrite SX in Hr. unfold ASHOFF in Hr. unfold asan_vis_app in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [<- | Hin];
          [ cbn [fst snd zv] in Hr;
            first [ match reverse goal with NHk : ~ _ |- _ => solve [clear -Hr NHk P208 P209 P0 P10 Hx LOW; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])] end
                  | solve [clear -Hr P208 P209 P0 P10 Hx LOW; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])] ]
          | try (match reverse goal with NHk : ~ _ |- _ => clear NHk end) ]).
        exact Hin.
    - mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
      rewrite SX.
      replace (2147450880 + x / 8) with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (x / 8 - 4096 * V 0%nat - 512 * V 10%nat + 1048576))
        by (clear; lia).
      apply ZW. clear -Hx WIN HAT P0 P6 P10. atop_facts. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
  Qed.

  Theorem ASECc_init : ASECc [] L (ST0 V) X0 m.
Proof.
    split; [exact asec_wf_init|]. split; [exact asec_arr_init|]. split; [exact asec_inst_init|]. split; [exact aprim0_init| exact ashz_init].
  Qed.

  Lemma sec_chunks_of_ST0 : sec_chunks_of (ST0 V) = [].
Proof. unfold sec_chunks_of, achunks, ST0, ainit. cbn. rewrite ?map_to_list_empty. reflexivity. Qed.

  Theorem ASEC_of_init : ASEC_of L (ST0 V) X0 m.
Proof. unfold ASEC_of. rewrite sec_chunks_of_ST0. exact ASECc_init. Qed.
End S.
End CANSEC1.
