(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (rbytes_at_zeros_sub, rrw_cells_of_zeros, rmrep_set_area_next and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_am_K () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_transI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C46Stdlib5Lists4List@nth_error_repeatK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib5Lists4List9nth_errorI47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Malloc6F_am_K<zeros_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C47Corelib5Lists7ListDef6repeatK47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain7RF_am_KCrbytes_at_zeros_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9wr_at_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_freeArw_cells_of_bytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeC59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B?rrw_cells_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C35stdpp4base6insertC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5Plain:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5Plain:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib6Malloc;MallocKit_B>actives_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib5Plain<RMallocKit_B=ru64arr_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B=usages_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BAunmap_seqs_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B<ru8arr_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B?bouncess_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5oconcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5Plain:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Plain:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame?wr_at_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B?rbytes_at_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B8rrepfootC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3sub".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1. Context {rc : runConstT}.
Lemma rbytes_at_zeros_sub m A n off k :
  bytes_at psegs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at psegs m (A + off) (zeros k).
Proof.
  intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
  intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrw_cells_of_zeros m A n off cs :
  bytes_at psegs m A (zeros n) -> wr_at psegs m A (Z.of_nat n) ->
  cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
  0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
  rw_cells psegs m (A + off) cs.
Proof.
  intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
  - rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
  - eapply wr_at_sub; [exact HW| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_set_area_next : forall st m m' a ar p,
  rmrep st m -> (s_areas st) !! a = Some ar -> is_Some ((s_regions st) !! (fst p)) ->
  munch [(conc st a + 8, conc st a + 16)]%Z m m' -> wmono psegs m m' ->
  rw_cells psegs m' (conc st a) [C8 (wz SECRET); C8 (wz (conc st p)); C4 (wz (a_nslots ar)); C4 (wz 0)] ->
  rmrep (set_areas (<[a := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st)) st) m'.
Proof.
  intros st m m' a ar p MR Ha Hp MU WM CH.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts.
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  assert (AG : forall A cs, rw_cells psegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells psegs m' A cs).
  { intros A cs H HD. pose proof (rw_cells_bound psegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
    intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - (* [comment removed for export] *) destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    unfold rmrep_ctx. change (rctx_head_cells st') with (rctx_head_cells st). change (actives st') with (actives st).
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    change (ctx_tail_cells st') with (ctx_tail_cells st).
    split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
    split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    apply AG; [exact C6| cbn; unfold RCTX; lia].
  - (* [comment removed for export] *) destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
    split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia].
  - (* [comment removed for export] *) intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
    destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
      split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
      * apply AG; [exact A3| cbn; lia].
    + rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
      destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
      assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
        - rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
          assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
          Z.div_mod_to_equations. lia.
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
      change (pw st' (a_next ar')) with (pw st (a_next ar')).
      split; [apply AG; [exact A1| cbn; lia]|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
      * apply AG; [exact A3| cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
    rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
    cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
    + eapply wr_at_transport; [exact HWr| exact WM].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
      eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); atop_facts; pose proof (round_up_pg_ge (r_len r)); lia).
      assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_new_area : forall st m (p : aptr) r chk,
  rmrep st m -> (s_areas st) !! p = None ->
  (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
  (forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  rw_cells psegs m (conc st p) [C8 (wz SECRET); C8 (wz 0); C4 (wz NSLOTS); C4 (wz 0)] ->
  (forall k, 0 <= k < NSLOTS -> rw_cells psegs m (conc st p + AREA_HDR + META_SIZE * k) (meta_cells st meta0)) ->
  rw_cells psegs m (conc st p + 4064) [CB 32 (zeros 32)] ->
  rmrep (set_areas (<[p := mkArea chk None NSLOTS]> (s_areas st)) st) m.
Proof.
  intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
    + exists r. repeat split; assumption.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - exact CX.
  - exact GL.
  - intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
    destruct (decide (a' = p)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
      split; [exact HDR|]. split; [| exact PAD].
      intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
  - exact GR.
  - exact SH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rfresh_page_avoids : forall st m (p : aptr) r a,
  rmrep st m -> (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup ->
  0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) -> snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
  (s_areas st) !! p = None ->
  conc st p <= a < conc st p + 4096 -> ~ rrepfoot st a.
Proof.
  intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). atop_facts.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - destruct C as (ak & ar & Hak & Hin).
    destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
    destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
    + rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
      assert (NEo : snd ak <> snd p).
      { intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
      Z.div_mod_to_equations. lia.
    + pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
  - destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
    assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
    pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
    assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
    pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

End CANSEC1.
