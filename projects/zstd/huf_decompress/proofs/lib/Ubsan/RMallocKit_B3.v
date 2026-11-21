(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (rmrep_set_usage, rmrep_set_seq, rmrep_set_unmap_seq and 1 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free MallocModel_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocKit_B3 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp8fin_mapsBlookup_delete_SomeI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B=usages_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_B3@usages_set_usageC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B@rmrep_ctx_frameWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BAunmap_seqs_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_B3>unmap_seqs_setC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5Ubsan:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B?rmrep_del_groupC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib5Ubsan:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5Ubsan:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B8rrepfootC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B9ivs_avoidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_BGrmrep_transport_unownedC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B?rmrep_del_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocModel_B7grp_delC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rmrep_set_usage : forall st m sc v,
  rmrep st m -> 0 <= sc < 48 ->
  rmrep (set_usage sc v st) (write_to_mem m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v))).
Proof.
  intros st m sc v MR Hsc. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (wz v)) as L8.
  pose proof (munch_write [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8)] m m (RCTX + 464 + 8 * sc) (le8 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v)) (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite usages_set_usage by lia. replace (RCTX + 464 + 8 * sc) with ((RCTX + 464) + 8 * sc) by lia.
    apply u64arr_write; [exact X3| rewrite usages_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmrep_set_seq : forall st m v,
  rmrep st m -> 0 <= v < 256 ->
  rmrep (upd_ctx (set_seq v) st) (write_to_mem m (wa (RCTX + 912)) [b8 v]).
Proof.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 912, RCTX + 913)] m m (RCTX + 912) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 912)) [b8 v] (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left.
    pose proof (rw_cells_write usegs m (RCTX + 912) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
    rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
    unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. exact W.
Qed.

(* [comment removed for export] *)
Lemma rmrep_set_unmap_seq : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) (write_to_mem m (wa (RCTX + 848 + i)) [b8 v]).
Proof.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 848 + i, RCTX + 848 + i + 1)] m m (RCTX + 848 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 848 + i)) [b8 v] (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite unmap_seqs_set by lia. replace (RCTX + 848 + i) with ((RCTX + 848) + i) by lia.
    apply (u8arr_write usegs m (RCTX + 848) (unmap_seqs st) i (b8 v)); [exact X4| rewrite unmap_seqs_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmrep_group_hdr_zero : forall st m p gh bs,
  rmrep st m -> (s_groups st) !! p = Some gh ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  length bs = 8%nat ->
  rmrep (del_group p st) (write_to_mem m (wa (conc st p)) bs).
Proof.
  intros st m p gh bs MR Hp UNK L8.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (rgroup_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  pose proof (round_up_pg_ge (r_len r)) as RU. atop_facts.
  eapply rmrep_transport_unowned.
  - apply rmrep_del_group. exact MR.
  - apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
  - apply wmono_write. apply wmono_refl.
  - intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin). cbn in Hak.
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
      assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      change (conc (del_group p st) ak) with (conc st ak) in Hin.
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
      destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
    + destruct C as (b & gh' & Hb & Hin). cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
      change (conc (del_group p st) b) with (conc st b) in Hin.
      destruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _).
      destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
        (Z.div_mod_to_equations; lia).
      * pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
    + destruct C as (rid & r' & v & Hr' & Hk' & Hin & HC). cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
      destruct (N.eq_dec rid (fst p)) as [E|NE].
      * subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
        destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
      * pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
Qed.

Lemma rmrep_grp_del_eq : forall st m g p, rmrep (del_group p st) m -> rmrep (grp_del st g p) m.
Proof. intros. unfold grp_del. apply rmrep_del_slots. exact H. Qed.
End CANSEC1.
