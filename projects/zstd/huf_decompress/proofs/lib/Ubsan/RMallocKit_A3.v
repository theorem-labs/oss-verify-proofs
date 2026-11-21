(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (rmrep_set_bounce, rconc_meta_inj, rmrep_regroup and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocKit_A3 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic6eq_indI35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base6LookupC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4gmapBgmap_partial_alterK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5Ubsan:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init9Datatypes6lengthK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B?bouncess_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_A3<bouncess_setC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B@rmrep_ctx_frameWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes3nat00I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5Ubsan:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C35stdpp4base7is_SomeK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Malloc9MallocRep9conc_aaddC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5Ubsan:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC47Corelib4Init5Logic9False_indC35stdpp4base6lookupC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5Ubsan:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B?rmrep_del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B8rrepfootC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepBrreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideC35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B=ivs_avoid_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B>ivs_avoid_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_BGrmrep_transport_unownedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan=RMallocKit_A2Crmrep_put_group_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_A3=put_group_delC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A3=rmrep_regroupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_A3?set_group_ai_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib6Malloc9MallocRep;wz_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z6inj_le".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1. Context {rc : runConstT}.
Lemma rmrep_set_bounce : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write usegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof.
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

End CANSEC2.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; tauto]);
    clear MUq WMq CH end.

(* [comment removed for export] *)
Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section CANSEC3. Context {rc : runConstT}.
Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some gh ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono usegs m m' ->
  rw_cells usegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m'.
Proof.
  intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
  pose proof (rmrep_del_group st m b MR) as MR1.
  assert (MR2 : rmrep (del_group b st) m').
  { eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
    intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
    pose proof (round_up_pg_ge (r_len r)).
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
      destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
      rewrite lookup_delete_ne in Hb2 by congruence.
      destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
      destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
      + rewrite E, Hr in Hr2. inversion Hr2; subst r2.
        assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
        assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
      + destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
    - change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
      destruct (N.eq_dec q (fst b)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
        rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold RGOT_SSP in R8. lia.
    - unfold RSSP_GUARD in R9. lia. }
  rewrite <- put_group_del.
  eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
  unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono usegs m m' ->
  rw_cells usegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (set_group_active_idx b ai st) m'.
Proof.
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
  ov_read_bytes usegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof.
  intros st m (_ & (HD & _) & _) CR.
  destruct HD as [[_ HB] _]. unfold rctx_head_cells, rsecw in HB. cbn [cells_bytes cbytes app] in HB.
  rewrite (bytes_at_read usegs m RCTX _ 12 1 HB).
  all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
  change (Z.to_nat 12) with 12%nat.
  unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
  rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End CANSEC3.
