(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (19 recorded proofs replaced by written proofs (rimplT_guard, rimplT_rd8, rimplT_rd16 and 16 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_enframe.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocKit_B2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMallocKit_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocKit_B2 () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree<rimplT_undefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5Plain;RMallocTree;rimplT_peekC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_B2<peek_ok_pansC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2:rimplT_rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4rd32C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib5Plain:RMallocRepArmrep_shadow_readC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>pans_mem_rangeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6Malloc9MallocRep;b8_unsignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib5Plain:RMallocRepCrreserved_disjoint1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg@ref_seg_rom_noneC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2:rwview_extC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B?rbytes_at_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2<rwr_at_agreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5Plain<RMallocKit_B8rrepfootC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2@rgrp_region_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2@rrw_cells_agree'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr<u64arr_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B>actives_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B=usages_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BAunmap_seqs_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B?bouncess_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib5Plain<RMallocKit_B<rrepfoot_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2>ru64arr_agree'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2=ru8arr_agree'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B>rrepfoot_mlockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B;rrepfoot_nlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B=rrepfoot_pgszC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B<rrepfoot_gotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B>rrepfoot_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B=rrepfoot_areaC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B>rrepfoot_groupC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib5Plain:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib5Plain<RMallocKit_B>rrepfoot_knownC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02c59OSSVerify5KrLib5Plain=RMallocKit_B2Ermrep_transport_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_B2Brpres_except_agreeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof.
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.

Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.

(* [comment removed for export] *)
Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)
Lemma rrdv_range : forall o st m q r,
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  0 <= rdv pans_mem o st q < 256.
Proof.
  intros o st m q r MR Hr Hk Ho. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - exact (proj2 (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E)).
  - apply pans_mem_range.
Qed.

(* [comment removed for export] *)
Lemma rrdv_cur : forall o st mX q r (x : byte),
  rmrep st mX ->
  (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  (forall h, cell_read (get_shadow st (fst q)) (snd q) = Unknown h -> o (wa (r_base r + snd q)) = mX (wa (r_base r + snd q))) ->
  bytes_at psegs mX (r_base r + snd q) [x] ->
  rdv pans_mem o st q = bv_unsigned x.
Proof.
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read psegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). atop_facts.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rwview_ext : forall m m' a, m' a = m a -> wview psegs m' a = wview psegs m a.
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

Lemma rwr_at_agree : forall m m' A n, wr_at psegs m A n -> agree_on m m' A n -> wr_at psegs m' A n.
Proof.
  intros m m' A n (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree' : forall m m' A cs,
  rw_cells psegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree' : forall m m' A ws,
  u64arr psegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr psegs m' A ws.
Proof.
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree' : forall m m' A bs,
  u8arr psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr psegs m' A bs.
Proof. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

Lemma rstk_agree : forall m m' lo hi, stk psegs m lo hi -> agree_on m m' lo (hi - lo) -> stk psegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & HS) AG. split; [exact H0|]. split; [exact H1|].
  intros a Ha. rewrite (rwview_ext m m') by (apply AG; lia). unfold mrd. rewrite (AG a) by lia. apply HS. exact Ha.
Qed.



(* [comment removed for export] *)
Definition rgrp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

Lemma rmrep_transport_agree : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a -> m' (wa a) = m (wa a)) ->
  (forall a, 0 <= a < 2^64 -> rgrp_region_addr st a -> wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None) ->
  rmrep st m'.
Proof.
  intros st m m' (WF & CX & GL & AR & GR & SH) AG WG.
  pose proof WF as (Hres & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells psegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells psegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound psegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound psegs m _ _ C2) as B2. pose proof (u64arr_bound psegs m _ _ C3) as B3.
    pose proof (u8arr_bound psegs m _ _ C4) as B4. pose proof (u8arr_bound psegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    destruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). atop_facts.
    split.
    + destruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| exists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rmrep_transport_agree' : forall st m m',
  rmrep st m ->
  (forall a, 0 <= a < 2^64 -> rrepfoot st a \/ rgrp_region_addr st a -> m' (wa a) = m (wa a)) ->
  rmrep st m'.
Proof.
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_of_munch_nw : forall C W m m',
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.

Lemma rpres_except_agree : forall C m m' A n,
  rpres_except C m m' -> 0 <= A -> A + n <= 2^64 -> (forall a, A <= a < A + n -> ~ C a) -> agree_on m m' A n.
Proof. intros C m m' A n HP HA HB HC a Ha. apply (HP a); [lia| apply HC; exact Ha]. Qed.

Lemma ru64arr_pres : forall C m m' A ws,
  rpres_except C m m' -> u64arr psegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> ~ C a) -> u64arr psegs m' A ws.
Proof.
  intros C m m' A ws HP H HC. pose proof (u64arr_bound psegs m A ws H).
  eapply ru64arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

Lemma ru8arr_pres : forall C m m' A bs,
  rpres_except C m m' -> u8arr psegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> u8arr psegs m' A bs.
Proof.
  intros C m m' A bs HP H HC. pose proof (u8arr_bound psegs m A bs H).
  eapply ru8arr_agree'; [exact H|]. eapply rpres_except_agree; eauto; lia.
Qed.

End CANSEC1.
