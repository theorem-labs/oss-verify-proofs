(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (renf_hyp_ret, rfail_hyp_ret, rmalloc_core_implT)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_malloc_core () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_malloc_join8renf_hypC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree:rimplT_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan>RF_malloc_join9rfail_hypC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree?rimplT_from_evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5Ubsan;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5Ubsan:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9expo_condC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib5Ubsan>RF_malloc_core6rcoreQC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan?RF_malloc_smallCrmalloc_small_implTC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_A8MFACTS_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib5Ubsan@RAllocSlot_iface<RAS_STACK_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan@RAllocSlot_iface9RAS_STACKC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMalloc_fp=rregion_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib6Malloc9MallocRep6W_highC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRepDrmrep_transport_highC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep>rmrep_set_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Malloc=MallocFacts_A8mf_ticksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRepAticks_ok_set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>unk_agree_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_join=unk_agree_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc=F_malloc_join?unk_agree_munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5Ubsan;RMallocTree>rauxv_ok_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib5Ubsan;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTreeErpres_except_of_munchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_gt_casesC59OSSVerify5KrLib5Ubsan?RF_malloc_entry?rentry_big_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan?RF_malloc_entry?rentry_big_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan?RF_malloc_entry;rentry_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan?RF_malloc_entryBrmalloc_entry_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>F_malloc_entryCsize_to_class_propsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4log2c59OSSVerify5KrLib5Ubsan>RF_malloc_core<renf_hyp_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan>RF_malloc_core=rfail_hyp_retC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr05C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_ltC46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_leK46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5Ubsan:RMallocRep=rmalloc_entryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RAUXV_CELLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan;RMallocTree9RAM_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9RDEBRUIJNC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x22924) fc None m1 (seg_rom usegs)
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv usegs m1
      /\ stk usegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
      /\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            rmalloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom usegs)
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp)
      /\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.

Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
           ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
  intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
  rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
            ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
  intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

(* [comment removed for export] *)
Definition rbig_stmt : Prop :=
  forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
         (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
         (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
  let st1 := set_tick t st in
  RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
  ATOP <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv usegs m1 ->
  stk usegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells usegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells usegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
                 s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x22674) fc None m1 (seg_rom usegs)).

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Lemma rmalloc_core_implT :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
  RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
  rimplT m (malloc_core full_lay (set_tick t st) n) s
        (rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= ATOP).
  { intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). atop_facts. lia. }
  pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. atop_facts.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; atop_facts; lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  - (* [comment removed for export] *)
    riprefixT. eapply evt_cut.
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| atop_facts; lia| lia| exact MI]. }
    intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
    destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| atop_facts; lia| lia| exact MI| exact NL]. }
    intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
    destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.
End CANSEC1.
