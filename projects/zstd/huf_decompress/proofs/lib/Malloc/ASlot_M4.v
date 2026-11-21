(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (ag_mmap_eq, ag_tail_kq_eq, mm_cnt_red_range and 9 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface F_malloc_bigw F_malloc_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_W14 ASlot_W15 ASlot_W16 ASlot_W17 ASlot_W18 ASlot_I ASlot_M0 ASlot_M2 ASlot_M3 ASlot_M4P.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M4 () := "K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I35stdpp9countable9Countable00C57Corelib7BinNums6PosDef3Pos4iterC56Stdlib6ZArith9BinIntDef1Z4iterC35stdpp8fin_maps:map_insertI35stdpp8fin_maps6FinMap00C47Corelib4Init9Datatypes3fstC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC56Stdlib6PArith6BinPos3Pos9iter_succC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W169mm_usage1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W16:mm_cnt_redC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W168mm_finalC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M48mm_afterC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I5as_kqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W18;as_queue_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W18;as_queue_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W148st_modelC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Malloc9ASlot_W18:as_fm_linkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W18<as_fm_singleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4iterC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc9set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W14=rec_hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB=rec_set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABEget_meta_rec_put_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W14=rec_put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W14=rec_set_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Malloc8ASlot_M4Around_up_pg_propsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K47Corelib4Init5Logic2or02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic7f_equalK47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02C56Stdlib6PArith6BinPos3Pos4iterC35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC56Stdlib6PArith6BinPos3Pos4succC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt5Pos2Z:pos_is_posC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC57Corelib7BinNums6IntDef1Z3mulC57Corelib7BinNums6IntDef1Z3addC56Stdlib6PArith6BinPos3Pos9peano_indC35stdpp4base6lookupI47Corelib4Init5Logic2ex00C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums8positive00C56Stdlib6ZArith6BinInt5Pos2Z8inj_succc59OSSVerify5KrLib6Malloc8ASlot_M4>pos_iter_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M45metaWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib6Malloc9ASlot_W185failWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_M44lowWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Malloc:MallocTreeDForall_disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_AB;step_seq_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?set_bounces_mapC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section MMEQ.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
  let size := UNIT * size_class sc in
  let st1 := step_seq (account_bounce sc st2) in
  fun r =>
        if negb (mmap_answer_ok (s_atop st1) (live_ranges st1) nd r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r nd st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if c - 1 <? ai then c - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

Lemma ag_mmap_eq st2 m cnt :
  ag_mmap sc req k bail st2 m cnt =
  (let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
                              (mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
                              (is_bouncing sc st2) in
   SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Lemma ag_tail_kq_eq stT mm p c ai :
  m_next (get_meta_rec stT mm) = None -> m_prev (get_meta_rec stT mm) = None -> active stT sc = None ->
  ag_tail full_lay stT sc mm p c ai (as_kq sc k bail) = k (st_model stT sc c ai mm p) 0.
Proof.
  intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
  rewrite as_queue_eq.
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
  unfold as_queue_st. cbn [get_head].
  match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
  rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mm_cnt_red_range sc size cnt u1 nos : 1 <= cnt <= 32 -> 1 <= mm_cnt_red sc size cnt u1 nos <= 32.
Proof.
  intros H. unfold mm_cnt_red.
  destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props x : 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma mm_final_props size req u1 cnt nos c nd :
  1 <= cnt <= 32 -> 16 <= size -> 0 <= req -> req + 4 <= size ->
  mm_final size req u1 cnt nos = (c, nd) ->
  1 <= c <= cnt /\ nd mod 4096 = 0 /\ req + 20 <= nd
  /\ (c = 1 /\ nd = round_up_pg (req + 20) \/ size * c + 16 <= nd /\ nd = round_up_pg (size * c + 16)).
Proof.
  intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
  pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
  pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
  change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
  change (size * cnt + UNIT) with (size * cnt + 16) in E.
  destruct (negb nos && (cnt <=? 7)).
  - destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
    + inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
    + destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
      * inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
      * inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
  - inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma pos_iter_slots (m p : aptr) (stride : Z) : forall n tb,
  0 < stride ->
  let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
  fst (Pos.iter F (0, tb) n) = Z.pos n
  /\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
    intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
    left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
  - rewrite Pos.iter_succ. destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
    unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
    split; [lia|]. split.
    + rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
    + intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
      * right. exists (Z.pos n). split; [lia| reflexivity].
      * rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first m p stride c st : 1 <= c -> 0 < stride ->
  (s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
  destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
  destruct (pos_iter_slots m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lowW (iv : Z * Z) : Prop :=
  0 <= fst iv /\ snd iv <= ATOP /\ (snd iv <= 0x19000 \/ 0x1b000 <= fst iv \/ (CTX <= fst iv /\ snd iv <= CTX + 928)).

Definition metaW (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (CTX + 16, CTX + 24).

Lemma failW_shape st mt :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (metaW st) (failW st mt).
Proof.
  intros MS FL. unfold failW.
  constructor; [left; exists mt; auto|].
  constructor; [right; reflexivity|].
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
  destruct (FL h eq_refl) as [MSh FP].
  constructor; [left; exists h; auto|].
  destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
  constructor; [left; exists p; auto| constructor].
Qed.

Lemma lowW_disjoint W a n : Forall lowW W -> ATOP <= a -> disjoint_from W a n.
Proof. intros FW Ha. eapply Forall_disjoint_from; [exact FW|]. intros lo hi (H1 & H2 & H3). cbn in *. lia. Qed.

Lemma lowW_disjoint_img W a n : Forall lowW W -> 0x19000 <= a -> a + n <= 0x1b000 -> (a + n <= CTX \/ CTX + 928 <= a) -> disjoint_from W a n.
Proof. intros FW H1 H2 H3. eapply Forall_disjoint_from; [exact FW|]. intros lo hi (X1 & X2 & X3). cbn in *. atop_facts. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stS_shape sc st2 : exists f, step_seq (account_bounce sc st2) = upd_ctx f st2
  /\ forall c, c_active (f c) = c_active c /\ c_usage (f c) = c_usage c /\ c_brk (f c) = c_brk c
     /\ c_mmap_counter (f c) = c_mmap_counter c /\ c_free_meta_head (f c) = c_free_meta_head c
     /\ c_avail_meta (f c) = c_avail_meta c /\ c_secret (f c) = c_secret c /\ c_init_done (f c) = c_init_done c
     /\ c_avail_meta_count (f c) = c_avail_meta_count c /\ c_avail_meta_area_count (f c) = c_avail_meta_area_count c
     /\ c_meta_alloc_shift (f c) = c_meta_alloc_shift c /\ c_meta_area_head (f c) = c_meta_area_head c
     /\ c_meta_area_tail (f c) = c_meta_area_tail c /\ c_avail_meta_areas (f c) = c_avail_meta_areas c.
Proof.
  assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
  { unfold account_bounce, set_bounce.
    destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
  destruct AB as (g & EG & HG).
  rewrite step_seq_eq. rewrite EG.
  destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
  - exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
  - exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AMP : AMP_AS am_pre.

Lemma errno_lit4 : errno_addr tp = 107900.
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.
End LEVEL.


End CANSEC1.
