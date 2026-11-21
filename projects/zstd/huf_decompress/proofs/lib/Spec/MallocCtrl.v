(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (48 recorded proofs replaced by written proofs (strip_strip, strip_wr8, strip_wr16 and 45 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocCtrl () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00c59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl4KRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_insertC47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec5STree4smapC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_deleteC59OSSVerify5KrLib4Spec5STree;strel_sbindC1?~~~~~~~~~~~~~~~C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;eruns_sbindC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC46Stdlib5Lists4List6nth_okC59OSSVerify5KrLib4Spec6Malloc@enframe_read_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAmalloc_small_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7decoderC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9dec_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base6Deletec59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDc59OSSVerify5KrLib4Spec:MallocCtrl5KREL0C1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base<PartialAlterC35stdpp4base5Mergec59OSSVerify5KrLib4Spec:MallocCtrl4BRELC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_unitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;havoc_pagesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6shadow01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc9zero_hdrsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3wr8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes7nat_indI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib4Spec6Malloc4wr32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6shiftlC59OSSVerify5KrLib4Spec6Malloc8set_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4wr16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>strip_set_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3lorc59OSSVerify5KrLib4Spec:MallocCtrl@strip_enframe_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl9strip_wr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_zero_hdrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;nest_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9get_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<brk_pages_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8get_headC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<okay_to_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8put_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_groupsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?get_group_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_group_active_idxC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9add_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C35stdpp4base5emptyC35stdpp8fin_maps:map_deleteK59OSSVerify5KrLib4Spec6Malloc6mstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps<delete_emptyC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;drop_regionC1?~~~~~~~~~~~~~~~C35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@get_region_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAset_unmap_seq_mapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_seqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl9ctx_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:record_seqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbc59OSSVerify5KrLib4Spec:MallocCtrl=bounces_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?unmap_seq_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc:m_set_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_set_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>strip_upd_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>strip_set_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>get_head_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlBget_meta_rec_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8am_carveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9am_finishC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<am_after_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:free_groupC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5strel02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib4Spec:MallocCtrl:queue_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlFgroup_active_idx_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>set_avail_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl=strip_upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl<am_take_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_set_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl=s_areas_stripC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6MallocBmprotect_answer_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib4Spec:MallocCtrl:conc_stripC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl=am_carve_ctrlC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5TWO64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@strip_new_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl<s_atop_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlAlive_ranges_stripC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>am_finish_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>brk0_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7set_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl=strip_dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=brk_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDmmap_fixed_answer_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlBbrk_pages_ok_stripC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@strip_upd_regionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>s_secret_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_secretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=set_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlAam_after_brk_ctrlC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9MAP_FIXEDC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lowbitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlCstrip_decay_bouncesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@strip_set_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlJstrip_set_group_active_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl<active_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9span_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl;ta_fin_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlCactivate_group_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9hdr_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9m_set_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>m_set_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?m_set_sizeclassC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_hdr_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_set_usageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_put_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_add_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl;usage_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6lh_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8lay_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlDstrip_account_bounceC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>strip_step_seqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlAstrip_nest_layoutC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl=slot_of_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlAis_bouncing_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4evenC56Stdlib6ZArith6BinInt1Z6shiftrK59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl<ag_tail_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>free_meta_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?alloc_meta_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@alloc_group_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5ctz32C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>try_avail_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl4DRELC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl=s_slots_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_del_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?strip_del_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@strip_record_seqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?free_group_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlBokay_to_free_stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl?alloc_slot_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4FUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlFmalloc_small_ctrl_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>size_overflowsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@munmap_answer_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl4CRELC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlAstrip_drop_regionC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic3and00K59OSSVerify5KrLib4Spec5STree5strel01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3rd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>peek_answer_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6ltb_geC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc4rd16C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl8rd8_prunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl9rd16_prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;slot_start'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec5STree9strel_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl<strel_smap_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree8steq_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec:MallocCtrl<strel_steq_lC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl@malloc_core_ctrlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlEenframe_read_off_prunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl;strip_stripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl;strip_havocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>enframe_at_ptrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl4MRELC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc9free_tailC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlDnontrivial_free_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7testbitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl6hdr_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8free_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5cfreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl4FRELC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrl>dec_slots_drelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec:MallocCtrlAfree_tail_controlC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

Section ORACLE.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.     (* [comment removed for export] *)
Variable pupd : O -> ev -> Z -> O.            (* [comment removed for export] *)

Definition psel (o : O) (e : ev) : option Z :=
  match e with EPeek p c h => Some (pans o p c h) | _ => None end.
Definition prun {R} (o : O) (t : M R) : M (O * R) := eruns psel pupd o t.

(* [comment removed for export] *)
Definition KREL {X R1 R2} (RR : O * R1 -> R2 -> Prop)
  (k1 : mstate -> X -> M R1) (k2 : mstate -> X -> M R2) : Prop :=
  forall o st cst x, cst = strip st -> strel RR (prun o (k1 st x)) (k2 cst x).
Definition KREL0 {R1 R2} (RR : O * R1 -> R2 -> Prop)
  (k1 : mstate -> M R1) (k2 : mstate -> M R2) : Prop :=
  forall o st cst, cst = strip st -> strel RR (prun o (k1 st)) (k2 cst).
Definition BREL {R1 R2} (RR : O * R1 -> R2 -> Prop) (b1 : M R1) (b2 : M R2) : Prop :=
  forall o, strel RR (prun o b1) b2.
End ORACLE.
Arguments psel {O} pans o e.
Arguments prun {O} pans pupd {R} o t.
Arguments KREL {O} pans pupd {X R1 R2} RR k1 k2.
Arguments KREL0 {O} pans pupd {R1 R2} RR k1 k2.
Arguments BREL {O} pans pupd {R1 R2} RR b1 b2.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strip_strip st : strip (strip st) = strip st.
Proof. reflexivity. Qed.

Lemma strip_wr8 p v st : strip (wr8 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr16 p v st : strip (wr16 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_wr32 p v st : strip (wr32 p v st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_havoc p n st : strip (havoc p n st) = strip st.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma strip_set_tick t st : strip (set_tick t st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_zero_hdrs p size i cnt st : strip (zero_hdrs p size i cnt st) = strip st.
Proof. revert i st; induction cnt; intros; simpl; auto. rewrite IHcnt. reflexivity. Qed.
Lemma strip_set_size p e n b st : strip (set_size p e n b st) = strip st.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma strip_enframe_at st g idx n off :
  strip (fst (enframe_at st g idx n off)) = strip st.
Proof.
  unfold enframe_at. destruct (negb (off =? 0)); cbn -[set_size wr8 wr16 strip]; rewrite strip_set_size; reflexivity.
Qed.
Lemma strip_hdr_havoc b st : strip (hdr_havoc b st) = strip st.
Proof. reflexivity. Qed.
Lemma strip_nest_layout st g idx j size cnt : strip (nest_layout st g idx j size cnt) = strip st.
Proof.
  unfold nest_layout. destruct (enframe_at st g idx _ 0) as [st1 p] eqn:E.
  rewrite strip_zero_hdrs, strip_wr8. pose proof (strip_enframe_at st g idx (UNIT * size_class j - IB) 0) as H.
  rewrite E in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_strip st : ctx (strip st) = ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;1p;2g01<cj11Tg00QUj20Tg00QoR0g01=Wf0R1#1'0X00P1O1W0o"). Qed.
Lemma s_ctx_strip st : s_ctx (strip st) = s_ctx st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;1p;2g01>Nj11Tg00QUj20Tg00QoR0g01=Wf0R1#1'0X00P1O1W0o"). Qed.
Lemma s_regions_strip st : s_regions (strip st) = s_regions st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;4p;1p;2g00MSj42Tg01?Dj11Tg00QUj20Tg00QoR0g00bRg01@>g01@Wg01A5C2f0R1#1'0X00P1O1W0o"). Qed.
Lemma s_metas_strip st : s_metas (strip st) = s_metas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;4p;6p;1p;2g01Anj44Tg01BLj63Tg00MSj40Tg01Bmj11Tg00QUj22Tg00QoR0g002\g00bRR1g01@>R2g00RhR3g00ciR4C4P1P2g01@WP3P4g00dBE3g01CeC0f0R4#1'2X00P4O1W0o"). Qed.
Lemma s_areas_strip st : s_areas (strip st) = s_areas st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;4p;6p;1p;2g01Anj44Tg01BLj63Tg00MSj40Tg01D\j11Tg00QUj22Tg00QoR0g002\g00bRR1g01@>R2g00RhR3g00ciR4C4P1P2g01@WP3P4g00dBE3g01ETC0f0R4#1'2X00P4O1W0o"). Qed.
Lemma s_groups_strip st : s_groups (strip st) = s_groups st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;4p;6p;1p;2g01Anj44Tg01BLj63Tg00MSj40Tg01FKj11Tg00QUj22Tg00QoR0g002\g00bRR1g01@>R2g00RhR3g00ciR4C4P1P2g01@WP3P4g00dBE3g01GDC0f0R4#1'2X00P4O1W0o"). Qed.
Lemma s_slots_strip st : s_slots (strip st) = s_slots st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;4p;6p;2p;1g01Anj45Tg01BLj64Tg00Scj20Tg00MSj41Tg01H;j13Tg00QUj22Tg00QoR0g002\R1g00bRR2g01@>R3g00RhR4g00ciR5C5P2P3g01@WP4P5g00dBE41014C1f0R4#3'2X00P4O1W0o"). Qed.
Lemma s_next_rid_strip st : s_next_rid (strip st) = s_next_rid st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;1p;2g01I3j11Tg00QUj20Tg00QoR0g00bRf0R1#1'0X00P1O1W0o"). Qed.
Lemma s_secret_strip st : s_secret (strip st) = s_secret st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;1p;2g01Inj11Tg00QUj20Tg00QoR0g00Rhf0R1#1'0X00P1O1W0o"). Qed.
Lemma s_reserved_strip st : s_reserved (strip st) = s_reserved st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;2p;1g00Scj23Tg00TCj12Tg01Jgj10Tg00QUj21Tg00QoR0g00RhR1/31#2f0R1#0'1X00P1O1W0o"). Qed.
Lemma s_atop_strip st : s_atop (strip st) = s_atop st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;1p;2g01Kbj11Tg00QUj20Tg00QoR0g00Rhf0R1#1'0X00P1O1W0o"). Qed.
Lemma active_strip st sc : active (strip st) sc = active st sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02sch12stp;2g01LYj21Tg00QUj20Tg00QoR0g00RhR1g00G]f1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma usage_strip st sc : usage (strip st) sc = usage st sc.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02sch12stp;2g01MPj21Tg00QUj20Tg00QoR0g00RhR1f1R2f0R3'1,01X01X10P2P3O2W0W1o"). Qed.
Lemma unmap_seq_strip st i : unmap_seq (strip st) i = unmap_seq st i.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ih12stp;2g01NFj21Tg00QUj20Tg00QoR0g00RhR1f1R2f0R3'1,01X01X10P2P3O2W0W1o"). Qed.
Lemma bounces_strip st i : bounces (strip st) i = bounces st i.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ih12stp;2g01O@j21Tg00QUj20Tg00QoR0g00RhR1f1R2f0R3'1,01X01X10P2P3O2W0W1o"). Qed.
Lemma get_meta_rec_strip st m : get_meta_rec (strip st) m = get_meta_rec st m.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01mh12stp;2g0106j21Tg00QUj20Tg00QoR0g002\R1g01Cef1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma get_group_strip st g : get_group (strip st) g = get_group st g.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01gh12stp;1p;2g01P8j12Tg01PZj21Tg00QUj20Tg00QoR0g002\R1g01GD#2f1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma group_active_idx_strip st g : group_active_idx (strip st) g = group_active_idx st g.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01gh12stp;2g01QTj21Tg00QUj20Tg00QoR0g002\R1g00Rhf1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma get_region_strip st r : get_region (strip st) r = get_region st r.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01rh12stp;1p;2g01P8j12Tg01RUj21Tg00QUj20Tg00QoR0g00bRR1g01A5#2f1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma conc_strip st p : conc (strip st) p = conc st p.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ph12stp;2g01SPj21Tg00QUj20Tg00QoR0g002\R1g00Rhf1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma live_ranges_strip st : live_ranges (strip st) = live_ranges st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02stp;2p;1g00Scj23Tg00TCj12Tg01TEj10Tg00QUj21Tg00QoR0g00RhR1/31#2f0R1#0'1X00P1O1W0o"). Qed.
Lemma brk_pages_ok_strip st lo len : brk_pages_ok (strip st) lo len = brk_pages_ok st lo len.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h03lenh12loh22stp;3p;2g01UAj31Tg00QUj20Tg00QoR0g00RhR1g00b2f2R2f1R3f0R431'0X01X11X20P2P3P4O3X01W1W2o"). Qed.  (* [comment removed for export] *)
Lemma get_head_strip st h : get_head (strip st) h = get_head st h.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "p'0h01hh12sth22sci002sci011lp;1p;2p;3g00P_j14Tg01V>j20Tg00__j33Tg01W7j12Tg00QUj21Tg00QoR0g01WoR1P1g00G]R2f2R3#4f0R4'0103433P4g00Rhf3%24'0,12W2P4O1f1R3g01Xg'0,12n0110100021010000X01X10P3P4O2W0W1o"). Qed.
Lemma is_bouncing_strip sc st : is_bouncing sc (strip st) = is_bouncing sc st.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02sch12stp;2g01Y_j21Tg00QUj20Tg00RhR0g00QoR1g00b2f1R2f0R3'1'0X11X00P2P3O2W1W0o"). Qed.
Lemma okay_to_free_strip st g : okay_to_free (strip st) g = okay_to_free st g.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01gh12stp;2g01Z[j21Tg00QUj20Tg00QoR0g002\R1g00b2f1R2f0R3'1'0X01X10P2P3O2W0W1o"). Qed.
Lemma slot_of_strip st g i : slot_of (strip st) g i = slot_of st g i.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01gh11ih22stp;3p;2g01[Xj31Tg00QUj20Tg00QoR0g002\R1g00RhR2f2R3f1R4f0R531,01X12X01X20P3P4P5O3W1W0W2o"). Qed.

Lemma strip_upd_ctx f st : upd_ctx f (strip st) = strip (upd_ctx f st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01fh12stp;2p;1g01\Pj22Tg00P_j11Tg00QUj20Tg01=WR0P0[R0g00QoR1f1R2f0R3'2#1,01X11X00P2P3O2W1W0o"). Qed.
Lemma strip_upd_meta m f st : upd_meta m f (strip st) = strip (upd_meta m f st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01fh11mh22stp;3p;1p;2g01]Hj32Tg00P_j11Tg00QUj20Tg002\R0g01CeR1P1[R1g00QoR2f2R3f1R4f0R532#1,02X22X01X10P3P4P5O3W2W0W1o"). Qed.
Lemma strip_put_meta m r st : put_meta m r (strip st) = strip (put_meta m r st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01mh11rh22stp;3p;1p;2g01^Aj32Tg00P_j11Tg00QUj20Tg002\R0g01CeR1g00QoR2f2R3f1R4f0R532#1,02X22X11X00P3P4P5O3W2W1W0o"). Qed.
Lemma strip_set_active sc v st : set_active sc v (strip st) = strip (set_active sc v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02sch12sth21vp;3p;1p;2g01_:j32Tg00P_j11Tg00QUj20Tg00RhR0g00G]R1g00QoR2f2R3f1R4f0R532#1,02X12X21X00P3P4P5O3W1W2W0o"). Qed.
Lemma strip_set_head h v st : set_head h v (strip st) = strip (set_head h v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "p'0h01hh12sth21vh32sci002sci011lp;1p;3p;2g00P_j10Tg01`5j31Tg00__j34Tg01W7j13Tg00QUj22Tg01WoR0g00G]R1g00QoR2P0f0R3f2R4f1R5#031A1345#0542P4g00Rh%33f3;14#0,22W3P3O1g01Xg?153#0,22n0110100021010000X12X21X00P4P5P3O3W1W2W0o"). Qed.
Lemma strip_set_usage sc v st : set_usage sc v (strip st) = strip (set_usage sc v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02sch12sth21vp;3p;1p;2g01`nj32Tg00P_j11Tg00QUj20Tg00RhR0g00QoR1f2R2f1R3f0R432#1,01X11X20X00P2P3P4O3W1X20W0o"). Qed.
Lemma strip_set_bounce i v st : set_bounce i v (strip st) = strip (set_bounce i v st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ih12sth21vp;3p;1p;2g01ahj32Tg00P_j11Tg00QUj20Tg00RhR0g00QoR1f2R2f1R3f0R432#1,01X11X20X00P2P3P4O3W1X20W0o"). Qed.
Lemma strip_set_areas a st : set_areas a (strip st) = strip (set_areas a st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ah12stp;4p;6p;2p;1g01Anj45Tg01BLj64Tg00MSj40Tg01bcj21Tg00P_j13Tg00QUj22Tg002\g00bRR0g01@>R1g00RhR2g00ciR3C5P0P1g01@WP2P3g00dBE4g01ETC0R3g00QoR2f1R1f0R0'1#3,22X12X03P1P0O2W1W0o"). Qed.
Lemma strip_put_group g m ai st : put_group g m ai (strip st) = strip (put_group g m ai st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h02aih11gh21mh32stp;4p;1p;2g01c]j42Tg00P_j11Tg00QUj20Tg002\R0g00G]R1g00RhR2g00QoR3f3R4f2R5f1R6f0R7C2#1,03X33X02X21X10P4P5P6P7O4W3W0W2W1o"). Qed.
Lemma strip_set_group_active_idx g ai st : set_group_active_idx g ai (strip st) = strip (set_group_active_idx g ai st).
Proof. unfold set_group_active_idx. rewrite get_group_strip. destruct (get_group st g); reflexivity. Qed.
Lemma strip_del_group g st : del_group g (strip st) = strip (del_group g st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01gh12stp;2p;1g01i]j22Tg00P_j11Tg00QUj20Tg002\R0g00QoR1f1R2f0R3'2#1,01X11X00P2P3O2W1W0o"). Qed.
Lemma strip_add_slots m p s c st : add_slots m p s c (strip st) = strip (add_slots m p s c st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ch11mh21ph31sh42stp;5p;1p;2g01jWj52Tg00P_j11Tg00QUj20Tg002\R0g00RhR1g00QoR2f4R3f3R4f2R5f1R6f0R7D2#1,02X42X01X31X20X10P3P4P5P6P7O5W4X01W3X20W1o"). Qed.
Lemma strip_del_slots p s c st : del_slots p s c (strip st) = strip (del_slots p s c st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocCtrl ()) [] "h01ch11ph21sh32stp;4p;1p;2g01kQj42Tg00P_j11Tg00QUj20Tg002\R0g00RhR1g00QoR2f3R3f2R4f1R5f0R6C2#1,02X32X01X21X10P3P4P5P6O4W3X01W2W1o"). Qed.
Lemma strip_drop_region rid st : drop_region rid (strip st) = strip (drop_region rid st).
Proof. unfold drop_region, strip; cbn. rewrite delete_empty. reflexivity. Qed.
Lemma strip_new_region k b l st :
  new_region k b l (strip st) = (strip (fst (new_region k b l st)), snd (new_region k b l st)).
Proof. reflexivity. Qed.
Lemma strip_upd_region rid f st : upd_region rid f (strip st) = strip (upd_region rid f st).
Proof. unfold upd_region. rewrite get_region_strip. destruct (get_region st rid); reflexivity. Qed.
Lemma strip_step_seq st : step_seq (strip st) = strip (step_seq st).
Proof. unfold step_seq. rewrite ctx_strip. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma strip_record_seq sc st : record_seq sc (strip st) = strip (record_seq sc st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma strip_account_bounce sc st : account_bounce sc (strip st) = strip (account_bounce sc st).
Proof. unfold account_bounce. rewrite !unmap_seq_strip, !bounces_strip, !ctx_strip.
  destruct (sc_in_seq_range sc); [|reflexivity]. destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. Qed.
Lemma strip_decay_bounces sc st : decay_bounces sc (strip st) = strip (decay_bounces sc st).
Proof. unfold decay_bounces. rewrite !bounces_strip. destruct (_ && _); reflexivity. Qed.
Lemma strip_dequeue h m st : dequeue h m (strip st) = strip (dequeue h m st).
Proof.
  unfold dequeue. rewrite !get_meta_rec_strip.
  destruct (negb _); [|rewrite strip_set_head; reflexivity].
  destruct (m_prev _); destruct (m_next _); rewrite ?strip_upd_meta, ?get_head_strip;
  destruct (optr_eqb _ _); rewrite ?strip_set_head, ?strip_upd_meta; reflexivity.
Qed.

Hint Rewrite ctx_strip s_ctx_strip s_regions_strip s_metas_strip s_areas_strip s_groups_strip s_slots_strip
  s_next_rid_strip s_secret_strip s_reserved_strip s_atop_strip active_strip usage_strip unmap_seq_strip bounces_strip
  get_meta_rec_strip get_group_strip group_active_idx_strip get_region_strip conc_strip live_ranges_strip brk_pages_ok_strip
  get_head_strip is_bouncing_strip okay_to_free_strip slot_of_strip
  strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_new_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue
  strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size strip_nest_layout strip_hdr_havoc
  : strip_rw.
(* [comment removed for export] *)
Hint Rewrite <- strip_upd_ctx strip_upd_meta strip_put_meta strip_set_active strip_set_head strip_set_usage strip_set_bounce
  strip_set_areas strip_put_group strip_set_group_active_idx strip_del_group strip_add_slots strip_del_slots
  strip_drop_region strip_upd_region strip_step_seq strip_record_seq strip_account_bounce
  strip_decay_bounces strip_dequeue : strip_in.
Hint Rewrite strip_strip strip_wr8 strip_wr16 strip_wr32 strip_havoc strip_set_tick strip_zero_hdrs strip_set_size
  strip_nest_layout strip_enframe_at strip_hdr_havoc : strip_in.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac csimp := cbn -[strip
   (* [comment removed for export] *) ctx active usage unmap_seq bounces get_meta_rec get_group group_active_idx get_region conc oconc
                   live_ranges brk_pages_ok get_head is_bouncing okay_to_free slot_of get_shadow
                   s_ctx s_regions s_shadow s_metas s_areas s_groups s_slots s_next_rid s_tick s_secret s_reserved s_atop
   (* [comment removed for export] *)   upd_ctx set_active set_head set_usage set_bounce put_meta upd_meta put_group set_group_active_idx
                   set_areas set_metas set_groups set_slots set_regions set_shadow set_next_rid set_tick
                   new_region drop_region del_group add_slots del_slots upd_region upd_shadow wr8 wr16 wr32 havoc hdr_havoc
                   step_seq record_seq account_bounce decay_bounces dequeue nest_layout enframe_at set_size zero_hdrs
   (* [comment removed for export] *) am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail alloc_group alloc_slot
                   malloc_small_ctrl malloc_core
                   nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                   enframe_read_off enframe_full get_meta get_nominal_size rd8 rd16 rd32
                   size_to_class size_class small_cnt_pick small_cnt halve_even halve_big med_cnt span_loop
                   mask_upto lowbit ctz32 bit u32 round_up_pg fold_off get_stride area_of
                   mmap_answer_ok brk0_answer_ok brk_answer_ok mmap_fixed_answer_ok munmap_answer_ok
                   mprotect_answer_ok peek_answer_ok is_err size_overflows
                   Z.add Z.sub Z.mul Z.div Z.modulo Z.eqb Z.leb Z.ltb Z.land Z.lor Z.ldiff Z.lxor Z.shiftl Z.shiftr
                   Z.pow Z.even Z.testbit Z.to_nat Z.iter N.succ N.eqb lookup insert delete empty map_to_list fmap].

Global Set Keyed Unification.
Ltac srw := autorewrite with strip_rw.

(* [comment removed for export] *)
Ltac strip_in1 :=
  first
  [ rewrite strip_nest_layout | rewrite strip_hdr_havoc | rewrite strip_enframe_at | rewrite strip_zero_hdrs | rewrite strip_set_size
  | rewrite strip_havoc | rewrite strip_wr32 | rewrite strip_wr16 | rewrite strip_wr8 | rewrite strip_set_tick
  | rewrite strip_strip
  | rewrite <- strip_dequeue | rewrite <- strip_step_seq | rewrite <- strip_record_seq
  | rewrite <- strip_account_bounce | rewrite <- strip_decay_bounces | rewrite <- strip_drop_region
  | rewrite <- strip_del_slots | rewrite <- strip_add_slots | rewrite <- strip_del_group
  | rewrite <- strip_set_group_active_idx | rewrite <- strip_put_group | rewrite <- strip_upd_region
  | rewrite <- strip_set_head | rewrite <- strip_set_active | rewrite <- strip_set_usage | rewrite <- strip_set_bounce
  | rewrite <- strip_upd_meta | rewrite <- strip_put_meta | rewrite <- strip_set_areas | rewrite <- strip_upd_ctx ].
Ltac solve_eq := repeat strip_in1; reflexivity.
(* [comment removed for export] *)
Ltac use_hyp :=
  match goal with
  | H : _ |- strel _ _ _ =>
      with_strategy opaque [am_take am_carve am_finish am_after_brk alloc_meta ta_fin try_avail ag_tail
                            alloc_group alloc_slot malloc_small_ctrl malloc_core
                            nontrivial_free free_group free_tail free_hdr queue free_meta activate_group
                            enframe_read_off enframe_full]
        (eapply H); (try assumption); (try solve_eq)
  end.
(* [comment removed for export] *)
Ltac not_numeric T :=
  lazymatch T with Z => fail | bool => fail | N => fail | nat => fail | (Z * Z)%type => fail | _ => idtac end.
Ltac scrut x :=
  match x with
  | context [if ?c then ?a else _] => let T := type of a in not_numeric T; scrut c
  | context [match ?y with _ => _ end] => let T := type of y in (lazymatch T with bool => fail | _ => idtac end); scrut y
  | _ => destruct x eqn:?
  end.
Ltac sync1 :=
  first
  [ lazymatch goal with
    | |- strel _ _ _ => fail
    | |- _ = _ => solve_eq                (* [comment removed for export] *)
    | |- _ => progress (hnf; intros);    (* [comment removed for export] *)
              try match goal with H : ?c = strip _ |- _ => is_var c; subst c end
    end
  | lazymatch goal with
    | |- strel _ (SRet _) (SRet _) => constructor
    | |- strel _ (SVis _ _) (SVis _ _) => constructor; intros ?
    | |- strel _ (eruns _ _ _ (if ?c then _ else _)) _ => scrut c
    | |- strel _ (eruns _ _ _ (match ?x with _ => _ end)) _ => scrut x
    | |- strel _ (prun _ _ _ (if ?c then _ else _)) _ => scrut c
    | |- strel _ (prun _ _ _ (match ?x with _ => _ end)) _ => scrut x
    | |- strel _ _ _ => use_hyp
    end
  | match goal with |- ?g => scrut g end ].
Ltac sync := csimp; srw; repeat (sync1; csimp; srw).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CPS.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Context {R1 R2 : Type} (RR : O * R1 -> R2 -> Prop).
Local Notation KREL := (KREL pans pupd).
Local Notation KREL0 := (KREL0 pans pupd).
Local Notation BREL := (BREL pans pupd).
Local Notation prun := (prun pans pupd).

Lemma queue_ctrl h m k1 k2 b1 b2 :
  KREL0 RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (queue h m st k1 b1)) (queue h m cst k2 b2).
Proof. intros HK HB o st cst ->. unfold queue, guard. sync. Qed.

Lemma free_meta_ctrl m k1 k2 b1 b2 :
  KREL0 RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (free_meta m st k1 b1)) (free_meta m cst k2 b2).
Proof. intros HK HB o st cst ->. unfold free_meta. eapply queue_ctrl; eauto. Qed.

Lemma activate_group_ctrl m k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (activate_group m st k1 b1)) (activate_group m cst k2 b2).
Proof. intros HK HB o st cst ->. unfold activate_group, guard. sync. Qed.

Lemma am_take_ctrl k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_take st k1 b1)) (am_take cst k2 b2).
Proof. intros HK HB o st cst ->. unfold am_take. sync. Qed.

Lemma am_carve_ctrl p k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_carve st p k1 b1)) (am_carve cst p k2 b2).
Proof. intros HK HB o st cst ->. pose proof (am_take_ctrl k1 k2 b1 b2 HK HB) as HT. unfold am_carve. sync. Qed.

Lemma am_finish_ctrl nu k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_finish st nu k1 b1)) (am_finish cst nu k2 b2).
Proof. intros HK HB o st cst ->. pose proof (am_carve_ctrl) as HC. unfold am_finish, bad_answer. sync. Qed.

Lemma am_after_brk_ctrl nu k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (am_after_brk st nu k1 b1)) (am_after_brk cst nu k2 b2).
Proof. intros HK HB o st cst ->. pose proof (am_finish_ctrl) as HF. unfold am_after_brk, bad_answer. sync. Qed.

Lemma alloc_meta_ctrl k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (alloc_meta st k1 b1)) (alloc_meta cst k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (am_after_brk_ctrl) as HA. pose proof (am_take_ctrl k1 k2 b1 b2 HK HB) as HT.
  unfold alloc_meta, bad_answer. sync.
Qed.

Lemma ta_fin_ctrl m mask k1 k2 :
  KREL RR k1 k2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (ta_fin st m mask k1)) (ta_fin cst m mask k2).
Proof. intros HK o st cst ->. unfold ta_fin. sync. Qed.

Lemma try_avail_ctrl sc k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (try_avail sc st k1 b1)) (try_avail sc cst k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (ta_fin_ctrl) as HF. pose proof (activate_group_ctrl) as HA.
  unfold try_avail, guard. sync.
Qed.

Lemma ag_tail_ctrl sc m p cnt ai k1 k2 :
  KREL RR k1 k2 ->
  forall o st cst, cst = strip st -> strel RR (prun o (ag_tail full_lay st sc m p cnt ai k1)) (ag_tail lay_none cst sc m p cnt ai k2).
Proof. intros HK o st cst ->. unfold ag_tail. cbn [lh_hdr full_lay lay_none]. rewrite <- (strip_hdr_havoc p st). sync.
Qed.

Lemma alloc_group_ctrl rec1 rec2 sc req k1 k2 b1 b2 :
  (forall sc' req' k1' k2' b1' b2', KREL RR k1' k2' -> BREL RR b1' b2' ->
     forall o st cst, cst = strip st -> strel RR (prun o (rec1 st sc' req' k1' b1')) (rec2 cst sc' req' k2' b2')) ->
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (alloc_group R1 full_lay rec1 st sc req k1 b1)) (alloc_group R2 lay_none rec2 cst sc req k2 b2).
Proof.
  intros HR HK HB o st cst ->. pose proof (ag_tail_ctrl) as HT. pose proof (free_meta_ctrl) as HF. pose proof (alloc_meta_ctrl) as HA.
  unfold alloc_group, bad_answer. cbn [lh_nest full_lay lay_none]. sync.
Qed.

Lemma alloc_slot_ctrl fuel : forall sc req k1 k2 b1 b2,
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (alloc_slot full_lay fuel st sc req k1 b1)) (alloc_slot lay_none fuel cst sc req k2 b2).
Proof.
  induction fuel as [|f IH]; intros sc req k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [alloc_slot]. sync. }
  pose proof (try_avail_ctrl) as HTA. pose proof (queue_ctrl) as HQ.
  pose proof (alloc_group_ctrl (alloc_slot full_lay f) (alloc_slot lay_none f)) as HG.
  cbn [alloc_slot]. sync.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DREL {X1 X2} (XX : O * X1 -> X2 -> Prop) (dec1 : decoder X1) (dec2 : decoder X2) : Prop :=
  forall p k1 k2 b1 b2,
    (forall o m idx, strel XX (prun o (k1 m idx)) (k2 m idx)) ->
    BREL XX b1 b2 ->
    forall o st cst, cst = strip st -> strel XX (prun o (dec1 st p k1 b1)) (dec2 cst p k2 b2).

Lemma dec_slots_drel : DREL RR (@dec_slots R1) (@dec_slots R2).
Proof.
  intros p k1 k2 b1 b2 HK HB o st cst ->. unfold dec_slots. srw.
  destruct (s_slots st !! p) as [[m idx]|]; [apply HK | sync].
Qed.

Lemma free_group_ctrl (dec1 : decoder R1) (dec2 : decoder R2) rec1 rec2 g k1 k2 b1 b2 :
  DREL RR dec1 dec2 ->
  (forall g' i' k1' k2' b1' b2', KREL RR k1' k2' -> BREL RR b1' b2' ->
     forall o st cst, cst = strip st -> strel RR (prun o (rec1 st g' i' k1' b1')) (rec2 cst g' i' k2' b2')) ->
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (free_group R1 dec1 rec1 st g k1 b1)) (free_group R2 dec2 rec2 cst g k2 b2).
Proof.
  intros HD HR HK HB o st cst ->. pose proof (free_meta_ctrl) as HF.
  unfold free_group. sync.
  (* [comment removed for export] *)
  all: try (eapply HD; [ intros ? ? ? | assumption | solve_eq ]; sync).
Qed.

Lemma nontrivial_free_ctrl (dec1 : decoder R1) (dec2 : decoder R2) (HD : DREL RR dec1 dec2) fuel :
  forall g i k1 k2 b1 b2,
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR (prun o (nontrivial_free dec1 fuel st g i k1 b1)) (nontrivial_free dec2 fuel cst g i k2 b2).
Proof.
  induction fuel as [|f IH]; intros g i k1 k2 b1 b2 HK HB o st cst ->.
  { cbn [nontrivial_free]. sync. }
  pose proof (free_group_ctrl dec1 dec2 (nontrivial_free dec1 f) (nontrivial_free dec2 f) g) as HG.
  pose proof (activate_group_ctrl) as HA. pose proof (queue_ctrl) as HQ.
  cbn [nontrivial_free]. unfold guard. sync.
Qed.

End CPS.

Section TOP.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Local Notation KREL := (KREL pans pupd).
Local Notation BREL := (BREL pans pupd).

Definition CREL (x : O * (mstate * option (aptr * Z))) (y : mstate * option (aptr * Z)) : Prop :=
  strip (fst (snd x)) = fst y /\ snd (snd x) = snd y.

Lemma malloc_small_ctrl_ctrl {R1 R2} (RR : O * R1 -> R2 -> Prop) n k1 k2 b1 b2 :
  KREL RR k1 k2 -> BREL RR b1 b2 ->
  forall o st cst, cst = strip st ->
  strel RR ((prun pans pupd) o (malloc_small_ctrl full_lay st n k1 b1)) (malloc_small_ctrl lay_none cst n k2 b2).
Proof.
  intros HK HB o st cst ->. pose proof (alloc_slot_ctrl pans pupd RR FUEL) as HS.
  unfold malloc_small_ctrl. sync.
Qed.

(* [comment removed for export] *)
Lemma malloc_core_ctrl n : forall o st cst, cst = strip st ->
  strel CREL ((prun pans pupd) o (malloc_core full_lay st n)) (malloc_core lay_none cst n).
Proof.
  intros o st cst ->.
  pose proof (@malloc_small_ctrl_ctrl _ _ CREL) as HS. pose proof (@alloc_meta_ctrl O pans pupd _ _ CREL) as HA.
  unfold malloc_core, bad_answer, ret. sync.
  all: try (split; [ solve_eq | reflexivity ]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma rd8_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd8 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd8. destruct (cell_read _ _) as [v|hint].
  - exists o, v; reflexivity.
  - unfold prun. cbn [eruns psel].
    destruct (peek_answer_ok (pans o p (conc st p) hint)) eqn:E.
    + eexists _, _; reflexivity.
    + exfalso. unfold peek_answer_ok in E. pose proof (Hpans o p (conc st p) hint).
      apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.

Lemma rd16_prun {R} st p (k : Z -> M R) o :
  exists o' v, (prun pans pupd) o (rd16 st p k) = (prun pans pupd) o' (k v).
Proof.
  unfold rd16. destruct (rd8_prun st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))) o) as (o1 & v1 & ->).
  destruct (rd8_prun st (aadd p 1) (fun b1 => k (v1 + 256 * b1)) o1) as (o2 & v2 & ->). eauto.
Qed.

Lemma enframe_read_off_prun {R} st g idx n ctr (k : Z -> M R) o :
  exists o' off, (prun pans pupd) o (enframe_read_off st g idx n ctr k) = (prun pans pupd) o' (k off).
Proof.
  unfold enframe_read_off.
  match goal with |- exists o' off, (prun pans pupd) o (rd8 ?s ?q ?kk) = _ => destruct (rd8_prun s q kk o) as (o1 & b3 & ->) end.
  destruct (negb (b3 =? 0)).
  - match goal with |- exists o' off, (prun pans pupd) o1 (rd16 ?s ?q ?kk) = _ => destruct (rd16_prun s q kk o1) as (o2 & v & ->) end. eauto.
  - eauto.
Qed.

Lemma enframe_at_ptr st g idx n off :
  snd (enframe_at st g idx n off) = slot_of st g idx \/ snd (enframe_at st g idx n off) = aadd (slot_of st g idx) (UNIT * off).
Proof.
  unfold enframe_at, slot_of, slot_start'. destruct (negb (off =? 0)); cbn -[Z.add Z.mul Z.sub get_stride]; auto.
Qed.

Definition MREL (x : O * (mstate * optr)) (y : mstate * option cptr) : Prop :=
  strip (fst (snd x)) = fst y /\
  match snd (snd x), snd y with
  | None, None => True
  | Some p, Some c => fst p = fst c /\ exists off, snd p = snd c + UNIT * off
  | _, _ => False
  end.

Lemma strel_smap_r {E A R1 R2 R3} (RR : R1 -> R2 -> Prop) (SS : R1 -> R3 -> Prop) (f : R2 -> R3)
  (t1 : stree E A R1) (t2 : stree E A R2) :
  strel RR t1 t2 -> (forall a b, RR a b -> SS a (f b)) -> strel SS t1 (smap f t2).
Proof. induction 1; intros; cbn; constructor; auto. Qed.

Lemma strel_steq_l {E A R1 R2} (RR : R1 -> R2 -> Prop) (t1 t1' : stree E A R1) (t2 : stree E A R2) :
  steq t1 t1' -> strel RR t1' t2 -> strel RR t1 t2.
Proof.
  intros H; revert t2; induction H; intros t2 Ht; inversion Ht; subst; constructor; eauto.
Qed.

(* [comment removed for export] *)
Theorem malloc_control st n o :
  strel MREL ((prun pans pupd) o (malloc st n)) (cmalloc (strip st) n).
Proof.
  unfold malloc, cmalloc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  eapply strel_sbind.
  { apply (malloc_core_ctrl n o (set_tick (N.succ (s_tick st)) st)). reflexivity. }
  intros [o1 [S r]] [S' r'] [HS Hr]; cbn in HS, Hr; subst r' S'.
  destruct r as [[g idx]|].
  - destruct (enframe_read_off_prun S g idx n (c_mmap_counter (ctx S))
               (fun off => let '(st1, p) := enframe_at S g idx n off in ret (havoc p n st1, Some p)) o1) as (o2 & off & E).
    unfold enframe_full. cbn [fst snd]. unfold prun in E |- *. rewrite E.
    destruct (enframe_at S g idx n off) as [st1 p] eqn:Ea. unfold prun, ret; cbn [eruns psel]. constructor.
    split; cbn.
    + rewrite strip_havoc, strip_strip. pose proof (strip_enframe_at S g idx n off) as H1. rewrite Ea in H1. exact H1.
    + rewrite ?get_meta_rec_strip. pose proof (enframe_at_ptr S g idx n off) as Hp. rewrite Ea in Hp.
      unfold slot_of, slot_start', aadd in Hp. cbn [fst snd] in Hp.
      destruct Hp as [-> | ->]; cbn [fst snd]; [split; [reflexivity| exists 0; lia] | split; [reflexivity | exists off; lia]].
  - unfold prun, ret; cbn [eruns psel]. constructor. split; cbn; [rewrite strip_strip; reflexivity | exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FREL (x : O * mstate) (y : mstate) : Prop := strip (snd x) = y.

(* [comment removed for export] *)
Theorem free_tail_control (dec1 dec2 : decoder mstate) :
  DREL pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 ->
  forall st g idx o cst, cst = strip st ->
  strel (fun x y => strip (snd x) = strip y) ((prun pans pupd) o (free_tail dec1 st g idx)) (free_tail dec2 cst g idx).
Proof.
  intros HD st g idx o cst ->.
  pose proof (nontrivial_free_ctrl pans pupd (fun x y => strip (snd x) = strip y) dec1 dec2 HD FUEL) as HN.
  unfold free_tail, guard, bad_answer, ret. sync.
  all: cbn; rewrite ?strip_strip; try reflexivity; try solve_eq.
Qed.

(* [comment removed for export] *)
Definition hdr_ok (st : mstate) (p : aptr) (c : cptr) : Prop :=
  exists st1 g idx,
    (forall o, (prun pans pupd) o (free_hdr st p) = SRet (o, Some (st1, g, idx)))
    /\ strip st1 = strip st
    /\ (s_slots st) !! c = Some (g, idx)
    /\ (forall o, strel (fun x y => strip (snd x) = strip y)
                        ((prun pans pupd) o (free_tail dec_hdr st1 g idx))
                        (free_tail dec_slots (strip st) g idx)).

(* [comment removed for export] *)
Theorem free_control st p c o :
  hdr_ok st p c ->
  strel FREL ((prun pans pupd) o (free st (Some p))) (cfree (strip st) (Some c)).
Proof.
  intros (st1 & g & idx & Hh & Hs & Hc & Ht).
  unfold free, cfree. rewrite s_slots_strip, Hc.
  eapply strel_steq_l. { unfold prun. apply eruns_sbind. }
  unfold prun in Hh, Ht |- *. rewrite Hh. cbn [sbind fst snd].
  change (x__ <-- free_tail dec_slots (strip st) g idx;; ret (strip x__))
    with (smap strip (free_tail dec_slots (strip st) g idx)).
  apply (strel_smap_r _ _ _ _ _ (Ht o)). intros [o1 S] S' HS. exact HS.
Qed.

(* [comment removed for export] *)
Lemma free_tail_slots_control st g idx o :
  strel (fun x y => strip (snd x) = strip y)
        ((prun pans pupd) o (free_tail dec_slots st g idx)) (free_tail dec_slots (strip st) g idx).
Proof. apply free_tail_control; [apply dec_slots_drel | reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint follow {R} (t : M R) (ans : list Z) : option R :=
  match t, ans with
  | SRet r, _ => Some r
  | SVis (EUndef _) _, _ => None
  | SVis _ k, a :: ans' => follow (k a) ans'
  | SVis _ _, [] => None
  end.

(* [comment removed for export] *)
Inductive reach : mstate -> list aptr -> list cptr -> Prop :=
| reach_init secret res atop : reach (minit secret res atop) [] []
| reach_malloc st L C n o ans o' st' p cst c :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', Some p)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, Some c) ->
    reach st' (p :: L) (c :: C)
| reach_malloc_null st L C n o ans o' st' cst :
    reach st L C ->
    follow ((prun pans pupd) o (malloc st n)) ans = Some (o', (st', None)) ->
    follow (cmalloc (strip st) n) ans = Some (cst, None) ->
    reach st' L C
| reach_free st L C i p c o ans o' st' :
    reach st L C ->
    nth_error L i = Some p -> nth_error C i = Some c ->
    follow ((prun pans pupd) o (free st (Some p))) ans = Some (o', st') ->
    reach st' (delete i L) (delete i C)
| reach_free_null st L C o ans o' st' :
    reach st L C ->
    follow ((prun pans pupd) o (free st None)) ans = Some (o', st') ->
    reach st' L C.

(* [comment removed for export] *)

End TOP.



