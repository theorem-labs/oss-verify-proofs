(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (carve_st_some, carve_st_none)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_am_A F_am_K.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_am_C () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC35stdpp4base6lookupC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib6Malloc6F_am_K8carve_stC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decI47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition pgal (z : Z) : Prop := z mod 4096 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carve_st_some st p tl ar :
  c_meta_area_tail (ctx st) = Some tl -> (s_areas st) !! tl = Some ar -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
  intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
  unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.

Lemma carve_st_none st p :
  c_meta_area_tail (ctx st) = None -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := upd_ctx (set_meta_area_head (Some p)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
  intros HT Hp. unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.

End CANSEC1.
