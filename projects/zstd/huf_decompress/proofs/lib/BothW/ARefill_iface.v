(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (cache_alloc_unfold, put_cls_put_cls, get_cls_put_cls and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ARep ALayout AHeapP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARefill_iface () := "I35stdpp9countable9Countable00C35stdpp4base;RelDecisionc59OSSVerify5KrLib5BothW=ARefill_ifaceAcache_refill_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aundef_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCpopulate_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;cache_allocC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC47Corelib4Init5Logic8eq_ind_rC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5BothW=ARefill_ifaceBcache_alloc_unfoldC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC35stdpp8fin_maps@insert_insert_eqC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6astate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp7tactics<f_equal_helpI47Corelib4Init5Logic2eq00I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C35stdpp4base6lookupI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlAcls_set_num_freedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ARefill_iface?put_cls_put_clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ARefill_iface?get_cls_put_clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW=ARefill_iface4apopC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition cache_refill_tree {R} (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).

Lemma cache_alloc_unfold : forall {R} st c (k : astate -> bool -> AM R),
  cache_alloc st c k =
    (if 0 <? c_count (get_cls st c) then k (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) true
     else cache_refill_tree st c k).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition apop (c : Z) (st : astate) : astate :=
  put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st.

Lemma put_cls_put_cls : forall c r1 r2 st, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof. intros. unfold put_cls, set_cls. cbn. f_equal. apply insert_insert_eq. Qed.
Lemma get_cls_put_cls : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma take_is_apop : forall c n st2,
  put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
  = apop c (put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2).
Proof. intros. unfold apop. rewrite get_cls_put_cls, put_cls_put_cls. reflexivity. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation AREFILL_STACK := 1536 (only parsing).
Notation arefill_W L st c sp :=
  ([(sp - AREFILL_STACK, sp);
    (al_t L + 208, al_t L + 3168);   (* [comment removed for export] *)
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition refill_ret (H : aholes) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    (* [comment removed for export] *)
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c').

Definition refill_stmt (H : aholes) : Prop :=
  forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st_r X' RNG' ms', refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36498) fc None m (seg_rom bsegs)).
End CANSEC2.
