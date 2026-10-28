(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ARep ALayout AHeapP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
            F (Z_to_bv 64 0x386ec) fc None m (seg_rom bsegs)).
End CANSEC2.
