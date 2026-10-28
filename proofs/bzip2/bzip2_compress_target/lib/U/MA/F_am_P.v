(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep F_malloc_free MallocTree MallocFacts_B MallocKit_B MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Export MallocFacts_AM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_A F_am_K.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_G.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_am_D F_am_E F_am_G.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.F_am_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_D OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_E OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_am_G.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_body {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  match c_free_meta_head (ctx st) with
  | Some m => k (dequeue LFree m st) (Some m)
  | None =>
    if negb (c_avail_meta_count (ctx st) =? 0) then am_take st k bail else
    let brk_dead := match c_brk (ctx st) with BrkDead => true | _ => false end in
    if (c_avail_meta_area_count (ctx st) =? 0) && negb brk_dead then
      match c_brk (ctx st) with
      | BrkUntried =>
        SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
            else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail
            else
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))
      | BrkLive rid off =>
        let old := conc st (rid, off) in
        let new := old + PGSZ in
        SVis (EBrk new) (fun r =>
          if negb (brk_answer_ok old new r) then bad_answer bail else
          if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
          else if negb (brk_pages_ok st old PGSZ) then bad_answer bail
          else
            let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st in
            let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                          (set_avail_meta_areas (Some (rid, off))
                                          (set_brk (BrkLive rid (off + PGSZ)) c))) st1 in
            am_after_brk st2 false k bail)
      | BrkDead => am_after_brk st true k bail
      end
    else am_after_brk st true k bail
  end.

Lemma alloc_meta_eq {R} st (k : mstate -> optr -> M R) bail : alloc_meta st k bail = am_body (am_init_st st) k bail.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctx_core_eq (c c' : mctx) : Prop :=
  c_mmap_counter c' = c_mmap_counter c /\ c_free_meta_head c' = c_free_meta_head c /\ c_avail_meta c' = c_avail_meta c
  /\ c_avail_meta_count c' = c_avail_meta_count c /\ c_meta_area_head c' = c_meta_area_head c /\ c_meta_area_tail c' = c_meta_area_tail c
  /\ c_active c' = c_active c /\ c_usage c' = c_usage c /\ c_unmap_seq c' = c_unmap_seq c /\ c_bounces c' = c_bounces c /\ c_seq c' = c_seq c.

Record AMI (st stX : mstate) : Prop := mkAMI {
  ami_ctx : ctx_core_eq (ctx st) (ctx stX);
  ami_secretr : 0 <= c_secret (ctx stX) < 2^64;
  ami_metas : s_metas stX = s_metas st;
  ami_areas : s_areas stX = s_areas st;
  ami_groups : s_groups stX = s_groups st;
  ami_slots : s_slots stX = s_slots st;
  ami_shadow : s_shadow stX = s_shadow st;
  ami_tick : s_tick stX = s_tick st;
  ami_reserved : s_reserved stX = s_reserved st;
  ami_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions stX) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  ami_new : forall rid r', (s_regions stX) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  ami_next : (s_next_rid st <= s_next_rid stX)%N;
  ami_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P st -> ptrs_in P stX;
  ami_fresh : forall rid, (s_next_rid stX <= rid)%N -> (s_regions stX) !! rid = None /\ (s_shadow stX) !! rid = None;
  ami_rpos : forall q rq, (s_regions stX) !! q = Some rq -> 0 < r_len rq
}.

Section PURE.
Variable st : mstate.
Hypothesis AMP : AMpre st.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End PURE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_carve_took {R} stZ p (k : mstate -> optr -> M R) bail :
  am_carve stZ p k bail = k (am_took (carve_st stZ p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof. reflexivity. Qed.

Lemma am_after_brk_false_eq {R} stB f p (k : mstate -> optr -> M R) bail :
  c_avail_meta_area_count (f (s_ctx stB)) <> 0 -> c_avail_meta_areas (f (s_ctx stB)) = Some p -> snd p mod PGSZ = 0 ->
  am_after_brk (upd_ctx f stB) false k bail = am_carve (upd_ctx f stB) p k bail.
Proof.
  intros H1 H2 H3. unfold am_after_brk, am_finish. cbn [ctx upd_ctx s_ctx].
  rewrite (proj2 (Z.eqb_neq _ _) H1), H2, H3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma carve_st_brk_irrel stB c1 a b p :
  carve_st (upd_ctx (fun c => set_avail_meta_area_count c1 (set_avail_meta_areas a (set_brk b c))) stB) p
  = carve_st (upd_ctx (fun c => set_avail_meta_area_count c1 (set_brk b c)) stB) p.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

End ACeilS1.
