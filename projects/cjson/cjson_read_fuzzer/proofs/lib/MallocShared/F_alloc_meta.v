(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_H.
Module F_am_P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_H.F_am_G.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_carve_took {R} stZ p (k : mstate -> optr -> M R) bail :
  am_carve stZ p k bail = k (am_took (carve_st stZ p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof.
  (* [comment removed for export] *)
  rewrite am_carve_eq. generalize (carve_st stZ p) as X. intros X. destruct X as [c ? ? ? ? ? ? ? ? ? ?]. destruct c. reflexivity.
Qed.

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

End CeilWrap.
End F_am_P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require  MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_mm_syscalls MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_K.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_am_K2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_H.F_am_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_H.F_am_G.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_am_H.
Import F_am_P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

End CeilWrap.
