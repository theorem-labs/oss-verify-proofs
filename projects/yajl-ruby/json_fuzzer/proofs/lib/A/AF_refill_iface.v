(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AF_fakestack_rep A_slack5 A_bundle A_init5 A_balloc5 A_rtok5 AF_alloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_REFILL : Z := 0x379f0.
(* [comment removed for export] *)
Definition K_REFILL : Z := 1760.

Section RefillIface.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).

(* [comment removed for export] *)
Definition RINV (Pq : list Z) (Dq : list batch) (a : astate) (m : mem) (mo : Model) : Prop :=
     ARep asegs E0 (DepotR asegs E0) a m /\ AWf E0 Pq Dq a /\ AKern E0 a mo /\ res_ok a /\ AQbound a /\ depot_inv E0 a
  /\ mem_inv asegs m /\ rt_misc5 FSB0 PL0 E0 m
  /\ sstats_ok a                                   (* [comment removed for export] *)
  /\ csmall a.                                     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition refill_room (a : astate) (c : Z) : Prop :=
  let r := get_region a c in
     rg_mapped_user r + kUserMapSize <= kFreeArrayOffset
  /\ 4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) + kFreeArrayMapSize <= kFreeArraySize
  /\ 4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) <= rg_mapped_fa r + kFreeArrayMapSize
  /\ kUserMapSize + kFreeArrayMapSize <= gapR a
  /\ rg_mapped_fa r + kFreeArrayMapSize <= kFreeArraySize.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition refill_same (a a' : astate) : Prop :=
     as_chunks a' = as_chunks a /\ as_dead a' = as_dead a /\ as_tq a' = as_tq a /\ as_gq a' = as_gq a
  /\ as_sec a' = as_sec a /\ as_sec_stale a' = as_sec_stale a /\ as_sec_stats a' = as_sec_stats a /\ as_ptr_committed a' = as_ptr_committed a
  /\ as_keys a' = as_keys a /\ as_frames a' = as_frames a /\ as_ndepot_ins a' = as_ndepot_ins a /\ as_nprim_ever a' = as_nprim_ever a
  /\ as_residue a' = as_residue a /\ as_node_blocks a' = as_node_blocks a /\ as_store_blocks a' = as_store_blocks a /\ as_store_stored a' = as_store_stored a
  /\ as_ia_inited a' = as_ia_inited a /\ as_cache_allocated a' = as_cache_allocated a /\ as_everc a' = as_everc a
  /\ as_glob_allocated a' = as_glob_allocated a /\ as_glob_mapped a' = as_glob_mapped a /\ as_oom a' = as_oom a.

(* [comment removed for export] *)
Definition refill_post (Pq : list Z) (Dq : list batch) (a a' : astate) (m m' : mem) (mo mo' : Model) (s : aps) (C C' c lo usp : Z) : Prop :=
     stk asegs m' lo usp /\ wmono asegs m m'
  /\ (exists W, munch W m m' /\ Forall (aw_ok E0 a a' lo usp) W
               /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W)
  /\ (exists fuel orc evs orc', arun fuel (refill E0 c a) orc = Some (a', ONorm true, evs, orc'))
  /\ RINV Pq Dq a' m' mo'
  /\ RTOKc C C' (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ refill_same a a' /\ (forall c', c' <> c -> get_cache a' c' = get_cache a c' /\ get_region a' c' = get_region a c')
  /\ as_cache_inited a' = true /\ zlen (get_cache a' c) = hint c.

(* [comment removed for export] *)
Definition refill_srz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (Pq : list Z) (Dq : list batch) (c lo C C' : Z) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> RINV Pq Dq a m mo -> 1 <= c <= kLargestClassID -> get_cache a c = [] -> refill_room a c ->
  0 <= as_nprim_ever a <= 12000 ->
  (* [comment removed for export] *)
  stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_REFILL -> usp mod 16 = 0 -> usp + 48 <= 2^47 ->   (* [comment removed for export] *)
  tp = wz 0x5e0b10 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     refill_post Pq Dq a a' m m' mo mo' s C C' c lo usp ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (T + kThrCache)) (wz (T + kThrCache + kPerClassSize * c)) (wz A_INST) (wz c) a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_REFILL) fc None m (seg_rom asegs)) mo) K.

End RefillIface.
End RC__1.
