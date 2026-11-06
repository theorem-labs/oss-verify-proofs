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

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_DEALLOCATE : Z := 0x328ec.
(* [comment removed for export] *)
Definition K_FREE : Z := 4096.
(* [comment removed for export] *)
Definition FSLACK : Z := 2^29.

Section FreeIface.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation AINVc := (AINV E0 FSB0 PL0).

(* [comment removed for export] *)
Definition fbudget_pre (a : astate) : Prop :=
  0 <= as_nprim_ever a /\ 0 <= as_ndepot_ins a /\ 10000 * as_nprim_ever a + as_ndepot_ins a + 1 <= kInitialCredit.

(* [comment removed for export] *)
Definition facct (a a' : astate) : Prop :=
     as_nprim_ever a' = as_nprim_ever a /\ as_residue a' = as_residue a
  /\ as_ndepot_ins a <= as_ndepot_ins a' <= as_ndepot_ins a + 1.

(* [comment removed for export] *)
Definition dealloc_post_state (a a' : astate) (m m' : mem) (mo mo' : Model) (s : aps) (C C' p n lo usp : Z) (key : list Z) : Prop :=
     (* [comment removed for export] *)
     stk asegs m' lo usp
  /\ (exists W, munch W m m' /\ Forall (aw_ok E0 a a' lo usp) W
               /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> (blo, bsz) <> (p, n) ->
                                    snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W)
     (* [comment removed for export] *)
  /\ (exists fuel orc evs orc', arun fuel (afree_core E0 key p a) orc = Some (a', ONorm tt, evs, orc'))
  /\ AINVc a' m' mo'
  /\ RTOKc (C - 1) (C' - FSLACK) (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ facct a a'
  /\ Permutation (live_blocks a) ((p, n) :: live_blocks a').

(* [comment removed for export] *)
Definition dealloc_srz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps)
         (p n lo B A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> 1 <= C -> FSLACK <= C' -> AINVc a m mo -> fbudget_pre a ->
  In (p, n) (live_blocks a) ->
  (* [comment removed for export] *)
  stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_FREE -> usp mod 16 = 0 ->
  tp = wz 0x5e0b10 ->
  (* [comment removed for export] *)
  usp <= B -> B + 16 <= A -> A + 8 * zlen ws < 2^47 ->
  rw_cells asegs m B [C8 (wz A); C8 (wz len)] -> u64arr asegs m A ws -> 1 <= len <= zlen ws -> zlen ws <= 30 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     dealloc_post_state a a' m m' mo mo' s C C' p n lo usp (bst_key len ws) ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz p) (wz 0) (wz 0) (wz B) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_DEALLOCATE) fc None m (seg_rom asegs)) mo) K.
End FreeIface.
End RC__1.
