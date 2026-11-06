(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanPS AsanRep AsanKern AsanBudget AsanBudget2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_fakestack_rep BF_kit BF_poison B_bundle B_balloc5 B_rtok5 BF_alloc_iface.
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
Definition A_POPULATE : Z := 0x37c04.
(* [comment removed for export] *)
Definition K_POP : Z := 1536.

Section PopIface.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation RI := (ae_region_info E0).
#[local] Notation T := (ae_thread E0).

(* [comment removed for export] *)
Definition pop_cells (a : astate) (c : Z) (m : mem) (fjunk : list word) (shj fshj : list byte) : Prop :=
  let r := get_region a c in
     rw_cells bsegs m (A_INST + 32) [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m (RI + kRegSize * c) (C8 (wz (2^60)) :: List.tl (region_cells r))   (* [comment removed for export] *)
  /\ wr_at bsegs m (region_beg SB c) (rg_mapped_user r)
  /\ u32arr bsegs m (free_array SB c) (map wz (rg_free r) ++ fjunk) /\ 4 * (zlen (rg_free r) + zlen fjunk) = rg_mapped_fa r
  /\ rw_cells bsegs m (kShadowBase + (region_beg SB c + rg_mapped_user r) / 8) [CB (Z.to_nat (kUserMapSize / 8)) shj]
  /\ rw_cells bsegs m (kShadowBase + (free_array SB c + rg_mapped_fa r) / 8) [CB (Z.to_nat (kFreeArrayMapSize / 8)) fshj]
  /\ rw_cells bsegs m (T + kThrStats + 72) [C8 (wz (ts_mmaps (as_ts a))); C8 (wz (ts_mmaped (as_ts a)))]
  /\ rw_cells bsegs m (T + kThrCacheStats + 24) [C8 (wz (as_cache_mapped a))].

(* [comment removed for export] *)
Definition pop_cells_out (a : astate) (c : Z) (m : mem) (fjunk : list word) : Prop :=
  let r := get_region a c in
     rw_cells bsegs m (A_INST + 32) [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m (RI + kRegSize * c) (C8 (wz (2^60)) :: List.tl (region_cells r))
  /\ wr_at bsegs m (region_beg SB c) (rg_mapped_user r)
  /\ u32arr bsegs m (free_array SB c) (map wz (rg_free r) ++ fjunk) /\ 4 * (zlen (rg_free r) + zlen fjunk) = rg_mapped_fa r
  /\ rw_cells bsegs m (T + kThrStats + 72) [C8 (wz (ts_mmaps (as_ts a))); C8 (wz (ts_mmaped (as_ts a)))]
  /\ rw_cells bsegs m (T + kThrCacheStats + 24) [C8 (wz (as_cache_mapped a))].

(* [comment removed for export] *)
Definition pop_statics (m : mem) : Prop := XB_mmap_fixed.statics m /\ poison_globals m.

(* [comment removed for export] *)
Definition pop_W (a a' : astate) (c usp : Z) : list (Z * Z) :=
  let r := get_region a c in let r' := get_region a' c in
  [ (usp - K_POP, usp)
  ; (RI + kRegSize * c, RI + kRegSize * c + kRegSize)
  ; (region_beg SB c + rg_mapped_user r, region_beg SB c + rg_mapped_user r')        (* [comment removed for export] *)
  ; (free_array SB c + 4 * zlen (rg_free r), free_array SB c + rg_mapped_fa r')
  ; (kShadowBase + (region_beg SB c + rg_mapped_user r) / 8, kShadowBase + (region_beg SB c + rg_mapped_user r') / 8)
  ; (kShadowBase + (free_array SB c + rg_mapped_fa r) / 8, kShadowBase + (free_array SB c + rg_mapped_fa r') / 8)
  ; (T + kThrStats + 72, T + kThrStats + 88)
  ; (T + kThrCacheStats + 24, T + kThrCacheStats + 32) ].

(* [comment removed for export] *)
Definition pop_post (a a' : astate) (c req : Z) (m m' : mem) (mo mo' : Model) (s : aps) (C C' lo usp : Z) : Prop :=
     (exists fuel orc evs orc', arun fuel (populate_free_array E0 c req a) orc = Some (a', ONorm true, evs, orc'))
  /\ AKern E0 a' mo' /\ RTOKc C C' (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ stk bsegs m' lo usp /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ munch (pop_W a a' c usp) m m'
  /\ (exists fjunk', pop_cells_out a' c m' fjunk')
  /\ pop_statics m'
  (* [comment removed for export] *)
  /\ rw_cells bsegs m' (kShadowBase + (region_beg SB c + rg_mapped_user (get_region a c)) / 8)
       [CB (Z.to_nat ((rg_mapped_user (get_region a' c) - rg_mapped_user (get_region a c)) / 8))
           (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((rg_mapped_user (get_region a' c) - rg_mapped_user (get_region a c)) / 8)))]
  /\ rw_cells bsegs m' (kShadowBase + (free_array SB c + rg_mapped_fa (get_region a c)) / 8)
       [CB (Z.to_nat ((rg_mapped_fa (get_region a' c) - rg_mapped_fa (get_region a c)) / 8))
           (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((rg_mapped_fa (get_region a' c) - rg_mapped_fa (get_region a c)) / 8)))].

(* [comment removed for export] *)
Definition populate_srz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (Pq : list Z) (Dq : list batch)
         (c req lo C C' : Z) (fjunk : list word) (shj fshj : list byte) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in let r := get_region a c in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> AKern E0 a mo -> AWf E0 Pq Dq a -> 1 <= c <= kLargestClassID -> 1 <= req <= hint c ->     (* [comment removed for export] *)
  rg_mapped_user r + kUserMapSize <= kFreeArrayOffset ->                                                     (* [comment removed for export] *)
  4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) + kFreeArrayMapSize <= kFreeArraySize ->   (* [comment removed for export] *)
  4 * (rg_num_freed r + (rg_mapped_user r + kUserMapSize - rg_alloc_user r) / class_size c) <= rg_mapped_fa r + kFreeArrayMapSize ->  (* [comment removed for export] *)
  kUserMapSize + kFreeArrayMapSize <= gapR a ->                                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_POP -> usp mod 16 = 0 -> usp < 2^47 -> mem_inv bsegs m ->
  tp = wz 0x5e1550 ->
  T mod 8 = 0 ->                                                   (* [comment removed for export] *)
  thread_cells m tp 0x6028f8 (fp_ctx PL0) T ->
  pop_cells a c m fjunk shj fshj -> pop_statics m ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     pop_post a a' c req m m' mo mo' s C C' lo usp ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz (T + kThrCacheStats)) (wz c) (wz (RI + kRegSize * c)) (wz req) a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_POPULATE) fc None m (seg_rom bsegs)) mo) K.
End PopIface.
End RC__1.
