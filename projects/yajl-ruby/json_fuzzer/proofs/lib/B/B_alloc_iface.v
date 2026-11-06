(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Nodes NodesCfg FP RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase KLink.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Export B_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ACREDIT0 : Z := 120000000.                      (* [comment removed for export] *)
Definition ycost (L : Z) : Z := 6600000 + 4 * L / 64.      (* [comment removed for export] *)
Definition afree_cost (A : Z) : Z := if Z.eqb A 0 then 0 else 1.
Definition count_yfuzz (H : list aevent) : nat := length (List.filter (fun e => match e with EvYfuzz => true | _ => false end) H).

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Stmts.
Variable segs : list Segment.          (* [comment removed for export] *)
Variable C : adrv_consts.

(* [comment removed for export] *)
Variable APS : Type.                                                   (* [comment removed for export] *)
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.                                        (* [comment removed for export] *)
Variable amalloc_rel : Z -> APS -> Model -> option Z -> APS -> Model -> Prop.
Variable afree_rel : Z -> APS -> Model -> APS -> Model -> Prop.
Variable ayfuzz_rel : APS -> Model -> APS -> Model -> Prop.
Variable aalloc_same : APS -> APS -> Prop.
Variable arealloc_rel : Z -> Z -> APS -> Model -> option Z -> APS -> Model -> Prop.
Variable acredit : APS -> Z.                                            (* [comment removed for export] *)
Variable acharge : Z -> Z.                                              (* [comment removed for export] *)
Variable arefund : Z -> Z.                                              (* [comment removed for export] *)
Variable uanchor : mem -> Z (* [comment removed for export] *) -> word (* [comment removed for export] *) -> word (* [comment removed for export] *) -> Prop.
Variable AHEAD : nat -> list (Z * Z) -> list aevent -> APS -> Model -> Prop.

#[local] Notation usp sp := (bv_unsigned sp).
#[local] Notation ST m lo sp := (stk segs m lo (bv_unsigned sp)).
#[local] Notation ablock_range := (B_base.ablock_range C).

(* [comment removed for export] *)
Definition aheap_pres (LB : list ablock) (LF : list fblock) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient_addr C LB LF SP a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Definition acharge_bound_stmt : Prop := forall n, 0 <= arefund n <= acharge n.
Definition ab_find (A : Z) (LB : list ablock) : option ablock := List.find (fun b => Z.eqb (ab_addr b) A) LB.
Definition arefund_at (A : Z) (LB : list ablock) : Z := match ab_find A LB with Some b => arefund (ab_size b) | None => 0 end.
(* [comment removed for export] *)
Definition nbig (LB : list ablock) : Z := Z.of_nat (length (List.filter (fun b => 64512 <? ab_size b) LB)).
Definition aalloc_same_refl_stmt : Prop := forall s, aalloc_same s s.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition afree_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (A lo : Z) (K : TSet),
  K [] ->
  AHK s LB LF m mo -> (A = 0 \/ exists b, In b LB /\ ab_addr b = A) ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AMALLOC_STACK -> usp sp mod 16 = 0 -> usp sp < 2^47 ->
  tp = wz (c_tp C) -> uanchor m (usp sp) ra s0 -> frm0 fc ->
  a0 = wz A -> afree_cost A <= acredit s ->      (* [comment removed for export] *)
  nbig LB <= 8000 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> aheap_pres (ab_remove A LB) LF (usp sp) m m' -> frm0 fc' -> SO s' = SO s ->
     AHK s' (ab_remove A LB) LF m' mo' -> afree_rel A s mo s' mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
     acredit s + arefund_at A LB - afree_cost A <= acredit s' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_free C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
Definition amalloc_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (n lo : Z) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AMALLOC_STACK -> usp sp mod 16 = 0 -> usp sp < 2^47 ->
  tp = wz (c_tp C) -> uanchor m (usp sp) ra s0 -> frm0 fc ->
  a0 = wz n -> 0 < n <= 2^27 -> acharge n <= acredit s -> nbig LB <= 8000 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (A : Z),
     ST m' lo sp -> aheap_pres LB LF (usp sp) m m' -> wmono segs m m' -> frm0 fc' -> SO s' = SO s ->
     amalloc_rel n s mo (Some A) s' mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> acredit s - acharge n <= acredit s' ->
     a0' = wz A -> ablock_range A n -> AHK s' (mkABlock A n :: LB) LF m' mo' ->
     (exists junk, length junk = Z.to_nat n /\ rw_cells segs m' A [CB (Z.to_nat n) junk]) ->
     block_shadow segs m' A_SB A n ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_malloc C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
Definition arealloc_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (A sz n lo : Z) (old : list byte) (K : TSet),
  K [] ->
  AHK s LB LF m mo -> In (mkABlock A sz) LB -> bytes_at segs m A old -> Z.of_nat (length old) = sz ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AMALLOC_STACK -> usp sp mod 16 = 0 -> usp sp < 2^47 ->
  tp = wz (c_tp C) -> uanchor m (usp sp) ra s0 -> frm0 fc ->
  a0 = wz A -> a1 = wz n -> 0 < n <= 2^27 -> acharge n + 1 <= acredit s -> nbig LB <= 8000 ->   (* [comment removed for export] *)
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (A' : Z),
     ST m' lo sp -> frm0 fc' -> SO s' = SO s ->
     arealloc_rel A n s mo (Some A') s' mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
     acredit s - acharge n - 1 <= acredit s' ->     (* [comment removed for export] *)
     a0' = wz A' -> ablock_range A' n -> AHK s' (mkABlock A' n :: ab_remove A LB) LF m' mo' ->
     acredit s - acharge n + arefund_at A LB - 1 <= acredit s' ->
     aheap_pres (ab_remove A LB) LF (usp sp) m m' ->
     (exists junk, rw_cells segs m' A' [CB (Z.to_nat (Z.min n sz)) (firstn (Z.to_nat (Z.min n sz)) old);
                                        CB (Z.to_nat (n - Z.min n sz)) junk]) ->
     block_shadow segs m' A_SB A' n ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_realloc C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
Definition arealloc_null_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (n lo : Z) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AMALLOC_STACK -> usp sp mod 16 = 0 -> usp sp < 2^47 ->
  tp = wz (c_tp C) -> uanchor m (usp sp) ra s0 -> frm0 fc ->
  a0 = wz 0 -> a1 = wz n -> 0 < n <= 2^27 -> acharge n <= acredit s -> nbig LB <= 8000 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (A : Z),
     ST m' lo sp -> aheap_pres LB LF (usp sp) m m' -> wmono segs m m' -> frm0 fc' -> SO s' = SO s ->
     arealloc_rel 0 n s mo (Some A) s' mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> acredit s - acharge n <= acredit s' ->
     a0' = wz A -> ablock_range A n -> AHK s' (mkABlock A n :: LB) LF m' mo' ->
     (exists junk, length junk = Z.to_nat n /\ rw_cells segs m' A [CB (Z.to_nat n) junk]) ->
     block_shadow segs m' A_SB A n ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_realloc C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ahead_malloc_stmt : Prop :=
  forall s mo n k X H A s' mo', AHEAD (S k) X H s mo -> 0 < n <= 2^26 -> amalloc_rel n s mo (Some A) s' mo' ->
    AHEAD k ((A, n) :: X) (EvMalloc n (Some A) :: H) s' mo'.
Definition ahead_free_stmt : Prop :=
  forall s mo A n k X H s' mo', AHEAD (S k) ((A, n) :: X) H s mo -> afree_rel A s mo s' mo' -> AHEAD k X (EvFree A :: H) s' mo'.
Definition ahead_free0_stmt : Prop :=
  forall s mo k X H s' mo', AHEAD (S k) X H s mo -> afree_rel 0 s mo s' mo' -> AHEAD k X (EvFree 0 :: H) s' mo'.
Definition ahead_perm_stmt : Prop :=
  forall s mo k X Y H, AHEAD k X H s mo -> Permutation X Y -> AHEAD k Y H s mo.
Definition ahead_weaken_stmt : Prop :=
  forall s mo k X H, AHEAD (S k) X H s mo -> AHEAD k X H s mo.
Definition ahead_yfuzz_stmt : Prop :=         (* [comment removed for export] *)
  forall s mo k X H s' mo', AHEAD (S k) X H s mo -> (count_yfuzz H < 4)%nat -> ayfuzz_rel s mo s' mo' -> AHEAD k X (EvYfuzz :: H) s' mo'.
Definition ahead_magree_stmt : Prop :=
  forall s mo mo' k X H, AHEAD k X H s mo -> magree mo mo' -> AHEAD k X H s mo'.
Definition ahead_vmsame_stmt : Prop :=
  forall s mo mo' k X H, AHEAD k X H s mo -> vm_same mo mo' -> AHEAD k X H s mo'.
Definition ahead_aps_stmt : Prop :=
  forall s s' mo k X H, AHEAD k X H s mo -> aalloc_same s s' -> AHEAD k X H s' mo.
Definition ahead_credit_malloc_stmt : Prop :=
  forall s mo k X H n, AHEAD (S k) X H s mo -> 0 <= n <= 2^26 -> acharge n <= acredit s.
Definition ahead_credit_free_stmt : Prop :=
  forall s mo k X H A, AHEAD (S k) X H s mo -> afree_cost A <= acredit s.
Definition ahead_reserve_stmt : Prop :=
  forall s mo k X H, AHEAD k X H s mo -> 2 <= acredit s.
Definition ahead_credit_yfuzz_stmt : Prop :=
  forall s mo k X H L, AHEAD k X H s mo -> (count_yfuzz H < 4)%nat -> 0 <= L < 2^26 -> ycost L <= acredit s.

End Stmts.

(* [comment removed for export] *)
Record a_alloc_iface (segs : list Segment) (C : adrv_consts) (APS : Type)
    (AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop) (SO : APS -> stdout_st)
    (amalloc_rel : Z -> APS -> Model -> option Z -> APS -> Model -> Prop)
    (afree_rel : Z -> APS -> Model -> APS -> Model -> Prop)
    (ayfuzz_rel : APS -> Model -> APS -> Model -> Prop)
    (aalloc_same : APS -> APS -> Prop)
    (arealloc_rel : Z -> Z -> APS -> Model -> option Z -> APS -> Model -> Prop)
    (acredit : APS -> Z) (acharge arefund : Z -> Z)
    (uanchor : mem -> Z -> word -> word -> Prop)
    (AHEAD : nat -> list (Z * Z) -> list aevent -> APS -> Model -> Prop) : Prop := mkAAllocIface {
  aai_charge   : acharge_bound_stmt acharge arefund;
  aai_asame_refl : aalloc_same_refl_stmt APS aalloc_same;
  aai_free     : afree_rz_stmt segs C APS AHK SO afree_rel acredit arefund uanchor;
  aai_malloc   : amalloc_rz_stmt segs C APS AHK SO amalloc_rel acredit acharge uanchor;
  aai_realloc  : arealloc_rz_stmt segs C APS AHK SO arealloc_rel acredit acharge arefund uanchor;
  aai_realloc0 : arealloc_null_rz_stmt segs C APS AHK SO arealloc_rel acredit acharge uanchor;
  aai_hd_malloc : ahead_malloc_stmt APS amalloc_rel AHEAD;
  aai_hd_free  : ahead_free_stmt APS afree_rel AHEAD;
  aai_hd_free0 : ahead_free0_stmt APS afree_rel AHEAD;
  aai_hd_perm  : ahead_perm_stmt APS AHEAD;
  aai_hd_weaken : ahead_weaken_stmt APS AHEAD;
  aai_hd_yfuzz : ahead_yfuzz_stmt APS ayfuzz_rel AHEAD;
  aai_hd_magree : ahead_magree_stmt APS AHEAD;
  aai_hd_vmsame : ahead_vmsame_stmt APS AHEAD;
  aai_hd_aps   : ahead_aps_stmt APS aalloc_same AHEAD;
  aai_hd_cmalloc : ahead_credit_malloc_stmt APS acredit acharge AHEAD;
  aai_hd_cfree : ahead_credit_free_stmt APS acredit AHEAD;
  aai_hd_reserve : ahead_reserve_stmt APS acredit AHEAD;
  aai_hd_cyfuzz : ahead_credit_yfuzz_stmt APS acredit AHEAD
}.
End RC__1.
