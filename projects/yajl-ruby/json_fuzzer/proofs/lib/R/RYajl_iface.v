(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Exec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Export NodesCfg.          (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Export MSuccIface.       (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import ImplRz ImplRzCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser
     YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition RY_TARGET_RUN : Z := 0x137a4.
Definition RY_FUZZ : Z := 0x13974.          (* [comment removed for export] *)
Definition RY_CB_NULL : Z := 0x139f0.
Definition RY_CB_BOOLEAN : Z := 0x139f8.
Definition RY_CB_NUMBER : Z := 0x13a00.
Definition RY_CB_STRING : Z := 0x13a34.
Definition RY_CB_START_MAP : Z := 0x13a3c.   (* [comment removed for export] *)
Definition RY_CB_MAP_KEY : Z := 0x13a54.     (* [comment removed for export] *)
Definition RY_CB_END_MAP : Z := 0x13a8c.     (* [comment removed for export] *)
Definition RY_CB_START_ARRAY : Z := 0x13ad0.
Definition RY_CB_END_ARRAY : Z := 0x13ae8.
Definition RY_ALLOC : Z := 0x13b2c.          (* [comment removed for export] *)
Definition RY_RESET : Z := 0x13c8c.          (* [comment removed for export] *)
Definition RY_FREE : Z := 0x13cdc.           (* [comment removed for export] *)
Definition RY_PARSE : Z := 0x13d54.          (* [comment removed for export] *)
Definition RY_SET_DEFAULT : Z := 0x13d84.    (* [comment removed for export] *)
Definition RY_MALLOC_W : Z := 0x13db0.       (* [comment removed for export] *)
Definition RY_FREE_W : Z := 0x13dbc.         (* [comment removed for export] *)
Definition RY_REALLOC_W : Z := 0x13dc4.      (* [comment removed for export] *)
Definition RY_LEX_ALLOC : Z := 0x13dd8.
Definition RY_LEX_REALLOC : Z := 0x13e5c.
Definition RY_LEX_FREE : Z := 0x13e94.
Definition RY_LEX_LEX : Z := 0x13ecc.
Definition RY_BUF_ERR : Z := 0x14f9c.
Definition RY_BUF_ALLOC : Z := 0x14fd0.
Definition RY_BUF_FREE : Z := 0x15030.
Definition RY_BUF_APPEND : Z := 0x1509c.
Definition RY_BUF_CLEAR : Z := 0x1523c.
Definition RY_BUF_DATA : Z := 0x152ac.
Definition RY_BUF_LEN : Z := 0x15310.
Definition RY_NOOP_MALLOC : Z := 0x15374.
Definition RY_NOOP_REALLOC : Z := 0x153a0.
Definition RY_NOOP_FREE : Z := 0x153cc.
Definition RY_DO_PARSE : Z := 0x153d0.
Definition RY_PARSE_HEAD : Z := 0x15460.     (* [comment removed for export] *)
Definition RY_BS_SET : Z := 0x1682c.         (* [comment removed for export] *)
Definition RY_STRING_DECODE : Z := 0x168a8.
Definition RY_HEXTODIGIT : Z := 0x16cb0.
Definition RREALLOC_SYM : Z := 0x19170.      (* [comment removed for export] *)
Definition RSTRLEN : Z := 0x22318.
Definition RMEMCPY : Z := 0x21e1c.
Definition RMEMSET : Z := 0x22220.

(* [comment removed for export] *)
Definition RY_CALLBACKS : Z := 0x24968.      (* [comment removed for export] *)
Definition RY_NOOP_ALLOCS : Z := 0x249c0.    (* [comment removed for export] *)
Definition RY_BUF_ALLOC_ERROR : Z := 0x249e0. (* [comment removed for export] *)
Definition RY_EMPTY : Z := 0x34c50.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RY_JT_LEX : Z := 0x10930.         (* [comment removed for export] *)
Definition RY_CHARTAB : Z := 0x109f8.        (* [comment removed for export] *)
Definition RY_JT_STATE : Z := 0x10af8.       (* [comment removed for export] *)
Definition RY_JT_TOKMAP : Z := 0x10b28.      (* [comment removed for export] *)
Definition RY_JT_TOKVAL : Z := 0x10b54.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ry_perr (e : perr) : Z :=
  match e with
  | PE_client_cancelled => 0x106b6        (* [comment removed for export] *)
  | PE_alloc_failed => 0x107cb            (* [comment removed for export] *)
  | PE_unallowed_token => 0x104b3         (* [comment removed for export] *)
  | PE_invalid_token_internal => 0x108e6  (* [comment removed for export] *)
  | PE_invalid_object_key => 0x10870      (* [comment removed for export] *)
  | PE_expect_colon => 0x10609            (* [comment removed for export] *)
  | PE_map_expect => 0x1050f              (* [comment removed for export] *)
  | PE_array_expect => 0x10753            (* [comment removed for export] *)
  end.
(* [comment removed for export] *)

Definition ryc : yconsts :=
  mkYC RY_MALLOC_W RY_REALLOC_W RY_FREE_W RY_CALLBACKS
       RY_CB_NULL RY_CB_BOOLEAN RY_CB_NUMBER RY_CB_STRING RY_CB_START_MAP RY_CB_MAP_KEY RY_CB_END_MAP
       RY_CB_START_ARRAY RY_CB_END_ARRAY ry_perr RY_BUF_ALLOC_ERROR RY_NOOP_ALLOCS.

Definition noop_allocs_cells : list cell :=
  [C8 (wz RY_NOOP_MALLOC); C8 (wz RY_NOOP_REALLOC); C8 (wz RY_NOOP_FREE); C8 (wz 0)].

(* [comment removed for export] *)
Definition RREALLOC_STACK : Z := 8256.                       (* [comment removed for export] *)
Definition RY_WRAP_STACK : Z := 8256.                        (* [comment removed for export] *)
Definition RY_BUF_ALLOC_STACK : Z := 32 + RY_WRAP_STACK.     (* [comment removed for export] *)
Definition RY_BUF_FREE_STACK : Z := 16 + RY_WRAP_STACK.
Definition RY_BUF_APPEND_STACK : Z := 48 + RY_WRAP_STACK.   (* [comment removed for export] *)
Definition RY_BUF_SMALL_STACK : Z := 16.                     (* [comment removed for export] *)
Definition RY_LEX_ALLOC_STACK : Z := 48 + RY_BUF_ALLOC_STACK.
Definition RY_LEX_REALLOC_STACK : Z := 16 + RY_BUF_SMALL_STACK.
Definition RY_LEX_FREE_STACK : Z := 16 + RY_BUF_FREE_STACK.
Definition RY_LEX_LEX_STACK : Z := 128 + RY_BUF_APPEND_STACK.
Definition RY_DECODE_STACK : Z := 208 + RY_BUF_APPEND_STACK. (* [comment removed for export] *)
Definition RY_RESET_STACK : Z := 16 + RY_LEX_REALLOC_STACK.
Definition RY_DO_PARSE_STACK : Z := 144 + RY_DECODE_STACK.   (* [comment removed for export] *)
Definition RY_ALLOC_STACK : Z := 96 + RY_LEX_ALLOC_STACK.
Definition RY_FREE_STACK : Z := 16 + RY_LEX_FREE_STACK.
Definition RY_PARSE_STACK : Z := RY_DO_PARSE_STACK.             (* [comment removed for export] *)
Definition RY_FUZZ_STACK : Z := 48 + RY_PARSE_STACK.

End RC__1.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RYajl.
(* [comment removed for export] *)
Variable HK : PState -> list block -> mem -> Model -> Prop.

(* [comment removed for export] *)
Definition HK_silent_stmt : Prop :=
  forall s LB m mo, HK s LB m mo -> m_halted mo = None /\ m_vm_lazy mo = [].

Definition HK_perm_stmt : Prop :=
  forall s LB LB' m mo, HK s LB m mo -> Permutation.Permutation LB LB' -> HK s LB' m mo.

(* [comment removed for export] *)
Definition HK_frame_stmt : Prop :=
  forall s LB m m' mo W,
    HK s LB m mo -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> HK s LB m' mo.

Definition HK_blocks_stmt : Prop :=
  forall s LB m mo, HK s LB m mo ->
    (forall b, In b LB -> rblock_range (blk_addr b) (blk_size b))
    /\ (forall b1 b2, In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
          blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1)
    /\ List.NoDup (map blk_id LB).

(* [comment removed for export] *)
Lemma rz_evt : forall (Q : machine_state -> Prop) ms mo (K : TSet),
  evt rsegs Q ms -> m_halted mo = None -> m_vm_lazy mo = [] ->
  (forall ms', Q ms' -> realizes_cfg acfg rsegs (mkCfg ms' mo) K) ->
  realizes_cfg acfg rsegs (mkCfg ms mo) K.
Proof.
  intros Q ms mo K (ms' & Hs & HQ) Hh Hl HK'. eapply (rz_msteps_lib_cfg acfg rsegs); eauto.
Qed.

(* [comment removed for export] *)
Definition yroom (REST : list block) (k : Z) : Prop := Z.of_nat (length REST) + k <= NHELDc.
Lemma yroom_le : forall REST k k', yroom REST k -> k' <= k -> yroom REST k'.
Proof. unfold yroom. intros. lia. Qed.
Lemma yroom_cons : forall b REST k, yroom REST (k + 1) -> yroom (b :: REST) k.
Proof. unfold yroom. intros b REST k H. cbn [length]. lia. Qed.
Lemma yroom_app : forall L REST k, yroom REST (k + Z.of_nat (length L)) -> yroom (L ++ REST) k.
Proof. unfold yroom. intros L REST k H. rewrite length_app. lia. Qed.
Lemma yroom_lt : forall REST k, yroom REST k -> 1 <= k -> Z.of_nat (length REST) < NHELDc.
Proof. unfold yroom. intros. lia. Qed.


(* [comment removed for export] *)

Definition rmalloc_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a0 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> HK s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells rsegs m' A [CB (Z.to_nat n) junk]) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RMALLOC_SYM) fc None m (seg_rom rsegs)) mo) K.

Definition rfree_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a0 = wz A ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv] ->
     rauxv_ok m' B -> rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     HK s' (lb_remove p LB) m' mo' ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RFREE_SYM) fc None m (seg_rom rsegs)) mo) K.

(* [comment removed for export] *)
Definition rrealloc_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (old : list byte) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo -> In (p, A, sz) LB -> bytes_at rsegs m A old -> Z.of_nat (length old) = sz ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a0 = wz A -> a1 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p' : bptr) (A' : Z),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B ->
     a0' = wz A' -> rblock_range A' n -> HK s' ((p', A', n) :: lb_remove p LB) m' mo' ->
     rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     (exists junk, rw_cells rsegs m' A' [CB (Z.to_nat (Z.min n sz)) (firstn (Z.to_nat (Z.min n sz)) old);
                                      CB (Z.to_nat (n - Z.min n sz)) junk]) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RREALLOC_SYM) fc None m (seg_rom rsegs)) mo) K.

(* [comment removed for export] *)
Definition rrealloc_null_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a0 = wz 0 -> a1 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> HK s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells rsegs m' A [CB (Z.to_nat n) junk]) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RREALLOC_SYM) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RYST (s : PState) (LB : list block) (m : mem) (mo : Model) : Prop :=
  HK s LB m mo
  /\ rw_cells rsegs m RY_CALLBACKS (callbacks_cells ryc)
  /\ rw_cells rsegs m RY_BUF_ALLOC_ERROR (buf_alloc_error_cells ryc)
  /\ rw_cells rsegs m RY_NOOP_ALLOCS noop_allocs_cells.

(* [comment removed for export] *)
Definition yframe_pre (m : mem) (sp tp : word) (lo B budget : Z) (errv : word) : Prop :=
  rauxv_ok m B /\ bv_unsigned sp <= B
  /\ stk rsegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - budget
  /\ rw_cells rsegs m (errno_addr tp) [C4 errv] /\ mem_inv rsegs m /\ tp = wz RATP.

(* [comment removed for export] *)
Fixpoint yin_ivs (X : list (Z * Z)) (a : Z) : Prop :=
  match X with [] => False | iv :: X' => (fst iv <= a < snd iv) \/ yin_ivs X' a end.

Definition ry_pres (REST : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr REST SP a -> ~ yin_ivs X a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma ry_pres_refl : forall LB SP X m, ry_pres LB SP X m m.
Proof. intros LB SP X m a _ _ _. auto. Qed.
Lemma ry_pres_trans : forall LB SP X m1 m2 m3,
  ry_pres LB SP X m1 m2 -> ry_pres LB SP X m2 m3 -> ry_pres LB SP X m1 m3.
Proof.
  intros LB SP X m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.
(* [comment removed for export] *)
Lemma ry_pres_weaken : forall LB LB' SP SP' X X' m m',
  ry_pres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, yin_ivs X a -> yin_ivs X' a) ->
  ry_pres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha Hc Hx. apply H; [exact Ha| |intros Hx'; apply Hx, HX, Hx'].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.
Lemma ry_pres_of_rheap_pres : forall LB SP X m m', rheap_pres LB SP m m' -> ry_pres LB SP X m m'.
Proof. intros LB SP X m m' H a Ha Hc _. exact (H a Ha Hc). Qed.
Lemma ry_pres_nil : forall LB SP m m', ry_pres LB SP [] m m' <-> rheap_pres LB SP m m'.
Proof.
  intros LB SP m m'. split; [| apply ry_pres_of_rheap_pres].
  intros H a Ha Hc. apply H; [exact Ha| exact Hc| intros F0; exact F0].
Qed.

Definition yframe_post (m m' : mem) (sp tp : word) (lo B : Z) (REST : list block) (X : list (Z * Z)) : Prop :=
  mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
  /\ (exists errv' : word, rw_cells rsegs m' (errno_addr tp) [C4 errv'])
  /\ rauxv_ok m' B
  /\ ry_pres REST (bv_unsigned sp) X m m'.

(* [comment removed for export] *)
Definition mh_same (mh mh' : mhand) : Prop :=
  mh_id mh' = mh_id mh /\ mh_addr mh' = mh_addr mh /\ mh_lid mh' = mh_lid mh /\ mh_lexer mh' = mh_lexer mh
  /\ mb_id (mh_lexbuf mh') = mb_id (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh') = mb_addr (mh_lexbuf mh)
  /\ mb_id (mh_decbuf mh') = mb_id (mh_decbuf mh) /\ mb_addr (mh_decbuf mh') = mb_addr (mh_decbuf mh)
  /\ mh_ctx mh' = mh_ctx mh.
Definition mb_same (mb mb' : mbuf) : Prop := mb_id mb' = mb_id mb /\ mb_addr mb' = mb_addr mb.

(* [comment removed for export] *)
Definition fregs_same (F F' : bvmap 5 word) : Prop := forall k : reg, reg_get F' k = reg_get F k.
Lemma fregs_same_refl : forall F, fregs_same F F.
Proof. intros F k. reflexivity. Qed.
Lemma fregs_same_trans : forall F1 F2 F3, fregs_same F1 F2 -> fregs_same F2 F3 -> fregs_same F1 F3.
Proof. intros F1 F2 F3 H1 H2 k. rewrite (H2 k). apply H1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition yaf_in (REST : list block) (AF : Z) : Prop :=
  exists b, In b REST /\ blk_addr b <= AF /\ AF + 32 <= blk_addr b + blk_size b.

Definition ysrc_range (REST : list block) (sp : word) (S n : Z) : Prop :=
  (exists bt, In bt REST /\ blk_addr bt <= S /\ S + n <= blk_addr bt + blk_size bt)
  \/ (0x10000 <= S /\ S + n <= 0x13000)
  \/ bv_unsigned sp <= S
  \/ n = 0.                    (* [comment removed for export] *)

Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation lexer_struct := (lexer_struct rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
Notation yalloc_cells := (alloc_cells ryc).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ywrap_malloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RY_WRAP_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a1 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> HK s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells rsegs m' A [CB (Z.to_nat n) junk]) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_MALLOC_W) fc None m (seg_rom rsegs)) mo) K.

(* [comment removed for export] *)
Definition ywrap_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RY_WRAP_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a1 = wz A ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv] ->
     rauxv_ok m' B -> rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     HK s' (lb_remove p LB) m' mo' ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_FREE_W) fc None m (seg_rom rsegs)) mo) K.

(* [comment removed for export] *)
Definition ywrap_free_null_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6', ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom rsegs)).
Definition ywrap_free_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem), a1 = wz 0 ->
  evt rsegs (ywrap_free_null_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_FREE_W) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition ywrap_realloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (p : bptr) (A sz n lo B : Z) (old : list byte) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo -> In (p, A, sz) LB -> bytes_at rsegs m A old -> Z.of_nat (length old) = sz ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RY_WRAP_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a1 = wz A -> a2 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p' : bptr) (A' : Z),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B ->
     a0' = wz A' -> rblock_range A' n -> HK s' ((p', A', n) :: lb_remove p LB) m' mo' ->
     rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' ->
     (exists junk, rw_cells rsegs m' A' [CB (Z.to_nat (Z.min n sz)) (firstn (Z.to_nat (Z.min n sz)) old);
                                      CB (Z.to_nat (n - Z.min n sz)) junk]) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_REALLOC_W) fc None m (seg_rom rsegs)) mo) K.

Definition ywrap_realloc_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (n lo B : Z) (errv : word) (K : TSet),
  K [] ->
  HK s LB m mo ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RY_WRAP_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = wz RATP ->
  a1 = wz 0 -> a2 = wz n -> 0 <= n <= NUSERc -> Z.of_nat (length LB) < NHELDc ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (errv' : word) (p : bptr) (A : Z),
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) -> rw_cells rsegs m' (errno_addr tp) [C4 errv'] ->
     rauxv_ok m' B -> rheap_pres LB (bv_unsigned sp) m m' ->
     a0' = wz A -> rblock_range A n -> HK s' ((p, A, n) :: LB) m' mo' ->
     (exists junk, rw_cells rsegs m' A [CB (Z.to_nat n) junk]) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_REALLOC_W) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ycb_null_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)  (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition ycb_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv rsegs m ->
  evt rsegs (ycb_null_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc  m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_NULL) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_boolean_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)  (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition ycb_boolean_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv rsegs m ->
  evt rsegs (ycb_boolean_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc  m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_BOOLEAN) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_string_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)  (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition ycb_string_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv rsegs m ->
  evt rsegs (ycb_string_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc  m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_STRING) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_number_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (l : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition ycb_number_stmt : Prop :=
  forall (l : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv rsegs m ->
  a2 = wz l ->
  0 < l < 2^32 ->
  evt rsegs (ycb_number_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc l m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_NUMBER) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_start_map_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(CX + 4, CX + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx + 1)).
Definition ycb_start_map_stmt : Prop :=
  forall (CX : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ctx_rep m CX cx ->
  cx_objectLevel cx + 1 < 2^31 ->
  mem_inv rsegs m ->
  a0 = wz CX ->
  evt rsegs (ycb_start_map_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_START_MAP) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_map_key_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ m' = m.
Definition ycb_map_key_stmt : Prop :=
  forall (CX : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ctx_rep m CX cx ->
  0 < cx_objectLevel cx ->
  mem_inv rsegs m ->
  a0 = wz CX ->
  evt rsegs (ycb_map_key_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_MAP_KEY) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_end_map_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(CX + 4, CX + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx) (cx_objectLevel cx - 1)).
Definition ycb_end_map_stmt : Prop :=
  forall (CX : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ctx_rep m CX cx ->
  0 < cx_objectLevel cx ->
  mem_inv rsegs m ->
  a0 = wz CX ->
  evt rsegs (ycb_end_map_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_END_MAP) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_start_array_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(CX, CX + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx + 1) (cx_objectLevel cx)).
Definition ycb_start_array_stmt : Prop :=
  forall (CX : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ctx_rep m CX cx ->
  cx_arrayLevel cx + 1 < 2^31 ->
  mem_inv rsegs m ->
  a0 = wz CX ->
  evt rsegs (ycb_start_array_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_START_ARRAY) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ycb_end_array_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CX : Z) (cx : yctx) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(CX, CX + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz 1 /\ ctx_rep m' CX (mkCtx (cx_arrayLevel cx - 1) (cx_objectLevel cx)).
Definition ycb_end_array_stmt : Prop :=
  forall (CX : Z) (cx : yctx), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ctx_rep m CX cx ->
  0 < cx_arrayLevel cx ->
  mem_inv rsegs m ->
  a0 = wz CX ->
  evt rsegs (ycb_end_array_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc CX cx m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_CB_END_ARRAY) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition buf_cleared (b : ybuf) : ybuf := mkBuf BS_ok (yb_len b) 0 (yb_data b) [].
(* [comment removed for export] *)
Lemma ybuf_clear_leaf : forall b, yb_state b = BS_ok -> yleaf (ybuf_clear b) (buf_cleared b).
Proof. intros b Hs. unfold ybuf_clear. rewrite Hs. apply yl_ret. Qed.
Lemma ybuf_clear_leaf_inv : forall b b', yb_state b = BS_ok -> yleaf (ybuf_clear b) b' -> b' = buf_cleared b.
Proof. intros b b' Hs HL. unfold ybuf_clear in HL. rewrite Hs in HL. exact (yleaf_ret_inv _ _ HL). Qed.

(* [comment removed for export] *)
Definition lex_reset (lx : ylexer) : ylexer :=
  mkLexer 0 0 LE_ok (buf_cleared (lx_buf lx)) (lx_bufblk lx) 0 0 (lx_allowComments lx) (lx_validateUTF8 lx).
Lemma ylex_realloc_leaf : forall lx, yb_state (lx_buf lx) = BS_ok -> yleaf (ylex_realloc lx) (lex_reset lx).
Proof.
  intros lx Hs. unfold ylex_realloc. eapply yleaf_bind; [apply ybuf_clear_leaf; exact Hs|]. apply yl_ret.
Qed.
Lemma ylex_realloc_leaf_inv : forall lx lx', yb_state (lx_buf lx) = BS_ok -> yleaf (ylex_realloc lx) lx' -> lx' = lex_reset lx.
Proof.
  intros lx lx' Hs HL. unfold ylex_realloc in HL. apply yleaf_bind_inv in HL. destruct HL as (b & Hb & HR).
  apply (ybuf_clear_leaf_inv _ _ Hs) in Hb. subst b. exact (yleaf_ret_inv _ _ HR).
Qed.
Lemma lex_inv_reset : forall lx, lex_inv lx -> lex_inv (lex_reset lx).
Proof.
  intros lx (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold lex_inv, lex_reset, buf_cleared. cbn.
  rewrite H5, H6, H7. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition ybuf_err_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B st : Z) (rest : list cell) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ a0' = wz st /\ m' = m.
Definition ybuf_err_stmt : Prop :=
  forall (B st : Z) (rest : list cell), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m B (C4 (wz st) :: rest) ->
  0 <= st < 2^31 ->
  B <> 0 ->
  mem_inv rsegs m ->
  a0 = wz B ->
  evt rsegs (ybuf_err_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B st rest m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_ERR) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ybuf_len_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B D AF lo : Z) (b : ybuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ a0' = wz (yb_used b) /\ buf_struct m' B b D AF.
Definition ybuf_len_stmt : Prop :=
  forall (B D AF lo : Z) (b : ybuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  buf_struct m B b D AF ->
  yb_state b = BS_ok ->
  B <> 0 ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - RY_BUF_SMALL_STACK ->
  B + SIZEOF_BUF <= lo ->
  mem_inv rsegs m ->
  a0 = wz B ->
  evt rsegs (ybuf_len_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B D AF lo b m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_LEN) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ybuf_data_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B D AF lo : Z) (b : ybuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ a0' = wz D /\ buf_struct m' B b D AF.
Definition ybuf_data_stmt : Prop :=
  forall (B D AF lo : Z) (b : ybuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  buf_struct m B b D AF ->
  yb_state b = BS_ok ->
  B <> 0 ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - RY_BUF_SMALL_STACK ->
  B + SIZEOF_BUF <= lo ->
  mem_inv rsegs m ->
  a0 = wz B ->
  evt rsegs (ybuf_data_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B D AF lo b m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_DATA) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition ybuf_clear_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B D AF lo : Z) (b : ybuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch ([(lo, bv_unsigned sp); (B + 8, B + 12)] ++ match yb_data b with Some _ => [(D, D + 1)] | None => [] end) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ buf_struct m' B (buf_cleared b) D AF /\ buf_data m' D (buf_cleared b).
Definition ybuf_clear_stmt : Prop :=
  forall (B D AF lo : Z) (b : ybuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  buf_struct m B b D AF ->
  buf_data m D b ->
  yb_state b = BS_ok ->
  buf_inv b ->
  B <> 0 ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - RY_BUF_SMALL_STACK ->
  B + SIZEOF_BUF <= lo ->
  (yb_data b <> None -> D + yb_len b <= lo /\ (B + SIZEOF_BUF <= D \/ D + yb_len b <= B)) ->
  mem_inv rsegs m ->
  a0 = wz B ->
  evt rsegs (ybuf_clear_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B D AF lo b m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_CLEAR) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ybs_set_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (h : yhandle) (mh : mhand) (s s' : ystate) (rest : list ystate) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(lo, bv_unsigned sp); (mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ hand_struct m' h mh /\ bs_rep m' (mh_stack mh) (h_set_stack h (s' :: rest)).
Definition ybs_set_stmt : Prop :=
  forall (h : yhandle) (mh : mhand) (s s' : ystate) (rest : list ystate) (lo : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  hand_struct m h mh ->
  bs_rep m (mh_stack mh) h ->
  h_stack h = s :: rest ->
  h_stack_blk h <> None ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - 16 ->
  mh_addr mh + SIZEOF_HANDLE <= lo ->
  mh_stack mh + h_stack_size h <= lo ->
  (mh_addr mh + SIZEOF_HANDLE <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mh_addr mh) ->
  mem_inv rsegs m ->
  a0 = wz (mh_addr mh + 48) ->
  a1 = wz (state_code s') ->
  evt rsegs (ybs_set_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h mh s s' rest lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BS_SET) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yhexToDigit_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (VP S v lo : Z) (h0 h1 h2 h3 : Z) (v' : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(lo, bv_unsigned sp); (VP, VP + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' VP [C4 (wz v')] /\ bytes_at rsegs m' S (zbytes [h0; h1; h2; h3]).
Definition yhexToDigit_stmt : Prop :=
  forall (VP S v lo : Z) (h0 h1 h2 h3 : Z) (v' : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m VP [C4 (wz v)] ->
  0 <= v < 2^16 ->
  bytes_at rsegs m S (zbytes [h0; h1; h2; h3]) ->
  is_vhc h0 = true ->
  is_vhc h1 = true ->
  is_vhc h2 = true ->
  is_vhc h3 = true ->
  hex_loop v [h0; h1; h2; h3] = Some v' ->
  (S + 4 <= VP \/ VP + 4 <= S) ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - 16 ->
  bv_unsigned sp <= VP ->
  (S + 4 <= lo \/ bv_unsigned sp <= S) ->
  mem_inv rsegs m ->
  a0 = wz VP ->
  a1 = wz S ->
  evt rsegs (yhexToDigit_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc VP S v lo h0 h1 h2 h3 v' m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_HEXTODIGIT) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yset_default_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (YAF : Z) (junk : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(YAF, YAF + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' YAF yalloc_cells.
Definition yset_default_stmt : Prop :=
  forall (YAF : Z) (junk : list byte), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m YAF [CB 32 junk] ->
  mem_inv rsegs m ->
  a0 = wz YAF ->
  evt rsegs (yset_default_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc YAF junk m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_SET_DEFAULT) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ylex_realloc_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (L AF lo : Z) (lx : ylexer) (mbl : mbuf) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(lo, bv_unsigned sp); (L, L + 48); (mb_addr mbl, mb_addr mbl + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ a0' = wz L /\ lexer_rep m' L (lex_reset lx) mbl AF.
Definition ylex_realloc_stmt : Prop :=
  forall (L AF lo : Z) (lx : ylexer) (mbl : mbuf), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  lexer_rep m L lx mbl AF ->
  yb_state (lx_buf lx) = BS_ok ->
  buf_inv (lx_buf lx) ->
  yb_data (lx_buf lx) = None ->
  L <> 0 ->
  mb_addr mbl <> 0 ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - RY_LEX_REALLOC_STACK ->
  L + SIZEOF_LEXER <= lo ->
  mb_addr mbl + SIZEOF_BUF <= lo ->
  (L + SIZEOF_LEXER <= mb_addr mbl \/ mb_addr mbl + SIZEOF_BUF <= L) ->
  mem_inv rsegs m ->
  a0 = wz L ->
  evt rsegs (ylex_realloc_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L AF lo lx mbl m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_LEX_REALLOC) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition yreset_parser_rpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (h : yhandle) (mh : mhand) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))
    /\ munch [(lo, bv_unsigned sp); (mh_addr mh + 16, mh_addr mh + 24); (mh_lexer mh, mh_lexer mh + 48); (mb_addr (mh_lexbuf mh), mb_addr (mh_lexbuf mh) + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp) /\ hand_struct m' h mh /\ lexer_rep m' (mh_lexer mh) (lex_reset (h_lexer h)) (mh_lexbuf mh) (mh_addr mh + 72).
Definition yreset_parser_stmt : Prop :=
  forall (h : yhandle) (mh : mhand) (lo : Z), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  hand_struct m h mh ->
  lexer_rep m (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) ->
  yb_state (lx_buf (h_lexer h)) = BS_ok ->
  buf_inv (lx_buf (h_lexer h)) ->
  yb_data (lx_buf (h_lexer h)) = None ->
  mh_addr mh <> 0 ->
  mh_lexer mh <> 0 ->
  mb_addr (mh_lexbuf mh) <> 0 ->
  stk rsegs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - RY_RESET_STACK ->
  mh_addr mh + SIZEOF_HANDLE <= lo ->
  mh_lexer mh + SIZEOF_LEXER <= lo ->
  mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= lo ->
  (mh_addr mh + SIZEOF_HANDLE <= mh_lexer mh \/ mh_lexer mh + SIZEOF_LEXER <= mh_addr mh) ->
  (mh_addr mh + SIZEOF_HANDLE <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= mh_addr mh) ->
  (mh_lexer mh + SIZEOF_LEXER <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + SIZEOF_BUF <= mh_lexer mh) ->
  mem_inv rsegs m ->
  a0 = wz (mh_addr mh) ->
  evt rsegs (yreset_parser_rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h mh lo m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_RESET) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ybuf_alloc_rpost (sp tp : word) (m : mem) (REST : list block) (AF lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (p : bptr) (B0 : Z) : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' AF yalloc_cells
  /\ a0' = wz B0 /\ B0 <> 0 /\ buf_struct m' B0 ybuf_zero 0 AF
  /\ RYST s' ((p, B0, SIZEOF_BUF) :: REST) m' mo'.
Definition ybuf_alloc_stmt : Prop :=
  forall (REST : list block) (AF lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s REST m mo ->
  rw_cells rsegs m AF yalloc_cells ->
  yaf_in REST AF ->
  yroom REST 1 ->
  yframe_pre m sp tp lo B RY_BUF_ALLOC_STACK errv ->
  a0 = wz AF ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (p : bptr) (B0 : Z),
     ybuf_alloc_rpost sp tp m REST AF lo B errv a0' m' mo' s' p B0 ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_ALLOC) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ybuf_free_rpost (sp tp : word) (m : mem) (REST : list block) (mb : mbuf) (b : ybuf) (AF lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState)  : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' AF yalloc_cells /\ RYST s' REST m' mo' .
Definition ybuf_free_stmt : Prop :=
  forall (REST : list block) (mb : mbuf) (b : ybuf) (AF lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (buf_blocks mb b ++ REST) m mo ->
  buf_rep m mb b AF ->
  rw_cells rsegs m AF yalloc_cells ->
  yaf_in REST AF ->
  yframe_pre m sp tp lo B RY_BUF_FREE_STACK errv ->
  a0 = wz (mb_addr mb) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) ,
     ybuf_free_rpost sp tp m REST mb b AF lo B errv a0' m' mo' s'  ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_FREE) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ybuf_append_rpost (sp tp : word) (m : mem) (REST : list block) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (b' : ybuf) (mb' : mbuf) (LK : list block) : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' AF yalloc_cells
  /\ yleaf (ybuf_append b src) b' /\ buf_rep m' mb' b' AF /\ mb_same mb mb'
  /\ LK = [] /\ RYST s' (buf_blocks mb' b' ++ LK ++ REST) m' mo' .
Definition ybuf_append_stmt : Prop :=
  forall (REST : list block) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (buf_blocks mb b ++ REST) m mo ->
  buf_rep m mb b AF ->
  buf_inv b ->
  rw_cells rsegs m AF yalloc_cells ->
  yaf_in REST AF ->
  bytes_at rsegs m S (zbytes src) ->
  Forall (fun c => 0 <= c < 256) src ->
  (0 < zlength src -> S <> 0) ->
  S + zlength src <= 2^64 ->
  yb_used b + zlength src < 2^26 ->
  ysrc_range REST sp S (zlength src) ->
  yroom REST 3 ->
  yframe_pre m sp tp lo B RY_BUF_APPEND_STACK errv ->
  a0 = wz (mb_addr mb) ->
  a1 = wz S ->
  a2 = wz (zlength src) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (b' : ybuf) (mb' : mbuf) (LK : list block),
     ybuf_append_rpost sp tp m REST mb b AF S src lo B errv a0' m' mo' s' b' mb' LK ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_BUF_APPEND) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ylex_alloc_rpost (sp tp : word) (m : mem) (REST : list block) (AF aC v8 lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (L : Z) (lid : bptr) (mbl : mbuf) (lx : ylexer) : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' AF yalloc_cells
  /\ a0' = wz L /\ L <> 0 /\ (exists blk, yleaf (ylex_alloc aC v8) (Some (blk, lx)))
  /\ lexer_rep m' L lx mbl AF /\ mb_data mbl = 0
  /\ RYST s' (lexer_blocks lid L mbl lx ++ REST) m' mo'.
Definition ylex_alloc_stmt : Prop :=
  forall (REST : list block) (AF aC v8 lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s REST m mo ->
  rw_cells rsegs m AF yalloc_cells ->
  yaf_in REST AF ->
  0 <= aC <= 1 ->
  0 <= v8 <= 1 ->
  yroom REST 2 ->
  yframe_pre m sp tp lo B RY_LEX_ALLOC_STACK errv ->
  a0 = wz AF ->
  a1 = wz aC ->
  a2 = wz v8 ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (L : Z) (lid : bptr) (mbl : mbuf) (lx : ylexer),
     ylex_alloc_rpost sp tp m REST AF aC v8 lo B errv a0' m' mo' s' L lid mbl lx ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_LEX_ALLOC) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ylex_free_rpost (sp tp : word) (m : mem) (REST : list block) (lid : bptr) (L AF : Z) (mbl : mbuf) (lx : ylexer) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState)  : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' AF yalloc_cells /\ RYST s' REST m' mo' .
Definition ylex_free_stmt : Prop :=
  forall (REST : list block) (lid : bptr) (L AF : Z) (mbl : mbuf) (lx : ylexer) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (lexer_blocks lid L mbl lx ++ REST) m mo ->
  lexer_rep m L lx mbl AF ->
  rw_cells rsegs m AF yalloc_cells ->
  yaf_in REST AF ->
  yframe_pre m sp tp lo B RY_LEX_FREE_STACK errv ->
  a0 = wz L ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) ,
     ylex_free_rpost sp tp m REST lid L AF mbl lx lo B errv a0' m' mo' s'  ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_LEX_FREE) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)
Definition outref_addr (T D : Z) (ob : outref) : Z :=
  match ob with OB_null => 0 | OB_text i => T + i | OB_lexbuf i => D + i end.


(* [comment removed for export] *)
Definition ylex_lex_rpost (sp tp : word) (m : mem) (REST : list block) (h : yhandle) (mh : mhand) (T : Z) (txt : list Z) (off OBP OLP : Z) (obw olw : word) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (lx' : ylexer) (tok : ytok) (off' : Z) (ob : outref) (n : Z) (mbl' : mbuf) (LK : list block) : Prop :=
  yframe_post m m' sp tp lo B REST [(OLP, OLP + 4); (OBP, OBP + 8)]
  /\ yleaf (ylex_lex (h_lexer h) txt (zlength txt) off) (lx', tok, off', ob, n)
  /\ a0' = wz (tok_code tok)
  /\ hand_struct m' (h_set_lex_off h lx' off') mh
  /\ lexer_rep m' (mh_lexer mh) lx' mbl' (mh_addr mh + 72) /\ mb_same (mh_lexbuf mh) mbl'
  /\ rw_cells rsegs m' OBP [C8 (wz (outref_addr T (mb_data mbl') ob))] /\ rw_cells rsegs m' OLP [C4 (wz n)]
  /\ text_at m' T txt
  /\ LK = [] /\ RYST s' ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: lexer_blocks (mh_lid mh) (mh_lexer mh) mbl' lx' ++ LK ++ REST) m' mo' .
Definition ylex_lex_stmt : Prop :=
  forall (REST : list block) (h : yhandle) (mh : mhand) (T : Z) (txt : list Z) (off OBP OLP : Z) (obw olw : word) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h) ++ REST) m mo ->
  hand_struct m h mh ->
  lexer_rep m (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) ->
  lex_inv (h_lexer h) ->
  h_bytesConsumed h = off ->
  0 <= off <= zlength txt ->
  zlength txt < 2^26 ->
  text_at m T txt ->
  (exists bt, In bt REST /\ blk_addr bt <= T /\ T + zlength txt <= blk_addr bt + blk_size bt) \/ zlength txt = 0 ->
  rw_cells rsegs m OBP [C8 obw] ->
  rw_cells rsegs m OLP [C4 olw] ->
  bv_unsigned sp <= OLP ->
  OLP + 4 <= OBP ->
  OBP + 8 <= B ->
  yroom REST 5 ->
  yframe_pre m sp tp lo B RY_LEX_LEX_STACK errv ->
  a0 = wz (mh_lexer mh) ->
  a1 = wz T ->
  a2 = wz (zlength txt) ->
  a3 = wz (mh_addr mh + 32) ->
  a4 = wz OBP ->
  a5 = wz OLP ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (lx' : ylexer) (tok : ytok) (off' : Z) (ob : outref) (n : Z) (mbl' : mbuf) (LK : list block),
     ylex_lex_rpost sp tp m REST h mh T txt off OBP OLP obw olw lo B errv a0' m' mo' s' lx' tok off' ob n mbl' LK ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_LEX_LEX) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ystring_decode_rpost (sp tp : word) (m : mem) (REST : list block) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (db' : ybuf) (mbd' : mbuf) (LK : list block) : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' AF yalloc_cells
  /\ yleaf (ystring_decode db str n) db' /\ buf_rep m' mbd' db' AF /\ mb_same mbd mbd'
  /\ bytes_at rsegs m' S (zbytes str)
  /\ LK = [] /\ RYST s' (buf_blocks mbd' db' ++ LK ++ REST) m' mo' .
Definition ystring_decode_stmt : Prop :=
  forall (REST : list block) (mbd : mbuf) (db : ybuf) (AF S : Z) (str : list Z) (n lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (buf_blocks mbd db ++ REST) m mo ->
  buf_rep m mbd db AF ->
  buf_inv db ->
  yb_used db = 0 ->
  rw_cells rsegs m AF yalloc_cells ->
  yaf_in REST AF ->
  bytes_at rsegs m S (zbytes str) ->
  Forall (fun c => 0 <= c < 256) str ->
  n = zlength str ->
  n < 2^26 ->
  S <> 0 ->
  S + n < 2^62 ->
  sbody_ix str 0 n ->
  (exists bt, In bt REST /\ blk_addr bt <= S /\ S + n <= blk_addr bt + blk_size bt) \/ n = 0 ->
  yroom REST 3 ->
  yframe_pre m sp tp lo B RY_DECODE_STACK errv ->
  a0 = wz (mb_addr mbd) ->
  a1 = wz S ->
  a2 = wz n ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (db' : ybuf) (mbd' : mbuf) (LK : list block),
     ystring_decode_rpost sp tp m REST mbd db AF S str n lo B errv a0' m' mo' s' db' mbd' LK ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_STRING_DECODE) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ydo_parse_rpost (sp tp : word) (m : mem) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block) : Prop :=
  yframe_post m m' sp tp lo B REST [(mh_ctx mh, mh_ctx mh + 8)]
  /\ yleaf (ydo_parse jf_callbacks txt (zlength txt) h cx) (st, h', cx')
  /\ a0' = wz (status_code st)
  /\ hand_rep m' h' mh' /\ mh_same mh mh' /\ ctx_rep m' (mh_ctx mh) cx' /\ text_at m' T txt
  /\ LK = [] /\ RYST s' (yblocks mh' h' ++ LK ++ REST) m' mo' .
Definition ydo_parse_stmt : Prop :=
  forall (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (yblocks mh h ++ REST) m mo ->
  hand_rep m h mh ->
  ctx_rep m (mh_ctx mh) cx ->
  text_at m T txt ->
  zlength txt < 2^26 ->
  (exists bt, In bt REST /\ blk_addr bt <= T /\ T + zlength txt <= blk_addr bt + blk_size bt) \/ zlength txt = 0 ->
  hinv (zlength txt) (h_set_off h 0) cx ->
  bv_unsigned sp <= mh_ctx mh ->
  mh_ctx mh + 8 <= B ->
  yroom REST 8 ->
  yframe_pre m sp tp lo B RY_DO_PARSE_STACK errv ->
  a0 = wz (mh_addr mh) ->
  a1 = wz T ->
  a2 = wz (zlength txt) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (F' : bvmap 5 word) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block),
     ydo_parse_rpost sp tp m REST h mh cx T txt lo B errv a0' m' mo' s' st h' cx' mh' LK ->
     fregs_same F F' ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_DO_PARSE) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)
Definition yparse_rpost (sp tp : word) (m : mem) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block) : Prop :=
  yframe_post m m' sp tp lo B REST [(mh_ctx mh, mh_ctx mh + 8)]
  /\ yleaf (ydo_parse jf_callbacks txt (zlength txt) h cx) (st, h', cx')
  /\ a0' = wz (status_code st)
  /\ hand_rep m' h' mh' /\ mh_same mh mh' /\ ctx_rep m' (mh_ctx mh) cx' /\ text_at m' T txt
  /\ LK = [] /\ RYST s' (yblocks mh' h' ++ LK ++ REST) m' mo' .
Definition yparse_stmt : Prop :=
  forall (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (yblocks mh h ++ REST) m mo ->
  hand_rep m h mh ->
  ctx_rep m (mh_ctx mh) cx ->
  text_at m T txt ->
  zlength txt < 2^26 ->
  (exists bt, In bt REST /\ blk_addr bt <= T /\ T + zlength txt <= blk_addr bt + blk_size bt) \/ zlength txt = 0 ->
  hinv (zlength txt) (h_set_off h 0) cx ->
  bv_unsigned sp <= mh_ctx mh ->
  mh_ctx mh + 8 <= B ->
  yroom REST 8 ->
  yframe_pre m sp tp lo B RY_DO_PARSE_STACK errv ->
  a0 = wz (mh_addr mh) ->
  a1 = wz T ->
  a2 = wz (zlength txt) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (F' : bvmap 5 word) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block),
     yparse_rpost sp tp m REST h mh cx T txt lo B errv a0' m' mo' s' st h' cx' mh' LK ->
     fregs_same F F' ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_PARSE) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)
Definition yparse_head_state (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (H T len used : Z)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 (wz H) (wz (H + 48)) (wz used) a1 a2 a3 a4 a5 a6 a7
          (wz len) (wz T) (wz (H + 32)) s5v s6v (wz 11) s8v (wz RY_JT_TOKVAL) (wz 13) (wz RY_JT_STATE) t3 t4 t5 t6)
     F (wz RY_PARSE_HEAD) fc None m (seg_rom rsegs).

Definition yparse_frame (m : mem) (sp : word) (ra0 s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 padw obw olw : word) : Prop :=
  rw_cells rsegs m (bv_unsigned sp)
    [C8 (wz (2^63 + 1)); C8 (wz 0x108e6); C4 padw; C4 olw; C8 obw; C8 fs0;
     C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra0].

(* [comment removed for export] *)
Definition yparse_head_inv (ra sp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 : word)
    (m : mem) (mo : Model) (s : PState) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx)
    (T : Z) (txt : list Z) (lo B : Z) : Prop :=
  RYST s (yblocks mh h ++ REST) m mo
  /\ hand_rep m h mh /\ ctx_rep m (mh_ctx mh) cx /\ text_at m T txt /\ zlength txt < 2^26
  /\ ((exists bt, In bt REST /\ blk_addr bt <= T /\ T + zlength txt <= blk_addr bt + blk_size bt) \/ zlength txt = 0)
  /\ loop_pre (zlength txt) h cx /\ 0 < h_used h /\ yroom REST 8
  /\ (exists padw obw olw, yparse_frame m sp ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 padw obw olw)
  /\ rauxv_ok m B /\ bv_unsigned sp + 144 <= mh_ctx mh /\ mh_ctx mh + 8 <= B
  /\ stk rsegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp + 144 - RY_DO_PARSE_STACK
  /\ (exists errv : word, rw_cells rsegs m (errno_addr tp) [C4 errv]) /\ mem_inv rsegs m /\ tp = wz RATP.

(* [comment removed for export] *)
Definition yparse_exit_cont (K : TSet) (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (REST : list block) (mh : mhand) (T : Z) (txt : list Z) (lo B : Z)
    (R : ystatus * yhandle * yctx -> Prop) : Prop :=
  forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (F' : bvmap 5 word)
         (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block),
    yframe_post m m' (wz (bv_unsigned sp + 144)) tp lo B REST [(mh_ctx mh, mh_ctx mh + 8)] ->
    R (st, h', cx') -> a0' = wz (status_code st) ->
    hand_rep m' h' mh' -> mh_same mh mh' -> ctx_rep m' (mh_ctx mh) cx' -> text_at m' T txt ->
    LK = [] -> RYST s' (yblocks mh' h' ++ LK ++ REST) m' mo' ->
    fregs_same F F' ->
    realizes_cfg acfg rsegs (mkCfg (MS (mkR ra (wz (bv_unsigned sp + 144)) gp tp t0' t1' t2' s0e s1e a0' a1' a2' a3' a4' a5' a6' a7'
                                   s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3' t4' t5' t6')
                           F' (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K.

Definition yparse_loop_stmt : Prop :=
  forall (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word)
         (mo : Model) (s : PState) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z)
         (fuel : nat) (lo B : Z) (K : TSet),
  K [] ->
  yparse_head_inv ra sp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 m mo s REST h mh cx T txt lo B ->
  (passes_left (zlength txt) h <= Z.of_nat fuel)%Z ->
  yparse_exit_cont K ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m REST mh T txt lo B
     (yleaf (yparse_loop jf_callbacks txt (zlength txt) fuel h cx)) ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m
                           (mh_addr mh) T (zlength txt) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) K.

(* [comment removed for export] *)
Definition yparse_pass_stmt : Prop :=
  forall (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word)
         (mo : Model) (s : PState) (REST : list block) (h : yhandle) (mh : mhand) (cx : yctx) (T : Z) (txt : list Z)
         (lo B : Z) (K : TSet),
  K [] ->
  yparse_head_inv ra sp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 m mo s REST h mh cx T txt lo B ->
  yparse_exit_cont K ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m REST mh T txt lo B
     (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks txt (zlength txt) h cx) (SR_done st h' cx')) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s5v' s6v' s8v' : word) (m' : mem) (mo' : Model) (s' : PState)
          (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list block),
     yleaf (yparse_step jf_callbacks txt (zlength txt) h cx) (SR_again h' cx') ->
     mh_same mh mh' -> ry_pres REST (bv_unsigned sp + 144) [(mh_ctx mh, mh_ctx mh + 8)] m m' -> LK = [] ->
     yparse_head_inv ra sp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 m' mo' s' (LK ++ REST) h' mh' cx' T txt lo B ->
     realizes_cfg acfg rsegs (mkCfg (yparse_head_state ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m'
                              (mh_addr mh) T (zlength txt) (h_used h') t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s5v' s6v' s8v') mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state ra sp gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m
                           (mh_addr mh) T (zlength txt) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yalloc_rpost (sp tp : word) (m : mem) (REST : list block) (CFGP CX lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (h : yhandle) (mh : mhand) : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ rw_cells rsegs m' CFGP [C4 (wz 1); C4 (wz 1)]
  /\ a0' = wz (mh_addr mh) /\ mh_addr mh <> 0 /\ mh_ctx mh = CX
  /\ yleaf (yajl_alloc 1 1) (Some h) /\ hand_rep m' h mh
  /\ RYST s' (yblocks mh h ++ REST) m' mo'.
Definition yalloc_stmt : Prop :=
  forall (REST : list block) (CFGP CX lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s REST m mo ->
  rw_cells rsegs m CFGP [C4 (wz 1); C4 (wz 1)] ->
  bv_unsigned sp <= CFGP ->
  CFGP + 8 <= B ->
  yroom REST 5 ->
  yframe_pre m sp tp lo B RY_ALLOC_STACK errv ->
  a0 = wz RY_CALLBACKS ->
  a1 = wz CFGP ->
  a2 = wz 0 ->
  a3 = wz CX ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (h : yhandle) (mh : mhand),
     yalloc_rpost sp tp m REST CFGP CX lo B errv a0' m' mo' s' h mh ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_ALLOC) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yfree_rpost (sp tp : word) (m : mem) (REST : list block) (h : yhandle) (mh : mhand) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState)  : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ RYST s' REST m' mo' .
Definition yfree_stmt : Prop :=
  forall (REST : list block) (h : yhandle) (mh : mhand) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s (yblocks mh h ++ REST) m mo ->
  hand_rep m h mh ->
  yframe_pre m sp tp lo B RY_FREE_STACK errv ->
  a0 = wz (mh_addr mh) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) ,
     yfree_rpost sp tp m REST h mh lo B errv a0' m' mo' s'  ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_FREE) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition yfuzz_rpost (sp tp : word) (m : mem) (REST : list block) (T : Z) (txt : list Z) (lo B : Z) (errv : word)
    (a0' : word) (m' : mem) (mo' : Model) (s' : PState) (LK : list block) : Prop :=
  yframe_post m m' sp tp lo B REST [] /\ a0' = wz 0 /\ text_at m' T txt
  /\ yleaf (yLLVMFuzzerTestOneInput txt (zlength txt)) 0
  /\ LK = [] /\ RYST s' (LK ++ REST) m' mo' .
Definition yfuzz_stmt : Prop :=
  forall (REST : list block) (T : Z) (txt : list Z) (lo B : Z) (errv : word) (K : TSet), forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState),
  K [] ->
  RYST s REST m mo ->
  text_at m T txt ->
  zlength txt < 2^26 ->
  (exists bt, In bt REST /\ blk_addr bt <= T /\ T + zlength txt <= blk_addr bt + blk_size bt) \/ zlength txt = 0 ->
  yroom REST 8 ->
  yframe_pre m sp tp lo B RY_FUZZ_STACK errv ->
  a0 = wz T ->
  a1 = wz (zlength txt) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState) (F' : bvmap 5 word) (LK : list block),
     yfuzz_rpost sp tp m REST T txt lo B errv a0' m' mo' s' LK ->
     fregs_same F F' ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz RY_FUZZ) fc None m (seg_rom rsegs)) mo) K.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ybv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.
Lemma ysx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, ybv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma yzx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rheap_pres_agree : forall LB SP m m',
  rheap_pres LB SP m m' -> agree_on rsegs (rclient_addr LB SP) m m'.
Proof. intros LB SP m m' H a Ha Hc. exact (H a Ha Hc). Qed.
Lemma agree_rheap_pres : forall LB SP m m',
  agree_on rsegs (rclient_addr LB SP) m m' -> rheap_pres LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc. exact (H a Ha Hc). Qed.
Lemma ry_pres_agree : forall LB SP X m m',
  ry_pres LB SP X m m' -> agree_on rsegs (fun a => rclient_addr LB SP a /\ ~ yin_ivs X a) m m'.
Proof. intros LB SP X m m' H a Ha [Hc Hx]. exact (H a Ha Hc Hx). Qed.
Lemma agree_ry_pres : forall LB SP X m m',
  agree_on rsegs (fun a => rclient_addr LB SP a /\ ~ yin_ivs X a) m m' -> ry_pres LB SP X m m'.
Proof. intros LB SP X m m' H a Ha Hc Hx. exact (H a Ha (conj Hc Hx)). Qed.

(* [comment removed for export] *)
Lemma ryajl_pres_of_munch : forall LB SP X W m m',
  munch W m m' -> wmono rsegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ yin_ivs X a -> outside W a) ->
  ry_pres LB SP X m m'.
Proof.
  intros LB SP X W m m' MU WM HO a Ha Hc Hx. split.
  - apply MU. rewrite wa_unsigned by exact Ha. apply HO; assumption.
  - apply WM.
Qed.

(* [comment removed for export] *)
Lemma outside_frame : forall LB SP lo hi a,
  hi <= SP -> alloc_ceiling <= lo -> rclient_addr LB SP a ->
  (forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) ->
  outside [(lo, hi)] a.
Proof.
  intros LB SP lo hi a Hhi Hlo Hc HB. cbn. split; [|exact I].
  destruct Hc as [H|[H|(b & Hb & Hr)]].
  - lia.
  - unfold alloc_ceiling in *. lia.
  - destruct (HB b Hb) as (_ & _ & _ & B4 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma ry_errno_lit : forall tp : word, tp = wz RATP -> bv_unsigned tp + (-164) = RERRNO.
Proof. intros tp ->. unfold wz, RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ybytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.
Lemma yZ_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (ybytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.
Lemma yle4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (ybytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply yZ_to_le_bytes_to_Z.
Qed.
Lemma yle8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (ybytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply yZ_to_le_bytes_to_Z.
Qed.
Lemma ycb8_c8_in : forall m A pre post bs,
  rw_cells rsegs m A (pre ++ CB 8 bs :: post) -> rw_cells rsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite yle8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Lemma ycb4_c4_in : forall m A pre post bs,
  rw_cells rsegs m A (pre ++ CB 4 bs :: post) -> rw_cells rsegs m A (pre ++ C4 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite yle4_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
(* [comment removed for export] *)
Definition bsep (b1 b2 : block) : Prop :=
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Fixpoint sep_from (b : block) (l : list block) : Prop :=
  match l with [] => True | b' :: l' => bsep b b' /\ sep_from b l' end.
Fixpoint all_sep (l : list block) : Prop :=
  match l with [] => True | b :: l' => sep_from b l' /\ all_sep l' end.
Fixpoint all_range (l : list block) : Prop :=
  match l with [] => True | b :: l' => rblock_range (blk_addr b) (blk_size b) /\ all_range l' end.

Lemma sep_from_In : forall b l b', sep_from b l -> In b' l -> bsep b b'.
Proof. intros b l b'. induction l as [|x l IH]; cbn; [tauto|]. intros [H1 H2] [->|Hin]; auto. Qed.
Lemma sep_from_intro : forall b l, (forall b', In b' l -> bsep b b') -> sep_from b l.
Proof. intros b l. induction l as [|x l IH]; cbn; intros H; [exact I|]. split; [apply H; auto| apply IH; auto]. Qed.
Lemma all_range_In : forall l b, all_range l -> In b l -> rblock_range (blk_addr b) (blk_size b).
Proof. intros l b. induction l as [|x l IH]; cbn; [tauto|]. intros [H1 H2] [->|Hin]; auto. Qed.
Lemma all_range_intro : forall l, (forall b, In b l -> rblock_range (blk_addr b) (blk_size b)) -> all_range l.
Proof. intros l. induction l as [|x l IH]; cbn; intros H; [exact I|]. split; [apply H; auto| apply IH; auto]. Qed.
Lemma all_sep_app_r : forall l1 l2, all_sep (l1 ++ l2) -> all_sep l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; cbn; tauto. Qed.
Lemma all_range_app_r : forall l1 l2, all_range (l1 ++ l2) -> all_range l2.
Proof. intros l1 l2. induction l1 as [|x l1 IH]; cbn; tauto. Qed.
Lemma sep_from_app : forall b l1 l2, sep_from b (l1 ++ l2) <-> sep_from b l1 /\ sep_from b l2.
Proof. intros b l1 l2. induction l1 as [|x l1 IH]; cbn; tauto. Qed.

Lemma blocks_all_sep : forall LB,
  (forall b1 b2, In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
      blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1) ->
  List.NoDup (map blk_id LB) -> all_sep LB.
Proof.
  intros LB HP HN.
  assert (G : forall l, (forall b, In b l -> In b LB) -> List.NoDup (map blk_id l) -> all_sep l).
  { intros l. induction l as [|x l IH]; cbn; intros HI ND; [exact I|].
    inversion ND as [|y ys Hni Hnd]; subst. split.
    - apply sep_from_intro. intros b' Hb'. apply HP; [apply HI; auto| apply HI; auto|].
      intros E. apply Hni. rewrite E. apply in_map. exact Hb'.
    - apply IH; [intros b Hb; apply HI; auto| exact Hnd]. }
  apply G; [auto| exact HN].
Qed.

Lemma HK_blocks : HK_blocks_stmt -> forall s LB m mo, HK s LB m mo -> all_range LB /\ all_sep LB.
Proof.
  intros HB s LB m mo H. destruct (HB _ _ _ _ H) as (R & P & N).
  split; [apply all_range_intro; exact R| apply blocks_all_sep; assumption].
Qed.
Lemma RYST_blocks : HK_blocks_stmt -> forall s LB m mo, RYST s LB m mo -> all_range LB /\ all_sep LB.
Proof. intros HB s LB m mo (H & _). exact (HK_blocks HB _ _ _ _ H). Qed.


End RYajl.

(* [comment removed for export] *)
End RC__2.
Ltac ywordify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let rec go pre l := lazymatch l with
     | CB 8 ?b :: ?post => apply (ycb8_c8_in m A pre post b) in H; cbn [app] in H; go constr:(pre ++ [C8 (le_bytes_to_word b)]) post
     | CB 4 ?b :: ?post => apply (ycb4_c4_in m A pre post b) in H; cbn [app] in H; go constr:(pre ++ [C4 (le_bytes_to_word b)]) post
     | ?c :: ?l' => go constr:(pre ++ [c]) l'
     | [] => idtac end in
  go constr:(@nil cell) cs end.
