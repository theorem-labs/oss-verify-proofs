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
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_q_stmts.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AQCR : Z := 0x3414c.   (* [comment removed for export] *)
Definition ADOREC : Z := 0x34014. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qcr_frame (vs4 vs3 vs2 vs1 vs0 vra : word) : list cell := [C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra].

Definition alloc_cells (P S : Z) (j1 j2 j3 : list byte) : list cell :=
  [W8 P; W8 PRIM_RES_SIZE; CB 16 j1; W8 S; W4 (2^32 - 1); CB 4 j2; W8 (S + KSPACESIZE); W1 0; CB 7 j3].

(* [comment removed for export] *)
Definition qcr_prim_front16_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (P S cbA A n c mapped lo : Z) (j1 j2 j3 : list byte) (b1 : byte) (cid : word),
  let p := A - 16 in
  mem_inv asegs m ->
  a0 = wz cbA -> a1 = wz (A - 16) ->
  1 <= c <= 30 -> 0 <= n < 2^40 -> A mod 16 = 0 ->
  KHIGHMEM_BEG <= S -> S + KSPACESIZE + 4096 <= alloc_ceiling -> S mod 4096 = 0 ->
  (* [comment removed for export] *)
  (exists idx, 0 <= idx /\ p = S + c * KREGIONSIZE + idx * csize c /\ idx * csize c + csize c <= mapped) ->
  0 <= mapped <= KFREEARRAY_OFF ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m (S + KSPACESIZE + 128 * c + 48) [W8 mapped] ->
  rw_cells asegs m (A - 16) (hdr_cells CHUNK_QUARANTINE n b1 cid) ->
  hdr_b1_ok (bv_unsigned b1) ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x342b8) (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2' (wz cbA) (wz (A - 16))
                    (wz A) (wz ((usz n + 7) / 8 * 8)) (wz 250) a3' a4' a5' a6' a7'
                    (wz p) (wz A_ALLOC) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz APOISON_SHADOW) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (A - 16, A - 12)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells asegs m' (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3)
      /\ rw_cells asegs m' (S + KSPACESIZE + 128 * c + 48) [W8 mapped]
      /\ rw_cells asegs m' (A - 16) (hdr_cells CHUNK_INVALID n b1 cid))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQCR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition qcr_prim_frontbig_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (P S cbA A n c mapped lo : Z) (j1 j2 j3 : list byte) (b1 : byte) (cid : word),
  let p := A - rz_size n in
  mem_inv asegs m ->
  a0 = wz cbA -> a1 = wz (A - 16) ->
  1 <= c <= 30 -> 0 <= n < 2^40 -> A mod 16 = 0 -> 16 < rz_size n ->
  KHIGHMEM_BEG <= S -> S + KSPACESIZE + 4096 <= alloc_ceiling -> S mod 4096 = 0 ->
  (exists idx, 0 <= idx /\ p = S + c * KREGIONSIZE + idx * csize c /\ idx * csize c + csize c <= mapped) ->
  rz_size n + 16 <= csize c ->          (* [comment removed for export] *)
  0 <= mapped <= KFREEARRAY_OFF ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m (S + KSPACESIZE + 128 * c + 48) [W8 mapped] ->
  rw_cells asegs m (A - 16) (hdr_cells CHUNK_QUARANTINE n b1 cid) ->
  hdr_b1_ok (bv_unsigned b1) ->
  rw_cells asegs m p [W8 KALLOCBEG_MAGIC; W8 (A - 16)] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x342b8) (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2' (wz cbA) (wz (A - 16))
                    (wz A) (wz ((usz n + 7) / 8 * 8)) (wz 250) a3' a4' a5' a6' a7'
                    (wz p) (wz A_ALLOC) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz APOISON_SHADOW) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (A - 16, A - 12); (p, p + 8)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells asegs m' (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3)
      /\ rw_cells asegs m' (S + KSPACESIZE + 128 * c + 48) [W8 mapped]
      /\ rw_cells asegs m' (A - 16) (hdr_cells CHUNK_INVALID n b1 cid)
      /\ rw_cells asegs m' p [W8 0; W8 (A - 16)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQCR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition qcr_prim_tail_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (P S cbA A n c p cache lo : Z) (j1 j2 j3 : list byte) (b1 : byte) (cid f1 f2 : word),
  mem_inv asegs m -> leafc st m -> RTWF st -> tp = wz ATP ->
  s0 = wz cbA -> s1 = wz (A - 16) -> s2 = wz p -> s3 = wz A_ALLOC -> s4 = wz (2^37) ->
  1 <= c <= 30 -> 0 <= n < 2^40 ->
  KHIGHMEM_BEG <= S -> S = st_spacebeg st ->
  S + c * KREGIONSIZE <= p -> p + csize c <= S + (c + 1) * KREGIONSIZE ->     (* [comment removed for export] *)
  0 <= cache < 2^64 -> alloc_ceiling <= cbA -> cbA + 16 <= 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (qcr_frame vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m cbA [W8 cache] ->
  rw_cells asegs m (A - 16) (hdr_cells CHUNK_INVALID n b1 cid) ->
  rw_cells asegs m (st_t st + T_STATS + 40) [C8 f1; C8 f2] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (f1' f2' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0' t1' t2' vs0 vs1
                    (wz cache) (wz A_ALLOC) (wz c) (wz p) a4' a5' a6' a7'
                    vs2 vs3 vs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ACDEALLOC) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (st_t st + T_STATS + 40, st_t st + T_STATS + 56)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 48)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3)
      /\ rw_cells asegs m' cbA [W8 cache]
      /\ rw_cells asegs m' (A - 16) (hdr_cells CHUNK_INVALID n b1 cid)
      /\ rw_cells asegs m' (st_t st + T_STATS + 40) [C8 f1'; C8 f2'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x342b8) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition qcr_sec_front_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (P S cbA mch lo : Z) (j1 j2 j3 : list byte),
  mem_inv asegs m ->
  a0 = wz cbA -> a1 = wz mch ->
  0 <= S -> S + KSPACESIZE <= 2^64 -> 0 <= mch < 2^64 -> (mch < S \/ S + KSPACESIZE <= mch) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  evt asegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s2' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x341c4) (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2' (wz cbA) (wz mch)
                    (wz A_SECONDARY) (wz mch) a2' a3' a4' a5' a6' a7'
                    s2' (wz A_ALLOC) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz AGET_BLOCK_BEGIN) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells asegs m' (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQCR) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition qcr_sec_tail_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (P S cbA mch n p' lo : Z) (j1 j2 j3 : list byte) (b1 : byte) (cid f1 f2 : word),
  mem_inv asegs m -> leafc st m -> RTWF st -> tp = wz ATP ->
  a0 = wz p' -> s0 = wz cbA -> s1 = wz mch -> s3 = wz A_ALLOC -> s4 = wz (2^37) ->
  0 <= n < 2^40 ->
  0 <= S -> S + KSPACESIZE <= 2^64 -> 0 < p' < 2^64 -> (p' < S \/ S + KSPACESIZE <= p') ->
  16 <= mch -> mch + 16 <= alloc_ceiling ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (qcr_frame vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m mch (hdr_cells CHUNK_QUARANTINE n b1 cid) ->
  rw_cells asegs m (st_t st + T_STATS + 40) [C8 f1; C8 f2] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (f1' f2' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0' t1' t2' vs0 vs1
                    (wz A_SECONDARY) (wz A_GSTATS) (wz p') a3' a4' a5' a6' a7'
                    vs2 vs3 vs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ALARGE_DEALLOC) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (st_t st + T_STATS + 40, st_t st + T_STATS + 56)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 48)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3)
      /\ rw_cells asegs m' mch (hdr_cells CHUNK_QUARANTINE n b1 cid)
      /\ rw_cells asegs m' (st_t st + T_STATS + 40) [C8 f1'; C8 f2'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x341c4) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dor_frame (j0 : list byte) (cache stack : Z) (vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word) : list cell :=
  [CB 8 j0; W8 cache; W8 stack; C8 vs9; C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra].
Definition tmp_cells (tn tf tl tb : Z) : list cell := [W8 tn; W8 tf; W8 tl; W8 tb].

(* [comment removed for export] *)
Definition dor_pro_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tmpA tn tf tl tb cache stack lo : Z),
  mem_inv asegs m ->
  a1 = wz tmpA -> a2 = wz cache -> a3 = wz stack ->
  0 < tn < 2^63 -> 0 <= cache < 2^64 -> 0 <= stack < 2^64 ->
  bv_unsigned sp <= tmpA -> tmpA + 32 <= 2^64 ->         (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 112 <= bv_unsigned sp ->
  rw_cells asegs m tmpA (tmp_cells tn tf tl tb) ->
  evt asegs (fun ms' => exists (a1' : word) (j0 : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) (wz tn) a1' a2 a3 a4 a5 a6 a7
                    (wz A_SECONDARY) (wz A_GSTATS) s4 (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x3408c) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 112)
      /\ rw_cells asegs m' (bv_unsigned sp - 112) (dor_frame j0 cache stack s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' tmpA (tmp_cells tn tf tl tb))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ADOREC) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition dor_pro0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tmpA tf tl tb cache stack lo : Z),
  mem_inv asegs m ->
  a1 = wz tmpA -> a2 = wz cache -> a3 = wz stack -> 0 <= cache < 2^64 -> 0 <= stack < 2^64 ->
  bv_unsigned sp <= tmpA -> tmpA + 32 <= 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 112 <= bv_unsigned sp ->
  rw_cells asegs m tmpA (tmp_cells 0 tf tl tb) ->
  evt asegs (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' tmpA (tmp_cells 0 tf tl tb))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ADOREC) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition dor_pop_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tmpA tn bA tl tb bnx bsz bcnt : Z),
  mem_inv asegs m ->
  s0 = wz tmpA -> a0 = wz tn ->
  1 <= tn < 2^63 -> 0 <= bnx < 2^64 -> 0 <= bsz <= tb -> tb < 2^63 -> 0 <= bcnt <= QBATCH_CAP ->
  AIMG_HI <= bA -> bA + QBATCH_SIZE <= alloc_ceiling -> alloc_ceiling <= tmpA -> tmpA + 32 <= 2^64 ->
  rw_cells asegs m tmpA (tmp_cells tn bA tl tb) ->
  rw_cells asegs m bA [W8 bnx; W8 bsz; W8 bcnt] ->
  evt asegs (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 (wz bA) s5 (wz bcnt) (wz (bA + 152)) (wz (bcnt + 16)) (wz 16) s10 s11 t3 t4 t5 t6)
               F (wz (if bcnt =? 0 then 0x340e4 else 0x340cc)) fc None m' (seg_rom asegs)
      /\ munch [(tmpA, tmpA + 32)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' tmpA (tmp_cells (tn - 1) bnx (if bnx =? 0 then 0 else tl) (tb - bsz))
      /\ rw_cells asegs m' bA [W8 bnx; W8 bsz; W8 bcnt])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3408c) fc None m (seg_rom asegs)).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dor_slot_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bA i v : Z),
  mem_inv asegs m ->
  s7 = wz (bA + 152 + 8 * i) -> 0 <= i < QBATCH_CAP -> 0 <= v < 2^64 ->
  AIMG_HI <= bA -> bA + QBATCH_SIZE <= alloc_ceiling -> bv_unsigned sp + 112 <= 2^64 ->
  rw_cells asegs m (bA + 24 + 8 * i) [W8 v] ->
  evt asegs (fun ms' =>
      ms' = MS (mkR (wz 0x340d8) sp gp tp t0 t1 t2 s0 s1 (wz (bv_unsigned sp + 8)) (wz v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz AQCR) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x340cc) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition dor_slotnext_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bA i bcnt : Z),
  s7 = wz (bA + 152 + 8 * i) -> s8 = wz (bcnt + 16) -> s9 = wz (16 + i) ->
  0 <= i < bcnt -> bcnt <= QBATCH_CAP -> 0 <= bA -> bA + QBATCH_SIZE <= 2^64 ->
  evt asegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (bA + 152 + 8 * (i + 1))) s8 (wz (16 + (i + 1))) s10 s11 t3 t4 t5 t6)
               F (wz (if i + 1 =? bcnt then 0x340e4 else 0x340cc)) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x340d8) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition dor_batch_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P S bA cache stack : Z) (j0 j1 j2 j3 : list byte)
         (vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word),
  mem_inv asegs m ->
  s1 = wz A_ALLOC -> s4 = wz bA -> s5 = wz (2^37) ->
  KHIGHMEM_BEG <= S -> S + 24 * KREGIONSIZE <= bA -> bA + QBATCH_SIZE <= S + 25 * KREGIONSIZE -> S + KSPACESIZE <= alloc_ceiling ->
  0 <= cache < 2^64 -> alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 112 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (dor_frame j0 cache stack vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  evt asegs (fun ms' => exists (a4' : word),
      ms' = MS (mkR (wz 0x34110) sp gp tp t0 t1 t2 s0 s1 (wz cache) (wz A_ALLOC) (wz 24) (wz bA) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ACDEALLOC) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x340e4) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition dor_next_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tmpA tn tf tl tb : Z),
  mem_inv asegs m -> s0 = wz tmpA -> 0 <= tn < 2^63 -> alloc_ceiling <= tmpA -> tmpA + 32 <= 2^64 ->
  rw_cells asegs m tmpA (tmp_cells tn tf tl tb) ->
  evt asegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz tn) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if tn =? 0 then 0x34118 else 0x3408c)) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x34110) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition dor_epi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cache stack lo : Z) (j0 : list byte)
         (vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 112 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (dor_frame j0 cache stack vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  evt asegs (fun ms' =>
      ms' = MS (mkR vra (wz (bv_unsigned sp + 112)) gp tp t0 t1 t2 vs0 vs1 a0 a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m (seg_rom asegs)
      /\ stk asegs m lo (bv_unsigned sp + 112))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x34118) fc None m (seg_rom asegs)).


End CeilWrap.
End RTW_q_stmts.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_q_dor1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 RTW_q_stmts.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma A_ALLOC_lits : A_ALLOC = 683032 /\ A_SECONDARY = 683096 /\ A_GSTATS = 683720 /\ KREGIONSIZE = 4294967296 /\ KSPACESIZE = 137438953472
                     /\ QBATCH_SIZE = 8192 /\ QBATCH_CAP = 1021 /\ AQCR = 213324 /\ ACDEALLOC = 214352 /\ ADOREC = 213012
                     /\ KHIGHMEM_BEG = 17594333495296 /\ AIMG_HI = 6287360.
Proof. repeat split; reflexivity. Qed.

Ltac dlits := (nelimp A_ALLOC_lits 12%nat; intros EA1 EA2 EA3 EKR EKS EQS EQC EQCR ECD EDR EKH EIH).

(* [comment removed for export] *)
Theorem dor_pro_proof : dor_pro_stmt.
Proof.
  unfold dor_pro_stmt. intros until lo. intros MI -> -> -> Htn Hc Hs TA1 TA2 ST HCL LO TMP.
  dlits. unfold dor_frame, tmp_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite EDR, EA1, EA2, EA3. leaf_prep. cbv beta delta [wz] in TMP.
  carve_frame 112%nat ST.
  do 12 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  do 7 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Theorem dor_pro0_proof : dor_pro0_stmt.
Proof.
  unfold dor_pro0_stmt. intros until lo. intros MI -> -> -> Hc Hs TA1 TA2 ST HCL LO TMP.
  dlits. unfold tmp_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite EDR. leaf_prep. cbv beta delta [wz] in TMP.
  carve_frame 112%nat ST.
  do 12 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  do 11 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Definition dor_pop_stmt' : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tmpA tn bA tl tb bnx bsz bcnt : Z),
  mem_inv asegs m ->
  s0 = wz tmpA -> a0 = wz tn ->
  1 <= tn < 2^63 -> 0 <= bnx < 2^64 -> 0 <= bsz <= tb -> tb < 2^63 -> 0 <= bcnt <= QBATCH_CAP ->
  AIMG_HI <= bA -> bA + QBATCH_SIZE <= alloc_ceiling -> alloc_ceiling <= tmpA -> tmpA + 32 <= 2^64 ->
  rw_cells asegs m tmpA (tmp_cells tn bA tl tb) ->
  rw_cells asegs m bA [W8 bnx; W8 bsz; W8 bcnt] ->
  evt asegs (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 (wz bA) s5 (wz bcnt)
                    (if bcnt =? 0 then s7 else wz (bA + 152)) (if bcnt =? 0 then s8 else wz (bcnt + 16)) (if bcnt =? 0 then s9 else wz 16)
                    s10 s11 t3 t4 t5 t6)
               F (wz (if bcnt =? 0 then 0x340e4 else 0x340cc)) fc None m' (seg_rom asegs)
      /\ munch [(tmpA, tmpA + 32)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' tmpA (tmp_cells (tn - 1) bnx (if bnx =? 0 then 0 else tl) (tb - bsz))
      /\ rw_cells asegs m' bA [W8 bnx; W8 bsz; W8 bcnt])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3408c) fc None m (seg_rom asegs)).

Theorem dor_pop_proof : dor_pop_stmt'.
Proof.
  unfold dor_pop_stmt'. intros until bcnt. intros MI -> -> Htn Hbnx Hbsz Htb Hbcnt BLO BHI TLO THI TMP BAT.
  dlits. unfold tmp_cells in *.
  pose proof (munch_refl [(tmpA, tmpA + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  leaf_prep. idtac. cbv beta delta [wz] in TMP, BAT.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  destruct (Z.eqb_spec bnx 0) as [E|NE].
  - subst bnx. lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    destruct (Z.eqb_spec bcnt 0) as [E2|NE2].
    + subst bcnt. lstep; if_lia. finish; eassumption.
    + lstep; if_lia. lstep. lstep. lstep. finish; eassumption.
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep.
    lstep. lstep. lstep. lstep.
    lstep.
    destruct (Z.eqb_spec bcnt 0) as [E2|NE2].
    + subst bcnt. lstep; if_lia. finish; eassumption.
    + lstep; if_lia. lstep. lstep. lstep. finish; eassumption.
Qed.

(* [comment removed for export] *)
Theorem dor_slot_proof : dor_slot_stmt.
Proof.
  unfold dor_slot_stmt. intros until v. intros MI -> Hi Hv BLO BHI SPH CELL.
  unfold QBATCH_SIZE, QBATCH_CAP, AIMG_HI in *. dlits. leaf_prep. idtac. cbv beta delta [wz] in CELL.
  set (slot := bA + 24 + 8 * i) in *.
  replace (bA + 152 + 8 * i) with (slot + 128) by lia.
  assert (SR : 6287360 <= slot /\ slot + 8 <= alloc_ceiling) by lia. clearbody slot.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  finish.
Qed.

(* [comment removed for export] *)
Definition dor_slotnext_stmt' : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bA i bcnt : Z),
  s7 = wz (bA + 152 + 8 * i) -> s8 = wz (bcnt + 16) -> s9 = wz (16 + i) ->
  0 <= i < bcnt -> bcnt <= QBATCH_CAP -> 0 <= bA -> bA + QBATCH_SIZE <= 2^64 -> bA + QBATCH_SIZE <= alloc_ceiling ->
  evt asegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (bA + 152 + 8 * (i + 1))) s8 (wz (16 + (i + 1))) s10 s11 t3 t4 t5 t6)
               F (wz (if i + 1 =? bcnt then 0x340e4 else 0x340cc)) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x340d8) fc None m (seg_rom asegs)).

Theorem dor_slotnext_proof : dor_slotnext_stmt'.
Proof.
  unfold dor_slotnext_stmt'. intros until bcnt. intros -> -> -> Hi Hb B0 BH BC.
  unfold QBATCH_SIZE, QBATCH_CAP in *. dlits. leaf_prep. idtac.
  set (s7v := bA + 152 + 8 * i) in *.
  replace (bA + 152 + 8 * (i + 1)) with (s7v + 8) by lia.
  assert (SR : 0 <= s7v /\ s7v + 8 <= 2^64) by lia. clearbody s7v.
  lstep. lstep. (* [comment removed for export] *)
  destruct (Z.eqb_spec (i + 1) bcnt) as [E|NE].
  - lstep; if_lia. replace (16 + i + 1) with (16 + (i + 1)) by lia. finish.
  - lstep; if_lia. replace (16 + i + 1) with (16 + (i + 1)) by lia. finish.
Qed.

(* [comment removed for export] *)
Lemma cls24_of_region : forall bA S, S + 24 * 4294967296 <= bA -> bA + 8192 <= S + 25 * 4294967296 ->
  Z.shiftr (Z.shiftl (bA - S) 27 mod 18446744073709551616) 59 = 24.
Proof.
  intros bA S H1 H2. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 27) with 134217728. change (2 ^ 59) with 576460752303423488.
  rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Theorem dor_batch_proof : dor_batch_stmt.
Proof.
  unfold dor_batch_stmt. intros until vra. intros MI -> -> -> SLO BLO BHI SHI Hc SPL SPH FR AC.
  unfold QBATCH_SIZE, KREGIONSIZE, KSPACESIZE, KHIGHMEM_BEG, AIMG_HI, dor_frame, alloc_cells in *. dlits. leaf_prep. idtac.
  rewrite EA1 in *. cbv beta delta [wz] in FR, AC.
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite (cls24_of_region bA S) by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  rewrite <- EA1. finish.
Qed.

(* [comment removed for export] *)
Theorem dor_next_proof : dor_next_stmt.
Proof.
  unfold dor_next_stmt. intros until tb. intros MI -> Htn TLO THI TMP.
  unfold tmp_cells in *. dlits. leaf_prep. try idtac. cbv beta delta [wz] in TMP.
  lstep. (* [comment removed for export] *)
  destruct (Z.eqb_spec tn 0) as [E|NE].
  - subst tn. lstep; if_lia. finish.
  - lstep; if_lia. finish.
Qed.

(* [comment removed for export] *)
Theorem dor_epi_proof : dor_epi_stmt.
Proof.
  unfold dor_epi_stmt. intros until vra. intros MI ST HCL LO SPH FR.
  unfold dor_frame in *. try idtac. leaf_prep. cbv beta delta [wz] in FR.
  do 11 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 112).
  finish; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac dlits := (nelimp A_ALLOC_lits 12%nat; intros EA1 EA2 EA3 EKR EKS EQS EQC EQCR ECD EDR EKH EIH).
End RTW_q_dor1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
Module RTW_q_qcr1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 RTW_q_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma csize_max' : forall c, 1 <= c <= 30 -> csize c <= 65536.
Proof.
  intros c Hc.
  assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct H as [->|H]; [vm_compute; discriminate|]). subst. vm_compute. discriminate.
Qed.
Lemma csize_small' : forall c, 1 <= c <= 16 -> csize c = 32 * c.
Proof. intros c Hc. unfold csize. replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; lia). replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma land31_small : forall c, 0 <= c < 32 -> Z.land c 31 = c.
Proof. intros c Hc. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^5) with 32. lia. Qed.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma land_align4'' : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof. intros. apply land_align4'; assumption. Qed.

Lemma land_m8' : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. replace 18446744073709551608 with ((-8) mod 2^64) by reflexivity.
  rewrite land_mod_pow2_r by lia. replace (-8) with (Z.lnot (Z.ones 3)) by reflexivity. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shr32_class : forall d c K, d = c * 4294967296 + K -> 0 <= K < 4294967296 -> 0 <= c -> Z.shiftr d 32 = c.
Proof. intros d c K -> HK Hc. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Lemma class_bits : forall d c, 0 <= c < 32 -> c * 4294967296 <= d < (c + 1) * 4294967296 ->
  Z.shiftr ((Z.shiftl d 27) mod 18446744073709551616) 59 = c.
Proof.
  intros d c Hc Hd. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (split; [lia|]; change (2^27) with 134217728; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^59) with (4294967296 * 2^27). Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma divuw_lo : forall v i, 0 <= v < 2^64 -> 0 < i < 2^31 -> (v mod 4294967296) / i < 2^31 ->
  v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 ((v mod 4294967296) / i).
Proof.
  intros v i Hv Hi Hq. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite (Z.mod_small i) by lia. destruct (Z.eqb_spec i 0); [lia|].
  f_equal. pose proof (Z.div_pos (v mod 4294967296) i ltac:(Z.div_mod_to_equations; lia) ltac:(lia)).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (4294967296 `div` 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma cas_word30 : forall q, 0 <= q -> Z.land (3 + 256 * q) 255 = 3 /\ Z.lxor (3 + 256 * q) 3 = 256 * q.
Proof.
  intros q Hq.
  assert (M : forall k, 0 <= k < 256 -> Z.land (256 * q + k) 255 = k).
  { intros k Hk. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256. Z.div_mod_to_equations. nia. }
  assert (X : forall k, 0 <= k < 256 -> 256 * q + k = Z.lxor (256 * q) k).
  { intros k Hk. rewrite <- Z.add_nocarry_lxor by (apply land_hi_lo; lia). reflexivity. }
  replace (3 + 256 * q) with (256 * q + 3) by lia.
  split; [apply M; lia|].
  rewrite (X 3) by lia. rewrite Z.lxor_assoc. change (Z.lxor 3 3) with 0. rewrite Z.lxor_0_r. reflexivity.
Qed.

Lemma hdr_word_split0 : forall m p (b : byte) h, 0 <= h < 65536 ->
  rw_cells asegs m p [C4 (wz (256 * (bv_unsigned b + 256 * h)))] -> rw_cells asegs m p [C1 (zb 0); C1 b; C2 (wz h)].
Proof. intros m p b h Hh H. apply hdr_word_split; [lia| exact Hh|]. exact H. Qed.

Ltac cases_17_30 c :=
  let HH := fresh in
  assert (HH : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcr_size17 : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z) (Q : machine_state -> Prop),
  17 <= c <= 30 ->
  (forall a6' a7' : word,
     evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (wz c) (wz c) x14 (wz (csize c)) a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (wz 0x341fc) fc None m (seg_rom asegs))) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (wz c) (wz c) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (wz 0x341d8) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros Hc K. cbv beta delta [wz] in *.
  cases_17_30 c; do 9 (lstep; try fl); apply K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcr_prim_pre :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (P S cbA mch c idx p mapped lo : Z) (j1 j2 j3 : list byte) (Q : machine_state -> Prop),
  mem_inv asegs m ->
  a0 = wz cbA -> a1 = wz mch ->
  1 <= c <= 30 -> 0 <= idx -> p = S + c * KREGIONSIZE + idx * csize c -> idx * csize c + csize c <= mapped ->
  0 <= mapped <= KFREEARRAY_OFF -> p <= mch < p + csize c ->
  KHIGHMEM_BEG <= S -> S + KSPACESIZE + 4096 <= alloc_ceiling -> S mod 4096 = 0 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m (S + KSPACESIZE + 128 * c + 48) [W8 mapped] ->
  (forall (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
     mem_inv asegs m' -> munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono asegs m m' ->
     stk asegs m' lo (bv_unsigned sp - 48) ->
     rw_cells asegs m' (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra) ->
     rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3) ->
     rw_cells asegs m' (S + KSPACESIZE + 128 * c + 48) [W8 mapped] ->
     evt asegs Q (MS (mkR ra (wz (bv_unsigned sp - 48)) gp tp t0 t1 t2 (wz cbA) (wz mch) a0' a1' a2' a3' a4' a5' a6' a7'
                          (wz p) (wz A_ALLOC) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz 0x34240) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz AQCR) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros MI -> -> Hc Hidx Hp HK Hmp Hm HS1 HS2 HS3 ST CEIL LO AC RI K.
  pose proof (csize_pos c ltac:(lia)) as CP. pose proof (csize_max' c ltac:(lia)) as CL.
  set (cs := csize c) in *.
  assert (KR : 0 <= idx * cs /\ idx * cs + cs <= 3758096384) by (unfold KFREEARRAY_OFF in Hmp; nia).
  set (Kc := idx * cs) in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold alloc_cells in *. unfold AQCR, A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *.
  change (2 ^ 37) with 137438953472 in *. change (2 ^ 32) with 4294967296 in *.
  leaf_prep. idtac.
  carve_frame 48%nat ST.
  do 7 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  assert (E1 : Z.shiftr (mch - S) 32 = c) by (apply (shr32_class (mch - S) c (mch - p + Kc)); lia).
  rewrite E1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  (* [comment removed for export] *)
  assert (J : forall a5r a6r a7r : word, a5r = Z_to_bv 64 cs ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cbA) (Z_to_bv 64 mch)
                     (Z_to_bv 64 S) (Z_to_bv 64 (S + 137438953472)) (Z_to_bv 64 c) (Z_to_bv 64 c) (Z_to_bv 64 (mch - S)) a5r a6r a7r
                     s2 (Z_to_bv 64 683032) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x341fc) fc None m1 (seg_rom asegs))).
  { intros a5r a6r a7r ->.
    lstep. (* [comment removed for export] *)
    rewrite (divuw_lo (mch - S) cs) by (Z.div_mod_to_equations; nia).
    replace ((mch - S) mod 4294967296 / cs) with idx.
    2:{ replace ((mch - S) mod 4294967296) with (idx * cs + (mch - p)) by (Z.div_mod_to_equations; nia).
        rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    rewrite !Z.shiftl_mul_pow2 by lia. change (2^32) with 4294967296. change (2^7) with 128.
    setreg 12 (Z_to_bv 64 (S + 137438953472 + 128 * c)) ltac:(f_equal; lia).
    set (RIA := S + 137438953472 + 128 * c) in *.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (Z.shiftr (idx * 4294967296) 32) with idx
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296; rewrite Z.div_mul by lia; reflexivity).
    lstep. (* [comment removed for export] *)
    replace (cs * idx) with Kc by lia. try rewrite (Z.mod_small Kc 18446744073709551616) by lia.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    try rewrite (Z.mod_small (Kc + cs) 18446744073709551616) by lia.
    replace (mapped <? Kc + cs) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    try rewrite (Z.mod_small (c * 4294967296 + S + Kc) 18446744073709551616) by lia.
    replace (c * 4294967296 + S + Kc) with p by lia. rewrite (land_ones64 p) by lia.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    eapply K; [eassumption| exact MU| exact WM| exact ST| exact FR| eassumption| eassumption]. }
  lstep. (* [comment removed for export] *) rewrite (land31_small c) by lia.
  lstep. lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  if_cases K17; zify_cond K17.
  - (* [comment removed for export] *) apply qcr_size17; [lia|]. intros a6' a7'. apply J. reflexivity.
  - lstep. if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply J. f_equal. rewrite Z.shiftl_mul_pow2 by lia. subst cs. rewrite csize_small' by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcr_prim_hdr :
  forall (x1 sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mch n : Z) (b1 : byte) (cid : word) (Q : machine_state -> Prop),
  mem_inv asegs m ->
  0 <= n < 2^40 -> mch mod 16 = 0 -> KHIGHMEM_BEG <= mch -> mch + 16 <= alloc_ceiling ->
  rw_cells asegs m mch (hdr_cells CHUNK_QUARANTINE n b1 cid) -> hdr_b1_ok (bv_unsigned b1) ->
  (forall (a3' a4' a5' : word) (m' : word -> option byte),
     mem_inv asegs m' -> munch [(mch, mch + 4)] m m' -> wmono asegs m m' ->
     rw_cells asegs m' mch (hdr_cells CHUNK_INVALID n b1 cid) ->
     evt asegs Q (MS (mkR (wz 0x342b8) sp gp tp t0 t1 t2 s0 (wz mch) (wz (mch + 16)) (wz ((usz n + 7) / 8 * 8)) (wz 250) a3' a4' a5' a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (wz APOISON_SHADOW) fc None m' (seg_rom asegs))) ->
  evt asegs Q (MS (mkR x1 sp gp tp t0 t1 t2 s0 (wz mch) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0x3425c) fc None m (seg_rom asegs)).
Proof.
  intros until Q. intros MI Hn M16 M1 M2 HDR Hb1 K.
  (nelimp (size_hilo n Hn) 3%nat; intros SH1 SL1 SHL).
  pose proof (bv_unsigned_in_range 8 b1) as Rb. unfold bv_modulus in Rb. cbn in Rb.
  pose proof (munch_refl [(mch, mch + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold hdr_cells, CHUNK_QUARANTINE, CHUNK_INVALID, KHIGHMEM_BEG, AIMG_HI, APOISON_SHADOW in *. cbv beta delta [wz] in *. idtac.
  lstep. (* [comment removed for export] *) rewrite (land_align4'' mch) by lia.
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  replace (((mch ≪ 3) mod 18446744073709551616) mod 32) with 0
    by (symmetry; rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; rewrite (Z.mod_small (mch * 8) 18446744073709551616) by lia; Z.div_mod_to_equations; lia).
  change (bv_swrap 32 (255 ≪ 0)) with 255. change (bv_swrap 32 (3 ≪ 0)) with 3.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app _ _ [_; _; _] [_; _])) in HDR as [HW HR]. cbn [cells_size Cells.csize Nat.add] in HR.
  apply hdr_word_join in HW; [| lia| lia].
  set (q := bv_unsigned b1 + 256 * size_hi n) in HW.
  pose proof (cas_word30 q ltac:(lia)) as [CW1 CW2].
  assert (AL4 : mch mod 4 = 0) by (Z.div_mod_to_equations; lia).
  assert (AR : 0 <= mch < 2^64) by lia.
  cbv beta delta [wz] in HW.
  amo_zstep. (* [comment removed for export] *)
  rewrite (sx32_lit (3 + 256 * q)) by lia.
  lstep. (* [comment removed for export] *) rewrite CW1.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) try rewrite Z.lxor_0_r.
  lstep. (* [comment removed for export] *) rewrite CW1.
  lstep. (* [comment removed for export] *) rewrite CW2.
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  match goal with H : rw_cells _ _ mch [C4 _] |- _ => apply hdr_word_split0 in H; [| lia]; rename H into HW' end.
  pose proof HR as HR4. replace (mch + Z.of_nat 4) with (mch + 4) in HR4 by lia.
  lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
  lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *) rewrite size_join by lia.
  lstep. lstep. (* [comment removed for export] *) rewrite land_m8' by lia.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (proj2 (rw_cells_app mx mch [C1 (zb 0); C1 b1; C2 (Z_to_bv 64 (size_hi n))] [C4 (Z_to_bv 64 (size_lo n)); C8 cid]) (conj HW' HR)) as HDR' end.
  cbn [app] in HDR'.
  eapply K; [eassumption| exact MU| exact WM| exact HDR'].
Qed.

Ltac subfp := intros x Hx; cbn in Hx |- *; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem qcr_prim_front16_proof : qcr_prim_front16_stmt.
Proof.
  unfold qcr_prim_front16_stmt. intros until cid. cbv zeta.
  intros MI Ha0 Ha1 Hc Hn A16 HS1 HS2 HS3 (idx & Hidx & Hp & HK) Hmp ST CEIL LO AC RI HDR Hb1.
  pose proof (csize_pos c ltac:(lia)) as CP. pose proof (csize_max' c ltac:(lia)) as CL.
  assert (KR : 0 <= idx * csize c) by nia.
  pose proof HS2 as HS2'. unfold KSPACESIZE in HS2'. idtac. pose proof CEIL as CEIL'. idtac.
  pose proof Hp as Hp'. unfold KREGIONSIZE in Hp'. pose proof Hmp as Hmp'. unfold KFREEARRAY_OFF in Hmp'. pose proof HS1 as HS1'. unfold KHIGHMEM_BEG, AIMG_HI in HS1'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply qcr_prim_pre with (P := P) (S := S) (cbA := cbA) (mch := A - 16) (c := c) (idx := idx) (p := A - 16) (mapped := mapped) (lo := lo) (j1 := j1) (j2 := j2) (j3 := j3);
    [exact MI| exact Ha0| exact Ha1| exact Hc| exact Hidx| exact Hp| exact HK| exact Hmp| lia| exact HS1| exact HS2| exact HS3| exact ST| exact CEIL| exact LO| exact AC| exact RI|].
  intros a0' a1' a2' a3' a4' a5' a6' a7' m1 MI1 MU1 WM1 ST1 FR1 AC1 RI1. cbv beta delta [wz] in *.
  eapply rw_cells_transport in HDR; [| exact MU1| exact WM1| cbn; lia].
  lstep. if_lia. (* [comment removed for export] *)
  eapply qcr_prim_hdr with (n := n); [exact MI1| exact Hn| Z.div_mod_to_equations; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| exact HDR| exact Hb1|].
  intros a3'' a4'' a5'' m2 MI2 MU2 WM2 HDR2. cbv beta delta [wz] in *.
  replace (A - 16 + 16) with A by lia.
  apply evt_done. exists t0, t1, t2, a3'', a4'', a5'', a6', a7', t3, t4, t5, t6, m2.
  split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; subfp| eapply munch_weaken; [| exact MU2]; subfp]. }
  split; [eapply wmono_trans; [exact WM1| exact WM2]|].
  split; [exact MI2|].
  split; [eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact AC1| exact MU2| exact WM2| unfold A_ALLOC; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact RI1| exact MU2| exact WM2| unfold KSPACESIZE; cbn; lia]|].
  exact HDR2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem qcr_prim_frontbig_proof : qcr_prim_frontbig_stmt.
Proof.
  unfold qcr_prim_frontbig_stmt. intros until cid. cbv zeta.
  intros MI Ha0 Ha1 Hc Hn A16 Hrz HS1 HS2 HS3 (idx & Hidx & Hp & HK) Hcs Hmp ST CEIL LO AC RI HDR Hb1 BH.
  pose proof (csize_pos c ltac:(lia)) as CP. pose proof (csize_max' c ltac:(lia)) as CL. pose proof (rz_size_range n) as [RZ1 RZ2].
  assert (KR : 0 <= idx * csize c) by nia.
  pose proof HS2 as HS2'. unfold KSPACESIZE in HS2'. idtac. pose proof CEIL as CEIL'. idtac.
  pose proof Hp as Hp'. unfold KREGIONSIZE in Hp'. pose proof Hmp as Hmp'. unfold KFREEARRAY_OFF in Hmp'. pose proof HS1 as HS1'. unfold KHIGHMEM_BEG, AIMG_HI in HS1'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply qcr_prim_pre with (P := P) (S := S) (cbA := cbA) (mch := A - 16) (c := c) (idx := idx) (p := A - rz_size n) (mapped := mapped) (lo := lo) (j1 := j1) (j2 := j2) (j3 := j3);
    [exact MI| exact Ha0| exact Ha1| exact Hc| exact Hidx| exact Hp| exact HK| exact Hmp| lia| exact HS1| exact HS2| exact HS3| exact ST| exact CEIL| exact LO| exact AC| exact RI|].
  intros a0' a1' a2' a3' a4' a5' a6' a7' m1 MI1 MU1 WM1 ST1 FR1 AC1 RI1. cbv beta delta [wz] in *.
  unfold A_ALLOC, alloc_cells in AC1. unfold KSPACESIZE in RI1.
  eapply rw_cells_transport in HDR; [| exact MU1| exact WM1| cbn; lia].
  eapply rw_cells_transport in BH; [| exact MU1| exact WM1| cbn; lia].
  set (p := A - rz_size n) in *.
  assert (MUA : munch [(bv_unsigned sp + -48, bv_unsigned sp); (A - 16, A - 12); (p, p + 8)] m m1) by (eapply munch_weaken; [| exact MU1]; subfp).
  clear MU1.
  assert (AL8 : p mod 8 = 0) by (subst p; Z.div_mod_to_equations; lia). assert (PR : 0 <= p < 2^64) by lia.
  unfold KALLOCBEG_MAGIC in BH.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
  match goal with H : wmono asegs m m2 |- _ => rename H into WMA end.
  eapply qcr_prim_hdr with (n := n); [exact MI2| exact Hn| Z.div_mod_to_equations; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| eassumption| exact Hb1|].
  intros a3'' a4'' a5'' m3 MI3 MU3 WM3 HDR3. cbv beta delta [wz] in *.
  replace (A - 16 + 16) with A by lia.
  apply evt_done. exists t0, t1, t2, a3'', a4'', a5'', a6', a7', t3, t4, t5, t6, m3.
  split; [reflexivity|].
  split. { eapply munch_trans; [exact MUA| eapply munch_weaken; [| exact MU3]; subfp]. }
  split; [eapply wmono_trans; [exact WMA| exact WM3]|].
  split; [exact MI3|].
  split; [eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact AC1| exact MU3| exact WM3| unfold A_ALLOC; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact RI1| exact MU3| exact WM3| unfold KSPACESIZE; cbn; lia]|].
  split; [exact HDR3|].
  eapply rw_cells_transport; [exact BH| exact MU3| exact WM3| cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qcr_prim_tail_stmt2 : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (P S cbA A n c p cache lo : Z) (j1 j2 j3 : list byte) (b1 : byte) (cid f1 f2 : word),
  mem_inv asegs m -> leafc st m -> RTWF st -> tp = wz ATP ->
  s0 = wz cbA -> s1 = wz (A - 16) -> s2 = wz p -> s3 = wz A_ALLOC -> s4 = wz (2^37) ->
  1 <= c <= 30 -> 0 <= n < 2^40 ->
  KHIGHMEM_BEG <= S -> S = st_spacebeg st ->
  S + c * KREGIONSIZE <= p -> p + csize c <= S + (c + 1) * KREGIONSIZE ->
  0 <= cache < 2^64 -> alloc_ceiling <= cbA -> cbA + 16 <= 2^64 ->
  (* [comment removed for export] *) bv_unsigned sp + 48 <= cbA ->
  (* [comment removed for export] *) KHIGHMEM_BEG + 16 <= A -> (* [comment removed for export] *) A <= alloc_ceiling ->
  (* [comment removed for export] *) (A <= st_t st \/ st_t st + 4096 <= A - 16) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (qcr_frame vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m cbA [W8 cache] ->
  rw_cells asegs m (A - 16) (hdr_cells CHUNK_INVALID n b1 cid) ->
  rw_cells asegs m (st_t st + T_STATS + 40) [C8 f1; C8 f2] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (f1' f2' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0' t1' t2' vs0 vs1
                    (wz cache) (wz A_ALLOC) (wz c) (wz p) a4' a5' a6' a7'
                    vs2 vs3 vs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ACDEALLOC) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (st_t st + T_STATS + 40, st_t st + T_STATS + 56)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 48)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3)
      /\ rw_cells asegs m' cbA [W8 cache]
      /\ rw_cells asegs m' (A - 16) (hdr_cells CHUNK_INVALID n b1 cid)
      /\ rw_cells asegs m' (st_t st + T_STATS + 40) [C8 f1'; C8 f2'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x342b8) fc None m (seg_rom asegs)).

Theorem qcr_prim_tail_proof : qcr_prim_tail_stmt2.
Proof.
  unfold qcr_prim_tail_stmt2. intros until f2.
  intros MI LC WF TP -> -> -> -> -> Hc Hn HS1 HSS Hp1 Hp2 Hca C1 C2 C3 A1 A2 TA ST CEIL LO SP2 FR AC CB HDR TS.
  pose proof (csize_pos c ltac:(lia)) as CP. pose proof (t_range st WF) as TR. olin TR. (nelimp (size_hilo n Hn) 3%nat; intros SH1 SL1 SHL).
  pose proof (wb_P_S st (wf_base_ok st WF)) as [PS1 PS2].
  pose proof (wb_ranges st (wf_base_ok st WF) (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)) as PBR. cbn [fst snd] in PBR.
  unfold PRIM_RES_SIZE, KSPACESIZE in PS2, PBR. rewrite <- HSS in PS1, PS2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + T_STATS + 40, st_t st + T_STATS + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold alloc_cells, hdr_cells, qcr_frame in *.
  unfold ACDEALLOC, A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, T_STATS, CHUNK_INVALID in *. idtac.
  leaf_prep. subst tp.
  lstep. (* [comment removed for export] *)
  call get_thread_stats_c; [exact LC| exact WF| eassumption| reflexivity| exact ST| idtac; lia| lia|].
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. restk. unfold T_STATS.
  replace (st_t st + 2800 + 40) with (st_t st + 2840) in TS by lia.
  replace (st_t st + 2800 + 40) with (st_t st + 2840) in MU by lia. replace (st_t st + 2800 + 56) with (st_t st + 2856) in MU by lia.
  lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
  lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; try if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite (class_bits (p - S) c) by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  release_frame FR ST (bv_unsigned sp + 48).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem qcr_sec_front_proof : qcr_sec_front_stmt.
Proof.
  unfold qcr_sec_front_stmt. intros until j3.
  intros MI -> -> HS0 HS1 Hm Hout ST CEIL LO AC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold alloc_cells in *. unfold AQCR, AGET_BLOCK_BEGIN, A_SECONDARY, A_ALLOC, KSPACESIZE, PRIM_RES_SIZE, qcr_frame in *.
  change (2 ^ 37) with 137438953472 in *. change (2 ^ 32) with 4294967296 in *.
  leaf_prep.
  carve_frame 48%nat ST.
  do 7 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  if_cases K1; zify_cond K1.
  2: lstep; (lstep; try if_lia). (* [comment removed for export] *)
  all: lstep; lstep; lstep. (* [comment removed for export] *)
  all: try rewrite unsigned_lit in * by lia.
  all: finish; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qcr_sec_tail_stmt2 : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vs4 vs3 vs2 vs1 vs0 vra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (P S cbA mch n p' lo : Z) (j1 j2 j3 : list byte) (b1 : byte) (cid f1 f2 : word),
  mem_inv asegs m -> leafc st m -> RTWF st -> tp = wz ATP ->
  a0 = wz p' -> s0 = wz cbA -> s1 = wz mch -> s3 = wz A_ALLOC -> s4 = wz (2^37) ->
  0 <= n < 2^40 ->
  0 <= S -> S + KSPACESIZE <= 2^64 -> 0 < p' < 2^64 -> (p' < S \/ S + KSPACESIZE <= p') ->
  16 <= mch -> mch + 16 <= alloc_ceiling ->
  (* [comment removed for export] *) (mch + 16 <= st_t st \/ st_t st + 4096 <= mch) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (qcr_frame vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells asegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  rw_cells asegs m mch (hdr_cells CHUNK_QUARANTINE n b1 cid) ->
  rw_cells asegs m (st_t st + T_STATS + 40) [C8 f1; C8 f2] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (f1' f2' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0' t1' t2' vs0 vs1
                    (wz A_SECONDARY) (wz A_GSTATS) (wz p') a3' a4' a5' a6' a7'
                    vs2 vs3 vs4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ALARGE_DEALLOC) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (st_t st + T_STATS + 40, st_t st + T_STATS + 56)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 48)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells P S j1 j2 j3)
      /\ rw_cells asegs m' mch (hdr_cells CHUNK_QUARANTINE n b1 cid)
      /\ rw_cells asegs m' (st_t st + T_STATS + 40) [C8 f1'; C8 f2'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x341c4) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Ltac qcr_sec_fin ST :=
  lstep; lstep; lstep; (* [comment removed for export] *)
  do 6 lstep; (* [comment removed for export] *)
  lstep; lstep; (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia;
  match goal with H : rw_cells _ _ (bv_unsigned ?spx) [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- _ => release_frame H ST (bv_unsigned spx + 48) end;
  finish; eassumption.

Theorem qcr_sec_tail_proof : qcr_sec_tail_stmt2.
Proof.
  unfold qcr_sec_tail_stmt2. intros until f2.
  intros MI LC WF TP -> -> -> -> -> Hn HS0 HS1 Hp Hout M1 M2 TM ST CEIL LO SP2 FR AC HDR TS.
  pose proof (t_range st WF) as TR. olin TR. (nelimp (size_hilo n Hn) 3%nat; intros SH1 SL1 SHL).
  pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + T_STATS + 40, st_t st + T_STATS + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold alloc_cells, hdr_cells, qcr_frame in *.
  unfold ALARGE_DEALLOC, A_SECONDARY, A_GSTATS, A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, T_STATS, CHUNK_QUARANTINE, PRIM_RES_SIZE in *. idtac.
  change (2 ^ 37) with 137438953472 in *. change (2 ^ 32) with 4294967296 in *.
  replace (st_t st + 2800 + 40) with (st_t st + 2840) in TS by lia.
  replace (st_t st + 2800 + 40) with (st_t st + 2840) in MU by lia. replace (st_t st + 2800 + 56) with (st_t st + 2856) in MU by lia.
  leaf_prep. subst tp.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?Q (MS ?R ?Fq _ ?fcq ?rv ?mq ?ro) =>
    assert (J : evt asegs Q (MS R Fq (Z_to_bv 64 0x342b8) fcq rv mq ro)) end.
  { lstep. (* [comment removed for export] *)
    call get_thread_stats_c; [exact LC| exact WF| eassumption| reflexivity| exact ST| idtac; lia| lia|].
    cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. restk. unfold T_STATS.
    lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
    lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep; try if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    if_cases K2; zify_cond K2.
    - qcr_sec_fin ST.
    - lstep. lstep; try if_lia. (* [comment removed for export] *)
      qcr_sec_fin ST. }
  lstep. (* [comment removed for export] *)
  if_cases K1; zify_cond K1.
  - lstep; try if_lia. (* [comment removed for export] *) exact J.
  - lstep. (* [comment removed for export] *) exact J.
Qed.




End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac cases_17_30 c :=
  let HH := fresh in
  assert (HH : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].
Ltac subfp := intros x Hx; cbn in Hx |- *; lia.
Ltac qcr_sec_fin ST :=
  lstep; lstep; lstep; 
  do 6 lstep; 
  lstep; lstep; 
  try rewrite unsigned_lit in * by lia;
  match goal with H : rw_cells _ _ (bv_unsigned ?spx) [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] |- _ => release_frame H ST (bv_unsigned spx + 48) end;
  finish; eassumption.
End RTW_q_qcr1.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_apz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_ms.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_rec2.
Module RTW_q_rec3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_car OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_zone2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_ms OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_q_drainw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_drain2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_bz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2.RTW_q_recw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2.RTW_q_merge1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2.RTW_q_merge2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2.RTW_q_merge3 RTW_q_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac qlia := unfold QBATCH_CAP, QBATCH_SIZE, AIMG_HI, KHIGHMEM_BEG, CEIL in *; idtac; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition slw_ok (iv : Z * Z) : Prop := CEIL <= fst iv \/ (A_QUAR + 152 <= fst iv /\ snd iv <= A_QUAR + 156).

Lemma far_keep0 : forall K v W m m', RTWF K -> In (qb_addr v) (qbatch_addrs K) -> munch W m m' -> wmono asegs m m' ->
  Forall slw_ok W ->
     (coreC K m -> coreC K m') /\ (R_alloc4 K m -> R_alloc4 K m') /\ (QA m -> QA m') /\ (QS m -> QS m')
  /\ (forall n f l b, QH4 m n f l b -> QH4 m' n f l b)
  /\ (R_threadx K m -> R_threadx K m') /\ (forall qt, TC K m qt -> TC K m' qt)
  /\ (R_live K m -> R_live K m') /\ (R_quar K m -> R_quar K m')
  /\ (forall q, (forall x, In x q -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP) -> R_qlist m q -> R_qlist m' q)
  /\ (forall cu, (forall bd, In bd cu -> In (qb_addr (fst bd)) (qbatch_addrs K) /\ 0 <= qb_count (fst bd) <= QBATCH_CAP) -> QCUR m cu -> QCUR m' cu).
Proof.
  intros K v W m m' WF Hv MU WM HW.
  pose proof (t_range K WF) as [T1 T2].
  assert (HWz : Forall (ucz_ok K 24 (bk K v)) W).
  { eapply Forall_impl; [| exact HW]. intros [lo' hi'] X. unfold slw_ok in X. unfold ucz_ok. cbn [fst snd] in *. lia. }
  pose proof (bzone_a K WF v Hv W HWz m m' MU WM) as (Zc & Za & Zt & Zl & Zq & Zrl & Zcu & Zqb).
  assert (D : forall a sz, a + sz <= A_QUAR + 152 \/ (A_QUAR + 156 <= a /\ a + sz <= CEIL) -> disjoint_from W a sz).
  { intros a sz Ha. apply (disjoint_from_forallq _ W a sz HW). intros lo' hi' X. unfold slw_ok in X. cbn [fst snd] in X. pose proof A_QUAR_val. unfold CEIL in *. lia. }
  assert (QB : forall x nxt, In (qb_addr x) (qbatch_addrs K) -> 0 <= qb_count x <= QBATCH_CAP -> QBC m x nxt -> QBC m' x nxt).
  { intros x nxt Hx Cx Q. destruct (Z.eq_dec (qb_addr x) (qb_addr v)) as [E|NE]; [| exact (Zqb x nxt Hx Cx NE Q)].
    pose proof (batch_facts_a K x WF Hx) as (G1 & G2 & G3 & G4).
    apply QBC_split in Q as [L R]. apply QBC_split. split.
    - eapply (rwT W m m' MU WM); [exact L|]. cbn. apply D. right. unfold A_QUAR, A_ALLOC, QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia.
    - apply (QBCx_keep_a K W m m' x WF MU WM Hx Cx R). eapply Forall_impl; [| exact HW]. intros [lo' hi'] X. unfold slw_ok in X.
      cbn [fst snd] in *. unfold A_QUAR, A_ALLOC, AIMG_HI in *. lia. }
  split; [exact Zc|]. split; [exact Za|].
  split; [intros X; apply (UZ_QA W m m' MU WM X); apply D; left; lia|].
  split; [intros X; apply (UZ_QS W m m' MU WM X); apply D; right; unfold A_QUAR, A_ALLOC, CEIL; lia|].
  split; [intros n f l b X; apply (UZ_QH4 W m m' MU WM n f l b X); apply D; right; unfold A_QUAR, A_ALLOC, CEIL; lia|].
  split; [exact Zt|].
  split; [intros qt X; apply (UZ_TC K W m m' MU WM qt X); apply D; unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, CEIL in *; clear - T1 T2; blia|].   (* [comment removed for export] *)
  split; [exact Zl|]. split; [exact Zq|].
  split.
  - intros q SUB RL. apply (qlist_far m m' q); [| exact RL]. intros x nxt Hx Q. destruct (SUB x Hx) as [U1 U2]. exact (QB x nxt U1 U2 Q).
  - intros cu SUB RC bd Hbd. destruct (RC bd Hbd) as [[nx HL] HS]. destruct (SUB bd Hbd) as [U1 U2].
    destruct (QB (fst bd) nx U1 U2 (conj HL HS)) as [HL' HS']. split; [exists nx; exact HL'| exact HS'].
Qed.

(* [comment removed for export] *)
Lemma qc_first_range : forall K l, RTWF K -> (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) ->
  l <> [] -> KHIGHMEM_BEG <= qc_first l /\ qc_first l + QBATCH_SIZE <= CEIL.
Proof.
  intros K l WF Hl NE. destruct l as [|x l]; [congruence|]. cbn [qc_first].
  pose proof (batch_facts_a K x WF (Hl x ltac:(left; reflexivity))) as (G1 & G2 & _). lia.
Qed.
Lemma qc_last_range : forall K l, RTWF K -> (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) ->
  l <> [] -> KHIGHMEM_BEG <= qc_last l /\ qc_last l + QBATCH_SIZE <= CEIL.
Proof.
  intros K l WF Hl NE. destruct (snoc_or_nil' l) as [->|(q & x & ->)]; [congruence|]. rewrite qc_last_snoc.
  pose proof (batch_facts_a K x WF (Hl x ltac:(apply in_or_app; right; left; reflexivity))) as (G1 & G2 & _). lia.
Qed.
Lemma qc_first0 : forall K l, RTWF K -> (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) -> 0 <= qc_first l < 2^64.
Proof.
  intros K l WF Hl. destruct l as [|x l']; [cbn; lia|].
  pose proof (qc_first_range K (x :: l') WF Hl ltac:(discriminate)). unfold KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *. lia.
Qed.
Lemma qc_last0 : forall K l, RTWF K -> (forall x, In x l -> In (qb_addr x) (qbatch_addrs K)) -> 0 <= qc_last l < 2^64.
Proof.
  intros K l WF Hl. destruct l as [|x l']; [cbn; lia|].
  pose proof (qc_last_range K (x :: l') WF Hl ltac:(discriminate)). unfold KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, CEIL in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RECF.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (mn lo : Z).
Hypothesis Hmn : 0 <= mn < 2^62.
Local Notation rinv := (ainv K [] []).

(* [comment removed for export] *)
Definition rec_mid (gp tp a2 a3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (vs4 vs3 vs2 vs1 vs0 vra : word) (m : word -> option byte) (sp0 : Z) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' s0' s1' a4' a5' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m' : word -> option byte)
                    (Wd : list (Z * Z)) (qg2 tmp2 : list qbatch),
      ms' = MS (mkR ra' (wz (sp0 - 80)) gp tp t0' t1' t2' s0' s1' (wz A_QUAR) (wz mn) a2 a3 a4' a5' (wz (zlen qg2)) a7'
                    s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz 0x33d68) fc None m' (seg_rom asegs)
      /\ rinv qg2 tmp2 /\ QX K m' 1 1 [] qg2 tmp2 [] /\ qg2 <> []
      /\ rw_cells asegs m' (sp0 - 80) (rec_frame (zlen tmp2) (qc_first tmp2) (qc_last tmp2) (qc_bytes tmp2) vs4 vs3 vs2 vs1 vs0 vra)
      /\ stk asegs m' lo (sp0 - 80) /\ mem_inv asegs m'
      /\ munch Wd m m' /\ Forall (dwin K lo sp0) Wd /\ wmono asegs m m'.

(* [comment removed for export] *)
Definition recf_post (gp tp a2 a3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (vs4 vs3 vs2 vs1 vs0 vra : word) (m : word -> option byte) (sp0 : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word) (m' : word -> option byte)
                    (Wd : list (Z * Z)) (qgF tmpF : list qbatch),
      ms' = MS (mkR (wz 0x33e1c) (wz (sp0 - 80)) gp tp t0' t1' t2' s0' s1' (wz A_QUAR) (wz (sp0 - 80)) a2 a3 a4' a5' a6' a7'
                    s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ADOREC) fc None m' (seg_rom asegs)
      /\ rinv qgF tmpF /\ QX K m' 0 0 [] qgF tmpF [] /\ qc_bytes qgF <= mn
      /\ rw_cells asegs m' (sp0 - 80) (rec_frame (zlen tmpF) (qc_first tmpF) (qc_last tmpF) (qc_bytes tmpF) vs4 vs3 vs2 vs1 vs0 vra)
      /\ stk asegs m' lo (sp0 - 80) /\ mem_inv asegs m'
      /\ munch Wd m m' /\ Forall (dwin K lo sp0) Wd /\ wmono asegs m m'.

Lemma rinv_facts : forall qg tmp, rinv qg tmp ->
     (forall x, In x qg -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP)
  /\ (forall x, In x tmp -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP)
  /\ qc_bytes qg + qc_bytes tmp < 2^61.
Proof.
  intros qg tmp PI. pose proof PI as (_ & _ & _ & BB).
  assert (G : forall x, In x ([] ++ qg ++ tmp ++ map fst (@nil (qbatch * Z))) -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP).
  { intros x Hx. split; [exact (ainv_addr K [] [] _ _ x PI Hx)| exact (ainv_cnt K [] [] _ _ x PI Hx)]. }
  cbn [map app] in G. rewrite app_nil_r in G.
  split; [intros x Hx; apply G; apply in_or_app; left; exact Hx|].
  split; [intros x Hx; apply G; apply in_or_app; right; exact Hx| exact BB].
Qed.

(* [comment removed for export] *)
Lemma rec_front_mid :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (qg : list qbatch),
  rinv qg [] ->
  QX K m 0 1 [] qg [] [] -> mem_inv asegs m ->
  a0 = wz A_QUAR -> a1 = wz mn -> mn < qc_bytes qg -> qc_bytes qg <= QREC_MAX ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 96 <= bv_unsigned sp -> bv_unsigned sp <= 2^64 ->
  evt asegs (rec_mid gp tp a2 a3 s5 s6 s7 s8 s9 s10 s11 F fc s4 s3 s2 s1 s0 ra m (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQREC) fc None m (seg_rom asegs)).
Proof.
  intros until qg. intros PI X MI Ha0 Ha1 HB HBM ST HCL LO SPH.
  pose proof X as (CO & A4 & XA & XL & XH & XS & TX & TCq & LV & QR & RL1 & RL2 & RL3 & RC).
  destruct XL as (lb2 & lb3 & j4 & QL & QJ). unfold QH4 in XH.
  pose proof (t_range K WF) as [T1 T2]. pose proof HCL as HCL0. idtac.
  destruct (rinv_facts qg [] PI) as (ALL & _ & BB). change (qc_bytes []) with 0 in BB.
  assert (QNE : qg <> []) by (intros ->; cbn in HB; lia).
  pose proof (qc_bytes_lb qg) as NBL. pose proof (zlen_nonneg qg) as ZL. pose proof (qc_bytes_nonneg qg) as B0.
  pose proof (qc_first0 K qg WF (fun x Hx => proj1 (ALL x Hx))) as GF.
  pose proof (qc_last0 K qg WF (fun x Hx => proj1 (ALL x Hx))) as GL.
  destruct qg as [|b1 qr]; [congruence|].
  assert (H1 : In (qb_addr b1) (qbatch_addrs K)) by (apply (proj1 (ALL b1 ltac:(left; reflexivity)))).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rec_pro_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (zlen (b1 :: qr)) (qc_first (b1 :: qr)) (qc_last (b1 :: qr)) (qc_bytes (b1 :: qr)) lo lb2 lb3);
      [exact MI| exact Ha0| lia| unfold QBATCH_SIZE in NBL; lia| lia| exact GF| exact GL| exact ST| exact HCL0| lia| exact QL| exact XH]. }
  cbv beta. intros ms1 (t0' & t1' & a7' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & QL1 & XH1).
  assert (HW1 : Forall slw_ok [(bv_unsigned sp - 80, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156)]).
  { unfold slw_ok. apply Forall_cons; [cbn [fst snd]; left; unfold CEIL in *; lia|]. apply Forall_cons; [cbn [fst snd]; right; lia| apply Forall_nil]. }
  pose proof (far_keep0 K b1 _ m m1 WF H1 MU1 WM1 HW1) as (Yc & Ya & Yqa & Yqs & Yqh & Yt & Ytc & Yl & Yq & Yrl & Ycu).
  assert (QJ1 : rw_cells asegs m1 (A_QUAR + 156) [CB 4 j4]).
  { eapply (rwT _ m m1 MU1 WM1); [exact QJ|]. cbn. unfold A_QUAR, A_ALLOC, CEIL in *. repeat split; lia. }
  assert (X1 : QX K m1 1 1 [] (b1 :: qr) [] []).
  { split; [exact (Yc CO)|]. split; [exact (Ya A4)|]. split; [exact (Yqa XA)|]. split; [exists lb2, lb3, j4; split; [exact QL1| exact QJ1]|].
    split; [exact XH1|]. split; [exact (Yqs XS)|]. split; [exact (Yt TX)|]. split; [exact (Ytc _ TCq)|].
    split; [exact (Yl LV)|]. split; [exact (Yq QR)|].
    split; [exact (Yrl [] ltac:(intros x Hx; destruct Hx) RL1)|]. split; [exact (Yrl _ ALL RL2)|].
    split; [exact (Yrl [] ltac:(intros x Hx; destruct Hx) RL3)| exact (Ycu [] ltac:(intros bd Hbd; destruct Hbd) RC)]. }
  assert (HWd1 : Forall (dwin K lo (bv_unsigned sp)) [(bv_unsigned sp - 80, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156)]).
  { unfold dwin. apply Forall_cons; [cbn [fst snd]; left; lia|]. apply Forall_cons; [cbn [fst snd]; right; left; lia| apply Forall_nil]. }
  clear Yc Ya Yqa Yqs Yqh Yt Ytc Yl Yq Yrl Ycu CO A4 XA XH XS TX TCq LV QR RL1 RL2 RL3 RC QL QJ.
  (* [comment removed for export] *)
  assert (DEC : (8192 * zlen (b1 :: qr) = qc_bytes (b1 :: qr) \/ zlen (b1 :: qr) * 1638400 <= qc_bytes (b1 :: qr) * 100)
                \/ (8192 * zlen (b1 :: qr) < qc_bytes (b1 :: qr) /\ qc_bytes (b1 :: qr) * 100 < zlen (b1 :: qr) * 1638400))
    by (unfold QBATCH_SIZE in NBL; lia).
  destruct DEC as [NOM|TOM].
  - (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rec_nomerge_spec ra _ gp tp _ _ t2 s0 s1 a0 a1 a2 a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                (zlen (b1 :: qr)) (qc_bytes (b1 :: qr))); [reflexivity| reflexivity| reflexivity| lia| unfold QBATCH_SIZE in NBL; lia| unfold QREC_MAX, QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in HBM; lia| exact NOM]. }
    cbv beta. intros ms2 (a4' & a5' & a7'' & ->).
    apply evt_done. unfold rec_mid. rewrite Ha0, Ha1.
    do 16 eexists. exists m1, [(bv_unsigned sp - 80, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156)], (b1 :: qr), [].
    split; [reflexivity|]. split; [exact PI|]. split; [exact X1|]. split; [exact QNE|].
    split; [exact FR1|]. split; [exact ST1|]. split; [exact MI1|]. split; [exact MU1|]. split; [exact HWd1| exact WM1].
  - (* [comment removed for export] *)
    destruct TOM as [TM1 TM2].
    eapply evt_cut.
    { eapply (rec_tomerge_spec ra _ gp tp _ _ t2 s0 s1 a0 a1 a2 a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                (zlen (b1 :: qr)) (qc_bytes (b1 :: qr))); [exact Ha0| reflexivity| reflexivity| reflexivity| lia| exact TM1| unfold QREC_MAX, QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in HBM; lia| exact TM2]. }
    cbv beta. intros ms2 (a4' & a5' & a7'' & ->).
    eapply evt_cut.
    { eapply (mg_full K WF [] [] lo (bv_unsigned sp) (wz 0x33d54) (wz (bv_unsigned sp - 80)) gp tp _ _ t2 _ a1 _ _ a2 a3 _ _ _ _ a0 a3 a2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                s4 s3 s2 s1 s0 ra F fc m1 (b1 :: qr) []);
        [exact PI| exact QNE| exact X1| exact MI1| reflexivity| reflexivity
        | cbv delta [wz]; rewrite unsigned_lit by lia; lia| exact HCL0
        | cbv delta [wz]; rewrite unsigned_lit by lia; lia| cbv delta [wz]; rewrite unsigned_lit by lia; lia| lia
        | cbv delta [wz]; rewrite unsigned_lit by lia; exact ST1| cbv delta [wz]; rewrite unsigned_lit by lia; exact FR1]. }
    cbv beta. intros ms3 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m2 & Wd2 & qg' & tmp' & -> & PI2 & X2 & NE2 & FR2 & MI2 & MU2 & HW2 & WM2).
    cbv delta [wz] in FR2. rewrite unsigned_lit in FR2 by lia.
    replace (ret_pc (wz 0x33d54)) with (wz 0x33d54 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof X2 as (CO2 & A42 & XA2 & XL2 & XH2 & XS2 & TX2 & TC2 & LV2 & QR2 & RL12 & RL22 & RL32 & RC2). unfold QH, QH4 in XH2.
    eapply evt_cut.
    { eapply (rec_aftermerge_spec (wz 0x33d54) _ gp tp _ _ _ _ a1 _ _ _ _ _ _ _ _ a0 a3 a2 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2
                (zlen qg') (qc_first qg') (qc_last qg') (qc_bytes qg')); [exact MI2| reflexivity| exact XH2]. }
    cbv beta. intros ms4 ->.
    apply evt_done. unfold rec_mid. rewrite Ha0, Ha1.
    do 16 eexists. exists m2, ([(bv_unsigned sp - 80, bv_unsigned sp); (A_QUAR + 152, A_QUAR + 156)] ++ Wd2), qg', tmp'.
    split; [reflexivity|]. split; [exact PI2|]. split; [exact X2|]. split; [exact NE2|].
    split; [exact FR2|].
    split; [eapply stk_wmono_noseg; [exact ST1| exact WM2| unfold AIMG_HI, CEIL in *; lia]|].
    split; [exact MI2|]. split; [eapply munch_cat; [exact MU1| exact MU2]|].
    split; [apply Forall_app; split; [exact HWd1| exact HW2]| eapply wmono_trans; [exact WM1| exact WM2]].
Qed.

(* [comment removed for export] *)
Theorem rec_front_full :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (qg : list qbatch),
  rinv qg [] ->
  QX K m 0 1 [] qg [] [] -> mem_inv asegs m ->
  a0 = wz A_QUAR -> a1 = wz mn -> mn < qc_bytes qg -> qc_bytes qg <= QREC_MAX ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 96 <= bv_unsigned sp -> bv_unsigned sp <= 2^64 ->
  evt asegs (recf_post gp tp a2 a3 s5 s6 s7 s8 s9 s10 s11 F fc s4 s3 s2 s1 s0 ra m (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQREC) fc None m (seg_rom asegs)).
Proof.
  intros until qg. intros PI X MI Ha0 Ha1 HB HBM ST HCL LO SPH.
  pose proof (t_range K WF) as [T1 T2]. pose proof HCL as HCL0. idtac.
  eapply evt_cut; [eapply rec_front_mid; eassumption|].
  cbv beta. intros ms1 (ra' & t0' & t1' & t2' & s0' & s1' & a4' & a5' & a7' & s2' & s3' & s4' & t3' & t4' & t5' & t6' & m1 & Wd1 & qg2 & tmp2
                        & -> & PI1 & X1 & NE1 & FR1 & ST1 & MI1 & MU1 & HW1 & WM1).
  destruct (rinv_facts qg2 tmp2 PI1) as (ALLg & ALLt & BB).
  pose proof (qc_bytes_nonneg qg2) as B0. pose proof (qc_bytes_nonneg tmp2) as BT0.
  pose proof X1 as (CO & A4 & XA & XL & XH & XS & TX & TCq & LV & QR & RL1 & RL2 & RL3 & RC). unfold QH, QH4 in XH.
  assert (SPR : bv_unsigned (wz (bv_unsigned sp - 80) : word) = bv_unsigned sp - 80) by (cbv delta [wz]; rewrite unsigned_lit by lia; reflexivity).
  (* [comment removed for export] *)
  eapply (evt_cut asegs (fun ms' => exists (t0'' t1'' t2'' a4'' a5'' a6'' a7'' : word) (m' : word -> option byte) (Wd : list (Z * Z)) (qgF tmpF : list qbatch),
      ms' = MS (mkR ra' (wz (bv_unsigned sp - 80)) gp tp t0'' t1'' t2'' s0' s1' (wz A_QUAR) (wz mn) a2 a3 a4'' a5'' a6'' a7''
                    s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz 0x33e04) fc None m' (seg_rom asegs)
      /\ rinv qgF tmpF /\ QX K m' 1 1 [] qgF tmpF [] /\ qc_bytes qgF <= mn
      /\ rw_cells asegs m' (bv_unsigned sp - 80) (rec_frame (zlen tmpF) (qc_first tmpF) (qc_last tmpF) (qc_bytes tmpF) s4 s3 s2 s1 s0 ra)
      /\ mem_inv asegs m' /\ munch Wd m1 m' /\ Forall (dwin K lo (bv_unsigned sp)) Wd /\ wmono asegs m1 m')).
  { destruct (Z_le_gt_dec (qc_bytes qg2) mn) as [LE|GT].
    - eapply evt_cut.
      { eapply (rec_nopop_spec ra' (wz (bv_unsigned sp - 80)) gp tp _ _ _ s0' s1' _ _ a2 a3 _ _ _ _ s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 _ _ _ _
                  s4 s3 s2 s1 s0 ra F fc m1 (zlen tmp2) (qc_first tmp2) (qc_last tmp2) (qc_bytes tmp2)
                  (zlen qg2) (qc_first qg2) (qc_last qg2) (qc_bytes qg2) mn);
          [exact MI1| reflexivity| reflexivity| lia| lia| exact LE| rewrite SPR; lia| rewrite SPR; exact FR1| exact XH]. }
      cbv beta. intros ms2 ->.
      apply evt_done. do 7 eexists. exists m1, [], qg2, tmp2.
      split; [reflexivity|]. split; [exact PI1|]. split; [exact X1|]. split; [exact LE|]. split; [exact FR1|].
      split; [exact MI1|]. split; [apply munch_refl|]. split; [apply Forall_nil| apply wmono_refl].
    - eapply evt_cut.
      { eapply (rec_popentry_spec ra' (wz (bv_unsigned sp - 80)) gp tp _ _ _ s0' s1' _ _ a2 a3 _ _ _ _ s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 _ _ _ _
                  s4 s3 s2 s1 s0 ra F fc m1 (zlen tmp2) (qc_first tmp2) (qc_last tmp2) (qc_bytes tmp2)
                  (zlen qg2) (qc_first qg2) (qc_last qg2) (qc_bytes qg2) mn);
          [exact MI1| reflexivity| reflexivity| lia| lia| lia| rewrite SPR; lia| rewrite SPR; exact FR1| exact XH]. }
      cbv beta. intros ms2 ->.
      eapply evt_cut.
      { eapply (pop_loop K WF [] [] mn lo (bv_unsigned sp) ltac:(lia) (length qg2)
                  ra' (wz (bv_unsigned sp - 80)) gp tp _ _ _ s0' s1' _ _ a2 a3 _ _ _ _ s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 _ _ _ _
                  s4 s3 s2 s1 s0 ra F fc m1 qg2 tmp2 (zlen tmp2) (qc_first tmp2) (qc_last tmp2));
          [lia| exact PI1| exact X1| exact MI1| lia| reflexivity| reflexivity| reflexivity| intros _; reflexivity| reflexivity| reflexivity
          | intros _; reflexivity| exact HCL0| rewrite SPR; lia| rewrite SPR; lia| exact SPH| rewrite SPR; exact FR1]. }
      cbv beta. intros ms3 (u0 & u1 & u2 & u4 & u5 & u6 & u7 & m2 & Wd2 & popped & qgF & -> & Eqg & LE & PI2 & X2 & FR2 & MI2 & MU2 & HW2 & WM2).
      rewrite SPR in FR2.
      apply evt_done. do 7 eexists. exists m2, Wd2, qgF, (tmp2 ++ popped).
      split; [reflexivity|]. split; [exact PI2|]. split; [exact X2|]. split; [exact LE|]. split; [exact FR2|].
      split; [exact MI2|]. split; [exact MU2|]. split; [exact HW2| exact WM2]. }
  cbv beta. intros ms2 (t0'' & t1'' & t2'' & a4'' & a5'' & a6'' & a7'' & m2 & Wd2 & qgF & tmpF & -> & PI2 & X2 & LE & FR2 & MI2 & MU2 & HW2 & WM2).
  clear CO A4 XA XL XH XS TX TCq LV QR RL1 RL2 RL3 RC.
  pose proof X2 as (CO & A4 & XA & XL & XH & XS & TX & TCq & LV & QR & RL1 & RL2 & RL3 & RC).
  destruct XL as (lb2 & lb3 & j4 & QL & QJ).
  destruct (rinv_facts qgF tmpF PI2) as (ALLg2 & ALLt2 & BB2).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rec_unlock_spec ra' (wz (bv_unsigned sp - 80)) gp tp _ _ _ s0' s1' _ _ a2 a3 _ _ _ _ s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 lb2 lb3);
      [exact MI2| reflexivity| exact QL]. }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & QL3).
  (* [comment removed for export] *)
  assert (HV : exists v, In (qb_addr v) (qbatch_addrs K)).
  { destruct (rinv_facts qg [] PI) as (ALL0 & _ & _). destruct qg as [|v l]; [cbn in HB; lia|].
    exists v. apply (proj1 (ALL0 v ltac:(left; reflexivity))). }
  destruct HV as (v & Hv).
  assert (HW3 : Forall slw_ok [(A_QUAR + 152, A_QUAR + 156)]).
  { unfold slw_ok. apply Forall_cons; [cbn [fst snd]; right; lia| apply Forall_nil]. }
  pose proof (far_keep0 K v _ m2 m3 WF Hv MU3 WM3 HW3) as (Yc & Ya & Yqa & Yqs & Yqh & Yt & Ytc & Yl & Yq & Yrl & Ycu).
  assert (QJ3 : rw_cells asegs m3 (A_QUAR + 156) [CB 4 j4]).
  { eapply (rwT _ m2 m3 MU3 WM3); [exact QJ|]. cbn. split; [lia| exact I]. }
  assert (X3 : QX K m3 0 0 [] qgF tmpF []).
  { split; [exact (Yc CO)|]. split; [exact (Ya A4)|]. split; [exact (Yqa XA)|]. split; [exists lb2, lb3, j4; split; [exact QL3| exact QJ3]|].
    split; [exact (Yqh _ _ _ _ XH)|]. split; [exact (Yqs XS)|]. split; [exact (Yt TX)|]. split; [exact (Ytc _ TCq)|].
    split; [exact (Yl LV)|]. split; [exact (Yq QR)|].
    split; [exact (Yrl [] ltac:(intros x Hx; destruct Hx) RL1)|]. split; [exact (Yrl _ ALLg2 RL2)|].
    split; [exact (Yrl _ ALLt2 RL3)| exact (Ycu [] ltac:(intros bd Hbd; destruct Hbd) RC)]. }
  assert (FR3 : rw_cells asegs m3 (bv_unsigned sp - 80) (rec_frame (zlen tmpF) (qc_first tmpF) (qc_last tmpF) (qc_bytes tmpF) s4 s3 s2 s1 s0 ra)).
  { eapply (rwT _ m2 m3 MU3 WM3); [exact FR2|]. cbn. unfold A_QUAR, A_ALLOC, CEIL in *. split; [lia| exact I]. }
  apply evt_done. unfold recf_post.
  do 16 eexists. exists m3, (Wd1 ++ Wd2 ++ [(A_QUAR + 152, A_QUAR + 156)]), qgF, tmpF.
  split; [reflexivity|]. split; [exact PI2|]. split; [exact X3|]. split; [exact LE|]. split; [exact FR3|].
  split; [eapply stk_wmono_noseg; [exact ST1| eapply wmono_trans; [exact WM2| exact WM3]| unfold AIMG_HI, CEIL in *; lia]|].
  split; [exact MI3|].
  split; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]|].
  split; [| eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]].
  apply Forall_app. split; [exact HW1|]. apply Forall_app. split; [exact HW2|].
  apply Forall_cons; [| apply Forall_nil]. unfold dwin. cbn [fst snd]. right. left. lia.
Qed.
End RECF.


End CeilWrap.
End RTW_q_rec3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_cd_stmt.
Module RTW_q_stmts2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_fresh OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_q_wf RTW_q_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_cd_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition AQCR_STACK : Z := 2048.

(* [comment removed for export] *)
Definition qblock (st : rtstate) (A n : Z) : Prop := In (A, n) (qelems st) \/ In (A, n) (st_qpend st).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition qcrec_rel (st st' : rtstate) (b : qbatch) (d : Z) : Prop :=
  same_but_quarantine st st'
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_qtmp st' = st_qtmp st /\ st_qpend st' = st_qpend st
  /\ st_qcur st' = [(b, d + 1)]
  /\ (forall c, 0 <= c < KNUMCLASSES -> fresh_cls st c -> fresh_cls st' c).

Definition qcrec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (b : qbatch) (d lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        qcrec_rel st st' b d
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'      (* [comment removed for export] *)
        /\ gmono g g' /\ budget_ok st g st' g' 0).

(* [comment removed for export] *)
Definition qcr_slot_spec (prim : bool) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (b : qbatch) (d A n cbA S lo : Z),
  RTS st m mo g ->
  st_qcur st = [(b, d)] -> 0 <= d < qb_count b -> nthz (qb_elems b) d (0, 0) = (A, n) -> bprim n = prim ->
  st_apend st = [] ->
  a0 = wz cbA -> a1 = wz (b_chunk_beg A) -> tp = wz ATP ->
  bv_unsigned sp <= cbA -> cbA + 16 <= st_sp0 st ->
  rw_cells asegs m cbA [W8 (acache st); W8 S] ->
  rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AQCR_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (qcrec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st b d lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AQCR) fc None m (seg_rom asegs)) mo g.
Definition qcr_prim_spec : Prop := qcr_slot_spec true.
Definition qcr_sec_spec : Prop := qcr_slot_spec false.

(* [comment removed for export] *)
Definition qcrp_rel (st st' : rtstate) (A n : Z) : Prop :=
  same_but_quarantine st st'
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st
  /\ st_qpend st' = remove_first ck_eqb (A, n) (st_qpend st)
  /\ (forall c, 0 <= c < KNUMCLASSES -> fresh_cls st c -> fresh_cls st' c).

Definition qcrp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (A n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        qcrp_rel st st' A n
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'      (* [comment removed for export] *)
        /\ gmono g g' /\ budget_ok st g st' g' 0).

Definition qcr_pend_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n cbA S lo : Z),
  RTS st m mo g ->
  In (A, n) (st_qpend st) -> bprim n = false ->
  a0 = wz cbA -> a1 = wz (b_chunk_beg A) -> tp = wz ATP ->
  bv_unsigned sp <= cbA -> cbA + 16 <= st_sp0 st ->
  rw_cells asegs m cbA [W8 (acache st); W8 S] ->
  rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AQCR_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (qcrp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AQCR) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition qcr_carve_stmt : Prop :=
  forall st m A n, RTWF st -> RTREP st m -> qblock st A n ->
  exists (j1 j2 j3 : list byte) (b1 : byte) (cid f1 f2 : word),
     rw_cells asegs m A_ALLOC (alloc_cells (st_pbase st) (st_spacebeg st) j1 j2 j3)
  /\ rw_cells asegs m (b_chunk_beg A) (hdr_cells CHUNK_QUARANTINE n b1 cid) /\ hdr_b1_ok (bv_unsigned b1)
  /\ rw_cells asegs m (st_t st + T_STATS + 40) [C8 f1; C8 f2]
  /\ leafc st m /\ icpt_cells m /\ poison_cells m
  /\ 0 <= n < 2^40 /\ A mod 16 = 0
  /\ ablk (b_lo A n) (b_hi A n) /\ b_lo A n <= b_chunk_beg A /\ A + usz n <= b_hi A n /\ b_hi A n <= CEIL   (* [comment removed for export] *)
  /\ (b_hi A n <= st_t st \/ st_t st + 4096 <= b_lo A n)
  /\ KHIGHMEM_BEG <= st_spacebeg st /\ st_spacebeg st + KSPACESIZE + 4096 <= alloc_ceiling /\ st_spacebeg st mod 4096 = 0
  /\ oclr (st_t st) (st_t st + 4096) /\ st_t st + 4096 <= CEIL.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition qcr_carve_prim_stmt : Prop :=
  forall st m A n, RTWF st -> RTREP st m -> In (A, n) (qelems st) -> bprim n = true ->
  let c := pclass n in let k := b_cptr st A n in let p := b_alloc_beg A n in let S := st_spacebeg st in
  exists (junk : list byte),
     1 <= c <= 30 /\ p = cptr_addr st c k /\ p = b_lo A n /\ b_hi A n = p + csize c /\ 16 <= rz_size n /\ p = A - rz_size n
  /\ S + c * KREGIONSIZE <= p /\ p + csize c <= S + (c + 1) * KREGIONSIZE
  /\ (exists idx, 0 <= idx /\ p = S + c * KREGIONSIZE + idx * csize c /\ idx * csize c + csize c <= r_mapped (rg st c))
  /\ 0 <= r_mapped (rg st c) <= KFREEARRAY_OFF
  /\ rw_cells asegs m (S + KSPACESIZE + 128 * c + 48) [W8 (r_mapped (rg st c))]
  /\ (16 < rz_size n -> rw_cells asegs m p [W8 KALLOCBEG_MAGIC; W8 (b_chunk_beg A)])
  /\ rw_cells asegs m (SH A) [CB (Z.to_nat ((usz n + 7) / 8 * 8 / 8)) junk]
  /\ A mod 8 = 0 /\ app_range A ((usz n + 7) / 8 * 8) /\ 8 <= (usz n + 7) / 8 * 8.

(* [comment removed for export] *)
Definition qcr_carve_sec_stmt : Prop :=
  forall st m A n, RTWF st -> RTREP st m -> qblock st A n -> bprim n = false ->
  let mb := b_map_beg A in let S := st_spacebeg st in
     In (mb, n) (st_sec st) /\ A = sec_user mb
  /\ sec_alloc_beg mb <= b_chunk_beg A < mb + smapsize n
  /\ (b_chunk_beg A < S \/ S + KSPACESIZE <= b_chunk_beg A)
  /\ (sec_alloc_beg mb < S \/ S + KSPACESIZE <= sec_alloc_beg mb) /\ 0 < sec_alloc_beg mb < 2^64
  /\ 16 <= b_chunk_beg A /\ b_chunk_beg A + 16 <= alloc_ceiling
  /\ (b_chunk_beg A + 16 <= st_t st \/ st_t st + 4096 <= b_chunk_beg A)
  /\ 0 <= S /\ S + KSPACESIZE <= 2^64.

(* [comment removed for export] *)
Definition qcz_ok (st : rtstate) (A n : Z) (iv : Z * Z) : Prop :=
     (b_lo A n <= fst iv /\ snd iv <= b_hi A n)                                 (* [comment removed for export] *)
  \/ (SH A <= fst iv /\ snd iv <= SH A + (usz n + 7) / 8 * 8 / 8)              (* [comment removed for export] *)
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)          (* [comment removed for export] *)
  \/ CEIL <= fst iv.                                                            (* [comment removed for export] *)

Definition RTREP_qchunk_stmt : Prop :=
  forall st m m' W b d A n,
  RTWF st -> RTREP st m ->
  st_qcur st = [(b, d)] -> 0 <= d < qb_count b -> nthz (qb_elems b) d (0, 0) = (A, n) -> bprim n = true -> st_apend st = [] ->
  munch W m m' -> wmono asegs m m' -> Forall (qcz_ok st A n) W ->
  rw_cells asegs m' (SH A) [CB (Z.to_nat ((usz n + 7) / 8 * 8 / 8)) (repeat (Z_to_bv 8 SV_HEAP_LEFT_RZ) (Z.to_nat ((usz n + 7) / 8 * 8 / 8)))] ->
  RTREP (st_qchunk st (pclass n) (b_cptr st A n)) m'.

(* [comment removed for export] *)
Definition secw_ok (st : rtstate) (iv : Z * Z) : Prop :=
     CEIL <= fst iv
  \/ (st_t st + T_STATS <= fst iv /\ snd iv <= st_t st + T_UNWINDING)
  \/ (A_SECONDARY + 616 <= fst iv /\ snd iv <= A_SECONDARY + 620).

Definition RTREP_keepS_stmt : Prop :=
  forall st m m' W, RTWF st -> RTREP st m -> munch W m m' -> wmono asegs m m' -> Forall (secw_ok st) W ->
  (exists j, rw_cells asegs m' (A_SECONDARY + 616) [W1 0; CB 3 j]) ->
  RTREP st m'.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_qchunk_eq : forall st b d c k, st_qcur st = [(b, d)] ->
  st_qchunk st c k = q_set st (st_qthread st) (st_qglobal st) ((c, k) :: st_apend st) (st_qpend st) (st_qtmp st) [(b, d + 1)].
Proof. intros st b d c k HC. unfold st_qchunk. rewrite HC. reflexivity. Qed.

Section QCHUNK_ABS.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (b : qbatch) (d A n : Z).
Hypothesis HC : st_qcur st = [(b, d)].
Hypothesis HD : 0 <= d < qb_count b.
Hypothesis HE : nthz (qb_elems b) d (0, 0) = (A, n).
Hypothesis HP : bprim n = true.
Hypothesis HAPE : st_apend st = [].
Let c := pclass n.
Let k := b_cptr st A n.
Let st1 := st_qchunk st c k.

Lemma RTWF_qchunk' : RTWF st1.
Proof.
  pose proof (wf_quar_ok st WF) as WQ.
  assert (Wq : RTWFq st1).
  { subst st1 c k. destruct st. eapply RTWFq_qchunk; try eassumption. apply RTWFq_of. exact WF. }
  apply RTWF_ofq; [exact Wq| |].
  - subst st1. rewrite (st_qchunk_eq st b d c k HC), (proj1 (q_set_fields st _ _ _ _ _ _)). exact (wq_thread_max st WQ).
  - subst st1. rewrite (st_qchunk_eq st b d c k HC), (proj1 (proj2 (q_set_fields st _ _ _ _ _ _))). exact (wq_global_max st WQ).
Qed.

Lemma rt_prov_qchunk' : rt_prov st1 = rt_prov st.
Proof. subst st1 c k. destruct st. eapply rt_prov_qchunk; try eassumption. Qed.

Lemma RTMODEL_qchunk' : forall mo, RTMODEL st mo -> RTMODEL st1 mo.
Proof. intros mo H. subst st1. rewrite (st_qchunk_eq st b d c k HC). apply RTMODEL_q_set. exact H. Qed.
Lemma GWIN_qchunk' : forall m mo g, GWIN st m mo g -> GWIN st1 m mo g.
Proof. intros m mo g H. subst st1. rewrite (st_qchunk_eq st b d c k HC). apply GWIN_q_set. exact H. Qed.
Lemma SWIN_qchunk' : forall g, SWIN st g -> SWIN st1 g.
Proof. intros g H. subst st1. rewrite (st_qchunk_eq st b d c k HC). apply SWIN_q_set. exact H. Qed.

Lemma qchunk_fields : st_qcur st1 = [(b, d + 1)] /\ st_apend st1 = [(c, k)] /\ st_qpend st1 = st_qpend st
  /\ st_qthread st1 = st_qthread st /\ st_qglobal st1 = st_qglobal st /\ st_qtmp st1 = st_qtmp st.
Proof.
  subst st1. rewrite (st_qchunk_eq st b d c k HC), HAPE.
  pose proof (q_set_fields st (st_qthread st) (st_qglobal st) [(c, k)] (st_qpend st) (st_qtmp st) [(b, d + 1)]) as (F1 & F2 & F3 & F4 & F5 & F6).
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma qchunk_same :
  st_sp0 st1 = st_sp0 st /\ st_pbase st1 = st_pbase st /\ st_spacebeg st1 = st_spacebeg st /\ st_regions st1 = st_regions st
  /\ st_cache_inited st1 = st_cache_inited st /\ st_cache st1 = st_cache st /\ st_pa st1 = st_pa st /\ st_nreserved st1 = st_nreserved st
  /\ st_sec st1 = st_sec st /\ st_depot st1 = st_depot st /\ st_trs st1 = st_trs st /\ st_trs0 st1 = st_trs0 st
  /\ st_fs st1 = st_fs st /\ st_hints st1 = st_hints st /\ st_lf st1 = st_lf st /\ st_t st1 = st_t st /\ st_ctx st1 = st_ctx st
  /\ st_tls st1 = st_tls st /\ st_loose0 st1 = st_loose0 st /\ st_ia_inited st1 = st_ia_inited st /\ st_lb st1 = st_lb st
  /\ st_spend st1 = st_spend st.
Proof. subst st1. rewrite (st_qchunk_eq st b d c k HC). destruct st. repeat split; reflexivity. Qed.

Lemma acache_qchunk' : acache st1 = acache st.
Proof. unfold acache. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 qchunk_same)))))))))))))))). reflexivity. Qed.
Lemma cptr_addr_qchunk' : forall c' k', cptr_addr st1 c' k' = cptr_addr st c' k'.
Proof. intros. subst st1. rewrite (st_qchunk_eq st b d c k HC). destruct st. reflexivity. Qed.
Lemma fresh_cls_qchunk' : forall c', fresh_cls st1 c' <-> fresh_cls st c'.
Proof. intros. subst st1. rewrite (st_qchunk_eq st b d c k HC). destruct st. split; intros H; exact H. Qed.
End QCHUNK_ABS.

(* [comment removed for export] *)
Lemma qblock_not_fresh : forall st A n, RTWF st -> qblock st A n -> bprim n = true -> ~ fresh_cls st (pclass n).
Proof.
  intros st A n WF HQ HP HF.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; destruct HQ; tauto).
  pose proof (block_geom st WF A n HB) as (_ & _ & G1 & G2 & G3 & G4 & _ & _ & _ & GP & _).
  destruct (GP HP) as (CR & R1 & R2 & _ & _ & R3).
  pose proof (fresh_cls_facts st (pclass n) HF) as (_ & RM & _).
  pose proof (csize_pos (pclass n) ltac:(lia)). unfold usz in *. lia.
Qed.

Lemma ru8_le : forall u d, u <= d -> d mod 8 = 0 -> (u + 7) / 8 * 8 <= d.
Proof. intros u d H M. Z.div_mod_to_equations. lia. Qed.
Lemma ru8_ge : forall u, u <= (u + 7) / 8 * 8 /\ ((u + 7) / 8 * 8) mod 8 = 0 /\ (u + 7) / 8 * 8 / 8 = (u + 7) / 8.
Proof. intros u. split; [Z.div_mod_to_equations; lia|]. split; [apply Z_mod_mult| apply Z.div_mul; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wstatic_not_client' : forall st SP a, RTWF st -> CEIL <= SP -> 0xa6c18 <= a < 0x5cc8d0 ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros st SP a WF HSP Ha HC. unfold CEIL in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H.
    destruct H as [H|[H|(H1 & H2 & H3)]]; [lia| lia|]. apply H2. exists 0xa6c18, 0x5cc8d0. split; [right; left; reflexivity| lia].
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n HB) as (_ & _ & X0 & X & Y & _). unfold usz, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    change FS_FRAMES_OFF with 36864 in X. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [blia|].
    pose proof (rt_SH_bounds F ltac:(blia)) as B. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.

Section CLIQC.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.

Lemma qblock_shadow_not_client : forall A n a, qblock st A n ->
  SH (b_lo A n) <= a < SH (b_hi A n) -> ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros A n a HQ Ha HCa.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; destruct HQ; tauto).
  pose proof (block_geom st WF A n HB) as (_ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (ablk_shad_lin _ _ G1 ltac:(unfold usz in *; lia)) as [S1 S1']. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in S1, S1'.   (* [comment removed for export] *)
  pose proof (rt_SH_mono (b_hi A n) (@CEIL ACEIL) ltac:(unfold CEIL; lia)) as S2. rewrite SH_CEIL in S2.
  destruct HCa as [H|[H|[(A' & n' & Hb & Hr)|[(F & j & Hb & Hr)|H]]]].
  - unfold CEIL in *. lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI in *. lia.
  - assert (HB' : In (A', n') (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A' n' HB') as (_ & _ & X0 & X & Y & _). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F j Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    pose proof (loose_blockfree st WF _ _ (wb_fs_loose st (wf_base_ok st WF)) A n HB) as D.
    change FS_FRAMES_OFF with 36864 in X. unfold FS_TOTAL in *.
    destruct Hr as [Hr|Hr]; [unfold KHIGHMEM_BEG, AIMG_HI in *; blia|].
    rewrite <- (rt_SH_aligned_add F (fsz j) AL) in Hr.
    destruct D as [D|D].
    + pose proof (rt_SH_mono (F + fsz j) (b_lo A n) ltac:(lia)). lia.
    + pose proof (rt_SH_mono (b_hi A n) F ltac:(lia)). lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.

Lemma cli_pres_qcz : forall A n W m m', qblock st A n ->
  munch W m m' -> wmono asegs m m' -> Forall (qcz_ok st A n) W -> (forall iv, In iv W -> CEIL <= fst iv -> snd iv <= SP) ->
  cli_pres st SP m m'.
Proof.
  intros A n W m m' HQ MU WM HW HS. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; destruct HQ; tauto).
  pose proof (block_geom st WF A n HB) as (_ & AA & G1 & G2 & G3 & G4 & AL & AH & _).
  pose proof (rt_SH_mono (b_lo A n) A ltac:(lia)) as M1.
  assert (M2 : SH A + (usz n + 7) / 8 * 8 / 8 <= SH (b_hi A n)).
  { assert (A8 : A mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia| lia| reflexivity| exact AA]).
    rewrite <- (rt_SH_aligned_add A ((usz n + 7) / 8 * 8) A8). apply rt_SH_mono.
    pose proof (ru8_le (usz n) (b_hi A n - A) ltac:(lia)) as R.
    assert (D8 : (b_hi A n - A) mod 8 = 0).
    { apply (mod0_trans _ 8 16); [lia| lia| reflexivity|]. rewrite Zminus_mod, AH, AA. reflexivity. }
    specialize (R D8). lia. }
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold qcz_ok in A1. cbn [fst snd] in A1. cbn.
  split; [| apply IH; [exact (Forall_inv_tail HW)| intros iv Hiv; apply HS; right; exact Hiv]].
  intros Hin. destruct A1 as [A1|[A1|[A1|A1]]].
  - apply (qchunk_not_client st WF A n HQ SP HSP a); [lia| exact HC].
  - apply (qblock_shadow_not_client A n a HQ); [lia| exact HC].
  - apply (tpage_not_client st WF SP HSP a); [unfold T_STATS, T_UNWINDING, T_ACACHE in *; lia| exact HC].
  - pose proof (HS (lo, hi) ltac:(left; reflexivity) A1). apply (below_sp_not_client st WF SP a); [cbn [fst snd] in *; lia| exact HC].
Qed.

Lemma cli_pres_secw : forall W m m',
  munch W m m' -> wmono asegs m m' -> Forall (secw_ok st) W -> (forall iv, In iv W -> CEIL <= fst iv -> snd iv <= SP) ->
  cli_pres st SP m m'.
Proof.
  intros W m m' MU WM HW HS. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold secw_ok in A1. cbn [fst snd] in A1. cbn.
  split; [| apply IH; [exact (Forall_inv_tail HW)| intros iv Hiv; apply HS; right; exact Hiv]].
  intros Hin. destruct A1 as [A1|[A1|A1]].
  - pose proof (HS (lo, hi) ltac:(left; reflexivity) A1). apply (below_sp_not_client st WF SP a); [cbn [fst snd] in *; lia| exact HC].
  - apply (tpage_not_client st WF SP HSP a); [unfold T_STATS, T_UNWINDING, T_ACACHE in *; lia| exact HC].
  - apply (wstatic_not_client' st SP a WF HSP); [unfold A_SECONDARY, A_ALLOC in A1; lia| exact HC].
Qed.
End CLIQC.


End CeilWrap.
End RTW_q_stmts2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_spz.
Module RTW_q_rep3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_rep RTW_q_stmts RTW_q_stmts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.RTW_m_lbz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma st_qstart_eq : forall st b r, st_qtmp st = b :: r ->
  st_qstart st = q_set st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)].
Proof. intros st b r HT. unfold st_qstart. rewrite HT. reflexivity. Qed.

Section QSTART_ABS.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (b : qbatch) (r : list qbatch).
Hypothesis HT : st_qtmp st = b :: r.
Hypothesis HC : st_qcur st = [].
Let st1 := st_qstart st.

Lemma RTWF_qstart' : RTWF st1.
Proof.
  pose proof (wf_quar_ok st WF) as WQ.
  assert (Wq : RTWFq st1).
  { subst st1. destruct st. eapply RTWFq_qstart; try eassumption. apply RTWFq_of. exact WF. }
  apply RTWF_ofq; [exact Wq| |].
  - subst st1. rewrite (st_qstart_eq st b r HT), (proj1 (q_set_fields st _ _ _ _ _ _)). exact (wq_thread_max st WQ).
  - subst st1. rewrite (st_qstart_eq st b r HT), (proj1 (proj2 (q_set_fields st _ _ _ _ _ _))). exact (wq_global_max st WQ).
Qed.

Lemma rt_prov_qstart' : rt_prov st1 = rt_prov st.
Proof. subst st1. destruct st. eapply rt_prov_qstart; try eassumption. Qed.
End QSTART_ABS.

Lemma RTREP_qstart : forall st m b r, RTREP st m -> st_qtmp st = b :: r -> st_qcur st = [] -> RTREP (st_qstart st) m.
Proof.
  intros st m b r HR HT HC. rewrite (st_qstart_eq st b r HT).
  destruct HR as [HL HCo HA HRI HRG HAV HCA HTh HLV [Q1 Q2] (B1 & B2 & B3 & B4) HP HD HF HIA HLS].
  rewrite HT in B3. cbn [R_qlist] in B3. destruct B3 as (BC & BS & B3).
  assert (RQ : R_quar (q_set st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]) m).
  { split.
    - intros A' n' Hin'. rewrite qelems_q_set in Hin'. cbn [flat_map fst snd Z.to_nat skipn] in Hin'. rewrite app_nil_r in Hin'.
      assert (Hin0 : In (A', n') (qelems st)).
      { unfold qelems. rewrite HT, HC. cbn [flat_map]. rewrite app_nil_r. rewrite !flat_map_app' in *. cbn [flat_map]. rewrite !in_app_iff in *. tauto. }
      pose proof (Q1 A' n' Hin0) as RB. destruct st; exact RB.
    - intros A' n' Hin'. rewrite (proj1 (proj2 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _))))) in Hin'.
      pose proof (Q2 A' n' Hin') as RB. destruct st; exact RB. }
  assert (RB : R_batches (q_set st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]) m).
  { unfold R_batches.
    destruct (q_set_fields st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]) as (F1 & F2 & F3 & F4 & F5 & F6).
    rewrite F1, F2, F5, F6. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    intros bd [<-|[]]. cbn [fst]. split; [exists (qc_first r); exact BC| exact BS]. }
  assert (RV : R_avail (q_set st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]) m).
  { intros c' k' Hc' Hin'. rewrite q_set_cptr_addr. rewrite q_set_avail in Hin'.
    unfold apend_cptrs in Hin'. rewrite (proj1 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _)))) in Hin'. exact (HAV c' k' Hc' Hin'). }
  clear Q1 Q2 B1 B2 B3 B4 BC BS HAV. destruct st. constructor; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QBATCH_ABS.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (b : qbatch) (kb : Z).
Hypothesis HC : st_qcur st = [(b, qb_count b)].
Hypothesis HK : qb_addr b = cptr_addr st 24 kb.
Hypothesis HAPE : st_apend st = [].
Let st1 := st_qbatch st kb.

Lemma RTWF_qbatch' : RTWF st1.
Proof.
  pose proof (wf_quar_ok st WF) as WQ.
  assert (Wq : RTWFq st1).
  { subst st1. destruct st. eapply RTWFq_qbatch; try eassumption. apply RTWFq_of. exact WF. }
  apply RTWF_ofq; [exact Wq| |].
  - subst st1. unfold st_qbatch. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). exact (wq_thread_max st WQ).
  - subst st1. unfold st_qbatch. rewrite (proj1 (proj2 (q_set_fields st _ _ _ _ _ _))). exact (wq_global_max st WQ).
Qed.

Lemma rt_prov_qbatch' : rt_prov st1 = rt_prov st.
Proof. subst st1. destruct st. eapply rt_prov_qbatch; try eassumption. Qed.

Lemma qbatch_fields : st_qcur st1 = [] /\ st_apend st1 = [(24, kb)] /\ st_qpend st1 = st_qpend st
  /\ st_qthread st1 = st_qthread st /\ st_qglobal st1 = st_qglobal st /\ st_qtmp st1 = st_qtmp st.
Proof.
  subst st1. unfold st_qbatch. rewrite HAPE.
  pose proof (q_set_fields st (st_qthread st) (st_qglobal st) [(24, kb)] (st_qpend st) (st_qtmp st) []) as (F1 & F2 & F3 & F4 & F5 & F6).
  repeat split; assumption.
Qed.
End QBATCH_ABS.

Lemma RTREP_qbatch : forall st m b kb, RTREP st m -> st_qcur st = [(b, qb_count b)] -> qb_addr b = cptr_addr st 24 kb ->
  RTREP (st_qbatch st kb) m.
Proof.
  intros st m b kb HR HC HK. unfold st_qbatch.
  destruct HR as [HL HCo HA HRI HRG HAV HCA HTh HLV [Q1 Q2] (B1 & B2 & B3 & B4) HP HD HF HIA HLS].
  destruct (B4 (b, qb_count b) ltac:(rewrite HC; left; reflexivity)) as (_ & _ & _ & BSH). cbn [fst] in BSH.
  assert (RQ : R_quar (q_set st (st_qthread st) (st_qglobal st) ((24, kb) :: st_apend st) (st_qpend st) (st_qtmp st) []) m).
  { split.
    - intros A' n' Hin'. rewrite qelems_q_set in Hin'. cbn [flat_map] in Hin'. rewrite app_nil_r in Hin'.
      assert (Hin0 : In (A', n') (qelems st)) by (unfold qelems; apply in_or_app; left; exact Hin').
      pose proof (Q1 A' n' Hin0) as RB. destruct st; exact RB.
    - intros A' n' Hin'. rewrite (proj1 (proj2 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _))))) in Hin'.
      pose proof (Q2 A' n' Hin') as RB. destruct st; exact RB. }
  assert (RB : R_batches (q_set st (st_qthread st) (st_qglobal st) ((24, kb) :: st_apend st) (st_qpend st) (st_qtmp st) []) m).
  { unfold R_batches.
    destruct (q_set_fields st (st_qthread st) (st_qglobal st) ((24, kb) :: st_apend st) (st_qpend st) (st_qtmp st) []) as (F1 & F2 & F3 & F4 & F5 & F6).
    rewrite F1, F2, F5, F6. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. intros bd []. }
  assert (RV : R_avail (q_set st (st_qthread st) (st_qglobal st) ((24, kb) :: st_apend st) (st_qpend st) (st_qtmp st) []) m).
  { intros c' k' Hc' Hin'. rewrite q_set_cptr_addr. rewrite q_set_avail in Hin'.
    unfold apend_cptrs in Hin'. rewrite (proj1 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _)))) in Hin'.
    cbn [List.filter fst] in Hin'. destruct (24 =? c') eqn:EC.
    - apply Z.eqb_eq in EC. subst c'. cbn [map snd] in Hin'. apply in_app_iff in Hin' as [H|[<-|H]].
      + apply HAV; [exact Hc'| apply in_or_app; left; exact H].
      + rewrite <- HK. exact BSH.
      + apply HAV; [exact Hc'| apply in_or_app; right; exact H].
    - apply HAV; [exact Hc'| exact Hin']. }
  clear Q1 Q2 B1 B2 B3 B4 BSH HAV. destruct st. constructor; assumption.
Qed.

End CeilWrap.
End RTW_q_rep3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_q_qcr.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_cd_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs RTW_q_stmts RTW_q_stmts2 RTW_q_qcr1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcur_in_qelems : forall st b d A n,
  st_qcur st = [(b, d)] -> 0 <= d < qb_count b -> nthz (qb_elems b) d (0, 0) = (A, n) -> In (A, n) (qelems st).
Proof.
  intros st b d A n HC HD HE. unfold qelems. rewrite HC. cbn [flat_map fst snd]. rewrite app_nil_r.
  rewrite (skipn_nthz_cons (qb_elems b) d (A, n) (0, 0)); [| exact HD| exact HE].
  apply in_or_app. right. left. reflexivity.
Qed.

Lemma disjoint_from_app : forall W1 W2 a len, disjoint_from W1 a len -> disjoint_from W2 a len -> disjoint_from (W1 ++ W2) a len.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a len H1 H2; [exact H2|]. cbn in *. split; [tauto| apply IH; tauto]. Qed.

Lemma leafc_qchunk : forall st b d c k m, st_qcur st = [(b, d)] -> leafc (st_qchunk st c k) m -> leafc st m.
Proof. intros st b d c k m H L. rewrite (st_qchunk_eq st b d c k H) in L. destruct st. exact L. Qed.

(* [comment removed for export] *)
Definition bsz (A n SP : Z) (iv : Z * Z) : Prop :=
  (b_lo A n <= fst iv /\ snd iv <= b_hi A n) \/ (CEIL <= fst iv /\ snd iv <= SP).

Section BSZ.
Variables (st : rtstate) (A n SP : Z).
Hypothesis K : ablk (b_lo A n) (b_hi A n).
Hypothesis LE : b_lo A n <= b_hi A n.
Hypothesis HSP : CEIL <= SP.
Lemma bsz_qcz : forall W, Forall (bsz A n SP) W -> Forall (qcz_ok st A n) W.
Proof. intros W H. eapply Forall_impl; [| exact H]. intros [lo hi] [X|X]; unfold qcz_ok; cbn [fst snd] in *; [left; exact X| right; right; right; tauto]. Qed.
Lemma bsz_stk : forall W, Forall (bsz A n SP) W -> forall iv, In iv W -> CEIL <= fst iv -> snd iv <= SP.
Proof.
  intros W H iv Hin HC. pose proof (proj1 (Forall_forall _ _) H iv Hin) as [X|X]; [| tauto].
  pose proof (ablk_top _ _ K). unfold CEIL in *. lia.
Qed.
Lemma bsz_high : forall W, Forall (bsz A n SP) W -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W.
Proof.
  intros W H. eapply Forall_impl; [| exact H]. intros [lo hi] [X|X]; cbn [fst snd] in *; pose proof (ablk_img _ _ K); pose proof (ablk_top _ _ K); unfold CEIL in *; lia.
Qed.
(* [comment removed for export] *)
Lemma bsz_sh : forall W a len, Forall (bsz A n SP) W -> SH (b_lo A n) <= a -> a + len <= SH (b_hi A n) -> disjoint_from W a len.
Proof.
  intros W a len H Ha Hl. apply (disjoint_from_forallq _ W a len H). intros lo hi [X|X]; cbn [fst snd] in X.
  - destruct (ablk_shad_disj _ _ K LE) as [D|D]; [right; lia|]. left. pose proof (rt_SH_mono (b_hi A n) (b_hi A n + 7) ltac:(lia)). lia.
  - left. pose proof (ablk_shad_lin _ _ K LE) as [_ S2]. unfold KHIGHMEM_BEG, CEIL in *. lia.
Qed.
(* [comment removed for export] *)
Lemma bsz_out : forall W a len, Forall (bsz A n SP) W -> (a + len <= b_lo A n \/ b_hi A n <= a) -> (a + len <= CEIL \/ SP <= a) -> disjoint_from W a len.
Proof.
  intros W a len H H1 H2. apply (disjoint_from_forallq _ W a len H). intros lo hi [X|X]; cbn [fst snd] in X; lia.
Qed.
End BSZ.

Section QCR.
Hypothesis CARVE : qcr_carve_stmt.
Hypothesis CARVEP : qcr_carve_prim_stmt.
Hypothesis CARVES : qcr_carve_sec_stmt.
Hypothesis REPQ : RTREP_qchunk_stmt.
Hypothesis REPS : RTREP_keepS_stmt.
Hypothesis PS : poison_shadow_spec.
Hypothesis CD : cache_dealloc_specC.
Hypothesis GBB : get_block_begin_spec.
Hypothesis LD : large_dealloc_spec.
Hypothesis LDP : large_dealloc_pend_spec.

Theorem qcr_prim_proof : qcr_prim_spec.
Proof.
  unfold qcr_prim_spec, qcr_slot_spec. intros until lo.
  intros (HR & WF & HM & HG & HFR & HSW) HC HD HE HP HAP -> -> TP CB1 CB2 CBC HRES ST HCL LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold AQCR_STACK in LO.
  apply lscps_assume. intros NWX HO HB.
  assert (HQE : In (A, n) (qelems st)) by (eapply qcur_in_qelems; eassumption).
  assert (HQB : qblock st A n) by (left; exact HQE).
  destruct (CARVE st m A n WF HR HQB) as (j1 & j2 & j3 & b1 & cid & f1 & f2 & AL & HDR & HB1 & TS & LC & IC & PC & Gn & GA & K & X & Y & CE & TB & S1 & S2 & S3 & TR & TC).
  pose proof (CARVEP st m A n WF HR HQE HP) as CP. cbv zeta in CP.
  destruct CP as (junk & Hc & Ep & Eplo & Ephi & RZ & Epz & P1 & P2 & IDX & MP & RI & BIGH & SHJ & A8 & APR & RU8).
  set (c := pclass n) in *. set (k := b_cptr st A n) in *. set (p := b_alloc_beg A n) in *.
  unfold b_chunk_beg in *.
  pose proof (csize_pos c ltac:(lia)) as CSP.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  assert (FRONT : evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (W1 : list (Z * Z)),
      ms' = MS (mkR (wz 0x342b8) (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2' (wz cbA) (wz (A - 16))
                    (wz A) (wz ((usz n + 7) / 8 * 8)) (wz 250) a3' a4' a5' a6' a7'
                    (wz p) (wz A_ALLOC) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz APOISON_SHADOW) fc None m' (seg_rom asegs)
      /\ munch W1 m m' /\ Forall (bsz A n (bv_unsigned sp)) W1
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells asegs m' (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m' A_ALLOC (alloc_cells (st_pbase st) (st_spacebeg st) j1 j2 j3)
      /\ rw_cells asegs m' (A - 16) (hdr_cells CHUNK_INVALID n b1 cid))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cbA) (Z_to_bv 64 (A - 16)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AQCR) fc None m (seg_rom asegs))).
  { destruct (Z.eq_dec (rz_size n) 16) as [RZ16|RZB].
    - assert (EP16 : p = A - 16) by (subst p; unfold b_alloc_beg; lia).
      eapply evt_mono.
      { eapply (qcr_prim_front16_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
                  (st_pbase st) (st_spacebeg st) cbA A n c (r_mapped (rg st c)) lo j1 j2 j3 b1 cid);
          [exact MI| reflexivity| reflexivity| exact Hc| exact Gn| exact GA| exact S1| exact S2| exact S3
          | rewrite <- EP16; exact IDX| exact MP| exact ST| exact HCL| lia| exact AL| exact RI| exact HDR| exact HB1]. }
      cbv beta. intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FR' & AL' & RI' & HDR').
      exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', [(bv_unsigned sp - 48, bv_unsigned sp); (A - 16, A - 12)].
      rewrite EP16. split; [reflexivity|]. split; [exact MU|].
      split; [repeat apply Forall_cons; try apply Forall_nil; unfold bsz; cbn [fst snd]; unfold CEIL, usz in *; (lia_on HCL LO CE Eplo Ephi CSP EP16 X)|].
      repeat (split; [assumption|]). assumption.
    - assert (RZB' : 16 < rz_size n) by lia.
      eapply evt_mono.
      { eapply (qcr_prim_frontbig_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
                  (st_pbase st) (st_spacebeg st) cbA A n c (r_mapped (rg st c)) lo j1 j2 j3 b1 cid);
          [exact MI| reflexivity| reflexivity| exact Hc| exact Gn| exact GA| exact RZB'| exact S1| exact S2| exact S3
          | rewrite <- Epz; exact IDX| | exact MP| exact ST| exact HCL| lia| exact AL| exact RI| exact HDR| exact HB1| rewrite <- Epz; exact (BIGH RZB')].
        pose proof (rz_size_range n) as [_ RZM]. pose proof (csize_mod32 c ltac:(lia)) as CM32.
        assert (rz_size n + usz n <= csize c) by (unfold usz in *; lia). unfold usz in *. clear - H RZM CM32. Z.div_mod_to_equations. lia. }
      cbv beta. intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & FR' & AL' & RI' & HDR' & BH').
      exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', [(bv_unsigned sp - 48, bv_unsigned sp); (A - 16, A - 12); (A - rz_size n, A - rz_size n + 8)].
      rewrite Epz. split; [reflexivity|]. split; [exact MU|].
      split; [repeat apply Forall_cons; try apply Forall_nil; unfold bsz; cbn [fst snd]; unfold CEIL, usz in *; (lia_on HCL LO CE Eplo Ephi Epz CSP RZB' X Y)|].
      repeat (split; [assumption|]). assumption. }
  eapply evt_cut; [exact FRONT|]. clear FRONT.
  cbv beta. intros ms1 (u0 & u1 & u2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m1 & W1 & -> & MU1 & HW1 & WM1 & MI1 & ST1 & FR1 & AL1 & HDR1).
  assert (LE : b_lo A n <= b_hi A n) by (unfold usz in *; lia).
  assert (HSPC : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
  assert (L8 : b_lo A n mod 8 = 0).
  { rewrite <- Eplo. subst p. unfold b_alloc_beg. pose proof (rz_size_range n) as [_ RZM]. clear - GA RZM. Z.div_mod_to_equations. lia. }
  set (ru := (usz n + 7) / 8 * 8) in *.
  assert (RUB : ru mod 8 = 0 /\ usz n <= ru < usz n + 8) by (subst ru; clear; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (SHIN : SH (b_lo A n) <= SH A /\ SH A + ru / 8 <= SH (b_hi A n)).
  { split; [apply rt_SH_mono; lia|]. rewrite <- (rt_SH_aligned_add A ru A8). apply rt_SH_mono.
    pose proof (csize_mod32 c ltac:(lia)) as CM32. rewrite Ephi. rewrite Ephi in Y. clear - Y RUB CM32 A8 Eplo L8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 A ru 250 lo junk);
      [ eapply icpt_cells_high; [exact MU1| eapply (bsz_high A n (bv_unsigned sp)); eassumption| exact IC]
      | eapply poison_cells_high; [exact MU1| eapply (bsz_high A n (bv_unsigned sp)); eassumption| exact PC]
      | exact MI1| rewrite unsigned_lit by lia; exact ST1| exact HCL| rewrite unsigned_lit by lia; unfold APOISON_STACK; lia
      | reflexivity| reflexivity| reflexivity| exact A8| tauto| lia| exact APR| lia| intros; lia
      | eapply rw_cells_transport; [exact SHJ| exact MU1| exact WM1|]; cbn [cells_size Cells.csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - RUB RU8; Z.div_mod_to_equations; lia);
        eapply (bsz_sh A n (bv_unsigned sp)); first [eassumption | tauto] ]. }
  cbv beta. intros ms2 (v0 & v1 & v2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & SHF & ST2).
  cbv beta delta [wz] in *. rewrite (unsigned_lit (bv_unsigned sp - 48)) in * by (lia_on HCL LO RSP RU8).
  replace (ret_pc (Z_to_bv 64 213688)) with (Z_to_bv 64 213688) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  set (W12 := W1 ++ [(SH A, SH A + ru / 8); (bv_unsigned sp - 48 - APOISON_STACK, bv_unsigned sp - 48)]).
  assert (MU12 : munch W12 m m2) by (eapply munch_cat; [exact MU1| exact MU2]).
  assert (WM12 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
  assert (HW12 : Forall (qcz_ok st A n) W12).
  { apply Forall_app. split; [eapply bsz_qcz; eassumption|]. repeat apply Forall_cons; try apply Forall_nil; unfold qcz_ok; cbn [fst snd]; unfold APOISON_STACK, CEIL in *; [right; left; (lia_on RU8 RUB)| right; right; right; lia]. }
  assert (HS12 : forall iv, In iv W12 -> CEIL <= fst iv -> snd iv <= bv_unsigned sp).
  { intros iv Hin HCE. apply in_app_or in Hin as [Hin|[<-|[<-|[]]]]; [eapply (bsz_stk A n (bv_unsigned sp)); eassumption| |cbn [fst snd]; lia].
    cbn [fst snd] in *. exfalso. pose proof (ablk_shad_lin _ _ K LE) as [_ S2']. unfold KHIGHMEM_BEG, CEIL in *. lia. }
  pose proof (REPQ st m m2 W12 b d A n WF HR HC HD HE HP HAP MU12 WM12 HW12 SHF) as HR2. fold c k in HR2.
  set (st1 := st_qchunk st c k) in *.
  (* [comment removed for export] *)
  pose proof (ablk_shad_lin _ _ K LE) as [SHL1 SHL2]. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in SHL1, SHL2.
  pose proof (ablk_shad_disj _ _ K LE) as SHD. pose proof (rt_SH_mono (b_hi A n) (b_hi A n + 7) ltac:(lia)) as SHM7.
  pose proof (ablk_lin _ _ K) as (KI & K0 & KT & _). unfold AIMG_HI in KI.
  pose proof (oclr_lin _ _ TR ltac:(lia)) as (TR1 & TR2 & TR3). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR2, TR3.
  destruct SHIN as [SHIN1 SHIN2]. unfold CEIL, APOISON_STACK, T_STATS in *.
  (* [comment removed for export] *)
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra))
    by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]; repeat split; lia]).
  assert (AL2 : rw_cells asegs m2 A_ALLOC (alloc_cells (st_pbase st) (st_spacebeg st) j1 j2 j3))
    by (eapply rw_cells_transport; [exact AL1| exact MU2| exact WM2| unfold A_ALLOC; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]; repeat split; lia]).
  assert (HDR2 : rw_cells asegs m2 (A - 16) (hdr_cells CHUNK_INVALID n b1 cid))
    by (eapply rw_cells_transport; [exact HDR1| exact MU2| exact WM2| cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]; unfold usz in *; repeat split; (lia_on Y TB Eplo Ephi RZ Epz A8 RU8 CSP SHIN1 SHIN2 SHL1 SHL2 SHD SHM7 TR2 HCL LO HSPC KT)]).
  assert (CB2' : rw_cells asegs m2 cbA [W8 (acache st)]).
  { apply (proj1 (rw_cells_app _ _ [_] [_])) in CBC as [CBC _].
    eapply rw_cells_transport; [exact CBC| exact MU12| exact WM12|]. subst W12. apply disjoint_from_app.
    - eapply (bsz_out A n (bv_unsigned sp)); [eassumption| |]; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]; unfold CEIL; lia.
    - cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]. repeat split; lia. }
  assert (TS2 : rw_cells asegs m2 (st_t st + 2800 + 40) [C8 f1; C8 f2]).
  { eapply rw_cells_transport; [exact TS| exact MU12| exact WM12|]. subst W12. apply disjoint_from_app.
    - eapply (bsz_out A n (bv_unsigned sp)); [eassumption| |]; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]; unfold CEIL; lia.
    - cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]. repeat split; (lia_on TB Eplo Ephi RZ Epz A8 RU8 CSP RUB SHIN1 SHIN2 SHL1 SHL2 SHD SHM7 KI TR2 HCL LO TC). }
  pose proof (wb_sp0 st (wf_base_ok st WF)) as (SP01 & SP02 & _).
  assert (LC2 : leafc st m2) by (eapply leafc_qchunk; [exact HC| exact (leafc_of_RTREP _ _ HR2)]).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply qcr_prim_tail_proof with (st := st) (P := st_pbase st) (S := st_spacebeg st) (cbA := cbA) (A := A) (n := n) (c := c) (p := p)
        (cache := acache st) (lo := lo) (j1 := j1) (j2 := j2) (j3 := j3) (b1 := b1) (cid := cid) (f1 := f1) (f2 := f2)
        (vs4 := s4) (vs3 := s3) (vs2 := s2) (vs1 := s1) (vs0 := s0) (vra := ra);
      [exact MI2| exact LC2| exact WF| exact TP| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hc| exact Gn
      | exact S1| reflexivity| exact P1| exact P2| unfold acache, T_ACACHE; lia| lia| lia
      | rewrite unsigned_lit by lia; lia| | lia| | rewrite unsigned_lit by lia; exact ST2| exact HCL
      | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact FR2| exact AL2| exact CB2'| exact HDR2| exact TS2].
    - clear - S1 P1 Hc Epz RZ. unfold KREGIONSIZE, KHIGHMEM_BEG in *. lia.
    - clear - TB X Y. unfold usz in *. lia. }
  cbv beta. intros ms3 (y0 & y1 & y2 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & f1' & f2' & m3 & -> & MU3 & WM3 & MI3 & ST3 & AL3 & CB3 & HDR3 & TS3).
  rewrite (unsigned_lit (bv_unsigned sp - 48)) in * by lia. replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) in * by lia.
  unfold T_STATS in MU3, TS3.
  (* [comment removed for export] *)
  set (W13 := W12 ++ [(lo, bv_unsigned sp - 48); (st_t st + 2800 + 40, st_t st + 2800 + 56)]).
  assert (MU13 : munch W13 m m3) by (eapply munch_cat; [exact MU12| exact MU3]).
  assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM12| exact WM3]).
  assert (HW13 : Forall (qcz_ok st A n) W13).
  { apply Forall_app. split; [exact HW12|]. repeat apply Forall_cons; try apply Forall_nil; unfold qcz_ok; cbn [fst snd]; unfold CEIL, T_STATS, T_UNWINDING in *; [right; right; right; lia| right; right; left; lia]. }
  assert (HS13 : forall iv, In iv W13 -> CEIL <= fst iv -> snd iv <= bv_unsigned sp).
  { intros iv Hin HCE. apply in_app_or in Hin as [Hin|[<-|[<-|[]]]]; [exact (HS12 iv Hin HCE)| cbn [fst snd]; lia|]. cbn [fst snd] in *. unfold CEIL in *. lia. }
  assert (SHF3 : rw_cells asegs m3 (SH A) [CB (Z.to_nat (ru / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (ru / 8)))]).
  { eapply rw_cells_transport; [exact SHF| exact MU3| exact WM3|]. cbn [cells_size Cells.csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RUB RU8; Z.div_mod_to_equations; lia).
    cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH]. repeat split; (lia_on HCL RU8 SHIN2 SHL2 TB Eplo Ephi RZ Epz A8 CSP RUB SHIN1 SHL1 SHD SHM7 KI TR2). }
  pose proof (REPQ st m m3 W13 b d A n WF HR HC HD HE HP HAP MU13 WM13 HW13 SHF3) as HR3. fold c k in HR3. fold st1 in HR3.
  assert (WF1 : RTWF st1) by (subst st1 c k; eapply RTWF_qchunk'; eassumption).
  assert (PV1 : rt_prov st1 = rt_prov st) by (subst st1 c k; eapply rt_prov_qchunk'; eassumption).
  destruct (qchunk_fields st b d A n HC HAP) as (F1 & F2 & F3 & F4 & F5 & F6). fold c k in F1, F2, F3, F4, F5, F6. fold st1 in F1, F2, F3, F4, F5, F6.
  pose proof (qchunk_same st WF b d A n HC HAP) as QS. fold c k in QS. fold st1 in QS.
  destruct QS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21 & Q22).
  assert (CP3 : cli_pres st (bv_unsigned sp) m m3) by (eapply (cli_pres_qcz st WF (bv_unsigned sp) HSPC A n W13); eassumption).
  assert (ES3 : errno_same m m3).
  { eapply errno_same_munch; [exact MU13|]. eapply Forall_impl; [| exact HW13]. intros [l h] Z. unfold qcz_ok in Z. cbn [fst snd] in *.
    clear - Z KI SHL1 SHIN1 TR3 HCL. unfold AERRNO, ATP, T_STATS, T_UNWINDING, CEIL, AIMG_LO, AIMG_HI in *. lia. }
  (* [comment removed for export] *)
  apply evt_done. cbv beta delta [wz]. rewrite Z_to_bv_bv_unsigned. eapply lscps_bind.
  { eapply (CD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo g st1 c k lo);
      [ apply RTS_intro; [exact HR3| exact WF1| subst st1 c k; eapply RTMODEL_qchunk'; eassumption
                         | subst st1 c k; eapply GWIN_qchunk'; [eassumption|]; eapply GWIN_mem; [exact HG| exact HO| exact WM13]
                         | exact HFR| subst st1 c k; eapply SWIN_qchunk'; eassumption]
      | rewrite F2; left; reflexivity| exact Hc
      | unfold acache; rewrite Q16; reflexivity| reflexivity| reflexivity
      | unfold wz; f_equal; rewrite Ep; subst st1; symmetry; apply (cptr_addr_qchunk' st WF b d A n HC HAP)
      | exact TP| rewrite PV1; exact HRES| exact ST3| exact HCL| unfold ACDEALLOC_STACK; lia| exact MI3 ]. }
  cbv beta. intros ms4 mo4 g4 PO.
  destruct PO as (e0 & e1 & e2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & e3 & e4 & e5 & e6 & m4 & st4 & -> & MI4 & REL & RTS4 & ST4 & CP4 & RF4 & GM4 & BO4).
  apply lscps_done. unfold qcrec_post, rt_post_std. do 15 eexists. exists m4, st4.
  split; [reflexivity|]. split; [exact MI4|].
  destruct REL as (SBP & AP4 & CI4 & OTH & AV4).
  destruct SBP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B21 & B22 & B23 & B24).
  assert (AP4' : st_apend st4 = []).
  { rewrite AP4, F2. cbn. unfold ck_eqb. cbn. rewrite !Z.eqb_refl. reflexivity. }
  split.
  { split.
    { unfold same_but_quarantine, dtls_same, loose0_ext in *. rewrite Q18 in B17. rewrite Q19 in B18.
      repeat split; try congruence; try (cut_on [HD RSP Gn TB Hc MP RUB SHD TR2 TR3 B17] tauto). }
    split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros c' Hc' FR. destruct (Z.eq_dec c' c) as [->|NE]; [exfalso; exact (qblock_not_fresh st A n WF HQB HP FR)|].
    destruct (OTH c' Hc' NE) as [E1 E2]. apply (proj2 (fresh_cls_qchunk' st WF b d A n HC HAP c')) in FR. fold c k in FR. fold st1 in FR.
    unfold fresh_cls in *. rewrite E1, E2. exact FR. }
  split; [exact RTS4|]. split; [exact ST4|].
  split.
  { unfold cli_pres in *. rewrite Q1, Q21, Q15 in CP4. eapply cj_pres_trans; [exact CP3| exact CP4]. }
  split.
  { eapply errno_same_trans; [exact ES3|]. eapply errno_same_rt_frame; [exact RF4| clear - HCL; unfold AERRNO, ATP; lia|].
    intros a Ha. apply (errno_notin_primary_fp st1 c a WF1 ltac:(unfold KNUMCLASSES; lia) Ha). }
  split; [exact GM4|].
  unfold budget_ok in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcr_sec_front_full :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n cbA lo : Z),
  RTS st m mo g -> LOK asegs mo ->
  qblock st A n -> bprim n = false ->
  a0 = wz cbA -> a1 = wz (b_chunk_beg A) -> tp = wz ATP ->
  bv_unsigned sp <= cbA -> cbA + 16 <= st_sp0 st ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AQCR_STACK ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                    (wz A_SECONDARY) (wz A_GSTATS) (wz (sec_alloc_beg (b_map_beg A))) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ALARGE_DEALLOC) fc None m' (seg_rom asegs)
      /\ RTS st m' mo g /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQCR) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros (HR & WF & HM & HG & HFR & HSW) HO HQB HP -> -> TP CB1 CB2 ST HCL LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold AQCR_STACK in LO.
  destruct (CARVE st m A n WF HR HQB) as (j1 & j2 & j3 & b1 & cid & f1 & f2 & AL & HDR & HB1 & TS & LC & IC & PC & Gn & GA & K & X & Y & CE & TB & S1 & S2 & S3 & TR & TC).
  pose proof (CARVES st m A n WF HR HQB HP) as CS. cbv zeta in CS.
  destruct CS as (HSEC & EA & RNG & OFF1 & OFF2 & PB & M16 & MCE & MT & S0 & S64).
  set (mb := b_map_beg A) in *. unfold b_chunk_beg in *.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as (SP01 & SP02 & _).
  pose proof (ablk_lin _ _ K) as (KI & K0 & KT & _). unfold AIMG_HI in KI.
  pose proof (oclr_lin _ _ TR ltac:(lia)) as (TR1 & TR2 & TR3). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR2, TR3.
  assert (HSPC : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
  cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (qcr_sec_front_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (st_pbase st) (st_spacebeg st) cbA (A - 16) lo j1 j2 j3);
      [exact MI| reflexivity| reflexivity| exact S0| exact S64| lia| exact OFF1| exact ST| exact HCL| lia| exact AL]. }
  cbv beta. intros ms1 (u0 & u1 & u2 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & s2' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & AL1).
  cbv beta delta [wz] in *.
  assert (HW1 : Forall (secw_ok st) [(bv_unsigned sp - 48, bv_unsigned sp)])
    by (repeat apply Forall_cons; try apply Forall_nil; unfold secw_ok; cbn [fst snd]; left; unfold CEIL; lia).
  assert (HR1 : RTREP st m1).
  { eapply (RTREP_high st _ m m1 WF); [| exact MU1| exact WM1| exact HR]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (GBB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo g st mb n (A - 16) lo);
      [ apply RTS_intro; [exact HR1| exact WF| exact HM| eapply GWIN_mem; [exact HG| exact HO| exact WM1]| exact HFR| exact HSW]
      | exact HSEC| exact RNG| reflexivity| reflexivity| rewrite unsigned_lit by lia; exact ST1| exact HCL
      | rewrite unsigned_lit by lia; unfold AGBB_STACK; lia| exact MI1 ]. }
  cbv beta. intros ms2 (v0 & v1 & v2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & (j3' & MX2) & ST2).
  rewrite (unsigned_lit (bv_unsigned sp - 48)) in * by lia.
  replace (ret_pc (Z_to_bv 64 213444)) with (Z_to_bv 64 213444) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  set (W12 := [(bv_unsigned sp - 48, bv_unsigned sp)] ++ [(lo, bv_unsigned sp - 48); (A_SECONDARY + 616, A_SECONDARY + 620)]).
  assert (MU12 : munch W12 m m2) by (eapply munch_cat; [exact MU1| exact MU2]).
  assert (WM12 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
  assert (HW12 : Forall (secw_ok st) W12).
  { repeat apply Forall_cons; try apply Forall_nil; unfold secw_ok; cbn [fst snd]; unfold CEIL; [left; lia| left; lia| right; right; lia]. }
  assert (HR2 : RTREP st m2) by (eapply (REPS st m m2 W12 WF HR MU12 WM12 HW12); exists j3'; exact MX2).
  assert (LC2 : leafc st m2) by exact (leafc_of_RTREP _ _ HR2).
  unfold CEIL, T_STATS in *.
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp - 48) (qcr_frame s4 s3 s2 s1 s0 ra))
    by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| unfold A_SECONDARY, A_ALLOC; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt]; repeat split; lia]).
  assert (AL2 : rw_cells asegs m2 A_ALLOC (alloc_cells (st_pbase st) (st_spacebeg st) j1 j2 j3))
    by (eapply rw_cells_transport; [exact AL1| exact MU2| exact WM2| unfold A_SECONDARY, A_ALLOC; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt]; repeat split; lia]).
  assert (HDR2 : rw_cells asegs m2 (A - 16) (hdr_cells CHUNK_QUARANTINE n b1 cid))
    by (eapply rw_cells_transport; [exact HDR| exact MU12| exact WM12| subst W12; unfold A_SECONDARY, A_ALLOC, usz in *; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt]; repeat split; lia]).
  assert (TS2 : rw_cells asegs m2 (st_t st + 2800 + 40) [C8 f1; C8 f2])
    by (eapply rw_cells_transport; [exact TS| exact MU12| exact WM12| subst W12; unfold A_SECONDARY, A_ALLOC; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt]; repeat split; lia]).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply qcr_sec_tail_proof with (st := st) (P := st_pbase st) (S := st_spacebeg st) (cbA := cbA) (mch := A - 16) (n := n)
        (p' := sec_alloc_beg mb) (lo := lo) (j1 := j1) (j2 := j2) (j3 := j3) (b1 := b1) (cid := cid) (f1 := f1) (f2 := f2)
        (vs4 := s4) (vs3 := s3) (vs2 := s2) (vs1 := s1) (vs0 := s0) (vra := ra);
      [exact MI2| exact LC2| exact WF| exact TP| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Gn
      | exact S0| exact S64| exact PB| exact OFF2| exact M16| exact MCE| exact MT
      | rewrite unsigned_lit by lia; exact ST2| exact HCL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact FR2| exact AL2| exact HDR2| exact TS2]. }
  cbv beta. intros ms3 (y0 & y1 & y2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & f1' & f2' & m3 & -> & MU3 & WM3 & MI3 & ST3 & AL3 & HDR3 & TS3).
  rewrite (unsigned_lit (bv_unsigned sp - 48)) in * by lia. replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) in * by lia.
  unfold T_STATS in MU3.
  set (W13 := W12 ++ [(lo, bv_unsigned sp - 48); (st_t st + 2800 + 40, st_t st + 2800 + 56)]).
  assert (MU13 : munch W13 m m3) by (eapply munch_cat; [exact MU12| exact MU3]).
  assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM12| exact WM3]).
  assert (HW13 : Forall (secw_ok st) W13).
  { apply Forall_app. split; [exact HW12|]. repeat apply Forall_cons; try apply Forall_nil; unfold secw_ok; cbn [fst snd]; unfold CEIL, T_STATS, T_UNWINDING; [left; lia| right; left; lia]. }
  assert (MX3 : rw_cells asegs m3 (A_SECONDARY + 616) [W1 0; CB 3 j3'])
    by (eapply rw_cells_transport; [exact MX2| exact MU3| exact WM3| unfold A_SECONDARY, A_ALLOC; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt]; repeat split; lia]).
  assert (HR3 : RTREP st m3) by (eapply (REPS st m m3 W13 WF HR MU13 WM13 HW13); exists j3'; exact MX3).
  apply evt_done. cbv beta delta [wz]. rewrite Z_to_bv_bv_unsigned.
  do 12 eexists. exists m3. split; [reflexivity|].
  split; [apply RTS_intro; [exact HR3| exact WF| exact HM| eapply GWIN_mem; [exact HG| exact HO| exact WM13]| exact HFR| exact HSW]|].
  split; [exact WM13|]. split; [exact MI3|]. split; [exact ST3|].
  split.
  2:{ eapply errno_same_munch; [exact MU13|]. eapply Forall_impl; [| exact HW13]. intros [l h] Z. unfold secw_ok in Z. cbn [fst snd] in *.
      pose proof (oclr_lin _ _ TR ltac:(lia)) as (_ & _ & TR3').
      clear - Z TR3' HCL. unfold AERRNO, ATP, T_STATS, T_UNWINDING, CEIL, AIMG_LO, AIMG_HI, A_SECONDARY, A_ALLOC in *. lia. }
  eapply (cli_pres_secw st WF (bv_unsigned sp) HSPC W13); [exact MU13| exact WM13| exact HW13|].
  intros iv Hin HCE. subst W13 W12. cbn [app] in Hin. unfold CEIL, A_SECONDARY, A_ALLOC in *.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in *; lia.
Qed.

Lemma loose0_ext_of_eq : forall st st', st_loose0 st' = st_loose0 st -> loose0_ext st st'.
Proof. intros st st' E. exists []. rewrite E. symmetry. apply app_nil_r. Qed.
Lemma fresh_cls_of_eq : forall st st' c, st_regions st' = st_regions st -> st_cache st' = st_cache st -> fresh_cls st c -> fresh_cls st' c.
Proof. intros st st' c E1 E2 H. unfold fresh_cls, rg, cch in *. rewrite E1, E2. exact H. Qed.

Theorem qcr_sec_proof : qcr_sec_spec.
Proof.
  unfold qcr_sec_spec, qcr_slot_spec. intros until lo.
  intros HRTS HC HD HE HP HAP -> -> TP CB1 CB2 CBC HRES ST HCL LO MI.
  apply lscps_assume. intros NWX HO HB.
  assert (HQE : In (A, n) (qelems st)) by (eapply qcur_in_qelems; eassumption).
  assert (HQB : qblock st A n) by (left; exact HQE).
  pose proof HRTS as (HR & WF & _).
  pose proof (CARVES st m A n WF HR HQB HP) as CS. cbv zeta in CS. destruct CS as (HSEC & EA & _).
  eapply lscps_step_evt.
  eapply evt_cut; [eapply (qcr_sec_front_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g st A n cbA lo); try eassumption; reflexivity|].
  cbv beta. intros ms3 (y0 & y1 & y2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & RTS3 & WM3 & MI3 & ST3 & CP3 & ES3).
  apply evt_done. eapply lscps_bind.
  { eapply (LD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo g st b d (b_map_beg A) n lo);
      [exact RTS3| exact HC| exact HD| rewrite <- EA; exact HE| exact HP| reflexivity| reflexivity| reflexivity| exact TP
      | exact ST3| exact HCL| unfold ALARGE_DEALLOC_STACK, AQCR_STACK in *; lia| exact MI3]. }
  cbv beta. intros ms4 mo4 g4 PO.
  destruct PO as (e0 & e1 & e2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & e3 & e4 & e5 & e6 & m4 & st4 & -> & MI4 & REL & RTS4 & ST4 & CP4 & RF4 & GM4 & BO4).
  apply lscps_done. unfold qcrec_post, rt_post_std. do 15 eexists. exists m4, st4.
  split; [reflexivity|]. split; [exact MI4|].
  destruct REL as (SBS & SPD & NRS & QC4 & PERM).
  destruct SBS as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B21 & B22 & B23 & B24).
  split.
  { split.
    { unfold same_but_quarantine. repeat (split; [first [assumption | apply dtls_same_of_eq; assumption | apply loose0_ext_of_eq; assumption]|]). assumption. }
    split; [exact B8|]. split; [exact B9|]. split; [exact B24|]. split; [exact B23|]. split; [exact QC4|].
    intros c' Hc' FR. exact (fresh_cls_of_eq st st4 c' B4 B6 FR). }
  split; [exact RTS4|]. split; [exact ST4|].
  split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP3| exact CP4]|].
  split.
  { eapply errno_same_trans; [exact ES3|]. eapply errno_same_rt_frame; [exact RF4| clear - HCL; unfold AERRNO, ATP; lia|].
    intros a Ha. apply (errno_notin_secondary_fp st (b_map_beg A) n a WF); [| exact Ha].
    assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; destruct HQB; tauto).
    pose proof (block_geom st WF A n HBA) as (_ & _ & K & _ & _ & _ & _ & _ & _ & _ & Gs). destruct (Gs HP) as (_ & EH & _).
    unfold b_lo in K, EH. rewrite HP in K, EH. rewrite EH in K. exact K. }
  split; [exact GM4| exact BO4].
Qed.

Theorem qcr_pend_proof : qcr_pend_spec.
Proof.
  unfold qcr_pend_spec. intros until lo.
  intros HRTS HIN HP -> -> TP CB1 CB2 CBC HRES ST HCL LO MI.
  apply lscps_assume. intros NWX HO HB.
  assert (HQB : qblock st A n) by (right; exact HIN).
  pose proof HRTS as (HR & WF & _).
  pose proof (CARVES st m A n WF HR HQB HP) as CS. cbv zeta in CS. destruct CS as (HSEC & EA & _).
  eapply lscps_step_evt.
  eapply evt_cut; [eapply (qcr_sec_front_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g st A n cbA lo); try eassumption; reflexivity|].
  cbv beta. intros ms3 (y0 & y1 & y2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & RTS3 & WM3 & MI3 & ST3 & CP3 & ES3).
  apply evt_done. eapply lscps_bind.
  { eapply (LDP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo g st A n (b_map_beg A) lo);
      [exact RTS3| exact HIN| exact HP| exact EA| reflexivity| reflexivity| reflexivity| exact TP
      | exact ST3| exact HCL| unfold ALARGE_DEALLOC_STACK, AQCR_STACK in *; lia| exact MI3]. }
  cbv beta. intros ms4 mo4 g4 PO.
  destruct PO as (e0 & e1 & e2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & e3 & e4 & e5 & e6 & m4 & st4 & -> & MI4 & REL & RTS4 & ST4 & CP4 & RF4 & GM4 & BO4).
  apply lscps_done. unfold qcrp_post, rt_post_std. do 15 eexists. exists m4, st4.
  split; [reflexivity|]. split; [exact MI4|].
  destruct REL as (SBS & QP4 & PERM).
  destruct SBS as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26).
  split.
  { split.
    { unfold same_but_quarantine. repeat (split; [first [assumption | apply dtls_same_of_eq; assumption | apply loose0_ext_of_eq; assumption]|]). assumption. }
    split; [exact B9|]. split; [exact B10|]. split; [exact B25|]. split; [exact B26|]. split; [exact QP4|].
    intros c' Hc' FR. exact (fresh_cls_of_eq st st4 c' B4 B6 FR). }
  split; [exact RTS4|]. split; [exact ST4|].
  split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP3| exact CP4]|].
  split.
  { eapply errno_same_trans; [exact ES3|]. eapply errno_same_rt_frame; [exact RF4| clear - HCL; unfold AERRNO, ATP; lia|].
    intros a Ha. apply (errno_notin_secondary_fp st (b_map_beg A) n a WF); [| exact Ha].
    assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; destruct HQB; tauto).
    pose proof (block_geom st WF A n HBA) as (_ & _ & K & _ & _ & _ & _ & _ & _ & _ & Gs). destruct (Gs HP) as (_ & EH & _).
    unfold b_lo in K, EH. rewrite HP in K, EH. rewrite EH in K. exact K. }
  split; [exact GM4| exact BO4].
Qed.
End QCR.
End CeilWrap.
End RTW_q_qcr.

(* [comment removed for export] *)
Module RTW_q_dorec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_cd_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs RTW_q_stmts RTW_q_stmts2 RTW_q_qcr1 RTW_q_qcr RTW_q_dor1 RTW_q_rep3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ADOREC_STACK : Z := 2160.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dstep_rel (st st' : rtstate) : Prop :=
  same_but_quarantine st st'
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_qpend st' = st_qpend st
  /\ (forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> fresh_cls st c -> fresh_cls st' c).

Definition dorec_rel (st st' : rtstate) : Prop := dstep_rel st st' /\ st_qtmp st' = [] /\ st_qcur st' = [].

Definition dorec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (tmpA lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        dorec_rel st st'
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' tmpA (tmp_cells 0 0 0 0)
        /\ cli_pres st (tmpA + 32) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).

(* [comment removed for export] *)
Definition dorec_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (tmpA Sx lo : Z),
  RTS st m mo g ->
  st_qcur st = [] -> st_apend st = [] ->
  a1 = wz tmpA -> a2 = wz (acache st) -> a3 = wz Sx -> tp = wz ATP -> 0 <= Sx < 2^64 ->
  bv_unsigned sp <= tmpA -> tmpA + 32 <= st_sp0 st ->
  rw_cells asegs m tmpA (tmp_cells (zlen (st_qtmp st)) (qc_first (st_qtmp st)) (qc_last (st_qtmp st)) (qc_bytes (st_qtmp st))) ->
  rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ADOREC_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (dorec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st tmpA lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ADOREC) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dtls_same_trans : forall a b c, dtls_same a b -> dtls_same b c -> dtls_same a c.
Proof. unfold dtls_same. intros a b c [H1 H2] [H3 H4]. split; congruence. Qed.

Lemma sbq_refl : forall st, same_but_quarantine st st.
Proof. intros st. unfold same_but_quarantine. repeat (split; [first [reflexivity | apply dtls_same_refl | apply loose0_ext_refl]|]). reflexivity. Qed.

Lemma sbq_trans : forall a b c, same_but_quarantine a b -> same_but_quarantine b c -> same_but_quarantine a c.
Proof.
  unfold same_but_quarantine. intros a b c
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18)
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18).
  repeat (split; [first [congruence | eapply dtls_same_trans; eassumption | eapply loose0_ext_trans; eassumption]|]). congruence.
Qed.

Lemma dstep_refl : forall st, dstep_rel st st.
Proof. intros st. split; [apply sbq_refl|]. repeat (split; [reflexivity|]). intros; assumption. Qed.

Lemma dstep_trans : forall a b c, dstep_rel a b -> dstep_rel b c -> dstep_rel a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
  split; [eapply sbq_trans; eassumption|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros k Hk NE FR. apply (B5 k Hk NE). apply (A5 k Hk NE). exact FR.
Qed.

(* [comment removed for export] *)
Lemma sbq_of_sbp : forall st st', same_but_primary st st' -> st_apend st' = st_apend st -> same_but_quarantine st st'.
Proof.
  unfold same_but_primary, same_but_quarantine. intros st st'
    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B21 & B22 & B23 & B24) AP.
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Definition dchain (X : Z) (st : rtstate) (m : word -> option byte) (g : lghost) (st' : rtstate) (m' : word -> option byte) (g' : lghost) : Prop :=
  dstep_rel st st' /\ cli_pres st X m m' /\ errno_same m m' /\ gmono g g' /\ budget_ok st g st' g' 0.

Lemma gmono_refl' : forall g, gmono g g. Proof. intros g w H; exact H. Qed.
Lemma gmono_trans' : forall g1 g2 g3, gmono g1 g2 -> gmono g2 g3 -> gmono g1 g3.
Proof. intros g1 g2 g3 H1 H2 w H. apply H2, H1, H. Qed.

Lemma dchain_refl : forall X st m g, dchain X st m g st m g.
Proof.
  intros. split; [apply dstep_refl|]. split; [unfold cli_pres; apply cj_pres_refl|]. split; [apply errno_same_refl|]. split; [apply gmono_refl'|]. unfold budget_ok. lia.
Qed.

Lemma dchain_trans : forall X st1 m1 g1 st2 m2 g2 st3 m3 g3,
  dchain X st1 m1 g1 st2 m2 g2 -> dchain X st2 m2 g2 st3 m3 g3 -> dchain X st1 m1 g1 st3 m3 g3.
Proof.
  intros X st1 m1 g1 st2 m2 g2 st3 m3 g3 (R1 & C1 & S1 & G1 & B1) (R2 & C2 & S2 & G2 & B2).
  split; [eapply dstep_trans; eassumption|].
  split.
  { destruct R1 as ((E1 & _ & _ & _ & _ & _ & _ & _ & _ & E10 & _ & _ & _ & _ & _ & E16 & _) & _).
    unfold cli_pres in *. rewrite E1, E10, E16 in C2. eapply cj_pres_trans; eassumption. }
  split; [eapply errno_same_trans; eassumption|].
  split; [eapply gmono_trans'; eassumption|]. unfold budget_ok in *. lia.
Qed.

(* [comment removed for export] *)
Lemma cli_pres_up : forall st SP SP' m m', cli_pres st SP m m' -> SP <= SP' -> cli_pres st SP' m m'.
Proof. intros st SP SP' m m' H LE. unfold cli_pres in *. eapply cj_pres_weaken; [exact H| exact LE| auto| auto]. Qed.

Lemma cli_pres_q_set : forall st qt qg ap qp tmp cur X m m', cli_pres (q_set st qt qg ap qp tmp cur) X m m' <-> cli_pres st X m m'.
Proof. intros. destruct st. split; intros H; exact H. Qed.
Lemma fresh_cls_q_set : forall st qt qg ap qp tmp cur c, fresh_cls (q_set st qt qg ap qp tmp cur) c <-> fresh_cls st c.
Proof. intros. destruct st. split; intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma sbq_qbatch_cd : forall st kb st3, same_but_primary (st_qbatch st kb) st3 -> st_apend st3 = st_apend st -> same_but_quarantine st st3.
Proof.
  intros st kb st3 H AP. destruct st. unfold same_but_primary, same_but_quarantine, st_qbatch, q_set, dtls_same, loose0_ext in *. cbn in *.
  (nelim H 24%nat; intros B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 B18 B19 B20 B21 B22 B23 B24).
  repeat (split; [assumption|]). assumption.
Qed.

Lemma bvu_wz : forall x, 0 <= x < 2^64 -> bv_unsigned (wz x) = x.
Proof. intros x Hx. cbv delta [wz]. apply unsigned_lit. exact Hx. Qed.

Lemma sbq_q_set : forall st qt qg qp tmp cur, same_but_quarantine st (q_set st qt qg (st_apend st) qp tmp cur).
Proof.
  intros. destruct st. unfold same_but_quarantine.
  repeat (split; [first [reflexivity | apply dtls_same_of_eq; reflexivity | apply loose0_ext_of_eq; reflexivity]|]). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tmp_pop_words : forall b r, (forall x, In x r -> qb_addr x <> 0) ->
     zlen (b :: r) - 1 = zlen r
  /\ (if qc_first r =? 0 then 0 else qc_last (b :: r)) = qc_last r
  /\ qc_bytes (b :: r) - qb_size b = qc_bytes r.
Proof.
  intros b r NZ. split; [rewrite zlen_cons; lia|]. split; [| rewrite qc_bytes_cons; lia].
  destruct r as [|x r']; [reflexivity|].
  cbn [qc_first]. destruct (qb_addr x =? 0) eqn:E; [apply Z.eqb_eq in E; exfalso; exact (NZ x ltac:(left; reflexivity) E)|].
  unfold qc_last. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DOR.
Hypothesis QCRP : qcr_prim_spec.
Hypothesis QCRS : qcr_sec_spec.
Hypothesis CD : cache_dealloc_specC.

Variables (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (SP tmpA lo cacheA Sx : Z) (j0 : list byte) (vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word).
Hypothesis TP : tp = wz ATP.
Hypothesis HSX : 0 <= Sx < 2^64.
Hypothesis HTA : SP <= tmpA.
Hypothesis HCL : alloc_ceiling <= lo.
Hypothesis LO : lo <= SP - ADOREC_STACK.
Hypothesis SPR : SP < 2^64.

(* [comment removed for export] *)
Definition dinv (st : rtstate) (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
  RTS st m mo g /\ st_apend st = [] /\ rt_prov st <= g_res g /\ mem_inv asegs m
  /\ stk asegs m lo (SP - 112)
  /\ rw_cells asegs m (SP - 112) (dor_frame j0 cacheA Sx vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra)
  /\ rw_cells asegs m tmpA (tmp_cells (zlen (st_qtmp st)) (qc_first (st_qtmp st)) (qc_last (st_qtmp st)) (qc_bytes (st_qtmp st)))
  /\ acache st = cacheA /\ tmpA + 32 <= st_sp0 st.

Lemma dinv_call : forall st m mo g st' m' mo' g',
  dinv st m mo g -> RTS st' m' mo' g' -> mem_inv asegs m' -> stk asegs m' lo (SP - 112) ->
  cli_pres st (SP - 112) m m' -> budget_ok st g st' g' 0 ->
  st_apend st' = [] -> st_qtmp st' = st_qtmp st -> st_t st' = st_t st -> st_sp0 st' = st_sp0 st ->
  dinv st' m' mo' g'.
Proof.
  intros st m mo g st' m' mo' g' (HRTS & HAP & HPV & MI & ST & FR & TMP & AC & SPB) HRTS' MI' ST' CP BO AP' QT' ET ES.
  unfold dinv. split; [exact HRTS'|]. split; [exact AP'|]. split; [unfold budget_ok in BO; lia|]. split; [exact MI'|]. split; [exact ST'|].
  unfold cli_pres in CP.
  split. { eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP); [exact FR|]. left. unfold dor_frame. cbn [cells_size Cells.csize Nat.add]. lia. }
  split. { rewrite QT'. eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP); [exact TMP|]. left. unfold tmp_cells. cbn [cells_size Cells.csize Nat.add]. lia. }
  split; [unfold acache in *; rewrite ET; exact AC| rewrite ES; exact SPB].
Qed.

(* [comment removed for export] *)
Definition at_slotnext (st0 : rtstate) (m0 : word -> option byte) (g0 : lghost) (b : qbatch) (d : Z) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
      ms' = MS (mkR (wz 0x340d8) (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz A_SECONDARY) (wz A_GSTATS) (wz (qb_addr b)) (wz (2^37)) (wz (qb_count b))
                    (wz (qb_addr b + 152 + 8 * (d + 1))) (wz (qb_count b + 16)) (wz (16 + (d + 1))) s10 s11 t3 t4 t5 t6)
               F (wz (if d + 1 =? qb_count b then 0x340e4 else 0x340cc)) fc None m' (seg_rom asegs)
      /\ dinv st' m' mo' g' /\ st_qcur st' = [(b, d + 1)] /\ dchain (tmpA + 32) st0 m0 g0 st' m' g' /\ st_qtmp st' = st_qtmp st0.

Lemma dor_slot_step :
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (b : qbatch) (d : Z),
  dinv st m mo g -> st_qcur st = [(b, d)] -> 0 <= d < qb_count b ->
  LSCPS asegs (at_slotnext st m g b d)
        (MS (mkR ra (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) a0 a1 a2 a3 a4 a5 a6 a7
                 (wz A_SECONDARY) (wz A_GSTATS) (wz (qb_addr b)) (wz (2^37)) (wz (qb_count b))
                 (wz (qb_addr b + 152 + 8 * d)) (wz (qb_count b + 16)) (wz (16 + d)) s10 s11 t3 t4 t5 t6)
            F (wz 0x340cc) fc None m (seg_rom asegs)) mo g.
Proof.
  intros until d. intros DI HC HD.
  apply lscps_assume. intros NWX HO HB.
  (nelimp DI 9%nat; intros HRTS HAP HPV MI ST FR TMP AC SPB).
  (nelimp HRTS 6%nat; intros HR WF HM HG HFR HSW).
  unfold ADOREC_STACK in LO.
  assert (HBQ : In b (qall st)) by (unfold qall; rewrite HC, !in_app_iff; cbn [map fst In]; tauto).
  destruct (nthz (qb_elems b) d (0, 0)) as [A n] eqn:HE.
  pose proof (qcur_in_qelems st b d A n HC HD HE) as HQE.
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact HQE).
  (nelimp (block_geom st WF A n HBA) 7%nat; intros Gn GA K X Y CE _).
  (nelimp (ablk_lin _ _ K) 4%nat; intros KI K0 KT K47).
  (nelimp (batch_geom st WF b HBQ) 5%nat; intros _ _ BG1 BG2 BAL).
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  pose proof (proj1 (wq_batch st (wf_quar_ok st WF) b HBQ)) as CNT. unfold QBATCH_CAP in CNT.
  (nelim (proj2 (proj2 (proj2 (rr_batches st m HR))) (b, d) ltac:(rewrite HC; left; reflexivity)) 4%nat; intros _ _ SL _). cbn [fst] in SL.
  specialize (SL d HD). rewrite HE in SL. cbn [fst] in SL.
  (* [comment removed for export] *)
  assert (CBC : rw_cells asegs m (SP - 112 + 8) [W8 (acache st); W8 Sx]).
  { unfold dor_frame in FR. apply (proj1 (rw_cells_app m (SP - 112) [_] (_ :: _))) in FR as [_ FR].
    cbn [cells_size Cells.csize Nat.add] in FR. change (Z.of_nat 8) with 8 in FR.
    apply (proj1 (rw_cells_app m (SP - 112 + 8) [_; _] (_ :: _))) in FR as [FR _]. rewrite AC. exact FR. }
  assert (SPV : bv_unsigned (wz (SP - 112) : word) = SP - 112) by (apply bvu_wz; lia).
  eapply lscps_step_evt.
  eapply evt_cut.
  { eapply (dor_slot_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (qb_addr b) d (b_chunk_beg A));
      [exact MI| reflexivity| unfold QBATCH_CAP; lia| unfold b_chunk_beg, AIMG_HI, usz in *; lia
      | unfold KHIGHMEM_BEG, AIMG_HI in *; lia| unfold QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF in *; lia| rewrite SPV; lia| exact SL]. }
  cbv beta. intros ms1 ->. rewrite SPV. apply evt_done.
  (* [comment removed for export] *)
  eapply lscps_bind.
  { destruct (bprim n) eqn:EP.
    - eapply (QCRP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g st b d A n (SP - 112 + 8) Sx lo);
        [exact HRTS| exact HC| exact HD| exact HE| exact EP| exact HAP| reflexivity| reflexivity| exact TP
        | rewrite SPV; lia| lia| exact CBC| exact HPV| rewrite SPV; exact ST| exact HCL| rewrite SPV; unfold AQCR_STACK; lia| exact MI].
    - eapply (QCRS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g st b d A n (SP - 112 + 8) Sx lo);
        [exact HRTS| exact HC| exact HD| exact HE| exact EP| exact HAP| reflexivity| reflexivity| exact TP
        | rewrite SPV; lia| lia| exact CBC| exact HPV| rewrite SPV; exact ST| exact HCL| rewrite SPV; unfold AQCR_STACK; lia| exact MI]. }
  cbv beta. intros ms2 mo2 g2 PO.
  (nelim PO 26%nat; intros e0 e1 e2 r0 r1 r2 r3 r4 r5 r6 r7 e3 e4 e5 e6 m2 st2 -> MI2 REL RTS2 ST2 CP2 ES2 GM2 BO2).
  rewrite SPV in ST2, CP2.
  (nelim REL 7%nat; intros SBQ QT2 QG2 QTM2 QP2 QC2 FR2).
  (nelimp SBQ 18%nat; intros E1 _ _ _ _ _ _ _ _ _ E11 _ _ _ _ _ E17 _).
  assert (DI2 : dinv st2 m2 mo2 g2).
  { eapply (dinv_call st m mo g st2 m2 mo2 g2); try eassumption. rewrite E17. exact HAP. }
  (* [comment removed for export] *)
  cbv beta delta [wz].
  replace (ret_pc (Z_to_bv 64 213208)) with (Z_to_bv 64 213208) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply lscps_step_evt.
  eapply evt_cut.
  { eapply (dor_slotnext_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (qb_addr b) d (qb_count b));
      [reflexivity| reflexivity| reflexivity| lia| unfold QBATCH_CAP; lia| unfold KHIGHMEM_BEG in *; lia
      | unfold QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF in *; lia| unfold QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF in *; lia]. }
  cbv beta. intros ms3 ->. apply evt_done. apply lscps_done.
  unfold at_slotnext. cbv beta delta [wz]. nexists 15%nat. exists m2, st2.
  split; [reflexivity|]. split; [exact DI2|]. split; [exact QC2|].
  split; [| exact QTM2]. split.
  { split; [exact SBQ|]. split; [exact QT2|]. split; [exact QG2|]. split; [exact QP2|]. intros c Hc _ FRc. exact (FR2 c Hc FRc). }
  split; [eapply cli_pres_up; [exact CP2| lia]|]. split; [exact ES2|]. split; [exact GM2| exact BO2].
Qed.


(* [comment removed for export] *)
Definition at_fb8 (st0 : rtstate) (m0 : word -> option byte) (g0 : lghost) (b : qbatch) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
      ms' = MS (mkR ra (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz A_SECONDARY) (wz A_GSTATS) (wz (qb_addr b)) (wz (2^37)) (wz (qb_count b)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x340e4) fc None m' (seg_rom asegs)
      /\ dinv st' m' mo' g' /\ st_qcur st' = [(b, qb_count b)] /\ dchain (tmpA + 32) st0 m0 g0 st' m' g' /\ st_qtmp st' = st_qtmp st0.

Lemma dor_slots : forall (k : nat)
         (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (b : qbatch) (d : Z),
  dinv st m mo g -> st_qcur st = [(b, d)] -> 0 <= d -> d + 1 + Z.of_nat k = qb_count b ->
  LSCPS asegs (at_fb8 st m g b)
        (MS (mkR ra (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) a0 a1 a2 a3 a4 a5 a6 a7
                 (wz A_SECONDARY) (wz A_GSTATS) (wz (qb_addr b)) (wz (2^37)) (wz (qb_count b))
                 (wz (qb_addr b + 152 + 8 * d)) (wz (qb_count b + 16)) (wz (16 + d)) s10 s11 t3 t4 t5 t6)
            F (wz 0x340cc) fc None m (seg_rom asegs)) mo g.
Proof.
  induction k as [|k IH]; intros until d; intros DI HC HD0 HK.
  - eapply lscps_bind; [eapply dor_slot_step; [exact DI| exact HC| lia]|].
    cbv beta. intros ms' mo' g' nelH_; (nelim nelH_ 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' st' -> DI' HC' CH QT').
    assert (E : d + 1 = qb_count b) by lia. rewrite E in HC'. rewrite E, Z.eqb_refl.
    apply lscps_done. unfold at_fb8. nexists 19%nat. exists m', st'.
    split; [reflexivity|]. split; [exact DI'|]. split; [exact HC'|]. split; [exact CH| exact QT'].
  - eapply lscps_bind; [eapply dor_slot_step; [exact DI| exact HC| lia]|].
    cbv beta. intros ms' mo' g' nelH_; (nelim nelH_ 22%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' st' -> DI' HC' CH QT').
    replace (d + 1 =? qb_count b) with false by (symmetry; apply Z.eqb_neq; lia).
    eapply lscps_mono; [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo' g' st' b (d + 1)); [exact DI'| exact HC'| lia| lia]|].
    cbv beta. intros ms2 mo2 g2 nelH_; (nelim nelH_ 26%nat; intros ra2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 q7 q8 q9 u3 u4 u5 u6 m2 st2 -> DI2 HC2 CH2 QT2).
    unfold at_fb8. nexists 19%nat. exists m2, st2.
    split; [reflexivity|]. split; [exact DI2|]. split; [exact HC2|]. split; [eapply dchain_trans; eassumption| congruence].
Qed.

(* [comment removed for export] *)
Definition at_next (st0 : rtstate) (m0 : word -> option byte) (g0 : lghost) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
      ms' = MS (mkR ra (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) (wz (zlen (st_qtmp st'))) a1 a2 a3 a4 a5 a6 a7
                    (wz A_SECONDARY) (wz A_GSTATS) s4 (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if zlen (st_qtmp st') =? 0 then 0x34118 else 0x3408c)) fc None m' (seg_rom asegs)
      /\ dinv st' m' mo' g' /\ st_qcur st' = [] /\ dchain (tmpA + 32) st0 m0 g0 st' m' g' /\ st_qtmp st' = st_qtmp st0.

Lemma dor_tail :
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (b : qbatch),
  dinv st m mo g -> st_qcur st = [(b, qb_count b)] ->
  LSCPS asegs (at_next st m g)
        (MS (mkR ra (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) a0 a1 a2 a3 a4 a5 a6 a7
                 (wz A_SECONDARY) (wz A_GSTATS) (wz (qb_addr b)) (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x340e4) fc None m (seg_rom asegs)) mo g.
Proof.
  intros until b. intros DI HC.
  apply lscps_assume. intros NWX HO HB.
  (nelimp DI 9%nat; intros HRTS HAP HPV MI ST FR TMP AC SPB).
  (nelimp HRTS 6%nat; intros HR WF HM HG HFR HSW).
  unfold ADOREC_STACK in LO.
  assert (HBQ : In b (qall st)) by (unfold qall; rewrite HC, !in_app_iff; cbn [map fst In]; tauto).
  (nelimp (batch_geom st WF b HBQ) 5%nat; intros _ _ BG1 BG2 BAL).
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  pose proof (rbeg_val st 24) as RB24.
  (nelimp (S_range st WF) 3%nat; intros S1 S2 S3). (nelimp (P_range st WF) 3%nat; intros P1 P2 P3).
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  destruct (bk_used st WF b HBQ) as [UKb HK]. set (kb := bk st b) in *.
  destruct (rr_alloc st m HR) as ((j1 & j2 & j3 & AL) & _).
  assert (SPV : bv_unsigned (wz (SP - 112) : word) = SP - 112) by (apply bvu_wz; lia).
  assert (ACR : 0 <= cacheA < 2^64) by (rewrite <- AC; unfold acache, T_ACACHE, CEIL in *; lia).
  eapply lscps_step_evt.
  eapply evt_cut.
  { eapply (dor_batch_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (st_pbase st) (st_spacebeg st) (qb_addr b) cacheA Sx j0 j1 j2 j3 vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra);
      [exact MI| reflexivity| reflexivity| reflexivity
      | unfold PRIM_RES_SIZE, KSPACESIZE in *; lia| rewrite <- RB24; exact BG1
      | rewrite RB24 in BG2; unfold QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF in *; lia
      | unfold PRIM_RES_SIZE, KSPACESIZE in *; lia| exact ACR| rewrite SPV; lia| rewrite SPV; lia
      | rewrite SPV; exact FR| exact AL]. }
  cbv beta. intros ms1 (a4' & ->). apply evt_done.
  (* [comment removed for export] *)
  set (st2 := st_qbatch st kb).
  assert (WF2 : RTWF st2) by (eapply RTWF_qbatch'; eassumption).
  assert (PV2 : rt_prov st2 = rt_prov st) by (eapply rt_prov_qbatch'; eassumption).
  (nelim (qbatch_fields st kb HAP) 6%nat; intros F1 F2 F3 F4 F5 F6). fold st2 in F1, F2, F3, F4, F5, F6.
  assert (RTS2 : RTS st2 m mo g).
  { apply RTS_intro; [eapply RTREP_qbatch; eassumption| exact WF2| apply RTMODEL_q_set; exact HM| apply GWIN_q_set; exact HG| exact HFR| apply SWIN_q_set; exact HSW]. }
  eapply lscps_bind.
  { eapply (CD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g st2 24 kb lo);
      [exact RTS2| rewrite F2; left; reflexivity| lia
      | unfold wz; f_equal; rewrite <- AC; symmetry; apply q_set_acache| reflexivity| reflexivity
      | unfold wz; f_equal; rewrite HK; symmetry; apply q_set_cptr_addr
      | exact TP| rewrite PV2; exact HPV| rewrite SPV; exact ST| exact HCL| rewrite SPV; unfold ACDEALLOC_STACK; lia| exact MI]. }
  cbv beta. intros ms3 mo3 g3 PO.
  (nelim PO 26%nat; intros e0 e1 e2 r0 r1 r2 r3 r4 r5 r6 r7 e3 e4 e5 e6 m3 st3 -> MI3 REL RTS3 ST3 CP3 RF3 GM3 BO3).
  rewrite SPV in ST3, CP3.
  (nelim REL 5%nat; intros SBP AP3 CI3 OTH AV3).
  assert (AP3' : st_apend st3 = []).
  { rewrite AP3, F2. cbn. unfold ck_eqb. cbn. rewrite !Z.eqb_refl. reflexivity. }
  assert (SBQ : same_but_quarantine st st3) by (eapply sbq_qbatch_cd; [exact SBP| rewrite AP3', HAP; reflexivity]).
  (nelimp SBP 24%nat; intros _ _ _ _ _ _ B7 B8 _ _ _ _ _ _ _ _ _ _ _ _ _ B22 B23 B24).
  (nelimp SBQ 12%nat; intros E1 _ _ _ _ _ _ _ _ _ E11 _).
  assert (CP3' : cli_pres st (SP - 112) m m3) by (pose proof CP3 as CPx; unfold st2, st_qbatch in CPx; apply cli_pres_q_set in CPx; exact CPx).
  assert (BO3' : budget_ok st g st3 g3 0) by (unfold budget_ok in *; lia).
  assert (DI3 : dinv st3 m3 mo3 g3).
  { eapply (dinv_call st m mo g st3 m3 mo3 g3); try eassumption. rewrite B23, F6. reflexivity. }
  assert (CH3 : dchain (tmpA + 32) st m g st3 m3 g3).
  { split.
    { split; [exact SBQ|]. split; [rewrite B7, F4; reflexivity|]. split; [rewrite B8, F5; reflexivity|]. split; [rewrite B22, F3; reflexivity|].
      intros c Hc NE FRc. destruct (OTH c Hc NE) as [G1 G2].
      assert (FRc2 : fresh_cls st2 c) by (unfold st2, st_qbatch; apply fresh_cls_q_set; exact FRc).
      unfold fresh_cls in *. rewrite G1, G2. exact FRc2. }
    split; [eapply cli_pres_up; [exact CP3'| lia]|].
    split.
    { eapply errno_same_rt_frame; [exact RF3| clear - HCL; unfold AERRNO, ATP; lia|].
      intros a Ha. apply (errno_notin_primary_fp st2 24 a WF2 ltac:(unfold KNUMCLASSES; lia) Ha). }
    split; [exact GM3| exact BO3']. }
  (* [comment removed for export] *)
  (nelimp DI3 9%nat; intros _ _ _ _ _ _ TMP3 _ _).
  pose proof (wq_rec_max st3 (wf_quar_ok st3 (proj1 (proj2 RTS3)))) as RM3.
  pose proof (qc_bytes_lb (st_qtmp st3)) as LB3. pose proof (qc_bytes_nonneg (st_qglobal st3)) as GN3.
  pose proof (qc_bytes_nonneg (map fst (st_qcur st3))) as CN3. pose proof (zlen_nonneg (st_qtmp st3)) as ZN3.
  cbv beta delta [wz].
  replace (ret_pc (Z_to_bv 64 213264)) with (Z_to_bv 64 213264) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply lscps_step_evt.
  eapply evt_cut.
  { eapply (dor_next_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 tmpA
              (zlen (st_qtmp st3)) (qc_first (st_qtmp st3)) (qc_last (st_qtmp st3)) (qc_bytes (st_qtmp st3)));
      [exact MI3| reflexivity| unfold QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in *; lia| lia| (nelimp (wb_sp0 st (wf_base_ok st WF)) 3%nat; intros _ SP047 _); lia| exact TMP3]. }
  cbv beta. intros ms4 ->. apply evt_done. apply lscps_done.
  unfold at_next. cbv beta delta [wz]. nexists 20%nat. exists m3, st3.
  split; [reflexivity|]. split; [exact DI3|]. split; [rewrite B24, F1; reflexivity|]. split; [exact CH3| rewrite B23, F6; reflexivity].
Qed.


(* [comment removed for export] *)
Definition dor_final (st0 : rtstate) (m0 : word -> option byte) (g0 : lghost) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
      ms' = MS (mkR vra (wz SP) gp tp t0 t1 t2 vs0 vs1 a0 a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ RTS st' m' mo' g' /\ stk asegs m' lo SP
      /\ rw_cells asegs m' tmpA (tmp_cells 0 0 0 0)
      /\ st_qtmp st' = [] /\ st_qcur st' = [] /\ dchain (tmpA + 32) st0 m0 g0 st' m' g'.

Lemma dor_loop : forall (k : nat)
         (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate),
  dinv st m mo g -> st_qcur st = [] -> length (st_qtmp st) = k ->
  LSCPS asegs (dor_final st m g)
        (MS (mkR ra (wz (SP - 112)) gp tp t0 t1 t2 (wz tmpA) (wz A_ALLOC) (wz (zlen (st_qtmp st))) a1 a2 a3 a4 a5 a6 a7
                 (wz A_SECONDARY) (wz A_GSTATS) s4 (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz (if zlen (st_qtmp st) =? 0 then 0x34118 else 0x3408c)) fc None m (seg_rom asegs)) mo g.
Proof.
  induction k as [|k IH]; intros until st; intros DI HC HLEN.
  - (* [comment removed for export] *)
    destruct (st_qtmp st) as [|b r] eqn:HT; [| discriminate HLEN].
    (nelimp DI 9%nat; intros HRTS HAP HPV MI ST FR TMP AC SPB). rewrite HT in TMP.
    unfold ADOREC_STACK in LO.
    assert (SPV : bv_unsigned (wz (SP - 112) : word) = SP - 112) by (apply bvu_wz; lia).
    change (zlen (@nil qbatch) =? 0) with true. cbv iota.
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (dor_epi_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cacheA Sx lo j0 vs9 vs8 vs7 vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra);
        [exact MI| rewrite SPV; exact ST| exact HCL| rewrite SPV; lia| rewrite SPV; lia| rewrite SPV; exact FR]. }
    cbv beta. intros ms1 (-> & ST1). rewrite SPV in *. replace (SP - 112 + 112) with SP in * by lia.
    apply evt_done. apply lscps_done. unfold dor_final. nexists 15%nat. exists m, st.
    split; [reflexivity|]. split; [exact MI|]. split; [exact HRTS|]. split; [exact ST1|]. split; [exact TMP|].
    split; [exact HT|]. split; [exact HC| apply dchain_refl].
  - (* [comment removed for export] *)
    destruct (st_qtmp st) as [|b r] eqn:HT; [discriminate HLEN|]. cbn [length] in HLEN. injection HLEN as HLEN.
    apply lscps_assume. intros NWX HO HB.
    (nelimp DI 9%nat; intros HRTS HAP HPV MI ST FR TMP AC SPB).
    (nelimp HRTS 6%nat; intros HR WF HM HG HFR HSW).
    unfold ADOREC_STACK in LO. rewrite HT in TMP.
    assert (SPV : bv_unsigned (wz (SP - 112) : word) = SP - 112) by (apply bvu_wz; lia).
    assert (INQ : forall x, In x (b :: r) -> In x (qall st)) by (intros x Hx; unfold qall; rewrite HT, !in_app_iff; tauto).
    assert (HBQ : In b (qall st)) by (apply INQ; left; reflexivity).
    assert (GEO : forall x, In x (b :: r) -> KHIGHMEM_BEG <= qb_addr x /\ qb_addr x + QBATCH_SIZE <= alloc_ceiling).
    { intros x Hx. (nelimp (batch_geom st WF x (INQ x Hx)) 5%nat; intros _ _ G1 G2 _).
      pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 7%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 _).
      unfold QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF in *. lia. }
    destruct (GEO b ltac:(left; reflexivity)) as [GB1 GB2].
    pose proof (proj1 (wq_batch st (wf_quar_ok st WF) b HBQ)) as CNT. assert (CNT0 : 0 <= qb_count b) by (unfold qb_count; lia).
    pose proof (wq_rec_max st (wf_quar_ok st WF)) as RM. rewrite HT in RM.
    pose proof (qc_bytes_lb (b :: r)) as LBT. pose proof (qc_bytes_nonneg (st_qglobal st)) as GN.
    pose proof (qc_bytes_nonneg (map fst (st_qcur st))) as CN. pose proof (zlen_nonneg r) as ZN. pose proof (qc_bytes_nonneg r) as RN.
    pose proof (qb_size_ge b) as BSG. rewrite qc_bytes_cons in RM, LBT. rewrite zlen_cons in LBT.
    assert (NXR : 0 <= qc_first r < 2^64).
    { destruct r as [|x r']; [cbn; lia|]. cbn [qc_first]. destruct (GEO x ltac:(right; left; reflexivity)). unfold KHIGHMEM_BEG, QBATCH_SIZE in *. lia. }
    pose proof (proj1 (proj2 (proj2 (rr_batches st m HR)))) as B3. rewrite HT in B3. cbn [R_qlist] in B3. (nelim B3 3%nat; intros BC _ _).
    (nelimp (wb_sp0 st (wf_base_ok st WF)) 3%nat; intros _ SP047 _).
    replace (zlen (b :: r) =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; lia).
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (dor_pop_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m tmpA
                (zlen (b :: r)) (qb_addr b) (qc_last (b :: r)) (qc_bytes (b :: r)) (qc_first r) (qb_size b) (qb_count b));
        [exact MI| reflexivity| reflexivity| rewrite zlen_cons; unfold QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in *; lia
        | exact NXR| rewrite qc_bytes_cons; unfold QBATCH_SIZE in *; lia| rewrite qc_bytes_cons; unfold QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in *; lia
        | lia| unfold KHIGHMEM_BEG, AIMG_HI in *; lia| exact GB2| lia| lia| exact TMP| exact BC]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros a0' a1' m1 -> MU WM MI1 TMP1 BAT1). apply evt_done.
    (* [comment removed for export] *)
    set (st1 := st_qstart st).
    assert (E1 : st1 = q_set st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]) by (apply st_qstart_eq; exact HT).
    (nelim (q_set_fields st (st_qthread st) (st_qglobal st) (st_apend st) (st_qpend st) r [(b, 0)]) 6%nat; intros F1 F2 F3 F4 F5 F6).
    rewrite <- E1 in F1, F2, F3, F4, F5, F6.
    assert (WF1 : RTWF st1) by (eapply RTWF_qstart'; eassumption).
    assert (PV1 : rt_prov st1 = rt_prov st) by (eapply rt_prov_qstart'; eassumption).
    assert (HRm : RTREP st m1).
    { eapply (RTREP_high st [(tmpA, tmpA + 32)] m m1 WF); [| exact MU| exact WM| exact HR]. constructor; [cbn [fst]; lia| constructor]. }
    assert (RTS1 : RTS st1 m1 mo g).
    { apply RTS_intro; [eapply RTREP_qstart; eassumption| exact WF1| rewrite E1; apply RTMODEL_q_set; exact HM
                       | rewrite E1; apply GWIN_q_set; eapply GWIN_mem; [exact HG| exact HO| exact WM]| exact HFR| rewrite E1; apply SWIN_q_set; exact HSW]. }
    assert (NZR : forall x, In x r -> qb_addr x <> 0).
    { intros x Hx. destruct (GEO x ltac:(right; exact Hx)). unfold KHIGHMEM_BEG in *. lia. }
    (nelim (tmp_pop_words b r NZR) 3%nat; intros TW1 TW2 TW3). rewrite TW1, TW2, TW3 in TMP1.
    assert (DI1 : dinv st1 m1 mo g).
    { unfold dinv. split; [exact RTS1|]. split; [rewrite F3; exact HAP|]. split; [rewrite PV1; exact HPV|]. split; [exact MI1|].
      split; [eapply (stk_transport_disjoint asegs [(tmpA, tmpA + 32)]); [exact ST| exact MU| exact WM|]; cbn; lia|].
      split; [eapply rw_cells_transport; [exact FR| exact MU| exact WM|]; unfold dor_frame; cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt]; repeat split; lia|].
      split; [rewrite F5; exact TMP1|].
      split; [rewrite E1, q_set_acache; exact AC| rewrite E1, q_set_sp0; exact SPB]. }
    assert (CH1 : dchain (tmpA + 32) st m g st1 m1 g).
    { split.
      { split; [rewrite E1; apply sbq_q_set|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|].
        intros c Hc _ FRc. rewrite E1. apply (proj2 (fresh_cls_q_set st _ _ _ _ _ _ c)). exact FRc. }
      split.
      { eapply (cli_pres_secw st WF (tmpA + 32) ltac:(unfold CEIL; lia) [(tmpA, tmpA + 32)]); [exact MU| exact WM| |].
        - constructor; [left; cbn [fst]; unfold CEIL; lia| constructor].
        - intros iv [<-|[]] _. cbn [snd]. lia. }
      split; [eapply errno_same_munch; [exact MU|]; constructor; [cbn [fst snd]; left; unfold AERRNO, ATP; lia| constructor]|].
      split; [apply gmono_refl'|]. unfold budget_ok. lia. }
    (* [comment removed for export] *)
    assert (REST : forall (ra' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 q6 q7 q8 q9 u3 u4 u5 u6 : word) (m2 : word -> option byte) (mo2 : Model) (g2 : lghost) (st2 : rtstate),
              dinv st2 m2 mo2 g2 -> st_qcur st2 = [(b, qb_count b)] -> st_qtmp st2 = r -> dchain (tmpA + 32) st m g st2 m2 g2 ->
              LSCPS asegs (dor_final st m g)
                (MS (mkR ra' (wz (SP - 112)) gp tp u0 u1 u2 (wz tmpA) (wz A_ALLOC) b0 b1 b2 b3 b4 b5 b6 b7
                         (wz A_SECONDARY) (wz A_GSTATS) (wz (qb_addr b)) (wz (2^37)) q6 q7 q8 q9 s10 s11 u3 u4 u5 u6)
                    F (wz 0x340e4) fc None m2 (seg_rom asegs)) mo2 g2).
    { intros until st2. intros DI2 HC2 QT2 CH2.
      eapply lscps_bind; [eapply dor_tail; [exact DI2| exact HC2]|].
      cbv beta. intros ms3 mo3 g3 nelH_; (nelim nelH_ 27%nat; intros ra3 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 p4 p6 p7 p8 p9 w3 w4 w5 w6 m3 st3 -> DI3 HC3 CH3 QT3).
      eapply lscps_mono; [eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo3 g3 st3); [exact DI3| exact HC3| rewrite QT3, QT2; exact HLEN]|].
      cbv beta. intros ms4 mo4 g4 nelH_; (nelim nelH_ 25%nat; intros z0 z1 z2 d0 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 m4 st4 -> MI4 RTS4 ST4 TMP4 QTM4 QC4 CH4).
      unfold dor_final. nexists 15%nat. exists m4, st4.
      split; [reflexivity|]. split; [exact MI4|]. split; [exact RTS4|]. split; [exact ST4|]. split; [exact TMP4|].
      split; [exact QTM4|]. split; [exact QC4|]. eapply dchain_trans; [exact CH2|]. eapply dchain_trans; eassumption. }
    destruct (qb_count b =? 0) eqn:EC.
    + apply Z.eqb_eq in EC. eapply REST; [exact DI1| rewrite F6, EC; reflexivity| exact F5| exact CH1].
    + apply Z.eqb_neq in EC.
      replace (wz (qb_addr b + 152)) with (wz (qb_addr b + 152 + 8 * 0)) by (f_equal; lia).
      change (wz 16) with (wz (16 + 0)).
      eapply lscps_bind; [eapply (dor_slots (Z.to_nat (qb_count b - 1))); [exact DI1| exact F6| lia| rewrite Z2Nat.id by lia; lia]|].
      cbv beta. intros ms2 mo2 g2 nelH_; (nelim nelH_ 26%nat; intros ra2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 q7 q8 q9 u3 u4 u5 u6 m2 st2 -> DI2 HC2 CH2 QT2).
      eapply REST; [exact DI2| exact HC2| rewrite QT2; exact F5| eapply dchain_trans; eassumption].
Qed.

End DOR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DORTOP.
Hypothesis QCRP : qcr_prim_spec.
Hypothesis QCRS : qcr_sec_spec.
Hypothesis CD : cache_dealloc_specC.

Theorem dorec_proof : dorec_spec.
Proof.
  unfold dorec_spec. intros until lo.
  intros HRTS HC HAP -> -> -> TP HSX HTA SPB TMP HPV ST HCL LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  apply lscps_assume. intros NWX HO HB.
  (nelimp HRTS 6%nat; intros HR WF HM HG HFR HSW).
  (nelimp (wb_sp0 st (wf_base_ok st WF)) 3%nat; intros _ SP047 _).
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  assert (ACR : 0 <= acache st < 2^64) by (unfold acache, T_ACACHE, CEIL in *; lia).
  unfold ADOREC_STACK in LO.
  destruct (st_qtmp st) as [|b0 r0] eqn:HT.
  - (* [comment removed for export] *)
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (dor_pro0_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m tmpA 0 0 0 (acache st) Sx lo);
        [exact MI| reflexivity| reflexivity| reflexivity| exact ACR| exact HSX| exact HTA| lia| exact ST| exact HCL| lia| exact TMP]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros a0' a1' m1 -> MU WM MI1 ST1 TMP1). apply evt_done. apply lscps_done.
    unfold dorec_post, rt_post_std. nexists 15%nat. exists m1, st.
    split; [reflexivity|]. split; [exact MI1|].
    split; [split; [apply dstep_refl| split; [exact HT| exact HC]]|].
    split.
    { apply RTS_intro; [| exact WF| exact HM| eapply GWIN_mem; [exact HG| exact HO| exact WM]| exact HFR| exact HSW].
      eapply (RTREP_high st [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 WF); [| exact MU| exact WM| exact HR]. constructor; [cbn [fst]; lia| constructor]. }
    split; [exact ST1|]. split; [exact TMP1|].
    split.
    { eapply (cli_pres_secw st WF (tmpA + 32) ltac:(unfold CEIL; lia) [(bv_unsigned sp - 112, bv_unsigned sp)]); [exact MU| exact WM| |].
      - constructor; [left; cbn [fst]; unfold CEIL; lia| constructor].
      - intros iv [<-|[]] _. cbn [snd]. lia. }
    split; [eapply errno_same_munch; [exact MU|]; constructor; [cbn [fst snd]; left; unfold AERRNO, ATP; lia| constructor]|].
    split; [apply gmono_refl'|]. unfold budget_ok. lia.
  - (* [comment removed for export] *)
    pose proof (wq_rec_max st (wf_quar_ok st WF)) as RM. rewrite HT in RM.
    pose proof (qc_bytes_lb (b0 :: r0)) as LBT. pose proof (qc_bytes_nonneg (st_qglobal st)) as GN.
    pose proof (qc_bytes_nonneg (map fst (st_qcur st))) as CN. pose proof (zlen_nonneg r0) as ZN.
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (dor_pro_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m tmpA
                (zlen (b0 :: r0)) (qc_first (b0 :: r0)) (qc_last (b0 :: r0)) (qc_bytes (b0 :: r0)) (acache st) Sx lo);
        [exact MI| reflexivity| reflexivity| reflexivity
        | rewrite zlen_cons in *; unfold QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in *; lia
        | exact ACR| exact HSX| exact HTA| lia| exact ST| exact HCL| lia| exact TMP]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 10%nat; intros a1' j0 m1 -> MU WM MI1 ST1 FR1 TMP1). apply evt_done.
    assert (HRm : RTREP st m1).
    { eapply (RTREP_high st [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 WF); [| exact MU| exact WM| exact HR]. constructor; [cbn [fst]; lia| constructor]. }
    assert (RTS1 : RTS st m1 mo g).
    { apply RTS_intro; [exact HRm| exact WF| exact HM| eapply GWIN_mem; [exact HG| exact HO| exact WM]| exact HFR| exact HSW]. }
    assert (CP1 : cli_pres st (tmpA + 32) m m1).
    { eapply (cli_pres_secw st WF (tmpA + 32) ltac:(unfold CEIL; lia) [(bv_unsigned sp - 112, bv_unsigned sp)]); [exact MU| exact WM| |].
      - constructor; [left; cbn [fst]; unfold CEIL; lia| constructor].
      - intros iv [<-|[]] _. cbn [snd]. lia. }
    rewrite <- HT in TMP1.
    assert (DI1 : dinv (bv_unsigned sp) tmpA lo (acache st) Sx j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra st m1 mo g).
    { unfold dinv. repeat (split; [first [assumption | reflexivity]|]). first [assumption | reflexivity]. }
    replace (wz 0x3408c) with (wz (if zlen (st_qtmp st) =? 0 then 0x34118 else 0x3408c))
      by (rewrite HT; replace (zlen (b0 :: r0) =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite zlen_cons; lia); reflexivity).
    rewrite <- HT.
    eapply lscps_mono.
    { eapply (dor_loop QCRP QCRS CD gp tp s10 s11 F fc (bv_unsigned sp) tmpA lo (acache st) Sx j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra
                TP HSX HTA HCL ltac:(unfold ADOREC_STACK; lia) ltac:(lia) (length (st_qtmp st)));
        [exact DI1| exact HC| reflexivity]. }
    cbv beta. intros ms4 mo4 g4 nelH_; (nelim nelH_ 25%nat; intros z0 z1 z2 d0 d1 d2 d3 d4 d5 d6 d7 z3 z4 z5 z6 m4 st4 -> MI4 RTS4 ST4 TMP4 QTM4 QC4 CH4).
    (nelim CH4 5%nat; intros R4 CP4 ES4 GM4 BO4).
    assert (ES1 : errno_same m m1) by (eapply errno_same_munch; [exact MU|]; constructor; [cbn [fst snd]; left; unfold AERRNO, ATP; lia| constructor]).
    unfold dorec_post, rt_post_std. cbv beta delta [wz]. rewrite Z_to_bv_bv_unsigned. nexists 15%nat. exists m4, st4.
    split; [reflexivity|]. split; [exact MI4|].
    split; [split; [exact R4| split; [exact QTM4| exact QC4]]|].
    split; [exact RTS4|]. split; [exact ST4|]. split; [exact TMP4|].
    split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP1| exact CP4]|].
    split; [eapply errno_same_trans; [exact ES1| exact ES4]|].
    split; [exact GM4| exact BO4].
Qed.
End DORTOP.

End CeilWrap.
End RTW_q_dorec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_quarantine_iface ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_cd_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz RTW_m_apz RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_m_c1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_depot_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_q_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_q_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_q_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_enq2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_q_wf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_q_needs.
Import RTW_q_stmts.
Import RTW_q_stmts2.
Import RTW_q_qcr1.
Import RTW_q_qcr.
Import RTW_q_dor1.
Import RTW_q_rep3.
Import RTW_q_dorec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_sec_dstate RTW_q_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_car.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_zone2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_q_ms.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_drain2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf3.RTW_q_bz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_rec2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_rec2.RTW_q_recw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_q_rec2.
Import RTW_q_rec3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_q_wf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition ADRAIN_STACK : Z := 80 + ADOREC_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition drain_rel (st st' : rtstate) : Prop :=
  same_but_quarantine st st' /\ st_qpend st' = st_qpend st
  /\ st_qthread st' = [] /\ st_qtmp st' = [] /\ st_qcur st' = []
  /\ (forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> fresh_cls st c -> fresh_cls st' c).

Definition drain_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        drain_rel st st'
        /\ RTS st' m' mo' g' /\ stk asegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).

(* [comment removed for export] *)
Definition drain_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (Sx lo : Z),
  RTREP st m -> RTWFq st -> RTMODEL st mo -> GWIN st m mo g -> FRONTR mo (g_res g) -> SWIN st g ->
  st_qthread st <> [] -> st_qtmp st = [] -> st_qcur st = [] -> st_apend st = [] ->
  QUAR_MAX_CACHE < qc_bytes (st_qthread st) ->
  qc_bytes (st_qglobal st) + qc_bytes (st_qthread st) <= QREC_MAX ->
  a0 = wz A_QUAR -> a1 = wz (qcache_t st) -> a2 = wz (acache st) -> a3 = wz Sx -> tp = wz ATP -> 0 <= Sx < 2^64 ->
  bv_unsigned sp <= st_sp0 st ->
  rt_prov st <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ADRAIN_STACK ->
  mem_inv asegs m ->
  LSCPS asegs (drain_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AQDRAIN) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DWIN.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (lo SP : Z).
Hypothesis HLO : alloc_ceiling <= lo.
Hypothesis HSP : CEIL <= SP.

Lemma cli_pres_dwin : forall W m m', munch W m m' -> wmono asegs m m' -> Forall (dwin K lo SP) W -> cli_pres K SP m m'.
Proof.
  intros W m m' MU WM HW. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  intros a Ha HC. clear MU WM. induction W as [|[l h] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as A1. unfold dwin in A1. cbn [fst snd] in A1. cbn.
  split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. destruct A1 as [A1|[A1|[A1|(b & Hb & A1)]]].
  - apply (below_sp_not_client K WF SP a); [unfold CEIL; lia| exact HC].
  - apply (wstatic_not_client' K SP a WF HSP); [unfold A_QUAR, A_ALLOC in A1; lia| exact HC].
  - apply (tpage_not_client_all K WF SP HSP a); [lia| exact HC].
  - apply (batch_not_client K WF SP HSP b a Hb); [lia| exact HC].
Qed.

Lemma errno_dwin : forall W m m', munch W m m' -> Forall (dwin K lo SP) W -> errno_same m m'.
Proof.
  intros W m m' MU HW. eapply errno_same_munch; [exact MU|]. eapply Forall_impl; [| exact HW].
  intros [l h] A1. unfold dwin in A1. cbn [fst snd] in *.
  pose proof (t_range K WF) as [TR TC]. pose proof (oclr_lin _ _ TR ltac:(lia)) as (_ & _ & TR3).
  destruct A1 as [A1|[A1|[A1|(b & Hb & A1)]]].
  - left. unfold AERRNO, ATP. lia.
  - right. unfold AERRNO, ATP, A_QUAR, A_ALLOC in *. lia.
  - unfold AERRNO, ATP, AIMG_LO, AIMG_HI in *. lia.
  - pose proof (batch_geom K WF b Hb) as (_ & _ & G1 & _).
    pose proof (region_facts K WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (Y1 & _).
    left. unfold AERRNO, ATP, KHIGHMEM_BEG in *. lia.
Qed.
End DWIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rt_prov_drain' : forall st, RTWFq st -> 2^20 < qc_bytes (st_qthread st) -> rt_prov (st_drain st) <= rt_prov st.
Proof. intros st WQ BIG. destruct st. eapply rt_prov_drain; eassumption. Qed.

Section CARRIER.
Variable st : rtstate.
Hypothesis WQ : RTWFq st.
Hypothesis HT : st_qtmp st = [].
Hypothesis HC : st_qcur st = [].
Hypothesis DQR : qc_bytes (st_qglobal st) + qc_bytes (st_qthread st) <= QREC_MAX.
Let K := Kst st.

Lemma WFK : RTWF K.
Proof. apply RTWF_Kst; [exact WQ|]. rewrite HT, HC. cbn [map]. rewrite !qc_bytes_nil. lia. Qed.

Lemma K_fields : st_qthread K = [] /\ st_qglobal K = [] /\ st_apend K = st_apend st /\ st_qpend K = st_qpend st
  /\ st_qtmp K = st_qthread st ++ st_qglobal st /\ st_qcur K = [].
Proof. destruct (Kst_fields st) as (F1 & F2 & F3 & F4 & F5 & F6). rewrite HT, app_nil_r in F5. rewrite HC in F6. repeat split; assumption. Qed.

Lemma K_perm : Permutation (st_qthread st ++ st_qglobal st ++ [] ++ map fst (@nil (qbatch * Z))) (qall K).
Proof. unfold K. rewrite Kst_qall. unfold qall. rewrite HT, HC. apply Permutation_refl. Qed.

Lemma ainv_drained : ainv K [] [] (st_qglobal st ++ st_qthread st) [].
Proof.
  unfold ainv. cbn [app map]. rewrite ?app_nil_r. split; [| split; [| split]].
  - unfold qbatch_addrs, K. rewrite Kst_qall. unfold qall. rewrite HT, HC. cbn [app map]. rewrite ?app_nil_r.
    apply Permutation_map. apply Permutation_app_comm.
  - intros b Hb. apply (proj1 (wq_batch K (wf_quar_ok K WFK) b ltac:(unfold K; rewrite Kst_qall; unfold qall; rewrite HT, HC; cbn [app map]; rewrite ?app_nil_r; apply in_app_iff; apply in_app_iff in Hb; tauto))).
  - unfold curpart. cbn [flat_map]. rewrite ?app_nil_r. unfold K. rewrite Kst_qelems. unfold qelems. rewrite HT, HC. cbn [flat_map]. rewrite ?app_nil_r.
    rewrite !flat_map_app'. apply Permutation_app_comm.
  - rewrite qc_bytes_app, qc_bytes_nil. unfold QREC_MAX, QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in DQR. lia.
Qed.

(* [comment removed for export] *)
Lemma sL_drained : sL K (st_qglobal st ++ st_qthread st) [] = st_drain st.
Proof. unfold sL, st_drain, K, Kst. rewrite HT, HC. destruct st. reflexivity. Qed.
End CARRIER.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma QA_consts : forall m, QA m -> rw_cells asegs m (A_QUAR + 64) [C8 (wz QUAR_MAX_SIZE); C8 (wz QUAR_MIN_SIZE); C8 (wz QUAR_MAX_CACHE)].
Proof.
  intros m (j1 & j2 & H). apply (proj1 (rw_cells_app m A_QUAR [_] (_ :: _))) in H as [_ H].
  cbn [cells_size Cells.csize Nat.add] in H. change (Z.of_nat 64) with 64 in H.
  apply (proj1 (rw_cells_app m (A_QUAR + 64) [_; _; _] [_])) in H as [H _]. exact H.
Qed.

Section DRAIN.
Hypothesis DOREC : dorec_spec.

Theorem drain_proof : drain_spec.
Proof.
  unfold drain_spec. intros until lo.
  intros HR WQ HM HG HFR HSW QTNE HT HC HAP BIGC DQR -> -> -> -> TP HSX SPB HPV ST HCL LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  unfold ADRAIN_STACK, ADOREC_STACK in LO.
  apply lscps_assume. intros NWX HO HB.
  set (K := Kst st).
  pose proof (WFK st WQ HT HC DQR) as WFK'. fold K in WFK'.
  destruct (K_fields st HT HC) as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6). fold K in KF1, KF2, KF3, KF4, KF5, KF6.
  pose proof (ainv_drained st WQ HT HC DQR) as AI. fold K in AI.
  pose proof (K_perm st HT HC) as PERM. fold K in PERM.
  pose proof (QX_of_RTREP st m HR) as X0. fold K in X0. rewrite HT, HC in X0.
  set (qt := st_qthread st) in *. set (qg := st_qglobal st) in *.
  pose proof (qc_bytes_nonneg qt) as BT. pose proof (qc_bytes_nonneg qg) as BG.
  assert (QKT : qcache_t K = qcache_t st) by (unfold K, Kst; apply q_set_qcache_t).
  assert (HSPC : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  eapply evt_cut.
  { eapply (drain_front_full K WFK' qt qg [] [] PERM QTNE BG BT ltac:(unfold QREC_MAX, QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in DQR; lia)
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo);
      [exact X0| exact MI| reflexivity| rewrite QKT; reflexivity| exact ST| exact HCL| lia]. }
  cbv beta. intros ms1 (t0' & t1' & a4' & a5' & a6' & a7' & j0 & m1 & Wd & -> & X1 & FR1 & ST1 & MI1 & MU1 & HW1 & WM1).
  assert (SPV : bv_unsigned (wz (bv_unsigned sp - 48) : word) = bv_unsigned sp - 48) by (apply bvu_wz; lia).
  pose proof X1 as (CO1 & A41 & XA1 & XL1 & XH1 & XS1 & TX1 & TC1 & LV1 & QR1 & RL11 & RL12 & RL13 & RC1). unfold QH4 in XH1.
  pose proof (QA_consts m1 XA1) as QC1.
  assert (CP1 : cli_pres st (bv_unsigned sp) m m1).
  { pose proof (cli_pres_dwin K WFK' lo (bv_unsigned sp) HCL HSPC Wd m m1 MU1 WM1 HW1) as CPK. unfold K, Kst in CPK. apply cli_pres_q_set in CPK. exact CPK. }
  assert (ES1 : errno_same m m1) by (eapply (errno_dwin K WFK' lo (bv_unsigned sp) HCL); eassumption).
  destruct (Z_le_gt_dec (qc_bytes (qg ++ qt)) QUAR_MAX_SIZE) as [SMALL|BIGG].
  - (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (drain_ret_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 s3 s2 s1 s0 ra F fc m1
                (zlen (qg ++ qt)) (qc_first (qg ++ qt)) (qc_last (qg ++ qt)) (qc_bytes (qg ++ qt)) lo);
        [exact MI1| reflexivity| pose proof (qc_bytes_nonneg (qg ++ qt)); lia| rewrite SPV; exact ST1| exact HCL| rewrite SPV; lia| rewrite SPV; lia
        | rewrite SPV; exact FR1| exact QC1| exact XH1]. }
    cbv beta. intros ms2 (a1' & a4'' & -> & ST2). rewrite SPV in *. replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) in * by lia.
    apply evt_done. apply lscps_done.
    set (st2 := sL K (qg ++ qt) []).
    assert (WF2 : RTWF st2) by (apply (RTWF_lists K WFK' KF1 KF2 KF6 (qg ++ qt) [] AI SMALL)).
    assert (PV2 : rt_prov st2 <= rt_prov st).
    { unfold st2, K, qg, qt. rewrite (sL_drained st WQ HT HC DQR). apply rt_prov_drain'; [exact WQ| unfold QUAR_MAX_CACHE in BIGC; fold qt; lia]. }
    assert (HR2 : RTREP st2 m1).
    { unfold st2, sL. apply (RTREP_of_QX K [] (qg ++ qt) [] [] m1 X1).
      intros e He. eapply Permutation_in; [apply (sL_qelems K (qg ++ qt) [] AI)| exact He]. }
    unfold drain_post, rt_post_std. cbv beta delta [wz]. rewrite Z_to_bv_bv_unsigned. do 15 eexists. exists m1, st2.
    split; [reflexivity|]. split; [exact MI1|].
    destruct (sL_fields K (qg ++ qt) []) as (G1 & G2 & G3 & G4 & G5 & G6). fold st2 in G1, G2, G3, G4, G5, G6.
    split.
    { split; [unfold st2, sL; eapply sbq_trans; [unfold K, Kst; apply sbq_q_set| apply sbq_q_set]|].
      split; [rewrite G4; exact KF4|]. split; [exact G1|]. split; [exact G5|]. split; [exact G6|].
      intros c Hc _ FRc. unfold st2, sL. apply fresh_cls_q_set. unfold K, Kst. apply fresh_cls_q_set. exact FRc. }
    split.
    { apply RTS_intro; [exact HR2| exact WF2| apply RTMODEL_lists; unfold K, Kst; apply RTMODEL_q_set; exact HM
                       | apply GWIN_lists; unfold K, Kst; apply GWIN_q_set; eapply GWIN_mem; [exact HG| exact HO| exact WM1]
                       | exact HFR| apply SWIN_lists; unfold K, Kst; apply SWIN_q_set; exact HSW]. }
    split; [exact ST2|]. split; [exact CP1|]. split; [exact ES1|]. split; [apply gmono_refl'|].
    unfold budget_ok. lia.
  - (* [comment removed for export] *)
    destruct XL1 as (b2 & b3 & j4 & LK1 & LJ1).
    assert (GBM : qc_bytes (qg ++ qt) <= QREC_MAX) by (rewrite qc_bytes_app; lia).
    eapply evt_cut.
    { eapply (drain_rec_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 s3 s2 s1 s0 ra F fc m1
                (zlen (qg ++ qt)) (qc_first (qg ++ qt)) (qc_last (qg ++ qt)) (qc_bytes (qg ++ qt)) lo b2 b3);
        [exact MI1| reflexivity| unfold QREC_MAX, QUAR_MAX_SIZE, QUAR_MAX_CACHE, QBATCH_SIZE in *; lia| rewrite SPV; exact ST1| exact HCL| rewrite SPV; lia| rewrite SPV; lia
        | rewrite SPV; exact FR1| exact QC1| exact LK1| exact XH1]. }
    cbv beta. intros ms2 (t0'' & a4'' & a5'' & a6'' & a7'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & LK2).
    rewrite SPV in *. replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) in * by lia.
    (* [comment removed for export] *)
    assert (INK : forall x, In x (qg ++ qt) -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP).
    { intros x Hx. split; [apply (ainv_addr K [] [] _ _ x AI)| apply (ainv_cnt K [] [] _ _ x AI)]; cbn [app map]; rewrite ?app_nil_r; exact Hx. }
    assert (HV : exists v, In (qb_addr v) (qbatch_addrs K)).
    { destruct qt as [|v qt'] eqn:EQT; [exfalso; apply QTNE; reflexivity|]. exists v. apply INK. apply in_or_app. right. left. reflexivity. }
    destruct HV as (v & Hv).
    assert (HW2 : Forall slw_ok [(A_QUAR + 152, A_QUAR + 156)]) by (constructor; [right; cbn [fst snd]; lia| constructor]).
    destruct (far_keep0 K v _ m1 m2 WFK' Hv MU2 WM2 HW2) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11).
    assert (X2 : QX K m2 0 1 [] (qg ++ qt) [] []).
    { unfold QX, QXb. split; [exact (Z1 CO1)|]. split; [exact (Z2 A41)|]. split; [exact (Z3 XA1)|].
      split.
      { exists b2, b3, j4. split; [exact LK2|]. eapply rw_cells_transport; [exact LJ1| exact MU2| exact WM2|]. cbn. lia. }
      split; [exact (Z5 _ _ _ _ XH1)|]. split; [exact (Z4 XS1)|]. split; [exact (Z6 TX1)|]. split; [exact (Z7 _ TC1)|].
      split; [exact (Z8 LV1)|]. split; [exact (Z9 QR1)|]. split; [exact I|]. split; [exact (Z10 _ INK RL12)|]. split; [exact I|].
      intros bd []. }
    assert (HMN : 0 <= QUAR_MIN_SIZE < 2^62) by (unfold QUAR_MIN_SIZE; lia).
    eapply evt_cut.
    { eapply (rec_front_full K WFK' QUAR_MIN_SIZE lo HMN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (qg ++ qt));
        [exact AI| exact X2| exact MI2| reflexivity| reflexivity| unfold QUAR_MIN_SIZE, QUAR_MAX_SIZE in *; lia| exact GBM
        | cbv delta [wz]; rewrite Z_to_bv_bv_unsigned; exact ST2| exact HCL
        | cbv delta [wz]; rewrite Z_to_bv_bv_unsigned; lia| cbv delta [wz]; rewrite Z_to_bv_bv_unsigned; lia]. }
    cbv beta. intros ms3 (u0 & u1 & u2 & v0 & v1 & w4 & w5 & w6 & w7 & v2 & v3 & v4 & u3 & u4 & u5 & u6 & m3 & Wd3 & qgF & tmpF
                          & -> & AI3 & X3 & SM3 & FR3 & ST3 & MI3 & MU3 & HW3 & WM3).
    assert (SPW : bv_unsigned (wz (bv_unsigned sp) : word) = bv_unsigned sp) by (apply bvu_wz; lia). rewrite SPW in *.
    apply evt_done.
    (* [comment removed for export] *)
    set (tmpA := bv_unsigned sp - 80).
    set (st3 := sL K qgF tmpF).
    destruct (sL_fields K qgF tmpF) as (G1 & G2 & G3 & G4 & G5 & G6). fold st3 in G1, G2, G3, G4, G5, G6.
    assert (WF3 : RTWF st3) by (apply (RTWF_lists K WFK' KF1 KF2 KF6 qgF tmpF AI3); unfold QUAR_MIN_SIZE, QUAR_MAX_SIZE in *; lia).
    assert (PVK : rt_prov K <= rt_prov st).
    { rewrite <- (rt_prov_lists K KF1 (qg ++ qt) [] AI). unfold K, qg, qt. rewrite (sL_drained st WQ HT HC DQR).
      apply rt_prov_drain'; [exact WQ| unfold QUAR_MAX_CACHE in BIGC; fold qt; lia]. }
    assert (PV3 : rt_prov st3 <= rt_prov st) by (unfold st3; rewrite (rt_prov_lists K KF1 qgF tmpF AI3); exact PVK).
    assert (HR3 : RTREP st3 m3).
    { unfold st3, sL. apply (RTREP_of_QX K [] qgF tmpF [] m3 X3).
      intros e He. eapply Permutation_in; [apply (sL_qelems K qgF tmpF AI3)| exact He]. }
    assert (WM13 : wmono asegs m1 m3) by (eapply wmono_trans; [exact WM2| exact WM3]).
    assert (WM03 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1| exact WM13]).
    assert (RTS3 : RTS st3 m3 mo g).
    { apply RTS_intro; [exact HR3| exact WF3| apply RTMODEL_lists; unfold K, Kst; apply RTMODEL_q_set; exact HM
                       | apply GWIN_lists; unfold K, Kst; apply GWIN_q_set; eapply GWIN_mem; [exact HG| exact HO| exact WM03]
                       | exact HFR| apply SWIN_lists; unfold K, Kst; apply SWIN_q_set; exact HSW]. }
    assert (SP3 : st_sp0 st3 = st_sp0 st) by (unfold st3, sL, K, Kst; rewrite !q_set_sp0; reflexivity).
    assert (AC3 : acache st3 = acache st) by (unfold st3, sL, K, Kst; rewrite !q_set_acache; reflexivity).
    assert (TPV : bv_unsigned (wz tmpA : word) = tmpA) by (apply bvu_wz; unfold tmpA; lia).
    unfold rec_frame in FR3.
    apply (proj1 (rw_cells_app m3 (bv_unsigned sp - 80) [_; _; _; _] (_ :: _))) in FR3 as [TMP3 SAV3].
    cbn [cells_size Cells.csize Nat.add] in SAV3. change (Z.of_nat 32) with 32 in SAV3.
    assert (CP13 : cli_pres st (bv_unsigned sp) m1 m3).
    { pose proof (cli_pres_dwin K WFK' lo (bv_unsigned sp) HCL HSPC _ m1 m3 (munch_cat _ _ _ _ _ MU2 MU3) WM13) as CPK.
      specialize (CPK ltac:(apply Forall_app; split; [constructor; [right; left; cbn [fst snd]; lia| constructor]| exact HW3])).
      unfold K, Kst in CPK. apply cli_pres_q_set in CPK. exact CPK. }
    assert (ES13 : errno_same m1 m3).
    { eapply (errno_dwin K WFK' lo (bv_unsigned sp) HCL); [exact (munch_cat _ _ _ _ _ MU2 MU3)|].
      apply Forall_app; split; [constructor; [right; left; cbn [fst snd]; lia| constructor]| exact HW3]. }
    (* [comment removed for export] *)
    fold tmpA.
    eapply lscps_bind.
    { eapply (DOREC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo g st3 tmpA Sx lo);
        [exact RTS3| exact G6| rewrite G3, KF3; exact HAP| reflexivity| rewrite AC3; reflexivity| reflexivity| exact TP| exact HSX
        | rewrite TPV; lia| rewrite SP3; unfold tmpA; lia| rewrite G5; exact TMP3| lia| rewrite TPV; exact ST3| exact HCL
        | rewrite TPV; unfold tmpA, ADOREC_STACK; lia| exact MI3]. }
    cbv beta. intros ms4 mo4 g4 PO.
    destruct PO as (e0 & e1 & e2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & e3 & e4 & e5 & e6 & m4 & st4 & -> & MI4 & REL & RTS4 & ST4 & TMP4 & CP4 & ES4 & GM4 & BO4).
    rewrite TPV in ST4.
    destruct REL as ((SBQ4 & QT4 & QG4 & QP4 & FR4) & QTM4 & QC4).
    (* [comment removed for export] *)
    assert (SAV4 : rw_cells asegs m4 (tmpA + 32) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { unfold cli_pres in CP4. eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4); [exact SAV3|]. left. cbn [cells_size Cells.csize Nat.add].
      rewrite SP3. unfold tmpA. lia. }
    assert (FR4' : rw_cells asegs m4 tmpA (rec_frame 0 0 0 0 s4 s3 s2 s1 s0 ra)).
    { unfold rec_frame. apply (proj2 (rw_cells_app m4 tmpA [_; _; _; _] (_ :: _))). split; [exact TMP4|].
      cbn [cells_size Cells.csize Nat.add]. change (Z.of_nat 32) with 32. exact SAV4. }
    cbv beta delta [wz].
    replace (ret_pc (Z_to_bv 64 212508)) with (Z_to_bv 64 212508) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (rec_epi_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s3 s2 s1 s0 ra F fc m4 0 0 0 0 lo);
        [exact MI4| fold (wz tmpA); rewrite TPV; exact ST4| exact HCL| fold (wz tmpA); rewrite TPV; unfold tmpA; lia
        | fold (wz tmpA); rewrite TPV; unfold tmpA; lia| fold (wz tmpA); rewrite TPV; exact FR4']. }
    cbv beta. intros ms5 (-> & ST5). fold (wz tmpA) in *. rewrite TPV in *. unfold tmpA in ST5. replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) in * by lia.
    apply evt_done. apply lscps_done.
    unfold drain_post, rt_post_std. cbv beta delta [wz]. unfold tmpA. replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia.
    rewrite Z_to_bv_bv_unsigned. do 15 eexists. exists m4, st4.
    split; [reflexivity|]. split; [exact MI4|].
    assert (SBQ3 : same_but_quarantine st st3) by (unfold st3, sL; eapply sbq_trans; [unfold K, Kst; apply sbq_q_set| apply sbq_q_set]).
    split.
    { split; [eapply sbq_trans; [exact SBQ3| exact SBQ4]|].
      split; [rewrite QP4, G4; exact KF4|]. split; [rewrite QT4; exact G1|]. split; [exact QTM4|]. split; [exact QC4|].
      intros c Hc NE FRc. apply (FR4 c Hc NE). unfold st3, sL. apply fresh_cls_q_set. unfold K, Kst. apply fresh_cls_q_set. exact FRc. }
    split; [exact RTS4|]. split; [exact ST5|].
    assert (CP34 : cli_pres st (bv_unsigned sp) m3 m4).
    { pose proof (cli_pres_up st3 (tmpA + 32) (bv_unsigned sp) m3 m4 CP4 ltac:(unfold tmpA; lia)) as CPx.
      unfold st3, sL in CPx. apply cli_pres_q_set in CPx. unfold K, Kst in CPx. apply cli_pres_q_set in CPx. exact CPx. }
    split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP1|]; eapply cj_pres_trans; [exact CP13| exact CP34]|].
    split; [eapply errno_same_trans; [exact ES1|]; eapply errno_same_trans; [exact ES13| exact ES4]|].
    split; [exact GM4|]. unfold budget_ok in *. lia.
Qed.
End DRAIN.

End CeilWrap.
