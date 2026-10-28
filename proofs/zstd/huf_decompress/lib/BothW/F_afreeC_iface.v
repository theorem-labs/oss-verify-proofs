(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AQConst ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit AKit2 AKitQ F_apoison F_aalloc_s F_aalloc1 F_afree_iseg F_afree_front F_adrain F_afree_tail F_afree_icpt
     F_aenqueueR F_afree_tailR F_afree_icptR.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition drain_torec_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33460) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xb7008 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0xb7010 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells bsegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Definition drain_torec_stmt : Prop := forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> Q_MAX < gqb + qb -> gqb + qb < 2^63 -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (if gfull then 0 < gnb /\ rw_cells bsegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (drain_torec_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x332bc) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dk_preC (ek : enq_kind) (g : gqd) (RNG : footprint) (t lst hm qb' : Z) (m : amem) : Prop :=
     g_drain g = true
  /\ rw_cells bsegs m 0xb7008 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0xb7010 [C8 (Z_to_bv 64 (g_nb g)); C8 (Z_to_bv 64 (g_fst g)); C8 (Z_to_bv 64 (g_lst g)); C8 (Z_to_bv 64 (g_qb g))]
  /\ 0 <= g_nb g < 2^62 /\ 0 <= g_qb g /\ 0 <= g_fst g < 2^64 /\ 0 <= g_lst g < 2^64
  /\ Q_CACHE < qb' /\ Q_MAX < g_qb g + qb' /\ g_qb g + qb' < 2^63
  /\ (if g_full g then 0 < g_nb g /\ rw_cells bsegs m (g_lst g) [C8 (Z_to_bv 64 (g_nx g))] /\ 0x10007fff8000 <= g_lst g /\ g_lst g + 8192 <= ATOP
                     /\ (t + 4096 <= g_lst g \/ g_lst g + 8192 <= t) /\ (hm + 16 <= g_lst g \/ g_lst g + 8 <= hm)
                     /\ (lst + 8192 <= g_lst g \/ g_lst g + 8192 <= lst) /\ (ek_b ek lst + 8192 <= g_lst g \/ g_lst g + 8192 <= ek_b ek lst)
                     /\ rng RNG (g_lst g) 8192
      else g_nb g = 0 /\ g_lst g = 0).

Definition dk_postC (g : gqd) (nb' fst' lst' qb' : Z) (m' : amem) : Prop :=
     rw_cells bsegs m' 0xb7008 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m' 0xb7010 [C8 (Z_to_bv 64 (g_nb g + nb')); C8 (Z_to_bv 64 (if g_full g then g_fst g else fst'));
                                 C8 (Z_to_bv 64 lst'); C8 (Z_to_bv 64 (g_qb g + qb'))]
  /\ (if g_full g then rw_cells bsegs m' (g_lst g) [C8 (Z_to_bv 64 fst')] else True).

(* [comment removed for export] *)
Definition put_frame (cbc cbs s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 cbc; C8 cbs; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition put_torec_post (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x35a90) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33460) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (shad (hm + 16), shad (hm + 16) + shlen (rup n 8));
              (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
              (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
              (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 80)
    /\ rw_cells bsegs m' (bv_unsigned sp - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'.

(* [comment removed for export] *)
Definition put_torec_stmt : Prop := forall (ek : enq_kind) (g : gqd) (t hm lst : Z) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo : Z) (sjunk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 0xb6f70 -> a1 = Z_to_bv 64 (t + 80) -> a2 = Z_to_bv 64 (t + 208) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells bsegs m 0xb6fb0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xb2120 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xb7b24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  poison_cells m ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> 0 <= b1 < 256 -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF bsegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x359b4) fc None m (seg_rom bsegs)).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_from_refill_torec_stmt : Prop := forall (full : bool) (g : gqd) (t hm lst b : Z) RNG
    (ra sp gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2' a3' a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (n nb fst0 qb b1 actx lo nx bsz cnt spacebeg : Z) (maxc csz stj idxw : word) (chunks hs : list word)
    (j0 : list byte),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -144) -> ATOP <= lo -> lo <= bv_unsigned sp - 144 ->
  mem_inv bsegs m ->
  a2 = Z_to_bv 64 (t + 208) ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -144)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 a2; C8 a3; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xb6f70); C8 (Z_to_bv 64 0x35b58)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xb6fb0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 16 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 16 <= t \/ t + 4096 <= hm) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xb6cb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 16 <= b \/ b + 8192 <= hm) -> (hm + 16 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  (* [comment removed for export] *)
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 16 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  iclr t 4096 ->                                            (* [comment removed for export] *)
  evtF bsegs RNG (put_torec_post ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a3 (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35cb8) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition free_torec_post (L : alayout) (ek : enq_kind) (g : gqd)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n nb fst0 lst qb b1 actx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) (t0 t1 t2 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' : list word)
                    (csA csT : list cell) (junk2 : list byte),
    let spP := bv_unsigned sp - 2128 in
    ms' = MS (mkR (Z_to_bv 64 0x35a90) (Z_to_bv 64 (spP - 80)) gp tp t0 t1 t2 xs0 xs1
                  (Z_to_bv 64 AQUAR_Q) (Z_to_bv 64 Q_MIN) (Z_to_bv 64 (t + 208)) a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x33460) fc None m' (seg_rom bsegs)
    /\ munch ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xbb500, 0xbb500 + 0x81030); (0x149d88, 0x149d88 + 4);
               (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
               (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
               (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
               (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
               (0xb7008, 0xb7008 + 4); (0xb7010, 0xb7010 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (spP - 80)
    /\ 0 < id < 2^31
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' (spP - 80) (put_frame (Z_to_bv 64 (t + 208)) a3 s6 ps5 ps4 ps3 ps2 ps1 ps0 (Z_to_bv 64 337368))
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' spP csA /\ cells_size csA = 16%nat
    /\ rw_cells bsegs m' (spP + 16) csT /\ cells_size csT = 2040%nat
    /\ rw_cells bsegs m' (bv_unsigned sp - 72) [C8 spv; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
    /\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ ek_post ek t lst hm n m'
    /\ dk_postC g (ek_nb ek nb) (ek_fst ek fst0) (ek_lst ek lst) (qb + ek_delta ek n) m'
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0x149d88 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xbb500 (0xbb500 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xbb508 + 8 * j) (le8 (Z_to_bv 64 0)))
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
Definition free_torec_stmt : Prop := forall (L : alayout) (ia : bool) (ek : enq_kind) (g : gqd) RNG
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (t ctx hm n b1 actx lo top bot nb fst0 lst qb : Z) (uw : word) (sj : list word) (sjunk : list byte) (trt : list Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (hm + 16) ->
  bv_unsigned sp mod 16 = 0 ->
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xbaffc [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0x14be4a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xb2108 [C8 (Z_to_bv 64 0x149da0)] -> rw_cells bsegs m 0x149da0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0x14bdc8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xb6fb0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xb2120 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xb7b24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0x149d88 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xbb500 (0xbb500 + 0x81030) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xbb508 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
  rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
  ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
  (hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
  ek_pre ek RNG t nb lst n hm m -> ek_seps ek L hm lst ->
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  afree_unw RNG lo m top sp s0 ra trt ->
  bv_unsigned s0 <> bv_unsigned sp + 8 ->
  In (AFREE_PC :: trt) (al_U L) ->
  0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF bsegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition free_from_refill_torec_stmt : Prop := forall (L : alayout) (full : bool) (g : gqd) RNG
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem)
    (t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
    (junk2 j0 : list byte) (trt : list Z),
  let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
  stk bsegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (bv_unsigned sp + -2208)
     [C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
      C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x52568); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x525d8)] ->
  rw_cells bsegs m (bv_unsigned sp + -2272)
     [CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
      C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0xb6f70); C8 (Z_to_bv 64 0x35b58)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xb6fb0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells bsegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
  1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
  rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
  sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x149d88 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m 0xbb500 (0xbb500 + 0x81030) ->
  (forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xbb508 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  (* [comment removed for export] *)
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
             /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat
             /\ rng RNG lst 8192
   else nb = 0 /\ lst = 0) ->
  rw_cells bsegs m 0xb6cb8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat 8192) bs]) ->
  0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
  (t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
  (hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
  rng RNG b 8192 ->
  ek_seps ek L hm lst ->
  (* [comment removed for export] *)
  dk_preC ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
  (* [comment removed for export] *)
  ADEPOT DI L m ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  bv_unsigned sp < 2^47 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->      (* [comment removed for export] *)
  evtF bsegs RNG (free_torec_post L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35cb8) fc None m (seg_rom bsegs)).
End WithDepot.
End CANSEC1.
