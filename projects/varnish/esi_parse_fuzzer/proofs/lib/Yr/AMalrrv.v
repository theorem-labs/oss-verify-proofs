(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AMalq4j.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ACells ARtStmts ARtSscs ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalz1i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Notation apart := AMallocA.apart (only parsing).

(* [comment removed for export] *)
Definition comb_frameR (n : Z) : list cell :=
  [C8 (wz (rz_size n)); C8 (wz (needed_size n)); C8 (wz 8); C8 (wz n); C8 (wz 1); C8 (wz 0x3743c)].
(* [comment removed for export] *)
Definition gfa_frameR (scr : list byte) (thr stkobj n C k E : Z) : list cell :=
  gfa_frame scr (wz 1) (wz thr) (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz 0xb1d58) (wz C) (wz 8) (wz k) (wz E) (wz refill_ret).

Section HT.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_head_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo n stkobj canfill thr c maxc sb ri : Z) (LW : list (Z * Z))
    (LINESP : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' =>
    let usp := bv_unsigned sp in let C := thr + 208 in let E := C + 80 * c in let R := ri + 128 * c in let k := Z.shiftr maxc 1 in
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (junk0 pad scr : list byte) (m' : word -> option byte),
      ms' = MS (mkR (wz refill_ret) (wz (usp + -128 + -48 + -32 + -128)) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (C + 2560)) (wz c) (wz (E + 16)) (wz k) a5' a6' a7'
                   (wz 8) (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) (wz thr) (wz 1) t3' t4' t5' t6')
               F (wz gfa_locked) fc None m' (seg_rom rsegs)
      /\ munch ([(usp - 1024, usp); (R, R + 8)] ++ LW) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -128 + -48 + -32 - 128)
      /\ rw_cells rsegs m' (usp + -128) (alloc_s1a_frame sp canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra junk0)
      /\ rw_cells rsegs m' (usp + -128 + -48) (comb_frameR n)
      /\ rw_cells rsegs m' (usp + -128 + -48 + -32) (refill_frame pad (wz E) (wz c) (wz comb_refill_ret))
      /\ rw_cells rsegs m' (usp + -128 + -48 + -32 + -128) (gfa_frameR scr thr stkobj n C k E)
      /\ rw_cells rsegs m' R [C8 (wz kMutexWriter)]
      /\ LINESP m'.

(* [comment removed for export] *)
Definition alloc_head_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (lo n stkobj canfill tsd ctx thr c maxc sb ri : Z) (ks : list word),
    let usp := bv_unsigned sp in
    (* [comment removed for export] *)
    mem_inv rsegs m -> stk rsegs m lo usp -> alloc_ceiling <= lo /\ lo <= usp - 1024 -> usp mod 16 = 0 -> usp + 65536 < 2^64 ->
    1 <= n <= 64512 -> 0 <= canfill <= 1 -> usp <= stkobj /\ stkobj + 2064 <= 2^47 ->
    (* [comment removed for export] *)
    rzlog_stmt -> get_thread_stmt -> classid_blk_stmt ->
    (* [comment removed for export] *)
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] -> ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m 0xb2b80 [C2 (wz 16); C2 (wz 2048)] -> ro_cells rsegs m 0xb2b78 [C8 (wz (2^40))] ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    (* [comment removed for export] *)
    thread_cells m tp tsd ctx thr -> ro_cells rsegs m thr [C8 (wz ctx)] -> ro_cells rsegs m (ctx + 8) [C4 (wz 0)] ->
    aobj thr 4096 /\ thr + 4096 <= alloc_ceiling -> thr mod 16 = 0 -> aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling ->
    0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000 -> bv_unsigned tp = 0x5e83d8 ->
    kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling ->
    apart thr 4096 sb (2^37) -> apart ctx 0x10000 sb (2^37) -> apart ctx 0x10000 thr 4096 ->
    (* [comment removed for export] *)
    c = size_class (needed_size n) ->
    rw_cells rsegs m (thr + 208 + 80 * c) [C4 (wz 0); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
    length ks = 16%nat -> 2 <= maxc <= 16 ->
    kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 -> sb mod 4096 = 0 ->
    apart thr 4096 ri 4096 -> apart ri 4096 sb (2^37) -> apart ctx 0x10000 ri 4096 ->
    rw_cells rsegs m (ri + 128 * c) [C8 (wz 0)] ->
    evt rsegs (alloc_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo n stkobj canfill thr c maxc sb ri [] (fun _ => True))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1d58) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x3719c) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition alloc_head0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (lo n stkobj canfill tsd ctx thr c sb ri : Z) (cnt mc0 cs0 : Z -> Z) (ks : Z -> list word),
    let usp := bv_unsigned sp in let C := thr + 208 in
    mem_inv rsegs m -> stk rsegs m lo usp -> alloc_ceiling <= lo /\ lo <= usp - 1024 -> usp mod 16 = 0 -> usp + 65536 < 2^64 ->
    1 <= n <= 64512 -> 0 <= canfill <= 1 -> usp <= stkobj /\ stkobj + 2064 <= 2^47 ->
    rzlog_stmt -> get_thread_stmt -> classid_blk_stmt ->
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] -> ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m 0xb2b80 [C2 (wz 16); C2 (wz 2048)] -> ro_cells rsegs m 0xb2b78 [C8 (wz (2^40))] ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m 0xb1d88 [C8 (wz ri)] ->
    thread_cells m tp tsd ctx thr -> ro_cells rsegs m thr [C8 (wz ctx)] -> ro_cells rsegs m (ctx + 8) [C4 (wz 0)] ->
    aobj thr 4096 /\ thr + 4096 <= alloc_ceiling -> thr mod 16 = 0 -> aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling ->
    0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000 -> bv_unsigned tp = 0x5e83d8 ->
    kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling ->
    apart thr 4096 sb (2^37) -> apart ctx 0x10000 sb (2^37) -> apart ctx 0x10000 thr 4096 ->
    c = size_class (needed_size n) ->
    (forall i, 1 <= i <= 31 ->
        0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ks i) = 16%nat /\
        rw_cells rsegs m (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ks i))]) ->
    mc0 c = 0 -> cnt c = 0 ->
    kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 -> sb mod 4096 = 0 ->
    apart thr 4096 ri 4096 -> apart ri 4096 sb (2^37) -> apart ctx 0x10000 ri 4096 ->
    rw_cells rsegs m (ri + 128 * c) [C8 (wz 0)] ->
    evt rsegs (alloc_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo n stkobj canfill thr c (max_count c) sb ri
                 [(C + 80, C + 2560)]
                 (fun m' => forall i, 1 <= i <= 31 ->
                    rw_cells rsegs m' (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ks i))]))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1d58) (wz n) (wz 8) (wz stkobj) (wz 1) (wz canfill) a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x3719c) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mg : word -> option byte) (lo n canfill thr c maxc sb AB q r8 d e n0 f0 ri nf0 : Z)
    (ks ws : list word) (b1w : byte) (na : word) (vs : list word) (D : list (list Z)) (k : list Z) (uj : list byte)
    (dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' : word) (m' md : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (AB + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (alloc_refill_W sp thr c AB n q r8 d e n0 f0 ri) mg m'
    /\ wmono rsegs mg m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (wz (Z.shiftr maxc 1 - 1)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s (ws ++ skipn (Z.to_nat (Z.shiftr maxc 1)) ks))]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' (ri + 128 * c) [C8 (wz 0)]
    /\ rw_cells rsegs m' (ri + 128 * c + 16) [C8 (wz nf0)]
    /\ rw_cells rsegs m' (ri + 128 * c + 72) [C8 (wz (bv_unsigned na + Z.shiftr maxc 1))]
    /\ u32arr rsegs m' (free_array_of sb c + 4 * nf0) ws
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0'; C8 v1'; C8 v2']
    /\ u64arr rsegs m' (thr + 2912) (upd vs (Z.to_nat c) vc')
    /\ rw_cells rsegs m' (AB + rz_size n + -16)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land (b1_mid (bv_unsigned b1w)) 243) 0));
          C2 (wz 0); C4 (wz n); C8 (wz (snd (depot_putC D k)))]
    /\ (rz_size n <> 16 -> rw_cells rsegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (AB + rz_size n + -16))])
    /\ bytes_at rsegs m' (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))
    /\ wr_at rsegs m' (q + r8 + kShadowOffset) d
    /\ (e <> 0 -> rw_cells rsegs m' (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)])
    /\ rw_cells rsegs m' (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) (fill_result canfill uj (Z.to_nat (Z.min n 4096)))]
    /\ dr AL_pasan rsegs (fst (depot_putC D k)) n0 f0 md
    /\ munch (alloc_hit_W2 sp thr c AB n q r8 d e) md m' /\ wmono rsegs md m'.

(* [comment removed for export] *)
Definition alloc_tail_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (F : bvmap 5 word) (fc : bv 32) (mg : word -> option byte)
         (lo n stkobj canfill tsd ctx thr c maxc sb AB q r8 d e n0 f0 ri nf0 : Z)
         (ks ws : list word) (b0w b1w : byte) (kw statv na h2 w4 d8 j0 j1 v0 v1 v2 : word) (vs : list word)
         (D : list (list Z)) (k : list Z) (olds uj : list byte) (oldp : byte) (junk0 pad : list byte)
         (dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop),
    let usp := bv_unsigned sp in let C := thr + 208 in let E := C + 80 * c in let R := ri + 128 * c in let kk := Z.shiftr maxc 1 in
    (* [comment removed for export] *)
    alloc_ceiling <= lo /\ lo <= usp - 1024 -> usp mod 16 = 0 -> usp + 65536 < 2^64 -> bv_unsigned ra mod 2 = 0 ->
    1 <= n <= 64512 -> n = 8 * d + e -> 0 <= e < 8 -> 0 <= canfill <= 1 -> usp <= stkobj /\ stkobj + 2064 <= 2^47 ->
    (* [comment removed for export] *)
    get_thread_stmt -> thread_stats_stmt -> poison_stmt -> depot_put_stmt dr -> classid_blk2_stmt ->
    (* [comment removed for export] *)
    poison_consts mg ->
    ro_cells rsegs mg 0xa9188 [C8 (wz 0xb2bb8)] -> ro_cells rsegs mg 0xb2c0d [C1 (Z_to_bv 8 1)] ->
    ro_cells rsegs mg 0xb2be4 [C4 (wz 4096)] -> ro_cells rsegs mg 0xb2bec [C4 (wz kMallocFillByte)] ->
    ro_cells rsegs mg 0xa9df0 [C8 (wz 0x10)] -> ro_cells rsegs mg (bv_unsigned tp + 16) [C4 (wz 0)] ->
    ro_cells rsegs mg 0x146e80 [C8 (wz 0)] -> ro_cells rsegs mg 0xb1d78 [C8 (wz sb)] ->
    (* [comment removed for export] *)
    thread_cells mg tp tsd ctx thr -> ro_cells rsegs mg thr [C8 (wz ctx)] -> ro_cells rsegs mg (ctx + 8) [C4 (wz 0)] ->
    aobj thr 4096 /\ thr + 4096 <= alloc_ceiling -> thr mod 16 = 0 -> aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling ->
    0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000 -> bv_unsigned tp = 0x5e83d8 ->
    kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling ->
    apart thr 4096 sb (2^37) -> apart ctx 0x10000 sb (2^37) -> apart ctx 0x10000 thr 4096 ->
    (* [comment removed for export] *)
    c = size_class (needed_size n) -> length ks = 16%nat -> 2 <= maxc <= 16 ->
    kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 -> sb mod 4096 = 0 ->
    apart thr 4096 ri 4096 -> apart ri 4096 sb (2^37) -> apart ctx 0x10000 ri 4096 ->
    apart n0 kDepotNodesBlock ri 4096 -> apart f0 kStackStoreBlockBytes ri 4096 ->
    (* [comment removed for export] *)
    length ws = Z.to_nat kk -> 0 <= nf0 /\ nf0 + kk < 2^27 ->
    nth_error ws (Z.to_nat (kk - 1)) = Some kw -> bv_unsigned kw < 2^32 ->
    AB + class_size c <= sb + c * 2^32 + 3758096384 ->
    (* [comment removed for export] *)
    rw_cells rsegs mg (thr + 208 + 2576) [C8 statv] -> rw_cells rsegs mg (thr + 2800) [C8 v0; C8 v1; C8 v2] ->
    u64arr rsegs mg (thr + 2912) vs -> length vs = 32%nat ->
    (* [comment removed for export] *)
    AB = sb + c * 2^32 + 16 * bv_unsigned kw -> AB mod 32 = 0 -> AB = 8 * q -> sb <= AB /\ AB + class_size c <= sb + 2^37 ->
    rz_size n = 8 * r8 ->
    rw_cells rsegs mg (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8] ->
    (rz_size n <> 16 -> rw_cells rsegs mg AB [C8 j0; C8 j1]) ->
    ro_cells rsegs mg (q + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)] ->
    u8arr rsegs mg (q + r8 + kShadowOffset) olds -> length olds = Z.to_nat d ->
    (e <> 0 -> rw_cells rsegs mg (q + r8 + d + kShadowOffset) [C1 oldp]) ->
    rw_cells rsegs mg (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj] ->
    (* [comment removed for export] *)
    dr AL_pasan rsegs D n0 f0 mg -> NoDup (map depot_hashC D) -> Z.of_nat (length D) + 1 < 65535 ->
    depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames ->
    aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling -> aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling ->
    apart n0 kDepotNodesBlock sb (2^37) -> apart f0 kStackStoreBlockBytes sb (2^37) ->
    apart n0 kDepotNodesBlock thr 4096 -> apart f0 kStackStoreBlockBytes thr 4096 ->
    apart n0 kDepotNodesBlock ctx 0x10000 -> apart f0 kStackStoreBlockBytes ctx 0x10000 ->
    (forall D' (m1 m2 : word -> option byte), dr AL_pasan rsegs D' n0 f0 m1 ->
        (forall a, depot_foot AL_pasan n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pasan rsegs D' n0 f0 m2) ->
    (1 <= length k <= 255)%nat -> Forall (fun w => 0 <= w < 2^64) k ->
    ro_cells rsegs mg stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length k)))] ->
    bytes_at rsegs mg (stkobj + 16) (u64s (map (Z_to_bv 64) k)) ->
    (* [comment removed for export] *)
    rw_cells rsegs mg (usp + -128) (alloc_s1a_frame sp canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra junk0) ->
    rw_cells rsegs mg (usp + -128 + -48) (comb_frameR n) ->
    rw_cells rsegs mg (usp + -128 + -48 + -32) (refill_frame pad (wz E) (wz c) (wz comb_refill_ret)) ->
    (* [comment removed for export] *)
    forall ms',
      gfa_post gp tp F fc (usp + -128 + -48 + -32) lo R (free_array_of sb c) nf0 kk E 0 maxc (class_size c) na ws ks
               (wz 1) (wz thr) (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz 0xb1d58) (wz C) (wz 8) (wz kk) (wz E) (wz refill_ret) mg ms' ->
      evt rsegs (alloc_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mg lo n canfill thr c maxc sb AB q r8 d e n0 f0 ri nf0
                   ks ws b1w na vs D k uj dr) ms'.

End HT.
