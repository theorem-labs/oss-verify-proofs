(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtS4t2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition lcdealloc_entry : Z := 0x397b8.
Definition lcdealloc_after : Z := 0x39968.
Definition lcdrain_entry : Z := 0x39b4c.
Definition lcdrain_ret : Z := 0x39bb0.
Definition rta_entry : Z := 0x39cf0.
Definition rta_efasret : Z := 0x39e54.
Definition efas_entry : Z := 0x3a018.
Definition mrtos_entry : Z := 0x3a198.

(* [comment removed for export] *)
Definition lcd_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition lcdrain_frame (scr : list byte) (ra : word) : list cell :=
  [CB 8 scr; C8 (wz 0xb1558); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 ra].
(* [comment removed for export] *)
Definition rta_frame (scr : list byte) (sem : Z) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 16 scr; C8 (wz sem); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition lcdealloc_push_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (lo C c sb k cnt maxc : Z) (ks : list word) (statv : word),
    let E := C + 80 * c in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz C -> a1 = wz 0xb1558 -> a2 = wz c -> a3 = wz (sb + c * 4294967296 + 16 * k) ->
    aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 -> 1 <= c <= 31 ->
    kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 -> 0 <= k < 2^28 ->
    0 <= cnt < maxc -> maxc <= 16 -> length ks = 16%nat ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' E [C4 (wz (cnt + 1)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat cnt) (wz k)))]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz lcdealloc_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition lcdealloc_full_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (lo C c p maxc : Z) (ks : list word) (Q : machine_state -> Prop),
    let E := C + 80 * c in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz C -> a1 = wz 0xb1558 -> a2 = wz c -> a3 = wz p ->
    aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 -> 1 <= c <= 31 -> 0 <= p < 2^64 ->
    1 <= maxc <= 16 -> length ks = 16%nat ->
    rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
    (forall (a4' a5' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (lcd_frame s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' E [C4 (wz maxc); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 48) ->
        evt rsegs Q (MS (mkR (wz lcdealloc_after) (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz E) (wz C)
                            (wz C) (wz E) (wz 0xb1558) (wz c) a4' a5' a6 a7
                            (wz 0xb1558) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz lcdrain_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz lcdealloc_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition lcdealloc_after_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo C c sb k cnt maxc : Z) (ks : list word) (statv s4v s3v s2v s1v s0v ra0 : word),
    let E := C + 80 * c in
    mem_inv rsegs m -> stk rsegs m lo (usp - 48) -> lo <= usp - 48 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 -> 1 <= c <= 31 ->
    kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 -> 0 <= k < 2^28 ->
    0 <= cnt < 16 -> 0 <= maxc < 2^32 -> length ks = 16%nat ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    rw_cells rsegs m (usp + -48) (lcd_frame s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 48, usp); (E, E + 80); (C + 2576, C + 2584)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' E [C4 (wz (cnt + 1)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat cnt) (wz k)))]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv'])
        (MS (mkR ra (wz (usp + -48)) gp tp t0 t1 t2 (wz E) (wz C) a0 a1 a2 a3 a4 a5 a6 a7
                 (wz 0xb1558) (wz c) (wz (sb + c * 4294967296 + 16 * k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz lcdealloc_after) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lcdrain_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (lo C E c cnt maxc csz : Z) (ks : list word) (Q : machine_state -> Prop),
    let h := Z.shiftr maxc 1 in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    aobj C 3888 -> C + 3888 <= alloc_ceiling -> aobj E 80 -> E + 80 <= alloc_ceiling -> 0 <= c < 2^64 ->
    0 <= maxc < 2^32 -> h <= cnt < 2^31 -> 0 <= csz < 2^64 -> length ks = 16%nat ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    (forall (a6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -64) (lcdrain_frame scr ra) ->
        rw_cells rsegs m' E [C4 (wz (cnt - h)); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
        munch [(bv_unsigned sp - 64, bv_unsigned sp); (E, E + 4)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 64) ->
        evt rsegs Q (MS (mkR (wz lcdrain_ret) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1
                            (wz 0xb1558) (wz (bv_unsigned sp + -56)) (wz (C + 2560)) (wz c) (wz (E + 16 + 4 * (cnt - h))) (wz h) a6' a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz rta_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz E) (wz 0xb1558) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz lcdrain_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition lcdrain_post_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo : Z) (scr : list byte) (ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 - 48 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    rw_cells rsegs m (usp + -64) (lcdrain_frame scr ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 64 - 48, usp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz lcdrain_ret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_lock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo ri sb c mm stat D n nf : Z) (Q : machine_state -> Prop),
    let R := ri + 128 * c in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> alloc_ceiling <= lo ->
    a1 = wz mm -> a2 = wz stat -> a3 = wz c -> a4 = wz D -> a5 = wz n ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m 0xb1588 [C8 (wz ri)] ->
    1 <= c <= 31 -> kHighMemBeg <= ri -> ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 -> kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling ->
    0 <= mm < 2^64 -> 0 <= stat < 2^64 -> 0 <= D < 2^64 -> 0 <= n < 2^32 -> 0 <= nf < 2^32 ->
    rw_cells rsegs m R [C8 (wz 0)] ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] ->
    (forall (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' R [C8 (wz kMutexWriter)] ->
        rw_cells rsegs m' (R + 16) [C8 (wz nf)] ->
        rw_cells rsegs m' (bv_unsigned sp + -128) (rta_frame scr (R + 8) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 128, bv_unsigned sp); (R, R + 8)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 128) ->
        evt rsegs Q (MS (mkR (wz rta_efasret) (wz (bv_unsigned sp + -128)) gp tp t0' t1' t2' (wz R) (wz nf)
                            (wz 0xb1558) (wz R) (wz (sb + c * 4294967296)) (wz (nf + n)) a4' a5' a6' (wz 1500)
                            (wz c) (wz mm) (wz 0xb1558) (wz n) (wz D) (wz (nf + n)) (wz 2305843009213693952) (wz (free_array_of sb c))
                            (wz 1152921504607895551) (wz kMutexWriter) t3' t4' t5' t6')
                        F (wz efas_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1558) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz rta_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition efas_fast_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo R num mfa : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a1 = wz R -> a3 = wz num ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> 0 <= num < 2^40 -> 4 * num <= mfa -> mfa < 2^64 ->
    rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz efas_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition mrtos_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo ri c : Z) (v16 v80 v88 : word),
    let R := ri + 128 * c in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> alloc_ceiling <= lo ->
    ro_cells rsegs m 0xb1588 [C8 (wz ri)] -> ro_cells rsegs m 0xb1580 [C4 (wz 4294967295)] ->
    ro_cells rsegs m 0xa8b50 [C8 (wz 0x144660)] -> ro_cells rsegs m 0x144660 [C8 (wz 4096)] ->
    1 <= c <= 30 -> kHighMemBeg <= ri -> ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 ->
    rw_cells rsegs m (R + 16) [C8 v16] -> rw_cells rsegs m (R + 80) [C8 v80; C8 v88] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1558) a1 (wz c) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz mrtos_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition rta_post_stmt : Prop :=
  mrtos_stmt ->
  forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo ri sb c mm D n nf r : Z) (nfs v88 : word) (ws junk : list word) (scr : list byte)
         (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    let R := ri + 128 * c in let fa := free_array_of sb c in
    mem_inv rsegs m -> stk rsegs m lo (usp - 128) -> lo <= usp - 128 - 80 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    ro_cells rsegs m 0xb1588 [C8 (wz ri)] -> ro_cells rsegs m 0xb1580 [C4 (wz 4294967295)] ->
    ro_cells rsegs m 0xa8b50 [C8 (wz 0x144660)] -> ro_cells rsegs m 0x144660 [C8 (wz 4096)] ->
    1 <= c <= 30 -> kHighMemBeg <= ri -> ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 ->
    kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 ->
    aobj D (4 * n) -> D + 4 * n <= alloc_ceiling -> D mod 4 = 0 ->
    1 <= n <= 8 -> 0 <= nf -> nf + n < 2^27 -> r <> 0 -> 0 <= r < 2^64 -> 0 <= mm < 2^64 ->
    length ws = Z.to_nat n -> length junk = Z.to_nat n ->
    (ri + 4096 <= sb \/ sb + 2^37 <= ri) -> (D + 4 * n <= sb \/ sb + 2^37 <= D) -> (D + 4 * n <= ri \/ ri + 4096 <= D) ->
    rw_cells rsegs m (usp + -128) (rta_frame scr (R + 8) s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m R [C8 (wz kMutexWriter)] ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] ->
    rw_cells rsegs m (R + 80) [C8 nfs; C8 v88] ->
    u32arr rsegs m D ws ->
    u32arr rsegs m (fa + 4 * nf) junk ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 128 - 80, usp); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (fa + 4 * nf, fa + 4 * nf + 4 * n)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' R [C8 (wz 0)]
                 /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf + n))]
                 /\ rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + n)); C8 v88]
                 /\ u32arr rsegs m' D ws
                 /\ u32arr rsegs m' (fa + 4 * nf) ws)
        (MS (mkR ra (wz (usp + -128)) gp tp t0 t1 t2 (wz R) (wz nf) (wz r) a1 a2 a3 a4 a5 a6 a7
                 (wz c) (wz mm) (wz 0xb1558) (wz n) (wz D) (wz (nf + n)) (wz 2305843009213693952) (wz fa)
                 (wz 1152921504607895551) (wz kMutexWriter) t3 t4 t5 t6)
            F (wz rta_efasret) fc None m (seg_rom rsegs)).

End CEIL.
