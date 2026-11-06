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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition gfa_entry : Z := 0x3c04c.
Definition gfa_locked : Z := 0x3c19c.
Definition gfa_popret : Z := 0x3c308.
Definition pop_entry : Z := 0x3c354.
Definition gfa_stack : Z := 128.
Definition kMutexWriter : Z := 1152921504606846976. (* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_array_of (sb c : Z) : Z := sb + c * 4294967296 + 3758096384.

(* [comment removed for export] *)
Definition gfa_frame (scr : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 24 scr; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition gfa_lock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo ri sb c : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 128 -> alloc_ceiling <= lo ->
    a0 = wz 0xb1558 -> a2 = wz c ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m 0xb1588 [C8 (wz ri)] ->
    1 <= c <= 31 -> kHighMemBeg <= ri -> ri + 4096 <= alloc_ceiling -> ri mod 128 = 0 -> 0 <= sb -> sb + 2^37 <= 2^47 ->
    rw_cells rsegs m (ri + 128 * c) [C8 (wz 0)] ->
    (forall (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (ri + 128 * c) [C8 (wz kMutexWriter)] ->
        rw_cells rsegs m' (bv_unsigned sp + -128) (gfa_frame scr s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 128, bv_unsigned sp); (ri + 128 * c, ri + 128 * c + 8)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 128) ->
        evt rsegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp tp t0' t1' t2' (wz (ri + 128 * c)) (wz 0xb1558) a0' a1 (wz c) a3 a4 a5' a6' a7'
                            s2 (wz 2305843009213693952) (wz (free_array_of sb c)) (wz 1099511627776) (wz 1152921504607895551)
                            (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
                        F (wz gfa_locked) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz gfa_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (usp lo R fa base n E cnt maxc csz : Z) (na : word)
    (ws ks : list word) (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
     ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 1) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
     /\ munch [(usp - 128, usp); (R, R + 8); (R + 16, R + 24); (R + 72, R + 80); (E + 16, E + 80)] m m'
     /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
     /\ rw_cells rsegs m' R [C8 (wz 0)]
     /\ rw_cells rsegs m' (R + 16) [C8 (wz base)]
     /\ rw_cells rsegs m' (R + 72) [C8 (wz (bv_unsigned na + n))]
     /\ u32arr rsegs m' (fa + 4 * base) ws
     /\ rw_cells rsegs m' E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s (ws ++ skipn (Z.to_nat n) ks))].

(* [comment removed for export] *)
Definition gfa_fast_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo R sb c nf n E cnt maxc csz : Z) (na : word) (ws ks : list word) (scr : list byte)
         (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    let fa := free_array_of sb c in
    mem_inv rsegs m -> stk rsegs m lo (usp - 128) -> lo <= usp - 128 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> R mod 8 = 0 ->
    aobj E 80 -> E + 80 <= alloc_ceiling -> E mod 16 = 0 ->
    kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 -> 1 <= c <= 31 ->
    1 <= n <= 8 -> n <= nf -> nf < 2^27 -> length ws = Z.to_nat n -> length ks = 16%nat ->
    0 <= cnt < 2^32 -> 0 <= maxc < 2^32 -> 0 <= csz < 2^64 ->
    (E + 80 <= R \/ R + 128 <= E) -> (E + 80 <= sb \/ sb + 2^37 <= E) -> (R + 128 <= sb \/ sb + 2^37 <= R) ->
    rw_cells rsegs m (usp + -128) (gfa_frame scr s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m R [C8 (wz kMutexWriter)] ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] ->
    rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - n)) ws ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (gfa_post gp tp F fc usp lo R fa (nf - n) n E cnt maxc csz na ws ks s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 m)
        (MS (mkR ra (wz (usp + -128)) gp tp t0 t1 t2 (wz R) (wz 0xb1558) a0 a1 (wz c) (wz (E + 16)) (wz n) a5 a6 a7
                 s2 (wz 2305843009213693952) (wz fa) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz gfa_locked) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_popcall_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a5 a6 a7 s2 s10 s11 t3 t4 t5 t6 s3 s4 s5 s6 s7 s8 s9 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp R this c nf n D : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> 0 <= usp - 128 -> usp <= 2^47 ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling ->
    0 <= n < 2^64 -> 0 <= nf < n -> 0 <= this < 2^64 -> 0 <= D < 2^64 ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] ->
    (forall (a5' : word),
        evt rsegs Q (MS (mkR (wz gfa_popret) (wz (usp + -128)) gp tp t0 t1 t2 (wz R) (wz this) (wz this) a1 (wz c) (wz R) (wz (n - nf)) a5' a6 a7
                            a0 s3 s4 (wz D) (wz n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz pop_entry) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -128)) gp tp t0 t1 t2 (wz R) (wz this) a0 a1 (wz c) (wz D) (wz n) a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz gfa_locked) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_popok_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo R sb c nf n E cnt maxc csz r : Z) (na : word) (ws ks : list word) (scr : list byte)
         (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    let fa := free_array_of sb c in
    mem_inv rsegs m -> stk rsegs m lo (usp - 128) -> lo <= usp - 128 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> R mod 8 = 0 ->
    aobj E 80 -> E + 80 <= alloc_ceiling -> E mod 16 = 0 ->
    kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 -> 1 <= c <= 31 ->
    1 <= n <= 8 -> n <= nf -> nf < 2^27 -> length ws = Z.to_nat n -> length ks = 16%nat ->
    0 <= cnt < 2^32 -> 0 <= maxc < 2^32 -> 0 <= csz < 2^64 -> r <> 0 -> 0 <= r < 2^64 ->
    (E + 80 <= R \/ R + 128 <= E) -> (E + 80 <= sb \/ sb + 2^37 <= E) -> (R + 128 <= sb \/ sb + 2^37 <= R) ->
    rw_cells rsegs m (usp + -128) (gfa_frame scr s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m R [C8 (wz kMutexWriter)] ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] ->
    rw_cells rsegs m (R + 72) [C8 na] ->
    u32arr rsegs m (fa + 4 * (nf - n)) ws ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (gfa_post gp tp F fc usp lo R fa (nf - n) n E cnt maxc csz na ws ks s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 m)
        (MS (mkR ra (wz (usp + -128)) gp tp t0 t1 t2 (wz R) (wz 0xb1558) (wz r) a1 a2 a3 a4 a5 a6 a7
                 s2 (wz 2305843009213693952) (wz fa) (wz (E + 16)) (wz n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz gfa_popret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_popfail_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo R : Z) (scr : list byte)
         (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp - 128) -> lo <= usp - 128 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> R mod 8 = 0 ->
    rw_cells rsegs m (usp + -128) (gfa_frame scr s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m R [C8 (wz kMutexWriter)] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 0) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 128, usp); (R, R + 8)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' R [C8 (wz 0)])
        (MS (mkR ra (wz (usp + -128)) gp tp t0 t1 t2 (wz R) (wz 0xb1558) (wz 0) a1 a2 a3 a4 a5 a6 a7
                 s2 (wz 2305843009213693952) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz gfa_popret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refill_entry : Z := 0x3bf4c.
Definition refill_ret : Z := 0x3bf8c.
Definition refill_frame (pad : list byte) (s1 s0 ra : word) : list cell := [CB 8 pad; C8 s1; C8 s0; C8 ra].
Definition refill_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo C E cl cnt maxc csz : Z) (ks : list word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> alloc_ceiling <= lo ->
    aobj C 3888 -> C + 3888 <= alloc_ceiling -> aobj E 80 -> E + 80 <= alloc_ceiling -> 0 <= cl < 2^64 ->
    0 <= cnt < 2^32 -> 1 <= maxc < 2^31 -> 0 <= csz < 2^64 -> length ks = 16%nat ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    (forall (pad : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -32) (refill_frame pad s1 s0 ra) ->
        rw_cells rsegs m' E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
        munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 32) ->
        evt rsegs Q (MS (mkR (wz refill_ret) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz E) (wz (Z.shiftr maxc 1))
                            (wz 0xb1558) (wz (C + 2560)) (wz cl) (wz (E + 16)) (wz (Z.shiftr maxc 1)) a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz gfa_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz E) (wz 0xb1558) (wz cl) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz refill_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition refill_pre0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo C cl : Z) (cnt mc0 cs0 : Z -> Z) (ks : Z -> list word)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> alloc_ceiling <= lo ->
    aobj C 3888 -> C + 3888 <= alloc_ceiling -> 1 <= cl <= 31 -> mc0 cl = 0 ->
    (forall i, 1 <= i <= 31 -> 0 <= cnt i < 2^32 /\ 0 <= mc0 i < 2^32 /\ 0 <= cs0 i < 2^64 /\ length (ks i) = 16%nat /\
       rw_cells rsegs m (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (mc0 i)); C8 (wz (cs0 i)); CB 64 (u32s (ks i))]) ->
    (forall (a5' a6' a7' t0' t1' t2' t3' t4' t5' : word) (pad : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -32) (refill_frame pad s1 s0 ra) ->
        (forall i, 1 <= i <= 31 ->
           rw_cells rsegs m' (C + 80 * i) [C4 (wz (cnt i)); C4 (wz (max_count i)); C8 (wz (class_size i)); CB 64 (u32s (ks i))]) ->
        munch [(bv_unsigned sp - 32, bv_unsigned sp); (C + 80, C + 2560)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 32) ->
        evt rsegs Q (MS (mkR (wz refill_ret) (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' (wz (C + 80 * cl)) (wz (refill_count cl))
                            (wz 0xb1558) (wz (C + 2560)) (wz cl) (wz (C + 80 * cl + 16)) (wz (refill_count cl)) a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
                        F (wz gfa_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz (C + 80 * cl)) (wz 0xb1558) (wz cl) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz refill_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition refill_epi_stmt : Prop :=
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo E n r cnt maxc csz : Z) (ks : list word) (pad : list byte)
         (s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 32) -> lo <= usp - 32 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    sp = wz (usp + -32) ->
    aobj E 80 -> E + 80 <= alloc_ceiling -> 0 <= n < 2^31 -> 0 <= r < 2^64 ->
    0 <= cnt < 2^32 -> 0 <= maxc < 2^32 -> 0 <= csz < 2^64 -> length ks = 16%nat ->
    rw_cells rsegs m (usp + -32) (refill_frame pad s1v s0v ra0) ->
    rw_cells rsegs m E [C4 (wz cnt); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
    bv_unsigned ra0 mod 2 = 0 ->
    (forall (m' : word -> option byte),
        rw_cells rsegs m' E [C4 (wz (if r =? 0 then cnt else n)); C4 (wz maxc); C8 (wz csz); CB 64 (u32s ks)] ->
        munch [(usp - 32, usp); (E, E + 4)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra0 (wz usp) gp tp t0 t1 t2 s0v s1v (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz refill_ret) sp gp tp t0 t1 t2 (wz E) (wz n) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz refill_ret) fc None m (seg_rom rsegs)).

End CEIL.
