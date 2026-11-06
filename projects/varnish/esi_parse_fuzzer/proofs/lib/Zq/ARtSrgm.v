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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSoqz ARtSnjd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition cbrec_tail : Z := 0x39520.
Definition gbb_entry : Z := 0x39638.
Definition ldealloc_entry : Z := 0x39980.
Definition ldealloc_poison : Z := 0x39a70.
Definition ldealloc_after : Z := 0x39a74.
Definition flush_entry : Z := 0x58558.
Definition unmapordie_entry : Z := 0x6c1c0.
Definition LMA_L : Z := 0xb1598.          (* [comment removed for export] *)
Definition LMA_STAT : Z := 0xb1808.       (* [comment removed for export] *)
Definition RI_PTR : Z := 0xb1588.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cbrec_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition nearest_step (m : Z) (acc h : Z) : Z :=
  if (m <? h) then acc else if (m - h <? m - acc) then h else acc.
Definition nearest (hs : list word) (m : Z) : Z := fold_left (fun acc h => nearest_step m acc (bv_unsigned h)) hs 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cbrec_stack : Z := 112.   (* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition cbrec_prim_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cb mh sb ri c idx d mu n b1 lo : Z) (old : list byte) (Q : machine_state -> Prop),
    let size := class_size c in
    let p := sb + c * 2^32 + idx * size in
    let r8 := round_up n 8 in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    a0 = wz cb -> a1 = wz mh ->
    mh = p + d -> 0 <= d < size -> d mod 16 = 0 -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * size <= mu -> 0 <= mu < 2^32 ->
    kHighMemBeg <= sb -> sb + 2^37 <= 2^47 -> sb mod 4096 = 0 -> sb + 2^37 <= ri -> ri + 4096 <= alloc_ceiling ->
    1 <= n < 2^32 -> mh + 16 + r8 <= 2^47 -> 0 <= b1 < 256 ->
    poison_consts m ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m RI_PTR [C8 (wz ri)] -> ro_cells rsegs m (ri + 128 * c + 48) [C8 (wz mu)] ->
    (d = 0 \/ rw_cells rsegs m p [C8 (wz kAllocBegMagic)]) ->
    rw_cells rsegs m mh [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh (mh + 16)) [CB (Z.to_nat (r8 / 8)) old] ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (cbrec_frame s4 s3 s2 s1 s0 ra) ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 48) ->
        evt rsegs Q (MS (mkR ra' (wz (bv_unsigned sp + -48)) gp tp t0' t1' t2' (wz cb) (wz mh) a0' a1' a2' a3' a4' a5' a6' a7'
                            (wz p) (wz 0xb1558) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz cbrec_tail) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition gbb_stack : Z := 32.
Definition gbb_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (mh pa mb ms u1 u2 lo : Z) (hs : list word),
    let n := Z.of_nat (length hs) in
    let nr := nearest hs mh in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> alloc_ceiling <= lo ->
    a0 = wz LMA_L -> a1 = wz mh ->
    0 <= mh < 2^64 -> aobj pa (8 * n) -> pa + 8 * n <= alloc_ceiling -> pa mod 8 = 0 -> 1 <= n < 2^20 ->
    0 <= u1 < 256 -> 0 <= u2 < 2^15 ->
    aobj mb ms -> nr mod 4096 = 0 -> mb <= nr -> nr + 16 <= mb + ms -> nr <= mh < mb + ms -> mb + ms <= alloc_ceiling -> 0 <= mb ->
    (nr + 16 <= pa \/ pa + 8 * n <= nr) ->
    ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)] -> ro_cells rsegs m 0xb15d0 [C8 (wz n)] ->
    rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
    u64arr rsegs m pa hs ->
    ro_cells rsegs m nr [C8 (wz mb); C8 (wz ms)] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (nr + 4096)) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0xb1800, 0xb1804)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)]
                 /\ u64arr rsegs m' pa hs)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz gbb_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition cbrec_sec_stack : Z := 80.   (* [comment removed for export] *)
Definition cbrec_sec_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cb mh sb pa mb ms u1 u2 lo : Z) (hs : list word) (Q : machine_state -> Prop),
    let n := Z.of_nat (length hs) in
    let nr := nearest hs mh in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> alloc_ceiling <= lo ->
    a0 = wz cb -> a1 = wz mh ->
    0 <= sb -> sb + 2^37 < 2^64 -> (0 <= mh < sb \/ sb + 2^37 <= mh < 2^64) ->
    aobj pa (8 * n) -> pa + 8 * n <= alloc_ceiling -> pa mod 8 = 0 -> 1 <= n < 2^20 ->
    0 <= u1 < 256 -> 0 <= u2 < 2^15 ->
    aobj mb ms -> nr mod 4096 = 0 -> mb <= nr -> nr + 16 <= mb + ms -> nr <= mh < mb + ms -> mb + ms <= alloc_ceiling -> 0 <= mb ->
    (nr + 16 <= pa \/ pa + 8 * n <= nr) -> (nr + 4096 < sb \/ sb + 2^37 <= nr + 4096) ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)] -> ro_cells rsegs m 0xb15d0 [C8 (wz n)] ->
    rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
    u64arr rsegs m pa hs ->
    ro_cells rsegs m nr [C8 (wz mb); C8 (wz ms)] ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (cbrec_frame s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        u64arr rsegs m' pa hs ->
        munch [(bv_unsigned sp - 80, bv_unsigned sp); (0xb1800, 0xb1804)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 48) ->
        evt rsegs Q (MS (mkR ra' (wz (bv_unsigned sp + -48)) gp tp t0' t1' t2' (wz cb) (wz mh) a0' a1' a2' a3' a4' a5' a6' a7'
                            (wz (nr + 4096)) (wz 0xb1558) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz cbrec_tail) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition cbrec_tail_stack : Z := 32.   (* [comment removed for export] *)
Definition cbrec_tailp_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo cb C mh p sb c off n st b1 tsd ctx thr rf rfd : Z) (s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 48) -> lo <= usp - 48 - 32 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    tp = wz TP ->
    p = sb + c * 2^32 + off -> 0 <= c <= 31 -> 0 <= off < 2^32 -> 0 < sb -> sb + 2^37 <= 2^47 ->
    aobj mh 16 -> mh + 16 <= alloc_ceiling -> 0 <= n < 2^32 -> 0 <= st < 256 -> 0 <= b1 < 256 ->
    alloc_ceiling <= cb -> cb + 16 <= 2^47 -> cb mod 8 = 0 -> (cb + 16 <= usp - 80 \/ usp <= cb) ->
    0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    ro_cells rsegs m cb [C8 (wz C)] ->
    ro_cells rsegs m mh [C1 (Z_to_bv 8 st); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    thread_cells m tp tsd ctx thr ->
    rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)] ->
    (mh + 16 <= thr \/ thr + 4096 <= mh) ->
    rw_cells rsegs m (usp + -48) (cbrec_frame s4v s3v s2v s1v s0v ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    (forall (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        munch [(usp - 80, usp)  ; (thr + 2840, thr + 2856)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz C) (wz 0xb1558)
                            (wz c) (wz p) a4' a5' a6' a7'
                            s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz lcdealloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -48)) gp tp t0 t1 t2 (wz cb) (wz mh) a0 a1 a2 a3 a4 a5 a6 a7
                        (wz p) (wz 0xb1558) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_tail) fc None m (seg_rom rsegs)).

Definition cbrec_tails_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo cb mh p sb n st b1 tsd ctx thr rf rfd : Z) (s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 48) -> lo <= usp - 48 - 32 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    tp = wz TP ->
    p <> 0 -> (0 <= p < sb \/ sb + 2^37 <= p < 2^64) -> 0 <= sb -> sb + 2^37 <= 2^47 ->
    aobj mh 16 -> mh + 16 <= alloc_ceiling -> 0 <= n < 2^32 -> 0 <= st < 256 -> 0 <= b1 < 256 ->
    0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    ro_cells rsegs m mh [C1 (Z_to_bv 8 st); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    thread_cells m tp tsd ctx thr ->
    rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)] ->
    (mh + 16 <= thr \/ thr + 4096 <= mh) ->
    rw_cells rsegs m (usp + -48) (cbrec_frame s4v s3v s2v s1v s0v ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        munch [(usp - 80, usp); (thr + 2840, thr + 2856)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz LMA_L) (wz LMA_STAT) (wz p) a3' a4' a5' a6' a7'
                            s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz ldealloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -48)) gp tp t0 t1 t2 (wz cb) (wz mh) a0 a1 a2 a3 a4 a5 a6 a7
                        (wz p) (wz 0xb1558) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_tail) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ldealloc_stack : Z := 32.
Definition ldealloc_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (h pa idx msz csz nf ca gA gM u1 u2 srt lo : Z) (hs : list word) (hl : word) (hlb hlm hls : word) (Q : machine_state -> Prop),
    let n := Z.of_nat (length hs) in
    let hla := bv_unsigned hl in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> alloc_ceiling <= lo ->
    a0 = wz LMA_L -> a1 = wz LMA_STAT -> a2 = wz (h + 4096) ->
    aobj h msz -> h + msz <= alloc_ceiling -> h mod 4096 = 0 -> 4096 + 32 <= msz ->
    aobj pa (8 * n) -> pa + 8 * n <= alloc_ceiling -> pa mod 8 = 0 -> 1 <= n < 2^20 ->
    0 <= idx < n -> nth_error hs (Z.to_nat idx) = Some (wz h) -> nth_error hs (Z.to_nat (n - 1)) = Some hl ->
    aobj hla 32 -> hla + 32 <= alloc_ceiling -> hla mod 8 = 0 ->
    (h + 32 <= pa \/ pa + 8 * n <= h) -> (hla + 32 <= pa \/ pa + 8 * n <= hla) ->
    0 <= u1 < 256 -> 0 <= u2 < 2^15 -> 0 <= srt < 256 -> 0 <= nf < 2^64 -> 0 <= ca < 2^64 -> 0 <= gA < 2^64 -> 0 <= gM < 2^64 ->
    0 <= csz < 2^64 ->
    ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)] ->
    rw_cells rsegs m 0xb15d0 [C8 (wz n); C1 (Z_to_bv 8 srt)] ->
    rw_cells rsegs m 0xb15e8 [C8 (wz nf); C8 (wz ca)] ->
    rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
    rw_cells rsegs m 0xb1818 [C8 (wz gA); C8 (wz gM)] ->
    u64arr rsegs m pa hs ->
    rw_cells rsegs m h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
    (hla = h \/ ((h + 32 <= hla \/ hla + 32 <= h) /\ rw_cells rsegs m hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (n - 1))])) ->
    (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
        u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl) ->
        rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
        (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
        munch [(bv_unsigned sp - 32, bv_unsigned sp); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8); (0xb1800, 0xb1804);
               (0xb1818, 0xb1828); (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 32) ->
        evt rsegs Q (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0' t1' t2' (wz h) (wz h) (wz h) (wz msz) (wz 0) a3' a4' a5' a6' a7'
                            (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz ldealloc_poison) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ldealloc_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)

End CEIL.
