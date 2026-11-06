(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v (donor image sha256 5973b76807d8), with its module paths changed, names decodesegs0 -> tfibsegs and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/DecodeCallocWrap.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B; lib/Lib/DecodeCallocKit.v to its image-B copy lib/B/DecodeCallocKit.v) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* The middle of the calloc walk of image A: from the wrapper's first call (lib/A/DecodeCallocSeed.v's at_C1,
   pc 0x5239c) to the call of __asan::asan_calloc at 0x524a4, whose target 0x31bd4 the reached state sits at.

   WHAT THE WRAPPER DOES ON THE WAY (image A, read with capstone from the ORIGINAL unstripped twin
   fuzz_decode.asan; the walk
   runs them out of lib/A/DecodeCallocTbl.v's tbl_calloc_A, whose words are the image's own):

     0x5239c  jal 0x590ac <TryAsanInitFromRtl>      the contract returns 1 (decode_try_init_spec_A)
     0x523a0  beqz a0, 0x52400                      NOT taken: the not-yet-initialised arm at 0x52400 is dead
     0x523a4  addi s5, s0, -0x800                   s5 = s0 - 0x858 = the BufferedStackTrace object [this]
     0x523a8  addi s5, s5, -0x58
     0x523ac  addi a0, s0, -0x800                   a0 = s0 - 0x848 = this + 16 = its trace buffer
     0x523b0  addi a0, a0, -0x48
     0x523b4  addi s6, s5, 0x7ff
     0x523b8  sd zero, 9(s6)                        [this + 2056] = 0   (0x7ff + 9 = 0x808 = 2056)
     0x523bc  sd a0, 0(s5)                          [this] = this + 16
     0x523c0  sd zero, 8(s5)                        [this + 8 .. this + 16) = 0
     0x523c4  jal 0x59e34 <GetMallocContextSize>    the contract returns the 4-byte cell 0xa1abc = 30
     0x523c8  addi a1, zero, 2
     0x523cc  bltu a1, a0, 0x52434                  TAKEN (2 < 30): the unwind arm.  The other arm,
                                                    0x523d0 .. 0x523fc (the small-depth arm: it records
                                                    GetCurrentPc's return 0x523e8, not 0x52438, and at a cell
                                                    value of 0 records nothing at all), is dead under MCS30
     0x52434  jal 0x72a08 <StackTrace::GetCurrentPc>  returns its own return address, 0x52438
     0x52438  auipc a1, 0x47                        a1 = 0x99438
     0x5243c  ld a1, -0x708(a1)                     a1 = [0x98d30] = 0x1328e8 (&common_flags_dont_use)
     0x52440  lbu s4, 0x22(a1)                      s4 = [0x13290a] = 1 (fast_unwind_on_malloc)
     0x52444  mv s3, a0                             s3 = 0x52438, the pc the trace records
     0x52448  jal 0x59e34 <GetMallocContextSize>    again 30
     0x5244c  mv a5, a0                             a5 = 30
     0x52450  seqz a0, a0    0x52454 addi a0, a0, -1   a0 = -1 (the cell is not 0)
     0x52458  and a1, a0, s0                        a1 = s0 = the entry sp
     0x5245c  addi a0, zero, 1
     0x52460  sd a1, 9(s6)                          [this + 2056] = the entry sp
     0x52464  bltu a0, a5, 0x52478                  TAKEN (1 < 30)
     0x52478  addi a0, s0, -0x800   0x5247c addi a0, a0, -0x58     a0 = this
     0x52480  mv a1, s3   0x52484 mv a2, s0   0x52488 mv a3, zero  0x5248c mv a4, s4
     0x52490  jal 0x59e44 <BufferedStackTrace::UnwindImpl>   a5 = 30, a4 = 1: decode_unwind_spec_A
     0x52494  addi a2, s0, -0x800   0x52498 addi a2, a2, -0x58     a2 = this
     0x5249c  mv a0, s2   (the count)   0x524a0 mv a1, s1   (the size)
     0x524a4  jal 0x31bd4 <asan_calloc>             the reached state: pc 0x31bd4, ra 0x524a8

   THE FRAME.  sp = entry sp - 2144 throughout (DecodeCallocSkel.ICPT_FRAME); the object is at entry sp - 2136
   (ICPT_TRACE) and its buffer at entry sp - 2120 (ICPT_BUF); the object's last byte is at entry sp - 73
   (this + BST_SIZE = entry sp - 72), and the eight registers the prologue saved stand at entry sp - 64 ..
   entry sp - 1.  So every byte the wrapper and its callees write lies inside the stack window
   [entry sp - ASTACK, entry sp) that the unit's call precondition hands over, and [at_C2] carries the frame
   fact (outside that window the memory is the entry memory) and the window's presence.

   THE TRACE.  The unwinder's post names tr = if bp + 16 <? ly_top ly then unwind_of_chain pc0 ((bp, ra0, nfp0)
   :: ch) else [pc0], at bp = the entry sp, ra0 = the entry ra and nfp0 = the entry s0 (the wrapper saved those
   two at entry sp - 8 and entry sp - 16, 0x52368 and 0x5236c), and pc0 = 0x52438.  That is, word for word,
   YG0d.v:224 call_trace ly DEC_A_calloc_ra0 regs0 ch: the trace the unit's calloc contract names.  [at_C2]
   states the object's three cells in the form YGAlloc.alloc_pre asks for them: [this] = the buffer,
   [this + 8] (8 bytes) = the length, and [buffer + 8 * i] = the i-th pc.  The 8-byte read of the length is the
   unwinder's 4-byte write at this + 8 above the four zero bytes 0x523c0 left at this + 12 (the unwinder writes
   nothing between this + 12 and this + 16).

   THE BRANCH AT 0x523cc, AND WHY THE SMALL-DEPTH ARM IS DEAD.  Both sides of that branch are taken into
   account, and the walk follows the one the image's own cell selects: __asan::malloc_context_size is 30
   ([dec_cells_A]'s second conjunct), so `bltu a1, a0` at a1 = 2 is taken and the executor walks 0x52434
   onwards.  The other side, 0x523d0 .. 0x523fc, cannot reach [at_C2] whatever this walk did with it: it calls
   GetCurrentPc at 0x523e4, so the pc it writes into the buffer is 0x523e8 and not 0x52438, and at a cell value
   of 0 it leaves the length 0 and writes no pc at all.  Neither trace is YG0d.v:224 call_trace at
   DEC_A_calloc_ra0, and the second breaks YGAlloc.alloc_pre's 1 <= length tr; so that arm has no post that the
   next segment can consume, and the cell value is what closes it.

   THE SECTION'S OPEN HYPOTHESES.  PRE (the unit's call precondition), the four runtime-entry contracts this
   segment consumes (decode_try_init_spec_A, decode_mcs_spec_A, decode_getpc_spec_A, decode_unwind_spec_A;
   decode_zero_fill_spec_A belongs to the entry, not to the wrapper), [IMG] (the layout's image extent covers
   this unit's image, cgif's A/AFip.v:121 img_cover), [HTP] (the unit's thread pointer is decode's
   DEC_A_TP = 0x5d3d58) and [CELLS] = [dec_cells_A]: the sixteen cells the contracts read through, each one
   measured and listed at its definition.  Every one of them is a START-UP fact about .bss or .data, which this
   unit's symbol record cannot yet state (B is abstract here), so they stand as hypotheses, exactly as cgif's
   own walk takes its unwinder contract and its img_cover as hypotheses.  Nothing else is open: [walk_C2] ends
   in Qed, and its Print Assumptions names only Rocq's own primitive-integer, primitive-string, primitive-array
   and functional-extensionality axioms, all of toolchain/allowed-axioms.txt. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import
YB1v DecodeCallocTbl DecodeCalloc DecodeCallocSkel DecodeCallocSeed DecodeCallocRt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import DecodeCallocKit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YN2j YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import CallocImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The wrapper's own offsets, from the instructions above.  ICPT_FRAME = 2144 is DecodeCallocSkel's. *)
(* 0x523a4 / 0x523a8 `addi s5, s0, -0x800` + `addi s5, s5, -0x58`: the BufferedStackTrace object. *)
Definition ICPT_TRACE : Z := 0x800 + 0x58.
(* 0x523ac / 0x523b0 `addi a0, s0, -0x800` + `addi a0, a0, -0x48`: its trace buffer, the object + 16. *)
Definition ICPT_BUF : Z := 0x800 + 0x48.
(* 0x524a4 `jal 0x31bd4`: the return address the call of asan_calloc leaves in ra. *)
Definition DEC_A_calloc_ret : Z := 0x57204.
(* The byte of common_flags_dont_use the wrapper passes as the unwinder's request_fast (0x52440
   `lbu s4, 0x22(a1)`, a1 = 0x1328e8). *)
Definition DEC_A_cf_fast : Z := DEC_A_common_flags + CF_FAST_UNWIND_ON_MALLOC.
(* __asan::malloc_context_size at the call: ASan's default, the value cgif's own image carries at its
   counterpart cell (A/AF0m.v:86 `z4 (ANum 0xa6cfc) 0x1e`).  The unwinder contract's a5 premise is 30. *)
Definition DEC_A_MCS : Z := 30.

(* A read-only region of the symbolic state over an image cell: cgif's A/AFhy.v:23-25 lit8 / lit1.  Its base is
   None, so its offsets are absolute addresses, and its writable window is empty. *)
Definition lit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition lit1 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 1) 0 0 [YP09.mkChunk a (CVal 1 (SLit v))].

(* The state at 0x5239c with the two image cells the walk reads through (the GOT slot 0x98d30 that
   0x5243c loads &common_flags_dont_use from, and the fast-unwind byte 0x13290a that 0x52440 reads) added as
   regions, as cgif's A/AFhy.v:83-106 REG0 carries the cells its segments hand to the runtime entries. *)
Definition REG_C1X : smem := lit8 DEC_A_got_common_flags DEC_A_common_flags :: lit1 DEC_A_cf_fast 1 :: REG_C1.
Definition SS_C1X : sstate := mkSS DEC_A_calloc_call1 SR_C1 REG_C1X None FG0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ------------------------------------------------------------------------------------------------------------
   The cells the contracts of lib/A/DecodeCallocRt.v read through, at this unit's measured addresses.  Each is a
   .bss or .data cell that start-up code writes, so each is a hypothesis of the walk, not a fact about the
   image's bytes; the addresses are DecodeCallocRt.v's table, which lists how each was measured. *)
Definition dec_cells_A (ly : alayout) (W : world tfibsegs) (mem : word -> option byte) : Prop :=
let m := mrestrict (w_H W) mem in
(* __asan::asan_inited = 1: the runtime is up (TryAsanInitFromRtl's premise). *)
val_mem tfibsegs m DEC_A_asan_inited 1 1 /\
(* __asan::malloc_context_size = 30 (GetMallocContextSize's premise, and the unwinder's max_depth). *)
val_mem tfibsegs m DEC_A_malloc_context_size 4 DEC_A_MCS /\
(* __asan::tsd_key_inited = 1 and __asan::tsd_key = 0 (GetCurrentThread's path). *)
val_mem tfibsegs m DEC_A_tsd_key_inited 1 1 /\
val_mem tfibsegs m DEC_A_tsd_key 4 0 /\
(* the thread descriptor's tsd array, and the AsanThreadContext it holds. *)
val_mem tfibsegs m (DEC_A_TP - TSD_OFF) 8 DEC_A_TSD /\
val_mem tfibsegs m DEC_A_TSD 8 (ly_C ly) /\
val_mem tfibsegs m (ly_C ly + 152) 8 (ly_T ly) /\
(* the thread object's cells the unwinder reads: the fake-stack byte, the stack bounds, the unwinding flag. *)
val_mem tfibsegs m (ly_T ly + 40) 1 0 /\
val_mem tfibsegs m (ly_T ly + 8) 8 (ly_top ly) /\
val_mem tfibsegs m (ly_T ly + 16) 8 (ly_bot ly) /\
val_mem tfibsegs m (ly_T ly + t_unwinding) 1 0 /\
apresent (w_H W) mem (ly_T ly + t_unwinding) /\
(* the GOT slot UnwindFast loads &PageSizeCached from, and the page size it holds. *)
val_mem tfibsegs m DEC_A_got_page_size 8 DEC_A_page_size_cached /\
val_mem tfibsegs m DEC_A_page_size_cached 8 4096 /\
(* the GOT slot 0x5243c loads &common_flags_dont_use from, and the fast-unwind byte 0x52440 reads. *)
val_mem tfibsegs m DEC_A_got_common_flags 8 DEC_A_common_flags /\
val_mem tfibsegs m DEC_A_cf_fast 1 1.

(* ------------------------------------------------------------------------------------------------------------
   Helpers.  Each is cgif's, restated at decodesegs0: A/AF0x.v:410-542 (the memory and reader helpers, the
   4+4 split of an 8-byte read, fpchain_ext2), A/AF0x.v:270-332 (the window and chunk readers),
   A/AF0x.v:345-362 (pinning a register to a value the state does not carry) and A/AFeq.v:28 (the trace's
   length). *)
Lemma mbyte_same : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof. intros m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.

Lemma apresent_same' : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H m' a.
Proof. intros H m m' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.

Lemma aview_same' : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros H m m' a E. unfold aview.
rewrite (mbyte_same (mrestrict H m) (mrestrict H m') a); [reflexivity|].
unfold mrestrict. rewrite E. reflexivity.
Qed.

Lemma val_mem_frameH : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v He Hv k Hk.
rewrite (mbyte_same (mrestrict H m) (mrestrict H m') (a + Z.of_nat k)); [exact (Hv k Hk)|].
unfold mrestrict. rewrite (He k Hk). reflexivity.
Qed.

Lemma val_mem_addr : forall m a a' (n : nat) v,
val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.

Lemma le_byte_zero : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma val_mem_zero_hi : forall m a, val_mem tfibsegs m a 8 0 -> val_mem tfibsegs m (a + 4) 4 0.
Proof.
intros m a H k Hk. replace (a + 4 + Z.of_nat k) with (a + Z.of_nat (4 + k)) by lia.
rewrite (H (4 + k)%nat ltac:(lia)). rewrite !le_byte_zero. reflexivity.
Qed.

Lemma le_byte_split_lo : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
YO0f.le_byte (lo + 2 ^ 32 * hi) 8 k = YO0f.le_byte lo 4 k.
Proof.
intros lo hi k Hlo Hhi Hk. unfold YO0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 32 * 2 ^ 32); nia).
rewrite (Z.mod_small lo) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
assert (Hk' : Z.of_nat k = 0 \/ Z.of_nat k = 1 \/ Z.of_nat k = 2 \/ Z.of_nat k = 3) by lia.
destruct Hk' as [E|[E|[E|E]]]; rewrite E.
- change (2 ^ (8 * 0)) with 1. rewrite !Z.div_1_r.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 32 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 32 * hi) with ((2 ^ 24 * hi) * 256) by lia. apply Z_mod_mult.
- change (2 ^ (8 * 1)) with 256.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 24 * hi) * 256) by lia. rewrite Z_div_plus by lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 24 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 24 * hi) with ((2 ^ 16 * hi) * 256) by lia. apply Z_mod_mult.
- change (2 ^ (8 * 2)) with 65536.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 16 * hi) * 65536) by lia. rewrite Z_div_plus by lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 16 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 16 * hi) with ((2 ^ 8 * hi) * 256) by lia. apply Z_mod_mult.
- change (2 ^ (8 * 3)) with 16777216.
replace (lo + 2 ^ 32 * hi) with (lo + (2 ^ 8 * hi) * 16777216) by lia. rewrite Z_div_plus by lia.
rewrite <- Zplus_mod_idemp_r. replace ((2 ^ 8 * hi) mod 256) with 0; [rewrite Z.add_0_r; reflexivity|].
symmetry. replace (2 ^ 8 * hi) with (hi * 256) by lia. apply Z_mod_mult.
Qed.

Lemma le_byte_split_hi : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
YO0f.le_byte (lo + 2 ^ 32 * hi) 8 (4 + k) = YO0f.le_byte hi 4 k.
Proof.
intros lo hi k Hlo Hhi Hk. unfold YO0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 32 * 2 ^ 32); nia).
rewrite (Z.mod_small hi) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
replace (8 * Z.of_nat (4 + k)) with (32 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia.
rewrite <- Z.div_div by lia. replace ((lo + 2 ^ 32 * hi) / 2 ^ 32) with hi; [reflexivity|].
symmetry. rewrite Z.mul_comm, Z_div_plus by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma val_mem_4_4 : forall (m : word -> option byte) a lo hi,
0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 ->
val_mem tfibsegs m a 4 lo -> val_mem tfibsegs m (a + 4) 4 hi ->
val_mem tfibsegs m a 8 (lo + 2 ^ 32 * hi).
Proof.
intros m a lo hi Hlo Hhi H1 H2 k Hk.
destruct (Nat.lt_ge_cases k 4) as [Hk4|Hk4].
- rewrite (le_byte_split_lo lo hi k Hlo Hhi Hk4). exact (H1 k Hk4).
- replace k with (4 + (k - 4))%nat by lia. rewrite (le_byte_split_hi lo hi (k - 4) Hlo Hhi ltac:(lia)).
replace (a + Z.of_nat (4 + (k - 4))) with (a + 4 + Z.of_nat (k - 4)) by lia.
exact (H2 (k - 4)%nat ltac:(lia)).
Qed.

Lemma unsigned_lit_small8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma le_bytes8_sum : forall z, 0 <= z < 2 ^ 64 ->
let b := fun k => YO0f.le_byte z 8 k in
b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat + 256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YO0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
change (2 ^ (8 * Z.of_nat 2)) with (256 * 256). change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256))
by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0z.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1z.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2z.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3z.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4z.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5z.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6z.
lia.
Qed.

Lemma val_mem_rdword : forall (H : word -> bool) mem a v,
0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) a 8 v ->
rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold rdword, aview.
assert (Bm : forall k, (k < 8)%nat ->
mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YO0f.le_byte v 8 k)))
by (intros k Hk; exact (Hm k Hk)).
assert (R : forall k, 0 <= YO0f.le_byte v 8 k < 256)
by (intros k; unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia.
replace (a + 3) with (a + Z.of_nat 3) by lia. replace (a + 4) with (a + Z.of_nat 4) by lia.
replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !Bm by lia. cbn [option_map]. rewrite !unsigned_lit_small8 by apply R.
f_equal. apply le_bytes8_sum. exact Hv.
Qed.

Lemma rdword_keep : forall (rd rd' : Z -> option Z) a v,
(forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v He Hv. unfold rdword in *.
replace a with (a + 0) in Hv |- * by lia. rewrite <- !Z.add_assoc in *. cbn [Z.add] in *.
rewrite !He by lia. exact Hv.
Qed.

Lemma fpchain_ext2 : forall (load load' : Z -> option Z) top ch bp,
fpchain load bp top ch -> bp < top - 16 ->
(forall a v, bp - 16 <= a -> a + 8 <= top - 16 -> load a = Some v -> load' a = Some v) ->
fpchain load' bp top ch.
Proof.
intros load load' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hlt Hx; cbn in *;
[destruct Hc as (r & Hr & Hr4); exists r; split; [apply Hx; [lia | lia | exact Hr] | exact Hr4]|].
destruct Hc as (Hfp & Hal & Hra & Hnfp & H4096 & Hrest). subst fp.
split; [reflexivity|]. split; [exact Hal|]. split; [apply Hx; [lia | lia | exact Hra]|].
split; [apply Hx; [lia | lia | exact Hnfp]|].
split; [exact H4096|]. destruct (bad_next bp top nfp) eqn:Hb; [exact Hrest|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
apply IH; [exact Hrest | lia |]. intros a v Ha Ha' Hv. apply Hx; [lia | lia | exact Hv].
Qed.

Lemma tr_len : forall pc0 (c : list (Z * Z * Z)), (1 <= length (unwind_of_chain pc0 c) <= 30)%nat.
Proof. intros pc0 c. unfold unwind_of_chain, kUnwindMax. rewrite firstn_length. cbn [length]. lia. Qed.

Lemma writable_of_apresent_high : forall (H : word -> bool) (m : word -> option byte) a,
IMG_TOP <= a < 2 ^ 64 -> apresent H m a -> writable_at tfibsegs (mrestrict H m) a.
Proof.
intros H m a Ha [Hh [b Hb]]. unfold writable_at, wview, mrestrict.
assert (Ha0 : 0 <= a) by (pose proof IMG_TOP_val; lia).
rewrite unsigned_lit_small by lia.
rewrite (find_segment_above tfibsegs a segs_in_asan (proj1 Ha)).
rewrite Hh, Hb. discriminate.
Qed.

Lemma st_ok_window_writable : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at tfibsegs (mrestrict H (ms_mem ms)) a.
Proof.
intros H E ss ms i r a HS Hi Ha.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.

Lemma st_ok_window_apresent_high : forall (H : word -> bool) E ss ms i r a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
IMG_TOP <= a < 2 ^ 64 -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hhi.
apply (apresent_of_writable_high H (ms_mem ms) a Hhi).
eapply st_ok_window_writable; eassumption.
Qed.

Lemma st_ok_chunk_val : forall (H : word -> bool) E ss ms i r j off (n : N) e v a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
a = base_val E (YP09.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros H E ss ms i r j off n e v a HS Hi Hj -> He Hv Hn.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok tfibsegs E _ _ off n e v); [| exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

Lemma st_ok_pin_reg : forall E ss ms (r : bv 5) e,
st_ok tfibsegs E ss ms -> r <> 0%bv -> sv_denot E e = YK11.getr (ms_regs ms) r ->
st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He.
apply (st_ok_regs tfibsegs E ss ms (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite sr_get_set_same;
[| destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr; apply bv_eq; apply Z.eqb_eq; exact Hb | reflexivity]].
rewrite He. exact (st_ok_reg tfibsegs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

Lemma kept_all_same : forall E (m m' : word -> option byte) rs,
(forall x : word, m' x = m x) -> Forall (region_kept tfibsegs E m m') rs.
Proof.
intros E m m' rs Heq. apply Forall_forall. intros r _. split.
- intros a _. apply mbyte_same. apply Heq.
- intros a _ Hw. eapply (writable_at_grows tfibsegs); [| exact Hw]. intros x Hx. rewrite Heq. exact Hx.
Qed.
End d.

(* [jafter_call2] of lib/Reusable/YI04.v:1649 for this walk's three-region state: the state after a call keeps
   the two image cells and the part of the wrapper's frame above [stklo], which is what the callee did not
   write.  The [Forall region_kept] premise is left as a goal, as jafter_call2 leaves it. *)
Ltac dcall3 HS k regs2 mem2 HP stklo HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let m := eval vm_compute in (ss_mem ss) in
let rs := lazymatch m with
| ?a :: ?b :: ?c :: nil => constr:(a :: b :: trim_lo c stklo :: nil)
end in
let retpc := eval vm_compute in (match sr_get (ss_regs ss) 1 with SLit z => z | _ => 0 end) in
pose proof (st_ok_after_call segs k E ss ms regs2 mem2 rs retpc HS
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_trim_lo|]; apply submem_nil)
ltac:(vm_compute; reflexivity) HP) as HS2;
let rsv := eval vm_compute in rs in change rs with rsv in HS2;
let ss2 := eval vm_compute in (ss_after_call ss rsv k retpc) in
change (ss_after_call ss rsv k retpc) with ss2 in HS2
end.

(* ------------------------------------------------------------------------------------------------------------
   The walk. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variables (W : world tfibsegs) (ly : alayout) (S : astate).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
(* The unit's call precondition at the trampoline (YG0d.v:226-234), as the seed takes it. *)
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
(* The layout's image extent covers this unit's image (cgif A/AFip.v:121 img_cover). *)
Hypothesis IMG : dec_img_cover ly.
(* The unit's thread pointer is the one measured in image A (DecodeCallocRt.v's table). *)
Hypothesis HTP : as_tp B = DEC_A_TP.
(* The four runtime-entry contracts this segment consumes. *)
Hypothesis RT_TRY : decode_try_init_spec_A.
Hypothesis RT_MCS : decode_mcs_spec_A.
Hypothesis RT_GETPC : decode_getpc_spec_A.
Hypothesis RT_UNW : decode_unwind_spec_A.
(* The sixteen start-up cells, at the entry memory. *)
Hypothesis CELLS : dec_cells_A ly W mem0.

Let sp0 : Z := spZ regs0.

(* The trace the call records: YG0d.v:224 call_trace at this unit's pc0 (0x52438). *)
Let DEC_tr : list Z := call_trace ly DEC_A_calloc_ra0 regs0 ch.

(* Item 4: the state at the call of asan_calloc, 0x524a4, whose target 0x31bd4 the run stops at. *)
Definition at_C2 (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
c' = cfg_at tfibsegs DEC_A_asan_calloc regs mem (with_vm_backing (m_vm_lazy md0) mat md0) /\
YK11.getr regs 1 = w64 DEC_A_calloc_ret /\
YK11.getr regs 2 = w64 (sp0 - ICPT_FRAME) /\
YK11.getr regs 3 = YK11.getr regs0 3 /\
YK11.getr regs 4 = YK11.getr regs0 4 /\
YK11.getr regs 8 = YK11.getr regs0 2 /\
YK11.getr regs 10 = YK11.getr regs0 10 /\
YK11.getr regs 11 = YK11.getr regs0 11 /\
YK11.getr regs 12 = w64 (sp0 - ICPT_TRACE) /\
(forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem a) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF) /\
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - ICPT_TRACE + 8) 8 (Z.of_nat (length DEC_tr)) /\
(forall i, (i < length DEC_tr)%nat ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp0 - ICPT_BUF + 8 * Z.of_nat i) 8 (nth i DEC_tr 0)).

(* The trace's length, and the object's alignment and room: the conjuncts YGAlloc.alloc_pre asks of the stack
   object and its buffer, which the next segment reads off [at_C2]'s addresses. *)
Lemma C2_tr_len : (1 <= length DEC_tr <= 30)%nat.
Proof.
unfold DEC_tr, call_trace. destruct (frame0_ok ly regs0); [apply tr_len | cbn [length]; lia].
Qed.

Lemma sp0_facts :
ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0 /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ layout_ok ly.
Proof.
pose proof PRE as (HAR & _ & _ & Hal & Hlo & Hbot & Hhi & _).
destruct HAR as (HARm & _). pose proof (am_layout _ _ _ _ HARm) as LY.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
unfold sp0, spZ in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal|].
split; [exact T7|]. split; [exact T4 | exact LY].
Qed.

Lemma C2_obj_ok :
(sp0 - ICPT_TRACE) mod 8 = 0 /\ (sp0 - ICPT_BUF) mod 8 = 0 /\
sp0 - ICPT_FRAME <= sp0 - ICPT_TRACE /\ sp0 - ICPT_TRACE + 16 <= ly_stk_hi ly /\
sp0 - ICPT_FRAME <= sp0 - ICPT_BUF /\ sp0 - ICPT_BUF + 8 * 30 <= ly_stk_hi ly.
Proof.
pose proof sp0_facts as (Flo & Fbot & Fhi & Fal & _).
assert (S8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16 sp0);
[exists 2; reflexivity | apply Z.mod_divide; [lia | exact Fal]]. }
assert (D : forall d, d mod 8 = 0 -> (sp0 - d) mod 8 = 0).
{ intros d Hd. replace (sp0 - d) with (sp0 + (-1) * d) by lia.
rewrite Z.add_mod by lia. rewrite S8. rewrite Z.mul_mod by lia. rewrite Hd. cbn. reflexivity. }
split; [apply D; reflexivity|]. split; [apply D; reflexivity|].
unfold ICPT_FRAME, ICPT_TRACE, ICPT_BUF, ASTACK in *. split; [lia|]. split; [lia|]. split; lia.
Qed.
(* The thread object and the AsanThreadContext lie outside the wrapper's stack window: they are owned extents
   of the layout, and [lo_disj] makes every owned extent disjoint from [ly_stk_lo, ly_stk_hi), which the window
   sits inside.  (cgif's A/AFis.v:487-496 stack_ivs, at decode's two cells.) *)
Lemma layout_ivs :
(ly_T ly + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= ly_T ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly).
Proof.
pose proof sp0_facts as (Flo & Fbot & Fhi & _ & _ & _ & LY).
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD.
cbn [pairwise app] in HD.
destruct HD as (_ & _ & HT & _ & _ & _ & HC & _).
do 5 (apply Forall_inv_tail in HT). apply Forall_inv in HT.
do 1 (apply Forall_inv_tail in HC). apply Forall_inv in HC.
unfold zdisjoint in HT, HC. cbn [fst snd] in HT, HC.
unfold ASTACK in *. split; lia.
Qed.

(* Those two extents are inside the application's address space, so their bytes have ordinary 64-bit
   addresses ([lo_app] of the layout, with the allocator ceiling's range). *)
Lemma T_C_range :
4096 <= ly_T ly /\ ly_T ly + kThreadObjSize < 2 ^ 64 /\ 4096 <= ly_C ly /\ ly_C ly + 256 < 2 ^ 64.
Proof.
pose proof sp0_facts as (_ & _ & _ & _ & _ & _ & LY).
pose proof (lo_app ly LY) as HA. unfold owned_extents in HA.
pose proof (proj1 (@ASAN_CEIL_range _)) as CR.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HA))) as HT.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail
(Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HA))))))) as HC.
cbn [fst snd] in HT, HC. unfold in_app in HT, HC.
unfold kThreadObjSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
destruct HT as (HT1 & [HT2|[HT2a HT2b]]); destruct HC as (HC1 & [HC2|[HC2a HC2b]]); lia.
Qed.

(* Every cell the contracts read is outside the wrapper's stack window, so the hypothesis [CELLS] about the
   entry memory holds of any memory that agrees with it outside that window. *)
Lemma cells_at : forall mem : word -> option byte,
(forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem x = mem0 x) -> dec_cells_A ly W mem.
Proof.
intros mem HM.
pose proof sp0_facts as (Flo & Fbot & Fhi & Fal & Fhmb & Fhme & LY).
pose proof layout_ivs as (IT & IC). pose proof T_C_range as (TR1 & TR2 & CR1 & CR2).
assert (HIT : IMG_TOP = 0x602000) by (apply IMG_TOP_val).
assert (IMGB : forall a : Z, 0 <= a < 0x602000 -> mem (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HM. rewrite unsigned_lit_small by lia.
unfold ASTACK, kHighMemBeg in *. lia. }
assert (TB : forall a : Z, ly_T ly <= a < ly_T ly + kThreadObjSize ->
mem (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HM. rewrite unsigned_lit_small by (unfold kThreadObjSize in *; lia).
unfold ASTACK, kThreadObjSize in *. lia. }
assert (CB : forall a : Z, ly_C ly <= a < ly_C ly + 256 -> mem (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HM. rewrite unsigned_lit_small by lia. unfold ASTACK in *. lia. }
unfold dec_cells_A in CELLS |- *.
destruct CELLS as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16).
cbv zeta in *.
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_asan_inited; lia | exact K1]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_malloc_context_size; lia | exact K2]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_tsd_key_inited; lia | exact K3]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_tsd_key; lia | exact K4]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_TP, DEC_A_builtin_tls, PTHREAD_SIZE, TSD_OFF; lia | exact K5]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_TSD; lia | exact K6]|].
split; [eapply val_mem_frameH; [intros k Hk; apply CB; lia | exact K7]|].
split; [eapply val_mem_frameH; [intros k Hk; apply TB; unfold kThreadObjSize; lia | exact K8]|].
split; [eapply val_mem_frameH; [intros k Hk; apply TB; unfold kThreadObjSize; lia | exact K9]|].
split; [eapply val_mem_frameH; [intros k Hk; apply TB; unfold kThreadObjSize; lia | exact K10]|].
split; [eapply val_mem_frameH; [intros k Hk; apply TB; unfold kThreadObjSize, t_unwinding; lia | exact K11]|].
split; [apply (apresent_same' (w_H W) mem0 mem (ly_T ly + t_unwinding));
[apply TB; unfold kThreadObjSize, t_unwinding; lia | exact K12]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_got_page_size; lia | exact K13]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_page_size_cached; lia | exact K14]|].
split; [eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_got_common_flags; lia | exact K15]|].
eapply val_mem_frameH; [intros k Hk; apply IMGB; unfold DEC_A_cf_fast, DEC_A_common_flags, CF_FAST_UNWIND_ON_MALLOC; lia | exact K16].
Qed.

(* Every writable window of the symbolic state sits inside [sp0 + lo, sp0): the stack region's, which is the
   only one with a base, and the image cells', which are empty.  [vm_compute] decides it at each stage. *)
Definition win_lo_ok (rs : smem) (lo : Z) : bool :=
forallb (fun r => ((YP09.r_whi r <=? YP09.r_wlo r) ||
((match YP09.r_base r with Some 2%nat => true | _ => false end) &&
(lo <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0)))%bool) rs.

Lemma wrange_window_lo : forall (E : env) (rs : smem) (a lo : Z),
bv_unsigned (ew E 2) = sp0 -> win_lo_ok rs lo = true -> in_wrange E rs a -> sp0 + lo <= a < sp0.
Proof.
intros E rs a lo HE Hok (r & Hin & Hr).
unfold win_lo_ok in Hok. rewrite forallb_forall in Hok. specialize (Hok r Hin). cbn beta in Hok.
apply orb_prop in Hok as [Hemp|Hst].
- apply Z.leb_le in Hemp. lia.
- apply andb_prop in Hst as [Hb1 H3]. apply andb_prop in Hb1 as [Hb H2].
apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct (YP09.r_base r) as [n|] eqn:Hbb; [|discriminate Hb].
destruct n as [|[|[|n]]]; try discriminate Hb.
rewrite ?Hbb in Hr. cbn [base_val] in Hr. rewrite HE in Hr. lia.
Qed.
(* A region the callee kept: it wrote nothing inside the region's extent, and the region's writable window is
   above the image, where a byte is writable exactly when it is present (cgif's A/AFis.v:473 kept_of_frame). *)
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) (r : YP09.region),
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
IMG_TOP <= a < 2 ^ 64) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_same.
unfold mrestrict. rewrite (Hfr (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha) as Hh.
apply (writable_of_apresent_high (w_H W) m1 a Hh). apply Hpr.
apply (apresent_of_writable_high (w_H W) m a Hh). exact Hw.
Qed.

(* Item 1-4: the run of the wrapper from its first call to the call of asan_calloc. *)
Lemma walk_C2 : SRr tfibsegs W (cfg_at tfibsegs DEC_A_wrap_calloc regs0 mem0 md0) at_C2.
Proof.
pose proof decode_wx as Hwx.
pose proof sp0_facts as (Flo & Fbot & Fhi & Fal & Fhmb & Fhme & LY).
pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hgp0 & Htp0 & (Hra4096 & Hchain) & _).
pose proof (lo_top ly LY) as (Ttop1 & Ttop2 & _).
assert (HIT : IMG_TOP = 0x602000) by (apply IMG_TOP_val).
assert (SPlo : 17594333511680 <= sp0) by (cbv [ASTACK kHighMemBeg] in Flo, Fhmb |- *; lia).
assert (SPhi : sp0 <= 140737488355328) by (cbv [kHighMemEnd] in Fhi, Fhme |- *; lia).
assert (E2 : bv_unsigned (ew (E0 regs0) 2) = sp0)
by (rewrite (E0_reg regs0 2 2%bv eq_refl); reflexivity).
eapply SRr_bind; [exact (walk_C1 B W ly S regs0 mem0 md0 ch PRE)|].
intros W1 c1 _ (-> & ms & mat & -> & HS & MEQ & PRES).
(* The two image cells the walk reads through, as regions of the symbolic state. *)
pose proof (cells_at (ms_mem ms) MEQ) as CUR. unfold dec_cells_A in CUR. cbv zeta in CUR.
destruct CUR as (XIN & XMCS & XTKI & XTK & XTSDP & XTSD & XC152 & XT40 & XT8 & XT16 & XTU & XTUP
& XGPS & XPS & XGCF & XCF).
apply (st_ok_add_region tfibsegs _ _ _ (lit1 DEC_A_cf_fast 1)) in HS;
[ | vm_compute; reflexivity
| unfold region_ok, lit1;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
cbv zeta; split; [vm_compute; discriminate|]; split; [vm_compute; discriminate|];
split; [intros o Ho; lia|]; apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val tfibsegs _ _ 0 DEC_A_cf_fast 1%N (SLit 1) 1);
[reflexivity | cbn; lia | cbn; lia | exact XCF]
| cbn [ss_mem SS_C1 REG_C1]; apply Forall_cons; [|apply Forall_nil];
unfold extent_disjoint, lit1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E2;
left; cbv [DEC_A_cf_fast DEC_A_common_flags CF_FAST_UNWIND_ON_MALLOC ASTACK]; lia ].
apply (st_ok_add_region tfibsegs _ _ _ (lit8 DEC_A_got_common_flags DEC_A_common_flags)) in HS;
[ | vm_compute; reflexivity
| unfold region_ok, lit8;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
cbv zeta; split; [vm_compute; discriminate|]; split; [vm_compute; discriminate|];
split; [intros o Ho; lia|]; apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val tfibsegs _ _ 0 DEC_A_got_common_flags 8%N (SLit DEC_A_common_flags) DEC_A_common_flags);
[reflexivity | cbn; cbv [DEC_A_common_flags]; lia | cbn; lia | exact XGCF]
| cbn [ss_mem SS_C1 REG_C1]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
unfold extent_disjoint, lit8, lit1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
[ left; cbv [DEC_A_got_common_flags DEC_A_cf_fast DEC_A_common_flags CF_FAST_UNWIND_ON_MALLOC]; lia
| rewrite E2; left; cbv [DEC_A_got_common_flags DEC_A_common_flags ASTACK]; lia ] ].
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with SS_C1X in HS by (vm_compute; reflexivity) end.
(* ---- 0x5239c `jal 0x590ac`: TryAsanInitFromRtl. ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_TryAsanInitFromRtl.
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
assert (MEQ0 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> ms_mem ms0 x = mem0 x).
{ intros x Hx. rewrite (HF x); [apply MEQ, Hx|]. intros Hin. apply Hx.
pose proof (wrange_window_lo (E0 regs0) (ss_mem SS_C1X) (bv_unsigned x) (- ASTACK) E2
ltac:(vm_compute; reflexivity) Hin) as HW. lia. }
assert (PRES0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Ha. eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2; cbv [ASTACK] in Ha |- *; lia
| rewrite HIT; cbv [ASTACK] in Ha |- *; lia]. }
clear HF HFr.
pose proof (cells_at (ms_mem ms0) MEQ0) as CUR0. unfold dec_cells_A in CUR0. cbv zeta in CUR0.
destruct CUR0 as (YIN & YMCS & YTKI & YTK & YTSDP & YTSD & YC152 & YT40 & YT8 & YT16 & YTU & YTUP
& YGPS & YPS & YGCF & YCF).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape.
cbn [ss_pc] in Hshape. rewrite Hshape.
eapply SRr_bind.
{ eapply RT_TRY.
- rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
- rewrite R2, unsigned_lit_small by lia.
replace (sp0 + -2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Fal.
- rewrite R2, unsigned_lit_small by lia. rewrite HIT. cbv [TAI_STK]. lia.
- intros a Ha. rewrite R2, unsigned_lit_small in Ha by lia. apply PRES0. cbv [TAI_STK ASTACK] in *. lia.
- exact YIN. }
intros W2 c2 _ (-> & regs1 & mem1 & mat1 & -> & HP & Ha0 & Hfr & Hpr). srr_norm_model.
(* The state after the call: the callee wrote only [sp - 16, sp), so the frame above it is kept. *)
assert (HFR : forall x : word, ~ (sp0 - 2160 <= bv_unsigned x < sp0 - 2144) -> mem1 x = ms_mem ms0 x).
{ intros x Hx. apply Hfr. rewrite R2, unsigned_lit_small by lia. cbv [TAI_STK]. lia. }
assert (MEQ1 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = mem0 x).
{ intros x Hx. rewrite HFR by (cbv [ASTACK] in Hx; lia). apply MEQ0, Hx. }
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a)
by (intros a Ha; apply Hpr, PRES0, Ha).
rewrite R1.
dcall3 HS 32%nat regs1 (mrestrict (w_H W) mem1) HP (-2144) HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
(eapply (kept_of_frame _ _ _ (fun a => sp0 - 2160 <= a < sp0 - 2144)); [exact HFR | exact Hpr | |]);
intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha |- *;
rewrite ?E2 in Ha; rewrite ?HIT; split; lia. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
(* a0 = 1: the runtime is initialised, so the branch at 0x523a0 is not taken. *)
apply (st_ok_pin_reg _ _ _ 10%bv (SLit 1)) in HS;
[ | intros Hc; discriminate | cbn [sv_denot ms_regs restrict mkst]; rewrite Ha0; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
(* ---- 0x523a0 .. 0x523c4: the branch (not taken), the stack object's three stores, and the first
   `jal 0x59e34` (GetMallocContextSize). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_GetMallocContextSize.
rreg HS (1%bv : bv 5) R1b.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ2 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ1, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- apply (apresent_same' (w_H W) mem1 _ a); [|apply PRES1; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (cells_at _ MEQ2) as CUR1. unfold dec_cells_A in CUR1. cbv zeta in CUR1.
destruct CUR1 as (ZIN & ZMCS & ZTKI & ZTK & ZTSDP & ZTSD & ZC152 & ZT40 & ZT8 & ZT16 & ZTU & ZTUP
& ZGPS & ZPS & ZGCF & ZCF).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape2.
cbn [ss_pc] in Hshape2. rewrite Hshape2.
eapply SRr_bind.
{ eapply (RT_MCS _ _ _ _ DEC_A_MCS).
- rewrite R1b. apply ret_ok_even. vm_compute. reflexivity.
- exact ZMCS.
- cbv [DEC_A_MCS]; lia. }
intros W3 c3 _ (-> & regs2 & mem2 & mat2 & -> & HP2 & Ha2 & Hfr2). srr_norm_model.
rewrite R1b.
jafter_call HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply kept_all_same. intros x. unfold mrestrict. rewrite Hfr2. reflexivity. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit DEC_A_MCS)) in HS;
[ | intros Hc; discriminate | cbn [sv_denot ms_regs restrict mkst]; rewrite Ha2; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (MEQ3 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem2 x = mem0 x)
by (intros x Hx; rewrite Hfr2; apply MEQ2, Hx).
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a)
by (intros a Ha; eapply (apresent_same' (w_H W) _ mem2 a);
[rewrite Hfr2; reflexivity | apply PRES2, Ha]).
(* ---- 0x523c8 .. 0x52434: the depth test (2 < 30, so the unwind arm), and `jal 0x72a08`
   (StackTrace::GetCurrentPc).  The small-depth arm 0x523d0 .. 0x523fc is the other side of the branch at
   0x523cc; the cell is 30, so the executor takes this one. ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_GetCurrentPc.
rreg HS (1%bv : bv 5) R1c.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ4 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ3, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES4 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- apply (apresent_same' (w_H W) mem2 _ a); [|apply PRES3; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape3.
cbn [ss_pc] in Hshape3. rewrite Hshape3.
eapply SRr_bind.
{ eapply RT_GETPC. rewrite R1c. apply ret_ok_even. vm_compute. reflexivity. }
intros W4 c4 _ (-> & regs3 & mem3 & mat3 & -> & HP3 & Ha3 & Hfr3). srr_norm_model.
rewrite R1c.
jafter_call HS 64%nat regs3 (mrestrict (w_H W) mem3) HP3 HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply kept_all_same. intros x. unfold mrestrict. rewrite Hfr3. reflexivity. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
(* a0 = 0x52438, the pc the trace records. *)
apply (st_ok_pin_reg _ _ _ 10%bv (SLit DEC_A_calloc_ra0)) in HS;
[ | intros Hc; discriminate
| cbn [sv_denot ms_regs restrict mkst]; rewrite Ha3, R1c; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (MEQ5 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem3 x = mem0 x)
by (intros x Hx; rewrite Hfr3; apply MEQ4, Hx).
assert (PRES5 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem3 a)
by (intros a Ha; eapply (apresent_same' (w_H W) _ mem3 a);
[rewrite Hfr3; reflexivity | apply PRES4, Ha]).
(* ---- 0x52438 .. 0x52448: the flags pointer, the fast-unwind byte, and the second
   `jal 0x59e34` (GetMallocContextSize). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_GetMallocContextSize.
rreg HS (1%bv : bv 5) R1d.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ6 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ5, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES6 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- apply (apresent_same' (w_H W) mem3 _ a); [|apply PRES5; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (cells_at _ MEQ6) as CUR3. unfold dec_cells_A in CUR3. cbv zeta in CUR3.
destruct CUR3 as (VIN & VMCS & VTKI & VTK & VTSDP & VTSD & VC152 & VT40 & VT8 & VT16 & VTU & VTUP
& VGPS & VPS & VGCF & VCF).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape4.
cbn [ss_pc] in Hshape4. rewrite Hshape4.
eapply SRr_bind.
{ eapply (RT_MCS _ _ _ _ DEC_A_MCS).
- rewrite R1d. apply ret_ok_even. vm_compute. reflexivity.
- exact VMCS.
- cbv [DEC_A_MCS]; lia. }
intros W5 c5 _ (-> & regs4 & mem4 & mat4 & -> & HP4 & Ha4 & Hfr4). srr_norm_model.
rewrite R1d.
jafter_call HS 80%nat regs4 (mrestrict (w_H W) mem4) HP4 HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply kept_all_same. intros x. unfold mrestrict. rewrite Hfr4. reflexivity. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit DEC_A_MCS)) in HS;
[ | intros Hc; discriminate | cbn [sv_denot ms_regs restrict mkst]; rewrite Ha4; reflexivity ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
assert (MEQ7 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem4 x = mem0 x)
by (intros x Hx; rewrite Hfr4; apply MEQ6, Hx).
assert (PRES7 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem4 a)
by (intros a Ha; eapply (apresent_same' (w_H W) _ mem4 a);
[rewrite Hfr4; reflexivity | apply PRES6, Ha]).
(* ---- 0x5244c .. 0x52490: the arguments of the unwinder (this, pc0, the entry sp as the frame pointer, 0,
   the fast-unwind byte, 30), and `jal 0x59e44` (BufferedStackTrace::UnwindImpl). ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_UnwindImpl.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQ8 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite (HF x); [apply MEQ7, Hx|]. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned x) (- ASTACK)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRES8 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144)) as [Hlo'|Hhi'].
- eapply (apresent_same' (w_H W) mem4 _ a); [|apply PRES7; lia].
apply HF. intros Hin.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned (Z_to_bv 64 a)) (-2144)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end.
rewrite unsigned_lit_small in HW by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
clear HF HFr.
pose proof (cells_at _ MEQ8) as CUR4. unfold dec_cells_A in CUR4. cbv zeta in CUR4.
destruct CUR4 as (UIN & UMCS & UTKI & UTK & UTSDP & UTSD & UC152 & UT40 & UT8 & UT16 & UTU & UTUP
& UGPS & UPS & UGCF & UCF).
(* The object's two cells, and the caller's saved ra and frame pointer, read off the state's chunks. *)
assert (E1 : ew (E0 regs0) 1 = YK11.getr regs0 1) by (apply (E0_reg regs0 1 1%bv); reflexivity).
assert (E8 : ew (E0 regs0) 8 = YK11.getr regs0 8) by (apply (E0_reg regs0 8 8%bv); reflexivity).
pose proof C2_obj_ok as (OA1 & OA2 & OA3 & OA4 & OA5 & OA6).
assert (S8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16 sp0);
[exists 2; reflexivity | apply Z.mod_divide; [lia | exact Fal]]. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX))
(sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF));
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 2%nat (-2136) 8%N (SOff 2 (-2120))
(sp0 - ICPT_BUF) (sp0 - ICPT_TRACE) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; cbv [ICPT_TRACE]; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E2; f_equal; cbv [ICPT_BUF]; lia
| cbn; cbv [ICPT_BUF]; lia | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (OBJZ : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msX)) (sp0 - ICPT_TRACE + 8) 8 0);
[ eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 1%nat (-2128) 8%N (SLit 0) 0
(sp0 - ICPT_TRACE + 8) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; cbv [ICPT_TRACE]; lia
| reflexivity | cbn; lia | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (RA0 : rdword (aview tfibsegs (w_H W) (ms_mem msX)) (sp0 - 8) = Some (raZ regs0));
[ apply val_mem_rdword; [apply u64_range|];
eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 10%nat (-8) 8%N (SOff 1 0) (raZ regs0) (sp0 - 8) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E1; unfold raZ; rewrite Z.add_0_r; reflexivity
| unfold raZ; apply u64_range | cbn; lia ]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (NFP0 : rdword (aview tfibsegs (w_H W) (ms_mem msX)) (sp0 - 16) = Some (s0Z regs0));
[ apply val_mem_rdword; [apply u64_range|];
eapply (st_ok_chunk_val (w_H W) _ _ _ 2%nat _ 9%nat (-16) 8%N (SOff 8 0) (s0Z regs0) (sp0 - 16) HS);
[ reflexivity | reflexivity
| cbn [YP09.r_base base_val]; rewrite ?ew_havoc_old by lia; rewrite E2; lia
| cbn [sv_denot]; rewrite ?ew_havoc_old by lia; rewrite E8; unfold s0Z; rewrite Z.add_0_r; reflexivity
| unfold s0Z; apply u64_range | cbn; lia ]
| ] end.
rreg HS (1%bv : bv 5) R1e. rreg HS (2%bv : bv 5) R2e. rewrite E2 in R2e.
rreg HS (4%bv : bv 5) R4e. rreg HS (10%bv : bv 5) R10e. rewrite E2 in R10e.
rreg HS (11%bv : bv 5) R11e. rreg HS (12%bv : bv 5) R12e.
rreg HS (13%bv : bv 5) R13e. rreg HS (14%bv : bv 5) R14e. rreg HS (15%bv : bv 5) R15e.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as Hshape5.
cbn [ss_pc] in Hshape5. rewrite Hshape5.
eapply SRr_bind.
{ apply (RT_UNW W ly _ _ _ (sp0 - ICPT_TRACE) DEC_A_calloc_ra0 sp0 (raZ regs0) (s0Z regs0) ch).
- exact LY.
- exact IMG.
- rewrite R10e; f_equal; cbv [ICPT_TRACE]; lia.
- rewrite R11e; reflexivity.
- rewrite R12e, <- E2; symmetry; apply Z_to_bv_bv_unsigned.
- exact R13e.
- exact R14e.
- exact R15e.
- rewrite R4e, (E0_reg regs0 4 4%bv eq_refl), Htp0, HTP; reflexivity.
- rewrite R1e; apply ret_ok_even; vm_compute; reflexivity.
- cbv [DEC_A_calloc_ra0]; lia.
- exact UIN.
- exact UTKI.
- exact UTK.
- exact UTSDP.
- exact UTSD.
- exact UC152.
- exact UT40.
- exact UT8.
- exact UT16.
- exact UTU.
- exact UTUP.
- exact UGPS.
- exact UPS.
- rewrite R2e, unsigned_lit_small by lia;
replace (sp0 + -2144) with (sp0 + (-134) * 16) by lia; rewrite Z_mod_plus_full; exact Fal.
- rewrite R2e, unsigned_lit_small by lia; cbv [UNW_STK ASTACK] in *; lia.
- intros a Ha; rewrite R2e, unsigned_lit_small in Ha by lia; apply PRES8;
cbv [UNW_STK ASTACK] in *; lia.
- exact OA1.
- cbv [ICPT_TRACE ASTACK] in *; lia.
- right; rewrite R2e, unsigned_lit_small by lia; cbv [ICPT_TRACE]; lia.
- intros a Ha; apply PRES8; cbv [ICPT_TRACE BST_SIZE ASTACK] in *; lia.
- cbv [ICPT_TRACE BST_SIZE]; lia.
- rewrite R2e, unsigned_lit_small by lia; lia.
- exact Fbot.
- exact Fhi.
- exact S8.
- exact RA0.
- exact NFP0.
- exact Hra4096.
- unfold frame0_ok in Hchain. replace (spZ regs0) with sp0 in Hchain by reflexivity.
destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hchain].
destruct (bad_next sp0 (ly_top ly) (s0Z regs0)) eqn:Hb; [exact Hchain|].
destruct Hchain as [H16 Hch']. split; [exact H16|].
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _].
apply Bool.orb_false_iff in Hb as [Hb1 Hb2]. apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
apply Z.ltb_lt in Hf0.
eapply fpchain_ext2; [exact Hch' | lia |].
intros aX vX HaX1 HaX2 HvX. eapply rdword_keep; [|exact HvX].
intros i Hi. apply aview_same'. apply MEQ8.
rewrite unsigned_lit_small by (cbv [kHighMemEnd] in Fhme |- *; lia). cbv [ASTACK]. lia. }
intros W6 c6 _ (-> & regs5 & mem5 & mat5 & -> & HP5 & Hfr5 & Hpr5 & HT1 & HT2 & HT3). srr_norm_model.
(* The unwinder wrote the three fields of the object and its own stack window, and nothing else. *)
assert (HFR5 : forall x : word, ~ (sp0 - 2288 <= bv_unsigned x < sp0 - 64) -> mem5 x = ms_mem ms4 x).
{ intros x Hx. apply Hfr5; cbv [UNW_STK ICPT_TRACE BST_SIZE]; rewrite ?R2e;
rewrite ?unsigned_lit_small by lia; lia. }
assert (OBJ0F : val_mem tfibsegs (mrestrict (w_H W) mem5) (sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF)).
{ eapply val_mem_frameH; [|exact OBJ0]. intros k Hk. apply Hfr5;
cbv [UNW_STK ICPT_TRACE BST_SIZE]; rewrite ?R2e; rewrite ?unsigned_lit_small by lia; lia. }
assert (OBJZF : val_mem tfibsegs (mrestrict (w_H W) mem5) (sp0 - ICPT_TRACE + 8 + 4) 4 0).
{ eapply val_mem_frameH; [|apply val_mem_zero_hi; exact OBJZ]. intros k Hk. apply Hfr5;
cbv [UNW_STK ICPT_TRACE BST_SIZE]; rewrite ?R2e; rewrite ?unsigned_lit_small by lia; lia. }
assert (LENF : val_mem tfibsegs (mrestrict (w_H W) mem5)
(sp0 - ICPT_TRACE + 8) 8 (Z.of_nat (length DEC_tr))).
{ replace (Z.of_nat (length DEC_tr)) with (Z.of_nat (length DEC_tr) + 2 ^ 32 * 0) by lia.
apply val_mem_4_4; [pose proof C2_tr_len; lia | lia | exact HT1 | exact OBJZF]. }
assert (MEQ9 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem5 x = mem0 x).
{ intros x Hx. rewrite HFR5 by (cbv [ASTACK] in Hx; lia). apply MEQ8, Hx. }
assert (PRES9 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem5 a)
by (intros a Ha; apply Hpr5, PRES8, Ha).
rewrite R1e.
dcall3 HS 96%nat regs5 (mrestrict (w_H W) mem5) HP5 (-64) HS1.
lazymatch type of HS1 with ?P -> _ => assert (KEPT : P) end.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
(eapply (kept_of_frame _ _ _ (fun a => sp0 - 2288 <= a < sp0 - 64)); [exact HFR5 | exact Hpr5 | |]);
intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha |- *;
rewrite ?ew_havoc_old in Ha by lia; rewrite ?E2 in Ha; rewrite ?HIT; split; lia. }
specialize (HS1 KEPT). clear KEPT.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
(* ---- 0x52494 .. 0x524a4: the three arguments of asan_calloc, and `jal 0x31bd4`. ---- *)
srr_run_to_sh tbl_calloc_A_ok HS DEC_A_asan_calloc.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (FRF : forall x : word, ~ (sp0 - 64 <= bv_unsigned x < sp0) -> mB x = mem5 x) end.
{ intros x Hx. apply HF. intros Hin. apply Hx.
lazymatch type of HF with frame_of ?Ex ?rsx _ _ =>
pose proof (wrange_window_lo Ex rsx (bv_unsigned x) (-64)
ltac:(rewrite ?ew_havoc_old by lia; exact E2) ltac:(vm_compute; reflexivity) Hin) as HW end. lia. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (MEQF : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mB x = mem0 x) end.
{ intros x Hx. rewrite FRF by (cbv [ASTACK] in Hx; lia). apply MEQ9, Hx. }
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (PRESF : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mB a) end.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hlo'|Hhi'].
- eapply (apresent_same' (w_H W) mem5 _ a); [|apply PRES9; lia].
apply FRF. rewrite unsigned_lit_small by (cbv [ASTACK] in Ha; lia). lia.
- eapply (st_ok_window_apresent_high (w_H W) _ _ _ 2%nat _ a HS);
[reflexivity | cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
rewrite ?ew_havoc_old by lia; rewrite E2; lia
| rewrite HIT; cbv [ASTACK] in Ha; lia]. }
(* The object's cells at the reached state: the last run stores nothing. *)
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (TR1 : val_mem tfibsegs (mrestrict (w_H W) mB) (sp0 - ICPT_TRACE) 8 (sp0 - ICPT_BUF));
[ eapply val_mem_frameH; [|exact OBJ0F]; intros k Hk; apply FRF;
rewrite unsigned_lit_small by (cbv [ICPT_TRACE]; lia); cbv [ICPT_TRACE]; lia | ] end.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (TR2 : val_mem tfibsegs (mrestrict (w_H W) mB)
(sp0 - ICPT_TRACE + 8) 8 (Z.of_nat (length DEC_tr)));
[ eapply val_mem_frameH; [|exact LENF]; intros k Hk; apply FRF;
rewrite unsigned_lit_small by (cbv [ICPT_TRACE]; lia); cbv [ICPT_TRACE]; lia | ] end.
pose proof C2_tr_len as TRLEN.
lazymatch type of HF with frame_of _ _ _ ?mB =>
assert (TR3 : forall i, (i < length DEC_tr)%nat ->
val_mem tfibsegs (mrestrict (w_H W) mB) (sp0 - ICPT_BUF + 8 * Z.of_nat i) 8 (nth i DEC_tr 0));
[ intros i Hi; eapply val_mem_frameH;
[ intros k Hk; apply FRF;
rewrite unsigned_lit_small by (cbv [ICPT_BUF]; lia); cbv [ICPT_BUF]; lia
| eapply val_mem_addr; [exact (HT2 i Hi) | cbv [ICPT_TRACE ICPT_BUF]; lia] ] | ] end.
clear HF HFr.
(* The registers at the call, and the close. *)
rreg HS (1%bv : bv 5) R1f. rreg HS (2%bv : bv 5) R2f. rewrite E2 in R2f.
rreg HS (3%bv : bv 5) R3f. rreg HS (4%bv : bv 5) R4f. rreg HS (8%bv : bv 5) R8f.
rreg HS (10%bv : bv 5) R10f. rreg HS (11%bv : bv 5) R11f.
rreg HS (12%bv : bv 5) R12f. rewrite E2 in R12f.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)) as HshapeF.
cbn [ss_pc] in HshapeF.
apply SRr_ret. rewrite HshapeF. unfold at_C2. split; [reflexivity|].
do 3 eexists. split; [unfold cfg_at; reflexivity|].
split; [rewrite R1f; reflexivity|].
split; [rewrite R2f; f_equal; cbv [ICPT_FRAME]; lia|].
split; [rewrite R3f; apply (E0_reg regs0 3 3%bv); reflexivity|].
split; [rewrite R4f; apply (E0_reg regs0 4 4%bv); reflexivity|].
split; [rewrite R8f; apply (E0_reg regs0 2 2%bv); reflexivity|].
split; [rewrite R10f; apply (E0_reg regs0 10 10%bv); reflexivity|].
split; [rewrite R11f; apply (E0_reg regs0 11 11%bv); reflexivity|].
split; [rewrite R12f; f_equal; cbv [ICPT_TRACE]; lia|].
split; [exact MEQF|]. split; [exact PRESF|].
split; [exact TR1|]. split; [exact TR2|]. exact TR3.
Qed.



End e.
