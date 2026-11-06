(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths changed; 17 of its 47 lines of code are new or changed and 22 lines of the source are left out. *)
(* Contract of check_round_trip in fuzz_frame.ubsan, the twin of Prog/check_round_trip_c.v
   (fuzz_frame.plain), in the form of libreac/fuzz_decode's lib/U/Prog/check_round_trip_c.v.
   Source: fuzz/fuzz_frame.c:114-200 at 835f336c. The binary inlines fuzz_alloc and fuzz_all
   (fuzz/fuzz.h:81-88, 100-106) and spec_system_at (fuzz/spec.h:264-270). It calls
   spec_build_frame (0x136a8, fuzz/spec.h:228-247) two times; fuzz_frame.plain inlines it.
   Address 0x131e4, size 796 bytes. Stack frame: 80 bytes (addi sp, sp, -0x50 at 0x131e4); the
   struct diginet_header h is at sp + 0 in it. The function calls malloc (0x14f2c) and free
   (0x14dec), each two or three times, memset (0x1c1a0), diginet_frame_build (0x13c44, stack
   240 with diginet_body_check), spec_build_frame (0x136a8, stack 96) and bcmp (0x1bd68). Its
   walk takes their contracts (the allocator contracts of Contract.v, U/Prog/memset_c.v,
   diginet_frame_build_c.v, spec_build_frame_c.v, bcmp_c.v) as hypotheses. It calls abort
   (0x14954) at 0x134f8. The stack constants U_CRT_FRAME (80) and U_CRT_STACK
   (U_CRT_FRAME + ALLOC_STACK) are in U/Prog/CheckStackU.v: malloc and free take ALLOC_STACK,
   more than diginet_frame_build and spec_build_frame; memset and bcmp use no stack.
   Argument: a0 is the address w of a struct spec_frame (80 bytes). The caller is
   LLVMFuzzerTestOneInput, at 0x12fc4, only for a frame b with fr_code b = 0; it gives its
   local spec_frame at its sp.
   Let n_want be crt_len b, the larger of 60 and 30 + fr_body_len b (fuzz_frame.c:116-118).
   Preconditions:
   - call_pre_k with U_CRT_STACK (so sp is 16-aligned); a0 is w;
   - fr_code b = 0 and the length of b is less than 2^26 (the caller refuses a larger input)
     for the bytes b at buf (the caller's copy of the input);
   - 0 < buf < 2^64 (the caller's malloc result, tested for 0), buf is in a block of the
     caller (in_block), and the bytes b are at buf (blk_data);
   - w is at sp or above, 8-aligned, w + 80 <= 2^63, and the 80 bytes at w are spec_bytes buf
     b (U/Prog/check_parse_fields_c.v), the struct that the inlined spec_read_frame of the
     caller writes: w->dst = buf, w->src = buf + 6, w->body = buf + 30, and the fields of b;
   - ro_agree, frm_zero of fcsr, res_ok_slots A sb;
   - room for the three blocks: sb_live sb + 3 <= sb_cap sb <= CAPMAX, 0 <= sb_bytes sb and
     sb_bytes sb + 3 * n_want <= 2^40.
   Result: the function returns to ra. It does not call abort. These are the 11 branches to
   0x134f8, with bb = fr_body b, of length fr_body_len b (DgnSpec.length_fr_body), and n the
   answer of diginet_frame_build, build_code bb cap (its contract):
   - 0x13230, 0x13240, 0x13450: malloc answers 0. The room premise excludes it: with
     res_ok_slots A sb, each of the three calls (n_want, n_want, n_want - 1 bytes, at most
     2^26 + 30) has room_slots (AllocRoom.room_slots_big), and malloc_contract (Contract.v)
     then answers an address res that is not 0, with res + n <= alloc_ceiling (fresh_block).
     So 0 < out < 2^64, the premise of the frame_build contract, and the same for want and
     shy;
   - 0x1334c: a body past 1484 bytes and n not -4. build_code tests 1484 < length bb first
     (DgnSpec.build_code); the binary branches on body_len < 1485 (bltu s5, 0x5cd at
     0x13344), and sltiu 0x5cd at 0x13350 computes the same fits for 0x13360 and 0x13374;
   - 0x13360: a body of at most 1484 bytes that holds F0 13 xx 70 and n not -10. The inlined
     spec_system_at (0x13284..0x132fc) answers sys = system_at bb (DgnSpec.system_at_true,
     system_at_false), and build_code then answers -10 (the library's own code is
     body_check, DgnLib.body_check_spec and lib_build_code_eq);
   - 0x13374: any other body and n not n_want. The cap is n_want = frame_len (length bb), so
     build_code answers frame_len (DgnLib.frame_build_ok);
   - 0x133c0: n = (int)n_want and bcmp of out and want not 0. n is -4 or -10 on the two cases
     above, and n_want is less than 2^31, so n = (int)n_want only in the case of 0x13374.
     There out holds build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
     (fr_cmd b) (fr_ncmds b) bb false (the frame_build contract; DgnLib.frame_build_ok),
     of n_want bytes (DgnSpec.length_build_frame). h carries w's counters, retry, cmd and
     ncmds at h + 4, and diginet_frame_build does not read h->numbytes and h->sum.
     spec_build_frame (0x133a8, zero_sum 0) writes the same n_want bytes in want (its
     contract);
   - 0x1342c, 0x13440: the build in the zero-sum mode (a7 = 1). build_code does not depend on
     the mode, so n is n_want, and out holds build_frame with zero_sum true, the bytes that
     spec_build_frame (0x133f4, zero_sum 1) writes in want;
   - 0x13490: the cap n_want - 1 is less than frame_len, so build_code answers -5;
   - 0x134a8: on a code under 0 diginet_frame_build writes no byte of its buffer (build_out
     is then oj), so each of the n_want - 1 bytes at shy is still the 0x5a of memset.
   UBSan checks: seven branches to the trap at 0x134f4 (unimp):
   - 0x13210: w & 7 is not 0 (the alignment of struct spec_frame). The premise w mod 8 = 0
     keeps it from firing;
   - 0x132b0, 0x132bc, 0x132c0: in the inlined spec_system_at (only when body_len >= 4),
     w->body + i wraps past 2^64, or w->body is 0; 0x132d0: w->body + i + 1 wraps; 0x132e0:
     w->body + i + 3 wraps. w->body is buf + 30 and the scan reads only i + 3 < body_len, so
     every address is in the block of buf (in_block); a block ends at or below alloc_ceiling
     (YI06.heap_blocks_range), and alloc_ceiling < sp < 2^63 (call_pre_k); none is taken;
   - 0x1349c: shy + i wraps past 2^64 in the inlined fuzz_all, for i < n_want - 1: shy is a
     fresh block of n_want - 1 bytes below alloc_ceiling, so it is not taken.
   The callees' own premises: diginet_frame_build needs h 4-aligned and its sp 8-aligned (h is
   at this function's sp - 80, 16-aligned by call_pre_k); spec_build_frame needs body =
   buf + 30 not 0 and its want block of exactly n_want bytes.
   After the frees, the blocks of the allocator are those before the call and res_ok_slots
   holds for sb again. The function writes only its scratch (the U_CRT_STACK bytes below sp)
   and memory of the allocator; each byte of each block of the caller stays the same
   (blocks_kept), and so do the bytes at w. It keeps sp, gp, tp and s0..s11 (call_post_k),
   frm of fcsr stays 0, the 8 bytes of the stack guard's .got slot stay the same (guard_kept),
   ro_agree holds after the call, and the allocator's start-up is done (st_init_done A' = true).
   Difference from the plain statement: the stack constant is U_CRT_STACK (80 + ALLOC_STACK)
   in place of CRT_STACK (144 + ALLOC_STACK). The premises are the plain ones: they already
   give w mod 8 = 0, a 16-aligned sp, and buf + length b at or below alloc_ceiling < 2^63.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_parse_fields_c CheckStackU.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_ROUND_TRIP : Z := 0x131e4.

(* n_want (fuzz_frame.c:116-118): the size of the blocks out and want, and one more than the
   size of shy. The same as in Prog/check_round_trip_c.v. *)
Definition crt_len (b : list byte) : Z := frame_len (length (fr_body b)).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition in_block (L : layout) (A : astate) (a n : Z) : Prop :=
  exists q k, In (q, k) (blocks L A) /\ q <= a /\ a + n <= q + k.

Definition check_round_trip_contract : Prop :=
  forall L A regs mem md (w buf : Z) (b : list byte) (sb : sbound),
    ms_segs B = rsegs ->
    call_pre_k B MR U_CRT_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 w ->
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 ->
    0 < buf < 2 ^ 64 -> in_block L A buf (Z.of_nat (length b)) -> blk_data B mem buf b ->
    spZ regs <= w -> w mod 8 = 0 -> w + 80 <= 2 ^ 63 ->
    blk_data B mem w (spec_bytes buf b) ->
    ro_agree (ms_segs B) mem ->
    frm_zero fp_csr ->
    res_ok_slots A sb ->
    sb_live sb + 3 <= sb_cap sb <= CAPMAX /\ 0 <= sb_bytes sb /\ sb_bytes sb + 3 * crt_len b <= 2 ^ 40 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         call_post_k B MR U_CRT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' sb /\
         st_init_done A' = true).

End K.
