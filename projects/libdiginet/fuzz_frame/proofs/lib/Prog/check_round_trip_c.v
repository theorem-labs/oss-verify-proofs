(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread_c.v, with its module paths and module names changed; 18 of its 49 lines of code are new or changed and 21 lines of the source are left out. *)
(* Contract of check_round_trip in fuzz_frame.plain, in the form of libreac/fuzz_decode's
   lib/Prog/check_round_trip_c.v.
   Source: fuzz/fuzz_frame.c:114-200 at 835f336c. The binary inlines fuzz_alloc and fuzz_all
   (fuzz/fuzz.h:81-88, 100-106), spec_system_at (fuzz/spec.h:264-270) and spec_build_frame
   (fuzz/spec.h:228-247, two times).
   Address 0x13058, size 1216 bytes. Stack frame: 144 bytes (addi sp, sp, -0x90 at 0x13058);
   the struct diginet_header h is at sp + 0x18 in it. The function calls malloc (0x149ec) and
   free (0x148ac), each two or three times, memset (0x1bc60), memcpy (0x1b85c), bcmp (0x1b828)
   and diginet_frame_build (0x138ac, stack 240 with diginet_body_check). It calls abort (0x14414)
   at 0x13514. CRT_STACK is CRT_FRAME + ALLOC_STACK: malloc and free take ALLOC_STACK, more
   than diginet_frame_build; memset, memcpy and bcmp use no stack.
   Argument: a0 is the address w of a struct spec_frame (80 bytes). The caller is
   LLVMFuzzerTestOneInput, at 0x12e54, only for a frame b with fr_code b = 0; it gives its
   local spec_frame at its sp.
   Let n_want be crt_len b, the larger of 60 and 30 + fr_body_len b (fuzz_frame.c:116-118).
   Preconditions:
   - call_pre_k with CRT_STACK; a0 is w;
   - fr_code b = 0 and the length of b is less than 2^26 (the caller refuses a larger input)
     for the bytes b at buf (the caller's copy of the input);
   - 0 < buf < 2^64 (the caller's malloc result, tested for 0), buf is in a block of the
     caller (in_block), and the bytes b are at buf (blk_data);
   - w is at sp or above, 8-aligned, w + 80 <= 2^63, and the 80 bytes at w are spec_bytes buf
     b (check_parse_fields_c.v), the struct that the inlined spec_read_frame of the caller
     writes: w->dst = buf, w->src = buf + 6, w->body = buf + 30, and the fields of b;
   - ro_agree, frm_zero of fcsr, res_ok_slots A sb;
   - room for the three blocks: sb_live sb + 3 <= sb_cap sb <= CAPMAX, 0 <= sb_bytes sb and
     sb_bytes sb + 3 * n_want <= 2^40.
   Result: the function returns to ra. It does not call abort. These are the 11 branches to
   0x13514, with bb = fr_body b, of length fr_body_len b (DgnSpec.length_fr_body), and n the
   answer of diginet_frame_build, build_code bb cap (its contract):
   - 0x130b0, 0x130c0, 0x13464: malloc answers 0. The room premise excludes it: with
     res_ok_slots A sb, each of the three calls (n_want, n_want, n_want - 1 bytes, at most
     2^26 + 30) has room_slots (AllocRoom.room_slots_big), and malloc_contract (Contract.v)
     then answers an address res that is not 0, with res + n <= alloc_ceiling (fresh_block).
     So 0 < out < 2^64, the premise of the frame_build contract, and the same for want and
     shy;
   - 0x131a0: a body past 1484 bytes and n not -4. build_code tests 1484 < length bb first
     (DgnSpec.build_code); the binary tests body_len < 1485 (sltiu 0x5cd);
   - 0x131b4: a body of at most 1484 bytes that holds F0 13 xx 70 and n not -10. The inlined
     spec_system_at (0x13104..0x13158) answers sys = system_at bb (DgnSpec.system_at_true,
     system_at_false), and build_code then answers -10 (the library's own code is
     body_check, DgnLib.body_check_spec and lib_build_code_eq);
   - 0x131c8: any other body and n not n_want. The cap is n_want = frame_len (length bb), so
     build_code answers frame_len (DgnLib.frame_build_ok);
   - 0x1330c: n = (int)n_want and bcmp of out and want not 0. n is -4 or -10 on the two cases
     above, and n_want is less than 2^31, so n = (int)n_want only in the case of 0x131c8. There
     out holds build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
     (fr_cmd b) (fr_ncmds b) bb false (the frame_build contract; DgnLib.frame_build_ok),
     of n_want bytes (DgnSpec.length_build_frame). h carries w's counters, retry, cmd and
     ncmds at h + 4, and diginet_frame_build does not read h->numbytes and h->sum. The
     inlined spec_build_frame (0x131cc..0x132ec) writes the same n_want bytes in want: zeros,
     the MACs, 0x885F, 16 + body_len, the 64-bit sum of bb cut to 16 bits by two sb, which is
     spec_sum bb (DgnSpec.spec_sum_eq), the counters, retry, cmd, ncmds and bb;
   - 0x13440, 0x13454: the build in the zero-sum mode (a7 = 1). build_code does not depend on
     the mode, so n is n_want, and out holds build_frame with zero_sum true, the bytes that
     the second inlined spec_build_frame (0x13314..0x13404) writes, with 0 as the sum;
   - 0x134a4: the cap n_want - 1 is less than frame_len, so build_code answers -5;
   - 0x134b0: on a code under 0 diginet_frame_build writes no byte of its buffer (build_out
     is then oj), so each of the n_want - 1 bytes at shy is still the 0x5a of memset.
   After the frees, the blocks of the allocator are those before the call and res_ok_slots
   holds for sb again. The function writes only its scratch (the CRT_STACK bytes below sp)
   and memory of the allocator; each byte of each block of the caller stays the same
   (blocks_kept), and so do the bytes at w. It keeps sp, gp, tp and s0..s11 (call_post_k),
   and frm of fcsr stays 0.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_ROUND_TRIP : Z := 0x13058.
(* addi sp, sp, -0x90 at 0x13058; the deepest callees are malloc and free (ALLOC_STACK, more
   than the 240 bytes of diginet_frame_build with diginet_body_check); memset, memcpy and bcmp
   use no stack. *)
Definition CRT_FRAME : Z := 144.
Definition CRT_STACK : Z := CRT_FRAME + ALLOC_STACK.

(* n_want (fuzz_frame.c:116-118): the size of the blocks out and want, and one more than the
   size of shy. *)
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
    call_pre_k B MR CRT_STACK L A regs mem md ->
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
         call_post_k B MR CRT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         guard_kept B mem mem' /\
         ro_agree (ms_segs B) mem' /\
         res_ok_slots A' sb /\
         st_init_done A' = true).

End K.
