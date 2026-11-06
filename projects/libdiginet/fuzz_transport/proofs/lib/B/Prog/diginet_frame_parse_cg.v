(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame's diginet_frame_parse in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v:189-317, :375-390 (cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), with a written range of the caller's side-stack frame (proofs/libreac/fuzz_decode/lib/A/Prog/DecodeCJ.v:51-56 twr_ok), at this unit's core names and image A; the shared definitions are lib/A/Prog/DgnFrameCg.v's. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A statement text lib/A/Prog/diginet_frame_parse_cg.v: module paths changed (the image-B core's lib/B/YB1v.v, YE2k.v, YCbq.v / YC5d.v; the listing names of lib/B/Prog/FrameBSyms.v / FrameBAddr.v; lib/B/Prog/DgnFrameCg.v), every address in the comments is fuzz_frame.asan-ubsan's, the frame is 80 bytes (FRAME_FP_FRAME 80), the holds statement also takes the leaf statements of image B's out-of-line rd32 (lib/B/Prog/rd32_cg.v, calls 0x82230 / 0x82258) and diginet_sum16 (lib/B/Prog/diginet_sum16_cg.v, call 0x823a4), which image A inlines, the written range frame_fp_wr is unchanged (re-derived from image B's stores), and ONE premise more than image A's text, image B's UBSan premise `f mod 8 = 0` (the trap 0x8215c `andi a0,s0,7` / 0x82160 `bnez a0`, unimp at 0x82428), in the shape of the UBSan image's lib/U/Prog/diginet_frame_parse_c.v. *)
(* diginet_frame_parse_cg (image B): the ASan walk contract of diginet_frame_parse (src/diginet_frame.c; plain
   contract lib/Prog/diginet_frame_parse_c.v) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x8b1f8 =
   transportb_sigma TB_diginet_frame_parse, size 0x53c (1340), as STATEMENTS only (no proof). It stores into no
   harness global and calls __asan_memcpy and the leaves rd32 and diginet_sum16, so it takes decode's caller-journal
   form (lib/B/Prog/DgnTransportBCg.v decode_cg_post over the caller's donor journal ajournal). Form:
   lib/A/Prog/diginet_frame_parse_cg.v (the same definitions and post; the premises and holds statement below).

   RELOCATED from libdiginet/fuzz_frame's image-B statement lib/B/Prog/diginet_frame_parse_cg.v (file sha256
   00afdbddfc4e; donor not released; fuzz_frame.asan-ubsan at 0x82050, size 0x53c): every pc that text names,
   moved by + 0x91a8, was read again on this
   unit's twin and holds the same instruction (the frame, the three tests for 0 and size, the runtime-cell load, the
   loads of buf, the two __asan_memcpy calls, the two rd32 calls, the diginet_sum16 call, the 13 stores into f, the 15
   UBSan branches, the trap word and the 24 error-path calls). The names change: frame_cg_post / frame_twr_ok /
   frame_rd_ok / frame_in_fake / frame_off_win / frame_cells / frame_leaf_at / frameb_sigma FB_* become this unit's
   decode_cg_post / decode_twr_ok / decode_rd_ok / decode_in_fake / decode_off_win / transport_cells /
   transport_leaf_at (lib/B/Prog/DgnTransportBCg.v) / transportb_sigma TB_* (DgnTransportBSyms, DgnTransportBAddr),
   frame_fp_* / FRAME_FP_* become trans_fp_* / TRANS_FP_*, frame_diginet_frame_parse_cg{,_holds_stmt} become
   transport_diginet_frame_parse_cg{,_holds_stmt} (image A's names), DgnFrameCg.v's frame_f_cells / FRAME_F_SIZE /
   frame_f_bytes are stated here as trans_fp_f_cells / TRANS_FP_F_SIZE / trans_fp_f_bytes, as image A's text states
   them (the same text as DgnTransportBCg.v's frame_f_cells / FRAME_F_SIZE / frame_f_bytes, over this unit's
   lib/Prog/diginet_frame_parse_c.v parse_cells), and the leaf statements are this unit's image-B
   lib/B/Prog/rd32_cg.v transport_rd32_cg and lib/B/Prog/diginet_sum16_cg.v transport_diginet_sum16_cg.
   One premise changes, the one image A's text changes for transport's call sites (its placement:
   DgnTransportBCg.v trans_src_ok; the code does not force it, transport's caller does): fuzz_frame's
   `frame_in_block B lyc Sc buf (length b)` (the bytes in
   one of the caller's heap blocks) becomes `trans_src_ok B lyc Sc W memc buf (length b)` with
   `decode_off_win regs TRANS_FP_STK buf (length b)`, both for every b, the empty one included, and the disjointness
   of f and the bytes at buf is asked when b is not empty: transport's diginet_session_rx passes the frame receive
   allocates (a heap block) or diginet_session_poll's local buffer (a side-stack frame). trans_src_ok's non-block
   cases carry decode_rd_ok (every byte visible, the range marked usable, buf + size <= 2 ^ 63), which is what the
   walk took from the block (AR_laws' block shadow and al_blocks), and decode_off_win keeps the range out of this
   call's stack window (and so out of the 16-byte frames of rd32 and diginet_sum16 below it), which the block gave by
   lying below alloc_ceiling. The two premises are not guarded by b <> []: at length 0 trans_src_ok still bounds buf
   (0 <= buf below 2 ^ 64 in each case), and without that bound buf = 2 ^ 64 would meet buf <> 0 while w64 buf = 0
   takes the code's buf = 0 test at 0x8b228 (a0 = -1, not fr_code [] = -2). When b is empty and buf is in range, the
   code returns -2 (0x8b240) before it reads buf.
   Against image A's text (lib/A/Prog/diginet_frame_parse_cg.v), which the B code forces:
   - ONE premise more, `f mod 8 = 0` (fuzz_frame's image-B premise): 0x8b304 a0 = f & 7 (s0 = f) and 0x8b308, a
     branch to the trap word 0x8b5d0 when a0 <> 0, on the code-0 path (UBSan's alignment check of memcpy (f->dst, ..));
     image A has no such check;
   - the frame is 80 bytes (TRANS_FP_FRAME 80; image A 48): image B saves s0 .. s7;
   - the holds statement takes the leaf statements of rd32 (calls 0x8b3d8 / 0x8b400) and diginet_sum16 (call
     0x8b54c) as well, which image A inlines; both are leaves of 16-byte frames inside ESTACK, so TRANS_FP_STK is
     image A's form (frame + ESTACK);
   - the written range trans_fp_wr is unchanged (re-derived from image B's stores below); image B reads f + 18 back
     (0x8b580) for the byte at f + 58.

   The contract. The caller's journal is the premise. a0 = buf, a1 = the length of the bytes b at buf, a2 = f, a
   struct diginet_frame of 64 bytes fj. buf is not 0 and lies with its bytes b where trans_src_ok places it, outside
   this call's stack window; f is not 0, is a multiple of 8, and lies in one of the caller's live side-stack frames,
   where the caller lets the call write it (decode_twr_ok), its bytes are visible and marked usable (decode_rd_ok), and
   it is outside this call's stack window; f and the bytes at buf do not overlap when b is not empty.
   The function returns to ra with a0 = fr_code b, the callee-saved registers kept, no allocator event, every byte
   outside its stack window and outside the bytes of f it stores kept, and the 64 bytes at f =
   trans_fp_f_bytes buf b fj: lib/Prog/diginet_frame_parse_c.v parse_cells when the code is 0, else fj. The written
   range E is the bytes of f any path stores: [f, f + 14) and [f + 16, f + 59). The post states all 64 bytes, so the
   7 bytes it never stores (14, 15, 59 .. 63) and, on a code that is not 0, all 64 bytes are fj.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 1340 code bytes of this function are equal in both files),
   symbol diginet_frame_parse, value 0x8b1f8, size 1340, 335 words:
     0x8b1f8  sp = sp - 80; ra at sp + 72, s0 .. s7 at sp + 64 .. sp + 8; no realignment, no frame pointer
              (s1 = size from 0x8b220, s0 = f from 0x8b22c, s2 = buf from 0x8b234);
     0x8b228 / 0x8b230  buf = 0 or f = 0 returns a0 = -1 (a1 = -1 at 0x8b224; kept unreached: buf <> 0 and
              buf < 2 ^ 64 by trans_src_ok with AR; f <> 0 and f + 64 <= 2 ^ 63 by decode_rd_ok);
     0x8b23c  size < 30 returns -2;
     0x8b25c - 0x8b264  the shadow base through its GOT word 0xa3cf0 (cell 0xac678: transport_cells rows 1-2) into s5;
     0x8b288 / 0x8b290  buf[12], buf[13] (the EtherType); not 0x885f returns -3 (0x8b2a4 to 0x8b59c, a1 = -3);
     0x8b2dc / 0x8b2e4  buf[14], buf[15] (numbytes, s6); s6 < 16 (0x8b2f8) or s6 > size - 14 (0x8b300) returns -4
              (a1 = -4 at 0x8b2f4);
     0x8b318  the call of __asan_memcpy (0x523ec = transportb_sigma TB___asan_memcpy) with (f, buf, 6); 0x8b330 the
              same with (f + 6, buf + 6, 6);
     0x8b3a0 / 0x8b3b8  buf[16], buf[17] (the sum); 0x8b3d8 the call of rd32 (0x8b734) with a0 = buf + 18 (0x8b3d4;
              send) and 0x8b400 with a0 = buf + 22 (0x8b3fc; ack), each reading 4 bytes of buf; 0x8b450 / 0x8b468
              buf[26], buf[27] (retry), 0x8b4a8 buf[28] (cmd), 0x8b4e0 buf[29] (ncmds);
     stores into f, each after the instrumented check of the shadow byte at (a >> 3) + 0x7fff8000: 2 bytes 0x885f at
              f + 12 (0x8b354), 2 bytes numbytes at f + 16 (0x8b36c), 2 bytes the sum at f + 18 (0x8b3cc), 4 bytes
              rd32's result at f + 20 (0x8b3f4) and at f + 24 (0x8b41c), 2 bytes retry at f + 28 (0x8b47c), 1 byte
              cmd at f + 30 (0x8b4b4), 1 byte ncmds at f + 31 (0x8b4ec), 8 bytes buf + 30 at f + 32 (0x8b510), 8
              bytes numbytes - 16 at f + 40 (0x8b52c), 8 bytes size - numbytes - 14 at f + 48 (0x8b548), 2 bytes
              diginet_sum16's result at f + 56 (0x8b564), 1 byte (sum = body sum) at f + 58 (0x8b594; the sum is
              read back from f + 18 by the 2-byte load at 0x8b580); a1 = 0 (0x8b588), returned in a0 (0x8b5a0);
     0x8b54c  the call of diginet_sum16 (0x8afd8) with a0 = buf + 30 (0x8b508) and a1 = numbytes - 16 (0x8b524): the
              body sum over buf[30 .. 30 + numbytes - 16) (diginet_sum16 returns 0 at once when a1 = 0);
     its loads of buf, and those of __asan_memcpy, rd32 and diginet_sum16, lie in [buf, buf + 14 + numbytes), inside
              [buf, buf + size) on every path that reaches them; every path with a code other than 0 returns before
              0x8b304 and stores nothing into f.
   UBSan checks: 15 branches to the trap word at 0x8b5d0 (a trap, which the statement counts as an error):
     0x8b308  after a0 = f & 7 (0x8b304): f is not 8-aligned, on the code-0 path, kept not taken by f mod 8 = 0;
     14 pointer-overflow checks: buf + 12 (0x8b24c, 0x8b258: buf + 12 = 2 ^ 64 - 1), h = buf + 14 (0x8b2ac,
              0x8b2b8: h = 2 ^ 64 - 1), buf + 6 (0x8b320), h + 2 (0x8b370, 0x8b37c: buf + 16 = 2 ^ 64 - 1), h + 4
              (0x8b3d0), h + 8 (0x8b3f8), h + 12 (0x8b420, 0x8b42c: buf + 26 = 2 ^ 64 - 1), h + 14 (0x8b480), h + 15
              (0x8b4b8), buf + 30 (0x8b4f0: f->body = buf + 30). Each runs after size < 30 returned (0x8b23c), so b
              is not empty, and trans_src_ok gives buf + size <= 2 ^ 63 (the block below alloc_ceiling, AR_laws'
              al_blocks, or decode_rd_ok), so buf + 30 does not wrap and none is taken.
   Error paths (24 calls, no abort): __asan_report_load1 (0x59504) x10 (0x8b5dc, 0x8b5ec, 0x8b5fc, 0x8b608, 0x8b634,
   0x8b644, 0x8b68c, 0x8b69c, 0x8b6b8, 0x8b6d4: loads of buf), kept unreached by trans_src_ok (the block's bytes are
   marked usable by AR_laws' AR_shadow_law; every other case carries decode_rd_ok's range_addressable of
   [buf, buf + size)); __asan_report_load2 (0x595a4) x1 (0x8b70c: the read of f + 18), __asan_report_store1 (0x59824)
   x3 (0x8b6c8, 0x8b6e4, 0x8b71c), __asan_report_store2 (0x598c4) x5 (0x8b618, 0x8b628, 0x8b658, 0x8b6ac, 0x8b6f8),
   __asan_report_store4 (0x59964) x2 (0x8b66c, 0x8b680), __asan_report_store8 (0x59a04) x3 (0x8b720, 0x8b728,
   0x8b730: shadow byte not 0 before an 8-byte store), kept unreached by decode_rd_ok's range_addressable of
   [f, f + 64): every byte accessed is addressable (YG0v.v saddr_ok: shadow 0, or a mod 8 below a shadow value under
   8), which is what each check tests; the granule each 8-byte store starts in has its last byte in the range, so its
   shadow byte is 0. The two __asan_memcpy calls need the 6 + 6 bytes at f and buf addressable, disjoint and outside
   the ESTACK below sp - 80 (decode_rd_ok, trans_src_ok, the disjointness premise, decode_off_win of f and of buf);
   the rd32 and diginet_sum16 calls need their bytes of buf visible, marked usable and outside their 16-byte frames
   (trans_src_ok, decode_off_win of buf).
   No store reaches a harness global: every store is to f (base register s0 and its offsets), in the caller's
   side-stack frame.
   Stack: 80 bytes of its own, and below sp - 80 the ESTACK __asan_memcpy uses (YG0d.v aintrin_realizes' ecall_pre);
   the leaves rd32 and diginet_sum16 use their 16-byte frames, inside the kit's ESTACK (LeafCgKit.v ecall_pre).

   The caller is diginet_session_rx at 0x878d0 (return address 0x878d4): a0 = buf (s8, its own second argument; not
   0 by the branch at 0x878b0), a1 = size (s7, its third argument), a2 = f (s6 = its class-1 side-stack frame + 32,
   0x878c0; the frame from __asan_stack_malloc_1 at 0x877fc, 128 bytes, description "1 32 64 5 f:265", its shadow
   bytes 4 .. 11 stored 0 at 0x87888 - 0x878a4). buf is receive's heap block (the __wrap_malloc call at 0x836dc, then
   diginet_session_rx at 0x837fc) or diginet_session_poll's local buffer, 1514 bytes at offset 32 of its class-5
   side-stack frame (s9 = frame + 32 at 0x8acc4; the calls at 0x8ad18 and 0x8ad90). It supplies: trans_src_ok (the
   block, or the side-stack frame with decode_rd_ok) and decode_off_win of the bytes at buf, from its own statement;
   fj, the 64 bytes at f, whatever they hold (diginet_session_rx does not fill them before the call); f mod 8 = 0 (a
   side-stack frame is 64-aligned, YG0f.v frame_addr); decode_in_fake (32 + 64 <= 128); decode_twr_ok (the frame is in
   its journal's own list, present and not owned: AR_frames_law); decode_rd_ok (its stores mark f's 8 shadow bytes 0;
   the frame's shadow bytes are present); decode_off_win of f and the disjointness (frames and blocks lie below
   alloc_ceiling and are pairwise disjoint: AR_sep_law). The size bound the code needs (the 64-bit compares at
   0x8b23c, 0x8b300) comes from trans_src_ok (the block below alloc_ceiling, or decode_rd_ok's
   buf + size <= 2 ^ 63). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require rd32_cg diginet_sum16_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module LRd := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.rd32_cg.
Module LSum := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_sum16_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_frame_parse's frame (`sp = sp - 80` at TB_diginet_frame_parse; no realignment) and the ESTACK its callees
   use below sp - 80: __asan_memcpy (aintrin_realizes' ecall_pre), and the leaves rd32 and diginet_sum16 within their
   16-byte frames (the kit's ecall_pre). *)
Definition TRANS_FP_FRAME : Z := 80.
Definition TRANS_FP_STK : Z := TRANS_FP_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame, and its two leaves record
   none. *)
Definition TRANS_FP_EV : Z := 0.

(* struct diginet_frame (include/diginet/diginet.h), 64 bytes, as diginet_frame_parse leaves it for the input bytes
   b at buf when fj are the 64 bytes before the call: parse_cells (lib/Prog/diginet_frame_parse_c.v) when the code is
   0, else fj (the plain contract's two cases). DgnTransportBCg.v frame_f_cells / FRAME_F_SIZE / frame_f_bytes, stated
   here as lib/A/Prog/diginet_frame_parse_cg.v states them. *)
Definition trans_fp_f_cells (buf : Z) (b fj : list byte) : list LC.cell :=
  if fr_code b =? 0 then PParse.parse_cells buf b fj else [LC.CB 64 fj].
Definition TRANS_FP_F_SIZE : Z := 64.
(* The same 64 bytes as values, in the form the walks' image view reads (garr8, YI00.v). *)
Definition trans_fp_f_bytes (buf : Z) (b fj : list byte) : list Z :=
  map (fun x : byte => bv_unsigned x) (LC.cells_bytes (trans_fp_f_cells buf b fj)).

(* The bytes of f the code stores on some path: the two __asan_memcpy destinations [f, f + 12) (0x8b318, 0x8b330)
   and the plain stores at f + 12 .. f + 58 (0x8b354 .. 0x8b594) except f + 14, f + 15 (struct diginet_frame's
   padding after the EtherType). *)
Definition trans_fp_wr (f a : Z) : Prop := f <= a < f + 14 \/ f + 16 <= a < f + 59.

Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, the written range trans_fp_wr f, no meter
   charge, a0 = fr_code b (sign-extended), and the 64 bytes at f as trans_fp_f_bytes gives them. *)
Definition trans_fp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (buf f : Z) (b fj : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TRANS_FP_STK TRANS_FP_EV 0
    (trans_fp_wr f)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (fr_code b) /\
       garr8 segs (mrestrict (w_H W2) mem2) f (trans_fp_f_bytes buf b fj)).

(* The contract at entry address a, in the caller-journal form. buf (a0) holds the bytes b (a1 = their length),
   placed by trans_src_ok and outside this call's stack window, for every b, the empty one included; f (a2) holds the
   64 bytes fj inside one of the caller's live side-stack frames, is a multiple of 8, writable by this call, visible,
   marked usable and outside its stack window; the two do not overlap when b is not empty. *)
Definition transport_diginet_frame_parse_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf f : Z) (b fj : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 buf -> YK11.getr regs 11 = w64 (Z.of_nat (length b)) -> YK11.getr regs 12 = w64 f ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRANS_FP_STK -> spZ regs <= sp0 ->
    buf <> 0 -> f <> 0 ->
    (* Image B's UBSan premise: 0x8b304 a0 = f & 7 (s0 = f) / 0x8b308 branch to the trap word 0x8b5d0 on an f that is
       not 8-aligned; image A's text lacks it. *)
    f mod 8 = 0 ->
    trans_src_ok B lyc Sc W memc buf (Z.of_nat (length b)) ->
    decode_off_win regs TRANS_FP_STK buf (Z.of_nat (length b)) ->
    garr8 segs (mrestrict (w_H W) memc) buf (map bz b) ->
    length fj = 64%nat ->
    garr8 segs (mrestrict (w_H W) memc) f (map bz fj) ->
    decode_in_fake lyc Sc f TRANS_FP_F_SIZE ->
    decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) f TRANS_FP_F_SIZE ->
    decode_rd_ok W memc f TRANS_FP_F_SIZE -> decode_off_win regs TRANS_FP_STK f TRANS_FP_F_SIZE ->
    ((0 < length b)%nat -> f + TRANS_FP_F_SIZE <= buf \/ buf + Z.of_nat (length b) <= f) ->
    st_nev S + k + TRANS_FP_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (trans_fp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs buf f b fj).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the allocator and
   meter laws, the contract of __asan_memcpy and the leaf statements of rd32 and diginet_sum16 give the contract at
   TB_diginet_frame_parse. *)
Definition transport_diginet_frame_parse_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LRd.transport_rd32_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSum.transport_diginet_sum16_cg) fx') ->
  transport_diginet_frame_parse_cg (transportb_sigma TB_diginet_frame_parse).
End fp.
