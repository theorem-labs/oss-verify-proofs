(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame's diginet_frame_parse in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v:189-317, :375-390 (cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), with a written range of the caller's side-stack frame (proofs/libreac/fuzz_decode/lib/A/Prog/DecodeCJ.v:51-56 twr_ok), at this unit's core names and image A; the shared definitions are lib/A/Prog/DgnFrameCg.v's. *)
(* diginet_frame_parse_cg: the ASan walk contract of diginet_frame_parse (src/diginet_frame.c; plain contract
   lib/Prog/diginet_frame_parse_c.v) on fuzz_transport.asan (e89be137db17) at 0x8b6fc =
   transport_sigma TS_diginet_frame_parse, size 0x5fc (1532), as STATEMENTS only (no proof). It stores into no
   harness global and calls __asan_memcpy, so it takes decode's caller-journal form (lib/A/Prog/DgnTransportCg.v
   decode_cg_post over the caller's donor journal ajournal).

   RELOCATED from libdiginet/fuzz_frame lib/A/Prog/diginet_frame_parse_cg.v (file sha256 a1f7ab71317d; donor not
   released; fuzz_frame.asan 67d7e481d74e at 0x82080), the same 1532 code bytes up to the
   pc-relative words (36 pc-relative words differ, no other; re-checked
   here word by word on the two symbol-bearing twins: 383 words, the 36 that differ are the GOT-word load at 0x8b740 /
   0x8b744, the two __asan_memcpy calls and the 32 error-path calls). Every pc below is frame's + 0x967c and was read
   again on transport's twin. The names change: frame_cg_post / frame_twr_ok / frame_rd_ok / frame_in_fake /
   frame_off_win / frame_cells / dgnframe_sigma DF_* become this unit's decode_cg_post / decode_twr_ok / decode_rd_ok /
   decode_in_fake / decode_off_win / transport_cells / transport_sigma TS_*, frame_fp_* / FRAME_FP_* become
   trans_fp_* / TRANS_FP_*, frame_diginet_frame_parse_cg{,_holds_stmt} become
   transport_diginet_frame_parse_cg{,_holds_stmt}, and DgnFrameCg.v's frame_f_cells / FRAME_F_SIZE / frame_f_bytes,
   which DgnTransportCg.v does not have, are stated here as trans_fp_f_cells / TRANS_FP_F_SIZE / trans_fp_f_bytes
   (the same text over this unit's lib/Prog/diginet_frame_parse_c.v parse_cells).
   One premise changes (its placement: DgnTransportCg.v trans_src_ok): frame's `frame_in_block B lyc Sc buf
   (length b)` (the bytes in one of the caller's heap blocks) becomes `trans_src_ok B lyc Sc W memc buf (length b)` with
   `decode_off_win regs TRANS_FP_STK buf (length b)`, both for every b, the empty one included, and the disjointness
   of f and the bytes at buf is asked when b is not empty: transport's diginet_session_rx passes the frame receive
   allocates (a heap block) or diginet_session_poll's local buffer (a side-stack frame). trans_src_ok's non-block
   cases carry decode_rd_ok (every byte visible, the range marked usable), which is what the walk took from the block
   (AR_laws' block shadow), and decode_off_win keeps the range out of this call's stack window, which the block gave
   by lying below alloc_ceiling. The two premises are not guarded by b <> []: at length 0 trans_src_ok still bounds
   buf (0 <= buf below 2 ^ 64 in each case), and without that bound buf = 2 ^ 64 would meet buf <> 0 while w64 buf = 0
   takes the code's buf = 0 test at 0x8b720 (a0 = -1, not fr_code [] = -2). When b is empty and buf is in range, the
   code returns -2 at 0x8b738 before it reads buf.

   The contract. The caller's journal is the premise. a0 = buf, a1 = the length of the bytes b at buf, a2 = f, a
   struct diginet_frame of 64 bytes fj. buf is not 0 and lies with its bytes b where trans_src_ok places it, outside
   this call's stack window; f is not 0 and lies in one of the caller's live
   side-stack frames, where the caller lets the call write it (decode_twr_ok), its bytes are visible and marked usable
   (decode_rd_ok), and it is outside this call's stack window; f and the bytes at buf do not overlap. The function
   returns to ra with a0 = fr_code b, the callee-saved registers kept, no allocator event, every byte outside its
   stack window and outside the bytes of f it stores kept, and the 64 bytes at f = trans_fp_f_bytes buf b fj:
   lib/Prog/diginet_frame_parse_c.v parse_cells when the code is 0, else fj. The written range E is the bytes of f any
   path stores: [f, f + 14) and [f + 16, f + 59). The post states all 64 bytes, so the 7 bytes it never stores (14,
   15, 59 .. 63) and, on a code that is not 0, all 64 bytes are fj.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 383 words:
     0x8b6fc  sp = sp - 48; ra at sp + 40, s0 .. s4 at sp + 32 .. sp + 0; no realignment, no frame pointer
              (s0 = f from 0x8b724);
    0x8b720 / 0x8b728  buf = 0 or f = 0 returns a0 = -1 (kept unreached: buf <> 0 and buf < 2 ^ 64 by trans_src_ok
             with AR; f <> 0 and f + 64 <= 2 ^ 63 by decode_rd_ok);
     0x8b734  size < 30 returns -2;
     0x8b740 - 0x8b748  the shadow base through its GOT word 0xa4090 (cell 0xac9f8: transport_cells rows 1-2);
     0x8b74c - 0x8b78c  buf[12], buf[13] (the EtherType); not 0x885f returns -3 (0x8baf0);
     0x8b790 - 0x8b7d8  buf[14], buf[15] (numbytes, s4); s4 < 16 or s4 > size - 14 returns -4;
     0x8b7e8  the call of __asan_memcpy (0x523b0 = transport_sigma TS___asan_memcpy) with (f, buf, 6); 0x8b7f8 the
              same with (f + 6, buf + 6, 6);
     stores into f, each after the instrumented check of the shadow byte at (a >> 3) + 0x7fff8000: 2 bytes 0x885f at
              f + 12 (0x8b81c), 2 bytes numbytes at f + 16 (0x8b830), 2 bytes at f + 18 (0x8b884), 4 bytes at f + 20
              (0x8b918), 4 bytes at f + 24 (0x8b9a8), 2 bytes at f + 28 (0x8b9f4), 1 byte at f + 30 (0x8ba20), 1 byte
              at f + 31 (0x8ba50), 8 bytes buf + 30 at f + 32 (0x8ba70), 8 bytes numbytes - 16 at f + 40 (0x8ba8c),
              8 bytes size - numbytes - 14 at f + 48 (0x8baa8), 2 bytes the body sum at f + 56 (0x8bb30), 1 byte
              (sum = body sum) at f + 58 (0x8bb54); a0 = 0 at 0x8bb48;
     0x8bab8 - 0x8badc  the body-sum loop over buf[30 .. 30 + numbytes - 16), skipped when numbytes = 16 (the branch
              on a3 = 0 at 0x8baac);
     its loads of buf lie in [buf + 12, buf + 14 + numbytes), inside [buf, buf + size) on every path that reaches
              them; every path with a code other than 0 returns before 0x8b7e8 and stores nothing into f.
   Error paths (32 calls, no abort): __asan_report_load1 (0x594c8) x19 (0x8baec, 0x8bb64 .. 0x8bcb8: loads of buf),
   kept unreached by trans_src_ok (the block's bytes are marked usable by AR_laws' AR_shadow_law; every other case
   carries decode_rd_ok's range_addressable of [buf, buf + size)); __asan_report_store1 (0x597e8) x3 (0x8bcac,
   0x8bcc8, 0x8bce8), __asan_report_store2 (0x59888) x5 (0x8bb98, 0x8bba8, 0x8bbd4, 0x8bc90, 0x8bcd8),
   __asan_report_store4 (0x59928) x2 (0x8bc18, 0x8bc60), __asan_report_store8 (0x599c8) x3 (0x8bcec, 0x8bcf0,
   0x8bcf4: shadow byte not 0 before an 8-byte store), kept unreached by decode_rd_ok's range_addressable of
   [f, f + 64): every byte stored is addressable (YG0v.v saddr_ok: shadow 0, or a mod 8 below a shadow value under
   8), which is what each check tests; the granule each 8-byte store starts in has its last byte in the range, so its
   shadow byte is 0. The two __asan_memcpy calls need the 6 + 6 bytes at f and buf addressable, disjoint and outside
   the ESTACK below sp - 48 (decode_rd_ok, trans_src_ok, the disjointness premise, decode_off_win of f and of buf).
   No store reaches a harness global: every store is to f (base register s0 and its offsets), in the caller's
   side-stack frame.
   Stack: 48 bytes of its own and the ESTACK __asan_memcpy uses below sp - 48 (YG0d.v aintrin_realizes' ecall_pre).

   The caller is diginet_session_rx at 0x876e0 (return address 0x876e4): a0 = buf (its own second argument, s8; not
   0 by the branch at 0x876c0), a1 = size (its third argument, s7), a2 = f (s6 = its class-1 side-stack frame + 32,
   0x876d0; the frame from __asan_stack_malloc_1 at 0x8760c, 128 bytes, its shadow bytes 4 .. 11 stored 0 at
   0x87698 - 0x876b4). buf is receive's heap block (the malloc wrapper call at 0x83814, then diginet_session_rx at
   0x83a40) or diginet_session_poll's local buffer, 1514 bytes at offset 32 of its class-5 side-stack frame (the calls
   at 0x8b000 and 0x8b078). It supplies: trans_src_ok (the block, or the side-stack frame with decode_rd_ok) and
   decode_off_win of the bytes at buf, from its own statement; fj, the 64 bytes at f, whatever they hold
   (diginet_session_rx does not fill them before the call); decode_in_fake (32 + 64 <= 128); decode_twr_ok (the
   frame is in its journal's own list, present and not owned: AR_frames_law); decode_rd_ok (its stores mark f's 8
   shadow bytes 0; the frame's shadow bytes are present); decode_off_win of f and the disjointness (frames and blocks
   lie below alloc_ceiling and are pairwise disjoint: AR_sep_law). The size bound the code needs (the 64-bit compares
   at 0x8b734, 0x8b7d8) comes from trans_src_ok (the block below alloc_ceiling, or decode_rd_ok's
   buf + size <= 2 ^ 63). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_frame_parse's frame (`sp = sp - 48` at TS_diginet_frame_parse; no realignment) and the ESTACK its only
   callee, __asan_memcpy, uses below sp - 48. *)
Definition TRANS_FP_FRAME : Z := 48.
Definition TRANS_FP_STK : Z := TRANS_FP_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition TRANS_FP_EV : Z := 0.

(* struct diginet_frame (include/diginet/diginet.h), 64 bytes, as diginet_frame_parse leaves it for the input bytes
   b at buf when fj are the 64 bytes before the call: parse_cells (lib/Prog/diginet_frame_parse_c.v) when the code is
   0, else fj (the plain contract's two cases). DgnFrameCg.v frame_f_cells / FRAME_F_SIZE / frame_f_bytes, stated at
   this unit. *)
Definition trans_fp_f_cells (buf : Z) (b fj : list byte) : list LC.cell :=
  if fr_code b =? 0 then PParse.parse_cells buf b fj else [LC.CB 64 fj].
Definition TRANS_FP_F_SIZE : Z := 64.
(* The same 64 bytes as values, in the form the walks' image view reads (garr8, YI00.v). *)
Definition trans_fp_f_bytes (buf : Z) (b fj : list byte) : list Z :=
  map (fun x : byte => bv_unsigned x) (LC.cells_bytes (trans_fp_f_cells buf b fj)).

(* The bytes of f the code stores on some path: the two __asan_memcpy destinations [f, f + 12) and the plain stores
   at f + 12 .. f + 58 except f + 14, f + 15 (struct diginet_frame's padding after the EtherType). *)
Definition trans_fp_wr (f a : Z) : Prop := f <= a < f + 14 \/ f + 16 <= a < f + 59.

Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, the written range trans_fp_wr f, no meter
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
   64 bytes fj inside one of the caller's live side-stack frames, writable by this call, visible, marked usable and
   outside its stack window; the two do not overlap when b is not empty. *)
Definition transport_diginet_frame_parse_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf f : Z) (b fj : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 buf -> YK11.getr regs 11 = w64 (Z.of_nat (length b)) -> YK11.getr regs 12 = w64 f ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRANS_FP_STK -> spZ regs <= sp0 ->
    buf <> 0 -> f <> 0 ->
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
   meter laws, and the contract of __asan_memcpy give the contract at TS_diginet_frame_parse. *)
Definition transport_diginet_frame_parse_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  transport_diginet_frame_parse_cg (transport_sigma TS_diginet_frame_parse).
End fp.
