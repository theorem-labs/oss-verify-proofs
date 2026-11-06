(* Modified by Theorem Labs, 2026-10: diginet_announce_parse's leaf statement and its translation lemma, in the form of
   libreac/fuzz_decode's lib/A/Prog/reac_decode_cg.v. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's text of this unit's image-A statement lib/A/Prog/diginet_announce_parse_cg.v, now in the caller-journal form of this unit's lib/A/Prog/diginet_frame_parse_cg.v and no longer the leaf form (image B's diginet_announce_parse calls copy_strz twice, at 0x82d38 and 0x82d5c, and has a 32-byte frame), so it has no translation lemma: the content of image A's leaf contract lib/A/Prog/diginet_announce_parse_c.v (arguments, the bytes read at f, the body bytes, the 40 bytes written at ap, the result; with its amendment `0 < body < 2^64`) placed in the caller's journal (f a readable range of the caller's caller, the body in one of the caller's heap blocks, which also bounds body + length bb below alloc_ceiling, ap in a live side-stack frame of the caller); module paths lib/B (the image-B core's lib/B/YB1v.v, YE2k.v, YCbq.v / YC5d.v; lib/B/Prog/FrameBSyms.v / FrameBAddr.v / DgnFrameCg.v), every address fuzz_frame.asan-ubsan's, the holds statement takes copy_strz's leaf statement lib/B/Prog/copy_strz_cg.v, and image B's UBSan premises `f mod 8 = 0` (0x82c68 `andi a1,a0,7` / 0x82c6c `bnez a1`) and `ap mod 8 = 0` (0x82ce4 `andi a0,s0,7` / 0x82ce8 `bnez a0`), unimp at 0x82d80, while `0 < body` (image A's amended premise) also refutes image B's null checks of body (0x82d24, 0x82d48 `beqz a1`), in the shape of the UBSan image's lib/U/Prog/diginet_announce_parse_c.v. *)
(* diginet_announce_parse_cg (image B): the ASan walk contract of diginet_announce_parse (fuzz_transport.asan-ubsan
   41113a03c82f, 0x8bdec = transportb_sigma TB_diginet_announce_parse, size 0x170 (368)), as STATEMENTS only (no
   proof). Image A's text of this name (lib/A/Prog/diginet_announce_parse_cg.v, with diginet_announce_parse_c.v and
   diginet_announce_parse_F_c.v) is a leaf statement with its translation lemma; image B's function calls copy_strz
   (0x8bf5c) twice and has a 32-byte frame, so this text is in the caller-journal form of
   lib/B/Prog/diginet_frame_parse_cg.v (a written range of the caller's side-stack frame, a leaf callee), with
   lib/B/Prog/DgnTransportBCg.v decode_cg_post as its post, and image B has no _c / _F_c file for it: the content of
   image A's leaf contract lib/A/Prog/diginet_announce_parse_c.v (its arguments, the bytes it reads at f, the body
   bytes, the 40 bytes of ap it writes and their values, its result) is placed in the caller's journal.

   RELOCATED from libdiginet/fuzz_frame's image-B statement lib/B/Prog/diginet_announce_parse_cg.v (file sha256
   40ebcd2fc895; donor not released; fuzz_frame.asan-ubsan at 0x82c44, size 0x170): every pc that text names,
   moved by + 0x91a8, was read again on this unit's twin and holds the same instruction (the frame, the tests for 0,
   the runtime-cell load, the loads of f, the two stores into ap, the two copy_strz calls, the 6 UBSan branches, the
   trap word and the 6 error-path calls). The names change: frame_cg_post / frame_twr_ok / frame_rd_ok /
   frame_in_fake / frame_off_win / frame_cells / frame_leaf_wr_at / FRAME_F_SIZE / frameb_sigma FB_* become this
   unit's decode_cg_post / decode_twr_ok / decode_rd_ok / decode_in_fake / decode_off_win / transport_cells /
   transport_leaf_wr_at / FRAME_F_SIZE (lib/B/Prog/DgnTransportBCg.v) / transportb_sigma TB_* (DgnTransportBSyms,
   DgnTransportBAddr), frame_anp_* / FRAME_ANP_* become trans_anp_* / TRANS_ANP_*,
   frame_diginet_announce_parse_cg{,_holds_stmt} become transport_diginet_announce_parse_cg{,_holds_stmt} (image A's
   name), and the leaf statement is this unit's image-B lib/B/Prog/copy_strz_cg.v transport_copy_strz_cg.
   One premise changes for transport's call site, as image A's text of diginet_frame_parse changes it (its placement:
   DgnTransportBCg.v trans_src_ok; the code does not force it, the caller does): fuzz_frame's `frame_in_block B lyc Sc
   body (length bb)` (bb in one of the caller's heap blocks) becomes `trans_src_ok B lyc Sc W memc body (length bb)`
   with `decode_off_win regs TRANS_ANP_STK body (length bb)`, both when bb is not empty, and the disjointness of ap's 40
   bytes and bb is asked when bb is not empty too: transport's body is buf + 30 of the buffer diginet_session_rx
   parsed, receive's heap block or diginet_session_poll's local buffer (a side-stack frame). trans_src_ok's non-block
   cases carry decode_rd_ok (every byte visible, the range marked usable, body + length bb <= 2 ^ 63), which is what
   the walk took from the block (AR_laws' block shadow and al_blocks), and decode_off_win keeps bb out of this call's
   stack window (and so out of copy_strz's 16-byte frame below it), which the block gave by lying below
   alloc_ceiling. The function reads bb only on the code-0 path, where length bb >= 33.
   Against image A's leaf text, which the B code forces: the caller-journal form (a callee, copy_strz), the 32-byte
   frame (TRANS_ANP_FRAME 32; image A 16), and image B's UBSan premises `f mod 8 = 0` and `ap mod 8 = 0` (fuzz_frame's
   image-B premises; image A has no alignment checks). `0 < body` is image A's premise `0 < body < 2^64`, which also
   refutes image B's two null checks of body.

   The contract. The caller's journal is the premise. a0 = f, the address of a struct diginet_frame; a1 = ap, the
   address of a struct diginet_announce (40 bytes aj). f and ap are not 0 and are multiples of 8. f is a readable
   range of 64 bytes of the caller's caller (decode_rd_ok) outside this call's stack window, with the byte cmd at
   f + 30, and the address body and the length of bb at f + 32 (8 + 8 bytes, little-endian); body is not 0 and the
   bytes bb at body, when not empty, lie where trans_src_ok places them, outside this call's stack window; ap lies in
   one of the caller's live side-stack frames, where the caller lets the call write it (decode_twr_ok), its 40 bytes
   are visible and marked usable (decode_rd_ok), and it is outside this call's stack window; the 40 bytes at ap
   overlap neither f's 64 bytes nor bb. The function returns to ra with a0 = ann_code cmd (length bb) (the libdiginet
   model; sign-extended), the callee-saved registers kept, no allocator event, no side-stack frame added, every byte
   outside its stack window and outside E kept, no meter charge, and the 40 bytes at ap = trans_anp_bytes:
   lib/Prog/diginet_announce_parse_c.v ann_cells body bb aj when the code is 0 (ann_ok: version, bytes 0..9, is
   ann_version; name, bytes 10..19, is ann_name; bytes 20..23 keep aj; unknown, byte 24, is body; unknown_len, byte
   32, is 15), else aj. The written range E (trans_anp_wr) is the bytes of ap any path stores: [ap, ap + 20) (the two
   copy_strz calls; copy_strz's statement writes only its 10-byte field [dst, dst + 10)) and [ap + 24, ap + 40) (its
   two 8-byte stores); no path stores ap + 20 .. ap + 23. On -9 and -4 it stores nothing outside its frame; the post
   states all 40 bytes, so on those codes they are aj.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 368 code bytes of this function are equal in both files),
   symbol diginet_announce_parse, value 0x8bdec, size 368, 92 words:
     0x8bdec  sp = sp - 32; ra at sp + 24, s0 at sp + 16, s1 at sp + 8, s2 at sp + 0; no realignment, no frame
              pointer (s0 = ap from 0x8be00); the restores 0x8bf10 - 0x8bf1c, sp = sp + 32 at 0x8bf20, the return at
              0x8bf24;
     0x8be08 / 0x8be0c  f = 0 or ap = 0 returns a0 = -1 (a1 = -1 at 0x8be04; kept unreached: f <> 0, ap <> 0);
     0x8be18 - 0x8be20  the shadow base through its GOT word 0xa3cf0 (cell 0xac678: transport_cells rows 1-2) into a2;
     0x8be38  the 1-byte load of cmd at f + 30 (shadow byte 0x8be30); (cmd & 0xfe) <> 0xe0 returns -9 (0x8be44,
              0x8be70);
     0x8be5c  the 8-byte load of the length at f + 40 (shadow byte 0x8be54); a length under 33 (unsigned, 0x8be64)
              returns -4 (0x8be68);
     0x8be78 - 0x8be84  s1 = f + 32, s2 = the address of its shadow byte, which it loads;
     0x8bea8  the 8-byte load of body at f + 32; 0x8beb4 stores body (8 bytes) at ap + 24 (shadow byte 0x8bea0);
              0x8bec8 stores 15 (8 bytes) at ap + 32 (shadow byte 0x8bebc);
     0x8bee0  the call of copy_strz (0x8bf5c) with a0 = ap, a1 = body + 15 (0x8bed8): the version field;
     0x8bee4 / 0x8beec  the shadow byte of f + 32 loaded again (s2), body loaded again from f + 32;
     0x8bf04  the call of copy_strz with a0 = ap + 10 (0x8befc), a1 = body + 24 (0x8bf00): the name field; a1 = 0
              (0x8bf08), returned in a0 at 0x8bf0c.
   copy_strz (0x8bf5c, size 244, a 16-byte frame; its own leaf statement lib/B/Prog/copy_strz_cg.v; dst_size 10 and
   n 9 folded in): for i = 0 .. 8 it reads src[i], stops at a 0 byte, else stores it at dst + i; then it stores 0 at
   dst + k (k <= 9). So the two calls read a prefix of [body + 15, body + 24) and of [body + 24, body + 33) and write
   inside [ap, ap + 10) and [ap + 10, ap + 20). Image A inlines both copies: the checks of image A's 4 one-byte
   stores of the strings and 2 one-byte loads of the body (6 of its 12 error paths) are copy_strz's in image B (its
   __asan_report_store1 calls at 0x8c008 / 0x8c044 and its __asan_report_load1 call at 0x8c04c, run in both calls).
   UBSan checks: 6 branches to the trap word at 0x8bf28 (a trap, which the statement counts as an error):
     0x8be14  after a1 = f & 7 (0x8be10): f is not 8-aligned (f->h.cmd), on every path past the two tests for 0; kept
              not taken by f mod 8 = 0;
     0x8be90  after a0 = ap & 7 (0x8be8c): ap is not 8-aligned (ap->unknown), on the code-0 path; kept not taken by
              ap mod 8 = 0;
     0x8becc / 0x8bef0  body = 0 before body + 15 / body + 24; kept not taken by 0 < body;
     0x8bed4 / 0x8bef8  body + 15 / body + 24 wraps (a0 = -15 and body >= a0 unsigned; a0 = -25 and a0 < body
              unsigned); kept not taken by trans_src_ok on the code-0 path, where length bb >= 33 (body + length bb
              <= 2 ^ 63: the block below alloc_ceiling, AR_laws' al_blocks, or decode_rd_ok).
   Error paths (6 calls, no abort): __asan_report_load1 (0x59504) at 0x8bf38 (cmd at f + 30), __asan_report_load8
   (0x596e4) at 0x8bf40 (f + 40), 0x8bf48 and 0x8bf58 (f + 32), kept unreached by decode_rd_ok's range_addressable of
   [f, f + 64) (8 usable bytes from f + 32 and from f + 40 hold the last byte of their 8-byte granules, so those
   shadow bytes are 0, f being a multiple of 8); __asan_report_store8 (0x59a04) at 0x8bf4c (ap + 24) and 0x8bf50
   (ap + 32), kept unreached by decode_rd_ok's range_addressable of [ap, ap + 40).
   copy_strz's own error paths and UBSan checks are refuted by its leaf statement's premises, which the walk gives at
   0x8bee0 / 0x8bf04 from these: src = body + 15 / body + 24 is not 0 (0 < body, no wrap), its 9 bytes lie inside bb
   (length bb >= 33 on the code-0 path) and are marked usable and outside the leaf's frame (trans_src_ok,
   decode_off_win of bb); dst = ap / ap + 10 has 10 visible, usable bytes (decode_rd_ok), not allocator-owned
   (decode_twr_ok) and not in the loaded image (decode_in_fake and AR_laws' al_client_img), apart from the source
   bytes (the ap / bb disjointness); the leaf's 16-byte frame lies inside the kit's ESTACK below sp - 32.
   Reads across the copy_strz calls: f + 32 is read again at 0x8beec; the leaf's post keeps every byte outside its
   frame and outside [dst, dst + 10), and f does not overlap [ap, ap + 40).
   No store reaches a harness global: its stores are to ap (base register s0) and, through copy_strz, inside
   [ap, ap + 20), in the caller's side-stack frame.
   Stack: 32 bytes of its own, and below sp - 32 the kit's ESTACK the leaf copy_strz needs (LeafCgKit.v ecall_pre).

   The caller is on_announce at 0x87e6c (return address 0x87e70): a0 = f (s6: its own second argument, the 64 bytes
   at diginet_session_rx's class-1 side-stack frame + 32 that diginet_frame_parse filled; diginet_session_rx's call at
   0x87b78), a1 = ap (s10 = on_announce's class-3 side-stack frame + 32, 0x87d74; the frame from
   __asan_stack_malloc_3 at 0x87d3c, a0 = 352 (fs_frame_bytes 3 = 512 bytes), description
   "3 32 40 5 a:186 112 72 5 n:196 224 72 6 fn:217", the shadow bytes 4 .. 8 of its 40 bytes stored 0 at 0x87dc4 and
   0x87e54 - 0x87e60), aj = the 40 bytes there, whatever they hold (on_announce does not fill them before the call).
   It supplies: decode_rd_ok and decode_off_win of f, and
   the bytes at f + 30 and f + 32, from diginet_frame_parse's post and its own statement; body = buf + 30, bb the
   frame's body bytes, inside the buffer diginet_session_rx parsed (trans_src_ok of a sub-range of the buffer's
   bytes); f mod 8 = 0 and ap mod 8 = 0 (a side-stack frame is 64-aligned, YG0f.v frame_addr, and both are frame +
   32); decode_in_fake (32 + 40 <= 512); decode_twr_ok (the frame is in its journal's own list, present and not
   owned: AR_frames_law); decode_rd_ok of ap (its stores mark the 5 shadow bytes 0); decode_off_win of ap and the two
   disjointness premises (frames and blocks lie below alloc_ceiling and are pairwise disjoint: AR_sep_law). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_announce_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require copy_strz_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
(* The plain contract, for its cell list ann_cells (which does not depend on the image). *)
Module PAnn := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_announce_parse_c.
Module LCpy := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.copy_strz_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_announce_parse's frame (`sp = sp - 32` at TB_diginet_announce_parse; no realignment) and the ESTACK below
   sp - 32 its leaf callee copy_strz needs (its 16-byte frame, inside the kit's ecall_pre). *)
Definition TRANS_ANP_FRAME : Z := 32.
Definition TRANS_ANP_STK : Z := TRANS_ANP_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame, and copy_strz records none. *)
Definition TRANS_ANP_EV : Z := 0.

(* The code is 0: cmd is e0 or e1 and bb has 33 bytes or more (DgnSpec.ann_code). Only then does the function read
   the body field and the body, and write the bytes at ap (image A's lib/A/Prog/diginet_announce_parse_c.v ann_ok). *)
Definition ann_ok (cmd : Z) (bb : list byte) : bool := ann_code cmd (Z.of_nat (length bb)) =? 0.

(* The 16 bytes at f + 32 the function reads: struct diginet_frame's body (the address body) and body_len (the length
   of bb), little-endian (the leaf contract's bytes_at (f + 32) (le8 body ++ le8 (length bb))). *)
Definition trans_anp_f32_bytes (body : Z) (bb : list byte) : list Z :=
  map bz (LC.cells_bytes [LC.C8 (w64 body); LC.C8 (w64 (Z.of_nat (length bb)))]).

(* The 40 bytes at ap after the call: the plain contract's two cases (ann_cells on code 0, else the old bytes aj). *)
Definition trans_anp_cells (cmd body : Z) (bb aj : list byte) : list LC.cell :=
  if ann_ok cmd bb then PAnn.ann_cells body bb aj else [LC.CB 40 aj].
Definition trans_anp_bytes (cmd body : Z) (bb aj : list byte) : list Z :=
  map bz (LC.cells_bytes (trans_anp_cells cmd body bb aj)).

(* The bytes of ap the code stores on some path: the two copy_strz fields [ap, ap + 10) and [ap + 10, ap + 20)
   (0x8bee0, 0x8bf04) and the two 8-byte stores at ap + 24 (0x8beb4) and ap + 32 (0x8bec8); not ap + 20 .. ap + 23. *)
Definition trans_anp_wr (ap x : Z) : Prop := ap <= x < ap + 20 \/ ap + 24 <= x < ap + 40.

Section anp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, the written range trans_anp_wr ap, no meter
   charge, a0 = ann_code cmd (length bb) (sign-extended), and the 40 bytes at ap as trans_anp_bytes gives them. *)
Definition trans_anp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (ap cmd body : Z) (bb aj : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TRANS_ANP_STK TRANS_ANP_EV 0
    (trans_anp_wr ap)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (ann_code cmd (Z.of_nat (length bb))) /\
       garr8 segs (mrestrict (w_H W2) mem2) ap (trans_anp_bytes cmd body bb aj)).

(* The contract at entry address a, in the caller-journal form (image A's leaf contract
   lib/A/Prog/diginet_announce_parse_c.v with each range placed). f (a0) is a readable 64-byte range outside this
   call's stack window, holding cmd at f + 30 and body, length bb at f + 32; bb lies at body, placed by trans_src_ok
   and outside this call's stack window when not empty; ap (a1) holds the 40 bytes aj inside one of the caller's live
   side-stack frames, writable by this call, visible, marked usable and outside its stack window, apart from f's 64
   bytes and, when bb is not empty, from bb. *)
Definition transport_diginet_announce_parse_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (f ap cmd body : Z) (bb aj : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 f -> YK11.getr regs 11 = w64 ap ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRANS_ANP_STK -> spZ regs <= sp0 ->
    f <> 0 -> ap <> 0 ->
    (* Image B's UBSan premises: 0x8be10 a1 = f & 7 / 0x8be14 (f) and 0x8be8c a0 = ap & 7 / 0x8be90 (ap) branch to
       the trap word 0x8bf28 on a struct pointer that is not 8-aligned; 0 < body (image A's leaf contract states
       0 < body < 2^64; here trans_src_ok bounds body above when bb is read) keeps 0x8becc / 0x8bef0, the branches on
       body = 0, not taken. *)
    f mod 8 = 0 -> ap mod 8 = 0 -> 0 < body ->
    0 <= cmd < 2 ^ 8 ->
    garr8 segs (mrestrict (w_H W) memc) (f + 30) [cmd] ->
    garr8 segs (mrestrict (w_H W) memc) (f + 32) (trans_anp_f32_bytes body bb) ->
    decode_rd_ok W memc f FRAME_F_SIZE -> decode_off_win regs TRANS_ANP_STK f FRAME_F_SIZE ->
    ((0 < length bb)%nat -> trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb))) ->
    ((0 < length bb)%nat -> decode_off_win regs TRANS_ANP_STK body (Z.of_nat (length bb))) ->
    garr8 segs (mrestrict (w_H W) memc) body (map bz bb) ->
    length aj = 40%nat ->
    garr8 segs (mrestrict (w_H W) memc) ap (map bz aj) ->
    decode_in_fake lyc Sc ap 40 ->
    decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) ap 40 ->
    decode_rd_ok W memc ap 40 -> decode_off_win regs TRANS_ANP_STK ap 40 ->
    ap + 40 <= f \/ f + FRAME_F_SIZE <= ap ->
    ((0 < length bb)%nat -> ap + 40 <= body \/ body + Z.of_nat (length bb) <= ap) ->
    st_nev S + k + TRANS_ANP_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (trans_anp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs ap cmd body bb aj).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the allocator and
   meter laws, and the leaf statement of copy_strz (a leaf that writes a range of its caller) give the contract at
   TB_diginet_announce_parse. *)
Definition transport_diginet_announce_parse_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @transport_leaf_wr_at rc B (@LCpy.transport_copy_strz_cg) fx') ->
  transport_diginet_announce_parse_cg (transportb_sigma TB_diginet_announce_parse).
End anp.
