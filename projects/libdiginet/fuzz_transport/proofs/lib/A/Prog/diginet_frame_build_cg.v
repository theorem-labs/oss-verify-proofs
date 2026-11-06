(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame's diginet_frame_build in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v:267-317 (cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), with a written range E and the caller's write right of proofs/libreac/fuzz_decode/lib/A/Prog/DecodeCJ.v:49-56 (DgnFrameCg.v frame_twr_ok), at this unit's core names and image A; the shared definitions are lib/A/Prog/DgnFrameCg.v's. *)
(* diginet_frame_build_cg: the ASan walk contract of diginet_frame_build (src/diginet_frame.c:93-127; plain contracts
   lib/Prog/diginet_frame_build_c.v and the wide lib/Prog/diginet_frame_build_w_c.v) on fuzz_transport.asan
   (e89be137db17) at 0x8bcf8 = transport_sigma TS_diginet_frame_build, size 1344, as STATEMENTS only (no proof). One
   of its callers, send_data, passes g_s.inflight_frame (a harness global) as out, so it is a G-form caller-journal
   walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell
   (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS).

   RELOCATED from libdiginet/fuzz_frame lib/A/Prog/diginet_frame_build_cg.v (file sha256 6514026a2eee; donor not
   released; fuzz_frame.asan 67d7e481d74e at 0x8267c), the same 1344 code bytes up to the pc-relative words (30
   pc-relative words differ, no other; re-checked here word by word on the two
   symbol-bearing twins: 336 words, the 30 that differ are the GOT-word load at 0x8bd8c, the call of
   diginet_body_check at 0x8bd9c, the three __asan_memcpy calls, the __asan_memset call and the 24 error-path calls).
   Every pc below is frame's + 0x967c and was read again on transport's twin. The names change: frame_cg_post /
   frame_twr_ok / frame_rd_ok / frame_in_fake / frame_off_win / frame_cells / dgnframe_sigma DF_* become this unit's
   transport_cg_post / transport_twr_ok_g / decode_rd_ok / decode_in_fake / decode_off_win / transport_cells /
   transport_sigma TS_*, frame_diginet_frame_build_cg{,_holds_stmt} become transport_diginet_frame_build_cg{,_holds_stmt},
   and the callee statement is this unit's diginet_body_check_cg.v transport_diginet_body_check_cg (with its
   TRANS_BC_STK and TRANS_BC_CID); FRAME_FB_FRAME / FRAME_FB_STK / FRAME_FB_EV, frame_fb_hdr_cells /
   frame_fb_hdr_bytes and frame_fb_post keep fuzz_frame's names.
   The changes:
   - the form (the G form, TransportGCg.v): frame's donor journal ajournal and frame_cg_post become the G
     journal ajournal_gx G_HARNESS 0 [] and transport_cg_post; the holds statement takes trans_g_unowned and
     trans_g_no_errno (DgnTransportCg.v; G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok / gx_noerrno, so the donor
     callee diginet_body_check is lifted by TransportGCg.v gx_call_cg through decode_cg_post_dcg), and
     trans_ro_rd_unowned and trans_rom_no_errno (as check_sent_frame_cg.v, desk_named_cg.v do): trans_src_ok's
     TRANS_RO_RD case keeps dst's, src's and the body's bytes across diginet_body_check only through acall_kept's
     image clause (DgnTransportCg.v trans_src_ok_acall, trans_src_ok_acall_g take both facts).
   - out: frame's `frame_in_block B lyc Sc out cap` becomes DgnTransportCg.v trans_out_ok (out in one of the caller's
     live side-stack frames, send_control; or in G with trans_sh_any, its two shadow facts at every AR state,
     send_data's g_s.inflight_frame; and decode_rd_ok), and frame_twr_ok becomes the G-form write right
     transport_twr_ok_g at the call's sp - 96 (each byte an awr_byte of the caller's journal, or a byte of G).
   - dst 6, src 6 and the body: frame's frame_in_block becomes DgnTransportCg.v trans_src_ok (a heap block; or, with
     decode_rd_ok, a side-stack frame, G with trans_sh_any, the machine stack, or TRANS_RO_RD with trans_sh_any) and
     decode_off_win at FRAME_FB_STK. Both callers pass g_s.desk_mac (s + 120) and g_s.cfg.host_mac (s + 0), the G
     case; send_control passes the body (0, 0) (trans_src_ok_null).
   - the body pointer: `body <> 0` becomes `body <> 0 \/ length bb = 0%nat`, the wide plain contract's premise
     (send_control passes a5 = a6 = 0 at 0x86ef8 / 0x86efc); diginet_body_check's statement asks the same.
   - mode: frame's `mode = 0 \/ mode = 1` becomes `-2 ^ 31 <= mode < 2 ^ 31` (a7 holds it sign-extended), the wide
     plain contract's premise: both callers pass s->cfg.sum_mode (a 4-byte signed load at s + 20), which nothing
     bounds. The code returns -1 for any other mode (0x8bd74), so a0 is diginet_frame_build_w_c.v build_code_w and the
     bytes at out are build_out_w (frame's build_code / build_out when mode is 0 or 1).
   - X gains TransportGCg.v gx_kept_ex G_HARNESS E: every byte of G outside E = [out, out + cap) is kept.
     acall_kept_g's image clause leaves G open (a G-form call may change a global), so without it a caller could not
     carry its world relation past the call. The walk has it: the code stores only into [out, out + len) and its own
     frame, the intrinsics keep every byte outside their destination and their stack, and diginet_body_check keeps
     every byte of G (gx_call_cg).

   The contract. The caller's G journal is the premise. a0 = out, a1 = cap (the length of the bytes oj at out),
   a2 = dst, a3 = src, a4 = hp, a5 = body, a6 = body_len (the length of the bytes bb at body), a7 = mode (an int,
   sign-extended). out, dst, src and hp are not 0; body is not 0 or bb is empty. [out, out + cap) lies where
   trans_out_ok places it, the caller lets the call write it (transport_twr_ok_g at the call's sp - 96), and it holds
   oj. The 6 bytes dmac at dst, the 6 bytes smac at src and bb at body lie where trans_src_ok places them, outside this
   call's stack window. The 12 bytes at hp + 4 (send_counter, ack_counter, retry, cmd, num_commands of a struct
   diginet_header) lie in a side-stack frame of the caller's state, visible, marked usable and outside this call's
   stack window. out's range is disjoint from the ranges it reads. Class 2 of the side stack has a free frame (for
   diginet_body_check). The function returns to ra with a0 = build_code_w bb cap mode (sign-extended), the
   callee-saved registers kept, the caller's G journal extended by no allocator event, no side-stack frame added, the
   bytes acall_kept_g G_HARNESS keeps (outside the stack window and outside E = [out, out + cap)), every byte of G
   outside E kept (gx_kept_ex), no meter charge, and the cap bytes at out = build_out_w dmac smac send ack retry cmd
   ncmds bb mode oj: build_frame then the old tail when the code is the frame length, oj unchanged when the code is
   negative.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 336 words:
     0x8bcf8  sp = sp - 96; ra at sp + 88, s0 .. s10 at sp + 80 .. sp + 0; no realignment, no frame pointer
              (s0 = out from 0x8bd58); these 12 stores into its own frame are loaded back at 0x8c0cc - 0x8c0f8;
     0x8bd2c  s8 = -1; out, dst, src or hp = 0 (0x8bd30, 0x8bd38, 0x8bd40, 0x8bd48) and body = 0 with body_len <> 0
              (0x8bd5c - 0x8bd68) return -1 (kept unreached by the premises); 1 < mode as a 64-bit unsigned value
              (0x8bd74) returns -1 (build_code_w's -1); 1484 < body_len (0x8bd7c, unsigned) returns -4 (0x8bd80);
     0x8bd88 - 0x8bd90 the shadow base through the GOT word 0xa4090 (transport_cells rows 1-2) into s10;
     0x8bd9c  the call of diginet_body_check (0x8c530 = transport_sigma TS_diginet_body_check; a0 = body,
              a1 = body_len), return address 0x8bda0; a result not 0 returns -10 (0x8bda4);
     0x8bdac - 0x8bdbc s9 = 30 + body_len, s8 = len = max 60 s9; 0x8bdc0 cap < len (unsigned) returns -5 (0x8bdc4);
     0x8bdd8  the call of __asan_memcpy (0x523b0 = transport_sigma TS___asan_memcpy) with (out, dst, 6), return
              address 0x8bddc; 0x8bde8 the same with (out + 6, src, 6), return address 0x8bdec;
     0x8bdec - 0x8c09c 18 byte stores to out + 12 .. out + 29, each after the instrumented check of its shadow byte
              k at (a >> 3) + 0x7fff8000 (k = 0, or (a & 7) < k, goes on; else the error path): 0x88, 0x5f,
              (16 + body_len) >> 8, 16 + body_len, sum >> 8, sum, then send and ack big-endian (4-byte loads at
              0x8bf10 from hp + 4 and 0x8bf94 from hp + 8), retry big-endian (2-byte load at 0x8c018 from hp + 12),
              cmd (1-byte load at 0x8c064 from hp + 14), num_commands (1-byte load at 0x8c094 from hp + 15); each load
              after the instrumented check of its shadow byte (an n-byte load goes on when k = 0 or ((a & 7) + n - 1)
              < k);
     0x8be68 - 0x8beb8 the sum loop when body_len <> 0 and mode = 0: a 1-byte load of each body byte after its
              instrumented check; 0x8beb8 a2 = the low 32 bits of the sum shifted right by 8; sum = 0 otherwise;
     0x8c0b0  the call of __asan_memcpy with (out + 30, body, body_len), return address 0x8c0b4, skipped when
              body_len = 0 (0x8c0a0);
     0x8c0c4  the call of __asan_memset (0x5284c = transport_sigma TS___asan_memset) with (out + 30 + body_len, 0,
              len - 30 - body_len), return address 0x8c0c8, skipped when 30 + body_len >= len (0x8c0b4);
     0x8c0c8  a0 = the low 32 bits of s8, sign-extended; ra, s0 .. s10 loaded back, sp = sp + 96, return at 0x8c100.
   Error paths: 24 calls: TS___asan_report_store1 (0x597e8) x18 (0x8c10c .. 0x8c234, before the stores to out + 12 ..
   out + 29), TS___asan_report_load4 (0x59608) x2 (0x8c158, 0x8c19c: hp + 4, hp + 8), TS___asan_report_load2
   (0x59568) x1 (0x8c1e0: hp + 12), TS___asan_report_load1 (0x594c8) x3 (0x8c208, 0x8c224: hp + 14, hp + 15; 0x8beb4:
   the body). Every one of them comes after the call of diginet_body_check, and each is kept unreached by the shadow
   of its range at that point: out, by trans_out_ok (a side-stack frame: its decode_rd_ok, the frames' shadow bytes
   kept by acall_kept; G: trans_sh_any at the state after the call; cap >= len >= 60 at the stores); the header range,
   a side-stack frame, as out; the body, by trans_src_ok (the heap blocks' and the stack's shadow by AR, a frame's by
   acall_kept, G and TRANS_RO_RD by trans_sh_any). No abort.
   The intrinsics' own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at with the destination
   [out, ...) given by transport_twr_ok_g): range_addressable and shadow_hull_vis of [out, out + 12), [out + 30,
   out + 30 + body_len), [out + 30 + body_len, out + len), of dst's and src's 6 bytes and of bb, the same way; the
   ranges are disjoint (the disjointness premises) and outside the ESTACK below sp - 96 (decode_off_win,
   trans_out_ok, transport_twr_ok_g).
   Writes into caller memory: only [out, out + len), by the three memcpy calls, the memset call and the 18 stores,
   and only when the result is len >= 0; no byte of out is written on a negative result (every negative return is
   before 0x8bdd8). E = [out, out + cap), and the post gives all cap bytes (build_out_w), so E costs the caller no
   fact. diginet_body_check writes no byte of its caller (its E is empty).
   Reads across the call of diginet_body_check (0x8bd9c): dst's, src's, the header's and the body's bytes, oj's tail
   and the shadow of all of them are read after it. Its post (DgnTransportCg.v decode_cg_post: YCbq.v acall_kept, E
   empty) keeps the bytes at or above alloc_ceiling outside its window (the machine stack), the image bytes outside
   the owned statics and errno (G: trans_g_unowned, trans_g_no_errno; TRANS_RO_RD: trans_ro_rd_unowned,
   trans_rom_no_errno), the caller's heap block bytes, and the bytes of the side-stack frames of the call state and
   their shadow bytes. Every shadow byte lies below alloc_ceiling; after the call one comes from AR at that state (the
   stack's zero range, the blocks' shadow, trans_sh_any for G and TRANS_RO_RD) or from the frames' clause
   (DgnTransportCg.v trans_src_ok_kept, trans_src_ok_acall_g).
   Stack: the frame (96), and below its sp the largest callee window: diginet_body_check's PBC.TRANS_BC_STK, ESTACK
   for __asan_memcpy and __asan_memset (YG0d.v aintrin_realizes).

   The callers, each supplying every premise from its own walk (s = &g_s = 0x5df9c0 in both):
   - send_control at 0x86f00 (return address 0x86f04): a0 = out = its class-2 side-stack frame + 32 (0x86ee4; the
     frame from __asan_stack_malloc_2 at 0x86dd4, 160 bytes; out's 60 bytes are marked usable by its shadow stores
     0x86e78 - 0x86e98: 7 shadow bytes 0 and one 4), a1 = 60, a2 = s + 120 (g_s.desk_mac), a3 = s
     (g_s.cfg.host_mac), a4 = hp = the frame + 128 (0x86eb0; h's two shadow bytes 0 at 0x86e64 - 0x86e68, its fields
     stored at 0x86e9c - 0x86ed0), a5 = a6 = 0, a7 = s->cfg.sum_mode (0x86ee0);
   - send_data at 0x8a2a8 (return address 0x8a2ac): a0 = out = s + 216 (g_s.inflight_frame, 0x8a288), a1 = 1514,
     a2 = s + 120, a3 = s, a4 = hp = its class-0 side-stack frame + 32 (s8, 0x8a1e0; the frame from
     __asan_stack_malloc_0 at 0x8a1a8, 64 bytes; h's two shadow bytes 0 at 0x8a214 - 0x8a218; h zeroed by its
     __asan_memset at 0x8a244, then its fields stored), a5 = its body argument, a6 = its body_len argument,
     a7 = s->cfg.sum_mode (0x8a284).
   For the g_s ranges (out = s + 216, 1514 bytes; dst, src) a caller proves trans_sh_any from g_s's zero-shadow row
   (DgnTransportCg.v trans_gs_zshadow, trans_sh_any_zshadow; their aligned shadow groups lie inside g_s).
   Template: proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v:267-317 (post and statement), :372-389 (holds
   statement); the post is TransportGCg.v transport_cg_post. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_body_check_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PBuildW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_build_w_c.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_frame_build's frame (`sp = sp - 96` at TS_diginet_frame_build; it does not realign sp), and the largest
   stack a callee uses below its sp: diginet_body_check's own window, ESTACK for __asan_memcpy and __asan_memset. *)
Definition FRAME_FB_FRAME : Z := 96.
Definition FRAME_FB_STK : Z := FRAME_FB_FRAME + Z.max ESTACK PBC.TRANS_BC_STK.
(* No allocator event: it calls no allocator, and diginet_body_check records none. *)
Definition FRAME_FB_EV : Z := 0.

(* The 12 bytes at hp + 4 the function reads (the plain contract's bytes_at (hp + 4)): send_counter and ack_counter
   (little-endian uint32), retry (little-endian uint16), cmd, num_commands. It does not read numbytes and sum (hp + 0
   .. hp + 3). *)
Definition frame_fb_hdr_cells (send ack retry cmd ncmds : Z) : list LC.cell :=
  [LC.C4 (w64 send); LC.C4 (w64 ack); LC.C2 (w64 retry); LC.C1 (b8 cmd); LC.C1 (b8 ncmds)].
Definition frame_fb_hdr_bytes (send ack retry cmd ncmds : Z) : list Z :=
  map bz (LC.cells_bytes (frame_fb_hdr_cells send ack retry cmd ncmds)).

Section fb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no allocator event, the written range
   [out, out + cap), no meter charge, and X: a0 = build_code_w bb cap mode, the cap bytes at out = build_out_w
   (lib/Prog/diginet_frame_build_w_c.v), and every byte of G outside [out, out + cap) kept (gx_kept_ex). *)
Definition frame_fb_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (out : Z) (dmac smac : list byte) (send ack retry cmd ncmds : Z) (bb : list byte)
    (mode : Z) (oj : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    FRAME_FB_STK FRAME_FB_EV 0
    (fun a => out <= a < out + Z.of_nat (length oj))
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (PBuildW.build_code_w bb (Z.of_nat (length oj)) mode) /\
       garr8 segs (mrestrict (w_H W2) mem2) out
         (map bz (PBuildW.build_out_w dmac smac send ack retry cmd ncmds bb mode oj)) /\
       gx_kept_ex segs TG.G_HARNESS (fun a => out <= a < out + Z.of_nat (length oj)) W memc W2 mem2).

(* The contract at entry address a, in the G-form caller-journal form (the wide plain contract's premises,
   lib/Prog/diginet_frame_build_w_c.v, with each range placed: out where trans_out_ok places it, writable by the call;
   dst, src and body where trans_src_ok places them; the header bytes in a side-stack frame of the caller's state).
   The function's write right on out is checked at its sp (spZ regs - FRAME_FB_FRAME), the sp of its three
   __asan_memcpy calls and its __asan_memset call. count_cid 2 (frames Sc) < fs_frames 2 is what diginet_body_check's
   statement asks. *)
Definition transport_diginet_frame_build_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (out dst src hp body mode send ack retry cmd ncmds : Z) (dmac smac bb oj : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 out -> YK11.getr regs 11 = w64 (Z.of_nat (length oj)) ->
    YK11.getr regs 12 = w64 dst -> YK11.getr regs 13 = w64 src ->
    YK11.getr regs 14 = w64 hp -> YK11.getr regs 15 = w64 body ->
    YK11.getr regs 16 = w64 (Z.of_nat (length bb)) -> YK11.getr regs 17 = w64 mode ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - FRAME_FB_STK -> spZ regs <= sp0 ->
    out <> 0 -> dst <> 0 -> src <> 0 -> hp <> 0 -> body <> 0 \/ length bb = 0%nat ->
    -2 ^ 31 <= mode < 2 ^ 31 ->
    0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
    trans_out_ok B lyc Sc W memc out (Z.of_nat (length oj)) ->
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs - FRAME_FB_FRAME)
      out (Z.of_nat (length oj)) ->
    garr8 segs (mrestrict (w_H W) memc) out (map bz oj) ->
    length dmac = 6%nat -> trans_src_ok B lyc Sc W memc dst 6 -> decode_off_win regs FRAME_FB_STK dst 6 ->
    garr8 segs (mrestrict (w_H W) memc) dst (map bz dmac) ->
    length smac = 6%nat -> trans_src_ok B lyc Sc W memc src 6 -> decode_off_win regs FRAME_FB_STK src 6 ->
    garr8 segs (mrestrict (w_H W) memc) src (map bz smac) ->
    trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb)) ->
    decode_off_win regs FRAME_FB_STK body (Z.of_nat (length bb)) ->
    garr8 segs (mrestrict (w_H W) memc) body (map bz bb) ->
    decode_in_fake lyc Sc (hp + 4) 12 ->
    decode_rd_ok W memc (hp + 4) 12 -> decode_off_win regs FRAME_FB_STK (hp + 4) 12 ->
    garr8 segs (mrestrict (w_H W) memc) (hp + 4) (frame_fb_hdr_bytes send ack retry cmd ncmds) ->
    out + Z.of_nat (length oj) <= dst \/ dst + 6 <= out ->
    out + Z.of_nat (length oj) <= src \/ src + 6 <= out ->
    out + Z.of_nat (length oj) <= hp + 4 \/ hp + 16 <= out ->
    out + Z.of_nat (length oj) <= body \/ body + Z.of_nat (length bb) <= out ->
    count_cid PBC.TRANS_BC_CID (frames Sc) < fs_frames PBC.TRANS_BC_CID ->
    st_nev S + k + FRAME_FB_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (frame_fb_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs out dmac smac send ack retry cmd ncmds
         bb mode oj).

(* The statement the walk will prove: the runtime cells, the record facts that no TRANS_RO_RD byte is an owned static
   or errno, the allocator and meter laws, the record facts that no byte of G is an owned static or errno (gx_ok /
   gx_noerrno: the donor callee keeps G, gx_call_cg), and the contracts of __asan_memcpy, __asan_memset and
   diginet_body_check give the contract at TS_diginet_frame_build. *)
Definition transport_diginet_frame_build_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  trans_g_unowned B -> trans_g_no_errno B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState,
     @PBC.transport_diginet_body_check_cg fx' rc B MT (transport_sigma TS_diginet_body_check)) ->
  transport_diginet_frame_build_cg (transport_sigma TS_diginet_frame_build).
End fb.
