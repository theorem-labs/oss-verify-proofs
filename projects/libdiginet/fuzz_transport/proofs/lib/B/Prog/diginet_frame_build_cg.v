(* diginet_frame_build_cg (image B): the ASan walk contract of diginet_frame_build (src/diginet_frame.c:93-127;
   plain contracts lib/Prog/diginet_frame_build_c.v and the wide lib/Prog/diginet_frame_build_w_c.v) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x8b818 = DgnTransportBAddr.v transportb_sigma TB_diginet_frame_build,
   size 1492, as STATEMENTS only (no proof). One of its callers, send_data, passes g_s.inflight_frame (a harness
   global) as out, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over
   G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B). Form: lib/A/Prog/diginet_frame_build_cg.v
   (the same definitions, premises, post and holds statement; what image B's code forces is listed at the end of this
   comment).

   The form (the G form, TransportGCg.v) and the changes are image A's (lib/A/Prog/diginet_frame_build_cg.v):
   - the holds statement takes trans_g_unowned and trans_g_no_errno (DgnTransportBCg.v; G_HARNESS_gx_ok /
     G_HARNESS_gx_noerrno give gx_ok / gx_noerrno, so the donor callee diginet_body_check is lifted by TransportGCg.v
     gx_call_cg through decode_cg_post_dcg), and trans_ro_rd_unowned and trans_rom_no_errno (as check_sent_frame_cg.v,
     desk_named_cg.v do): trans_src_ok's TRANS_RO_RD case keeps dst's, src's and the body's bytes across
     diginet_body_check only through acall_kept's image clause (DgnTransportBCg.v trans_src_ok_acall,
     trans_src_ok_acall_g take both facts).
   - out: DgnTransportBCg.v trans_out_ok (out in one of the caller's live side-stack frames, send_control; or in G
     with trans_sh_any, its two shadow facts at every AR state, send_data's g_s.inflight_frame; and decode_rd_ok),
     and the G-form write right transport_twr_ok_g at the call's sp - 96 (each byte an awr_byte of the caller's
     journal, or a byte of G).
   - dst 6, src 6 and the body: DgnTransportBCg.v trans_src_ok (a heap block; or, with decode_rd_ok, a side-stack
     frame, G with trans_sh_any, the machine stack, or TRANS_RO_RD with trans_sh_any) and decode_off_win at
     FRAME_FB_STK. Both callers pass g_s.desk_mac (s + 120) and g_s.cfg.host_mac (s + 0), the G case; send_control
     passes the body (0, 0) (trans_src_ok_null).
   - the body pointer: `body <> 0 \/ length bb = 0%nat`, the wide plain contract's premise (send_control passes
     a5 = a6 = 0 at 0x87078 / 0x8707c); diginet_body_check's statement asks the same.
   - mode: `-2 ^ 31 <= mode < 2 ^ 31` (a7 holds it sign-extended), the wide plain contract's premise: both callers
     pass s->cfg.sum_mode (a 4-byte signed load at s + 20), which nothing bounds. The code returns -1 for any other
     mode (0x8b894), so a0 is diginet_frame_build_w_c.v build_code_w and the bytes at out are build_out_w.
   - X gains TransportGCg.v gx_kept_ex G_HARNESS_B E: every byte of G outside E = [out, out + cap) is kept.
     acall_kept_g's image clause leaves G open (a G-form call may change a global), so without it a caller could not
     carry its world relation past the call. The walk has it: the code stores only into [out, out + len) and its own
     frame, the intrinsics keep every byte outside their destination and their stack, and diginet_body_check and
     diginet_sum16 keep every byte of G (gx_call_cg; a leaf's dleaf_post keeps every byte outside its stack window).

   The contract. The caller's G journal is the premise. a0 = out, a1 = cap (the length of the bytes oj at out),
   a2 = dst, a3 = src, a4 = hp, a5 = body, a6 = body_len (the length of the bytes bb at body), a7 = mode (an int,
   sign-extended). out, dst, src and hp are not 0; body is not 0 or bb is empty; hp is a multiple of 4 (image B's
   own premise, below). [out, out + cap) lies where trans_out_ok places it, the caller lets the call write it
   (transport_twr_ok_g at the call's sp - 96), and it holds oj. The 6 bytes dmac at dst, the 6 bytes smac at src and
   bb at body lie where trans_src_ok places them, outside this call's stack window. The 12 bytes at hp + 4
   (send_counter, ack_counter, retry, cmd, num_commands of a struct diginet_header) lie in a side-stack frame of the
   caller's state, visible, marked usable and outside this call's stack window. out's range is disjoint from the
   ranges it reads. Class 2 of the side stack has a free frame (for diginet_body_check). The function returns to ra
   with a0 = build_code_w bb cap mode (sign-extended), the callee-saved registers kept, the caller's G journal
   extended by no allocator event, no side-stack frame added, the bytes acall_kept_g G_HARNESS_B keeps (outside the
   stack window and outside E = [out, out + cap)), every byte of G outside E kept (gx_kept_ex), no meter charge, and
   the cap bytes at out = build_out_w dmac smac send ack retry cmd ncmds bb mode oj: build_frame then the old tail
   when the code is the frame length, oj unchanged when the code is negative.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 1492 code bytes are equal in both files), symbol
   diginet_frame_build, value 0x8b818, size 1492, 373 words:
     0x8b818  sp = sp - 96; ra at sp + 88, s0 .. s10 at sp + 80 .. sp + 0; no realignment, no frame pointer
              (s0 = out from 0x8b878); these 12 stores into its own frame are loaded back at 0x8bc60 - 0x8bc8c;
     0x8b84c  s8 = -1; out, dst, src or hp = 0 (0x8b850, 0x8b858, 0x8b860, 0x8b868) and body = 0 with body_len <> 0
              (0x8b87c - 0x8b888) return -1 (kept unreached by the premises); 1 < mode as a 64-bit unsigned value
              (0x8b894) returns -1 (build_code_w's -1); 1484 < body_len (0x8b89c, unsigned) returns -4 (0x8b8a0);
     0x8b8a8 - 0x8b8b0 the shadow base through the GOT word 0xa3cf0 (transport_cells rows 1-2) into s10;
     0x8b8bc  the call of diginet_body_check (0x8c0fc = transportb_sigma TB_diginet_body_check; a0 = body,
              a1 = body_len), return address 0x8b8c0; a result not 0 returns -10 (0x8b8c4);
     0x8b8cc - 0x8b8dc s9 = 30 + body_len, s8 = len = max 60 s9; 0x8b8e0 cap < len (unsigned) returns -5 (0x8b8e4);
     0x8b8f8  the call of __asan_memcpy (0x523ec = transportb_sigma TB___asan_memcpy) with (out, dst, 6), return
              address 0x8b8fc; 0x8b910 the same with (out + 6, src, 6), return address 0x8b914;
     0x8b91c - 0x8bc20 18 byte stores to out + 12 .. out + 29, each after the instrumented check of its shadow byte
              k at (a >> 3) + 0x7fff8000 (k = 0, or (a & 7) < k, goes on; else the error path): 0x88, 0x5f,
              (16 + body_len) >> 8, 16 + body_len, sum >> 8, sum, then send and ack big-endian (4-byte loads at
              0x8ba3c from hp + 4 and 0x8bae0 from hp + 8), retry big-endian (2-byte load at 0x8bb84 from hp + 12),
              cmd (1-byte load at 0x8bbe0 from hp + 14), num_commands (1-byte load at 0x8bc18 from hp + 15); each
              load after the instrumented check of its shadow byte (an n-byte load goes on when k = 0 or
              ((a & 7) + n - 1) < k);
     0x8b9b4 - 0x8b9d0 the sum: mode <> 0 gives sum = 0 (0x8b9b8 - 0x8b9c0); mode = 0 calls diginet_sum16
              (0x8afd8 = transportb_sigma TB_diginet_sum16; a0 = body, a1 = body_len) at 0x8b9cc, return address
              0x8b9d0, whose result its leaf statement gives as DgnSpec.lib_sum16 bb (build_frame's spec_sum bb by
              lib/Spec/DgnSpec.v lib_sum16_eq and spec_sum_eq); 0x8b9d0 a1 = the result shifted right by 8;
     0x8bc3c  the call of __asan_memcpy with (out + 30, body, body_len), return address 0x8bc40, skipped when
              body_len = 0 (0x8bc24);
     0x8bc58  the call of __asan_memset (0x52888 = transportb_sigma TB___asan_memset) with (out + 30 + body_len, 0,
              len - 30 - body_len), return address 0x8bc5c, skipped when 30 + body_len >= len (0x8bc40);
     0x8bc5c  a0 = the low 32 bits of s8, sign-extended; ra, s0 .. s10 loaded back, sp = sp + 96, return at 0x8bc94.
   UBSan checks (image B only): 22 branches to the trap word 0x8bc98:
     0x8ba14 after a0 = hp & 3 (0x8ba10, s3 = hp): hp is not 4-aligned (the uint32_t loads at hp + 4 and hp + 8),
       kept not taken by the premise hp mod 4 = 0;
     21 pointer-overflow checks of out + k: 0x8b900 (k = 6), 0x8b918 (12), 0x8b93c (13), 0x8b960 (14), 0x8b98c (15),
       0x8b9ac (16), 0x8b9ec (17), 0x8ba0c (18), 0x8ba50 (19), 0x8ba74 (20), 0x8ba98 (21), 0x8bab8 (22),
       0x8baf4 (23), 0x8bb18 (24), 0x8bb3c (25), 0x8bb5c (26), 0x8bb98 (27), 0x8bbb8 (28), 0x8bbf0 (29),
       0x8bc2c (30) and 0x8bc48 (30 + body_len, the memset's destination). Every one of them runs after the test
       cap < len returned -5 (0x8b8e0), so len <= cap with len = max 60 (30 + body_len), and trans_out_ok's
       decode_rd_ok gives out + cap <= 2 ^ 63: out + k <= out + len <= out + cap does not wrap and none is taken.
   Error paths: 23 calls: TB___asan_report_store1 (0x59824) x18 (0x8bca4, 0x8bcb0, 0x8bcc0, 0x8bccc, 0x8bcdc,
  0x8bcec, 0x8bd0c, 0x8bd1c, 0x8bd2c, 0x8bd38, 0x8bd58, 0x8bd68, 0x8bd78, 0x8bd84, 0x8bda4, 0x8bdb0, 0x8bdcc,
   0x8bde8: the stores to out + 12 .. out + 29), TB___asan_report_load4 (0x59644) x2 (0x8bd00, 0x8bd4c: hp + 4,
   hp + 8), TB___asan_report_load2 (0x595a4) x1 (0x8bd98: hp + 12), TB___asan_report_load1 (0x59504) x2 (0x8bdbc,
   0x8bdd8: hp + 14, hp + 15). Every one of them comes after the call of diginet_body_check, and each is kept
   unreached by the shadow of its range at that point: out, by trans_out_ok (a side-stack frame: its decode_rd_ok,
   the frames' shadow bytes kept by acall_kept; G: trans_sh_any at the state after the call; cap >= len >= 60 at the
   stores); the header range, a side-stack frame, as out. No abort.
   The intrinsics' own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at with the destination
   [out, ...) given by transport_twr_ok_g): range_addressable and shadow_hull_vis of [out, out + 12), [out + 30,
   out + 30 + body_len), [out + 30 + body_len, out + len), of dst's and src's 6 bytes and of bb, the same way; the
   ranges are disjoint (the disjointness premises) and outside the ESTACK below sp - 96 (decode_off_win,
   trans_out_ok, transport_twr_ok_g). diginet_sum16's leaf premises are the body's: p <> 0 when bb is not empty
   (the body premise; its statement asks it only then, diginet_sum16_c.v), the bytes at body (garr8), the range off
   its 16-byte frame (decode_off_win) and addressable when bb is not empty (trans_src_ok), with asan_cells from
   transport_cells.
   Writes into caller memory: only [out, out + len), by the three memcpy calls, the memset call and the 18 stores,
   and only when the result is len >= 0; no byte of out is written on a negative result (every negative return is
   before 0x8b8f8). E = [out, out + cap), and the post gives all cap bytes (build_out_w), so E costs the caller no
   fact. diginet_body_check writes no byte of its caller (its E is empty), and diginet_sum16 writes only its own
   frame.
   Reads across the call of diginet_body_check (0x8b8bc): dst's, src's, the header's and the body's bytes, oj's tail
   and the shadow of all of them are read after it. Its post (DgnTransportBCg.v decode_cg_post: YCbq.v acall_kept, E
   empty) keeps the bytes at or above alloc_ceiling outside its window (the machine stack), the image bytes outside
   the owned statics and errno (G: trans_g_unowned, trans_g_no_errno; TRANS_RO_RD: trans_ro_rd_unowned,
   trans_rom_no_errno), the caller's heap block bytes, and the bytes of the side-stack frames of the call state and
   their shadow bytes. Every shadow byte lies below alloc_ceiling; after the call one comes from AR at that state (the
   stack's zero range, the blocks' shadow, trans_sh_any for G and TRANS_RO_RD) or from the frames' clause
   (DgnTransportBCg.v trans_src_ok_kept, trans_src_ok_acall_g). The body is read again at the call of diginet_sum16
   (0x8b9cc), after the two memcpy calls into [out, out + 12) and the four stores to out + 12 .. out + 15: those
   write only out's bytes, which the disjointness premise keeps off the body, and the intrinsics keep every byte
   outside their destination and their stack.
   Stack: the frame (96), and below its sp the largest callee window: diginet_body_check's PBC.TRANS_BC_STK, ESTACK
   for __asan_memcpy and __asan_memset (YG0d.v aintrin_realizes) and for the leaf diginet_sum16, whose own frame is
   16 bytes (LeafCgKit.v ecall_pre).

   Image B against image A's code (lib/A/Prog/diginet_frame_build_cg.v, 0x8bcf8, 1344 bytes, 336 words): the same
   tests, stores and loads in the same order, with image B's addresses, and
   - the sum is an out-of-line call of diginet_sum16 (0x8b9cc), where image A inlines the loop (its 0x8be68 -
     0x8beb8) and makes mode = 0 with body_len = 0 skip it. Image B calls diginet_sum16 whenever mode = 0, also with
     body_len = 0, where it returns 0 at 0x8afe4 before it uses its pointer; so the holds statement takes
     diginet_sum16's leaf statement (lib/B/Prog/diginet_sum16_cg.v transport_diginet_sum16_cg, read at this unit's
     model by DgnTransportBCg.v transport_leaf_at), and the walk takes no new premise: diginet_sum16's p <> 0 is
     asked only when the body is not empty, which this statement's body premise gives;
   - ONE premise more, `hp mod 4 = 0` (image B's UBSan alignment check at 0x8ba10 - 0x8ba14; image A has none), which
     both callers give: send_control passes its class-2 side-stack frame + 128 and send_data its class-0 frame + 32,
     and a side-stack frame is 32-aligned (YG0d.v, AR's frames law: frame_addr ly cid pos mod 32 = 0);
   - 22 branches to the trap word 0x8bc98 (the UBSan build's alignment and pointer-overflow checks; image A has
     none), all ruled out above, 21 of them by premises image A's statement already has;
   - 23 error-path calls, not image A's 24: image A's third __asan_report_load1 (its 0x8beb4) guards the body byte
     of the inline sum loop, which in image B is diginet_sum16's own error path (0x8b04c);
   - image B's diginet_body_check has TRANS_BC_STK 4272 (image A's 4400), so FRAME_FB_STK is 4368 (image A's 4496).
   The statement is image A's but for `hp mod 4 = 0` and the sum16 leaf in the holds statement.

   The callers, each supplying every premise from its own walk (s = &g_s = 0x5df640 in both):
   - send_control at 0x87080 (return address 0x87084): a0 = out = its class-2 side-stack frame + 32 (0x87064; the
     frame from __asan_stack_malloc_2 at 0x86f4c, 160 bytes, description string 0x1d16b "2 32 60 4 f:99 128 16 5
     h:100"; out's 60 bytes are marked usable by its shadow stores 0x86fb4 - 0x87010: 7 shadow bytes 0 and one 4),
     a1 = 60 (0x8706c), a2 = s + 120 (g_s.desk_mac, 0x87068), a3 = s (g_s.cfg.host_mac, 0x87074), a4 = hp = the
     frame + 128 (0x87030; h's two shadow bytes 0 at 0x86fdc - 0x86fe0, its fields stored at 0x8703c - 0x87050),
     a5 = a6 = 0 (0x87078 / 0x8707c), a7 = s->cfg.sum_mode (the 4-byte signed load at s + 20, 0x87060);
   - send_data at 0x89efc (return address 0x89f00): a0 = out = s + 216 (g_s.inflight_frame, 0x89edc), a1 = 1514
     (0x89ee4), a2 = s + 120 (0x89ee0), a3 = s (0x89eec), a4 = hp = its class-0 side-stack frame + 32 (s8, 0x89e2c;
     the frame from __asan_stack_malloc_0 at 0x89df4, 64 bytes, description string 0x1d8a3 "1 32 16 5 h:390"; h's
     two shadow bytes 0 at 0x89e60 - 0x89e64; h's first 15 bytes zeroed by its __asan_memset at 0x89e90, then its
     fields stored, and num_commands at h + 15 by 0x89e98), a5 = its body argument (s6), a6 = its body_len argument
     (the word at s1 + 24, 0x89ef8), a7 = s->cfg.sum_mode (0x89ed8).
   For the g_s ranges (out = s + 216, 1514 bytes; dst, src) a caller proves trans_sh_any from g_s's zero-shadow row
   (DgnTransportBCg.v trans_gs_zshadow, trans_sh_any_zshadow; their aligned shadow groups lie inside g_s). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_body_check_cg diginet_sum16_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PBuildW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_build_w_c.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_body_check_cg.
Module LSum := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_sum16_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_frame_build's frame (`sp = sp - 96` at TB_diginet_frame_build; it does not realign sp), and the largest
   stack a callee uses below its sp: diginet_body_check's own window, ESTACK for __asan_memcpy, __asan_memset and
   the leaf diginet_sum16 (its own frame is 16 bytes). *)
Definition FRAME_FB_FRAME : Z := 96.
Definition FRAME_FB_STK : Z := FRAME_FB_FRAME + Z.max ESTACK PBC.TRANS_BC_STK.
(* No allocator event: it calls no allocator, and diginet_body_check and diginet_sum16 record none. *)
Definition FRAME_FB_EV : Z := 0.

(* The 12 bytes at hp + 4 the function reads (the plain contract's bytes_at (hp + 4)): send_counter and ack_counter
   (little-endian uint32), retry (little-endian uint16), cmd, num_commands. It does not read numbytes and sum (hp + 0
   .. hp + 3). *)
Definition frame_fb_hdr_cells (send ack retry cmd ncmds : Z) : list LC.cell :=
  [LC.C4 (w64 send); LC.C4 (w64 ack); LC.C2 (w64 retry); LC.C1 (b8 cmd); LC.C1 (b8 ncmds)].
Definition frame_fb_hdr_bytes (send ack retry cmd ncmds : Z) : list Z :=
  map bz (LC.cells_bytes (frame_fb_hdr_cells send ack retry cmd ncmds)).

Section fb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no allocator event, the written range
   [out, out + cap), no meter charge, and X: a0 = build_code_w bb cap mode, the cap bytes at out = build_out_w
   (lib/Prog/diginet_frame_build_w_c.v), and every byte of G outside [out, out + cap) kept (gx_kept_ex). *)
Definition frame_fb_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (out : Z) (dmac smac : list byte) (send ack retry cmd ncmds : Z) (bb : list byte)
    (mode : Z) (oj : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs FRAME_FB_STK FRAME_FB_EV 0
    (fun a => out <= a < out + Z.of_nat (length oj))
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (PBuildW.build_code_w bb (Z.of_nat (length oj)) mode) /\
       garr8 segs (mrestrict (w_H W2) mem2) out
         (map bz (PBuildW.build_out_w dmac smac send ack retry cmd ncmds bb mode oj)) /\
       gx_kept_ex segs TG.G_HARNESS_B (fun a => out <= a < out + Z.of_nat (length oj)) W memc W2 mem2).

(* The contract at entry address a, in the G-form caller-journal form (the wide plain contract's premises,
   lib/Prog/diginet_frame_build_w_c.v, with each range placed: out where trans_out_ok places it, writable by the
   call; dst, src and body where trans_src_ok places them; the header bytes in a side-stack frame of the caller's
   state). The function's write right on out is checked at its sp (spZ regs - FRAME_FB_FRAME), the sp of its three
   __asan_memcpy calls and its __asan_memset call. count_cid 2 (frames Sc) < fs_frames 2 is what diginet_body_check's
   statement asks. *)
Definition transport_diginet_frame_build_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (out dst src hp body mode send ack retry cmd ncmds : Z) (dmac smac bb oj : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 out -> YK11.getr regs 11 = w64 (Z.of_nat (length oj)) ->
    YK11.getr regs 12 = w64 dst -> YK11.getr regs 13 = w64 src ->
    YK11.getr regs 14 = w64 hp -> YK11.getr regs 15 = w64 body ->
    YK11.getr regs 16 = w64 (Z.of_nat (length bb)) -> YK11.getr regs 17 = w64 mode ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - FRAME_FB_STK -> spZ regs <= sp0 ->
    out <> 0 -> dst <> 0 -> src <> 0 -> hp <> 0 -> body <> 0 \/ length bb = 0%nat ->
    (* Image B's UBSan premise: 0x8ba10 a0 = hp & 3 (s3 = hp) / 0x8ba14 branch to the trap word 0x8bc98 on an hp
       that is not 4-aligned (the uint32_t loads at hp + 4 and hp + 8); image A's text lacks it. *)
    hp mod 4 = 0 ->
    -2 ^ 31 <= mode < 2 ^ 31 ->
    0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
    trans_out_ok B lyc Sc W memc out (Z.of_nat (length oj)) ->
    transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs - FRAME_FB_FRAME)
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
   gx_noerrno: the donor callee keeps G, gx_call_cg), and the contracts of __asan_memcpy, __asan_memset,
   diginet_body_check and the leaf diginet_sum16 give the contract at TB_diginet_frame_build. *)
Definition transport_diginet_frame_build_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  trans_g_unowned B -> trans_g_no_errno B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState,
     @PBC.transport_diginet_body_check_cg fx' rc B MT (transportb_sigma TB_diginet_body_check)) ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSum.transport_diginet_sum16_cg) fx') ->
  transport_diginet_frame_build_cg (transportb_sigma TB_diginet_frame_build).
End fb.
