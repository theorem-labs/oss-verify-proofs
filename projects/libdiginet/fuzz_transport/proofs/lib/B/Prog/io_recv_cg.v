(* io_recv_cg: image B's ASan walk contract of io_recv (fuzz/fuzz_transport.c:906-929; model lib/TModel/TCb.v
   io_recv_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x83368 = TImgB.v ti_io_recv timg_B (the twin's symbol
   io_recv, size 168; transportb_text + AF_io_recv in DgnTransportBList.v), as STATEMENTS only (no proof). It stores
   into g_rx_fail and g_rx_times, two harness globals, and calls m_rx, m_tick and __asan_memcpy, so it is a G-form
   caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v
   G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post
   (acall_kept_g over G_HARNESS_B). Image B's twin of lib/A/Prog/io_recv_cg.v; the differences are listed at the end
   of this comment.

   io_recv is not a direct call target and has no TB_ symbol: the program reaches it only through the session's
   recv pointer (struct diginet_session + 80, g_s.io.recv, which diginet_session_init copies from the 32 bytes of
   __const.LLVMFuzzerTestOneInput.io at 0xa39c0 = TRANS_IO, whose third word is 0x83368). The indirect call sites:
   diginet_session_poll 0x8acd4 and 0x8ad50. Each reads the pointer from the world (tw_read of S_io_recv; the model's
   call_recv, TSess.v, compares it with ti_io_recv timg_B) and applies this statement at that address.

   The contract. a1 = bp, a2 = cap (a0 = ctx and a3 = timeout_ms are not read, :908-909). The cap bytes at bp (the
   buffer) lie in a live side-stack frame of the caller (decode_in_fake), the caller lets the call write them
   (transport_twr_ok_g), they are visible and marked usable (decode_rd_ok), outside this call's stack window
   (decode_off_win) and outside G; 0 <= cap < 2 ^ 32. TF is the current heap frame (check_state_data_cg.v
   trans_tframe_at at this call's window IORECV_STK), and g_rx, when it is not 0, points into it (iorecv_rx_in). No
   byte the call may store is a byte of TF (iorecv_apart). The read-only bytes m_rx and its callees compare (HOST,
   SPEC_BCAST, SPEC_OUI, the two names) read as the image's (trans_rom_view_rd). The memory relates to the world Bw
   by image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and
   io_recv_m timg_B TF Bw cap = Some (Bw', r, got). The function returns to ra with a0 = r (-EIO = -5, 0, or the
   32-bit n sign-extended), the callee-saved registers kept, no allocator event and no meter charge, the caller's
   side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above
   alloc_ceiling outside the call's stack window [sp - IORECV_STK, sp), the image bytes outside G, the owned statics
   and errno, the caller's block and frame bytes outside iorecv_wr Bw bp cap), the world relation at Bw',
   g_fail_next Bw' <= 1, and the cap bytes X at bp with firstn (length got) X = got.

   The translation from the plain contract (lib/Prog/T/io_recv_c.v) is image A's: a1 = bp, a2 = cap
   kept; 0 <= cap kept and bounded (below); rw_cells m bp [CB cap J] and arg_blk sp FRAME bp cap -> decode_in_fake,
   transport_twr_ok_g, decode_rd_ok (__asan_memcpy's destination check), decode_off_win at IORECV_STK (off_window)
   and the range apart from G (off_world); the contents J are dropped (the code reads no byte of the buffer);
   io_recv_sep TF bp cap -> iorecv_apart, whose written range holds the buffer; tframe_at -> trans_tframe_at at
   IORECV_STK, and its off_world clause -> two facts (trans_src_ok alone admits a range of G, so trans_tframe_at
   gives neither): iorecv_apart, no byte the call stores is a byte of TF, and trans_tf_off_g (check_state_data_cg.v),
   no byte of TF is a byte of G. trans_tf_off_g carries TF's bytes across m_rx (call at 0x833d0, n <> 0), which
   writes G, to the copy at 0x833f0, which reads n of them: m_rx's acall_kept_g keeps the image bytes outside G
   only, and its X pins G only to the model world, so it carries no byte of a TF inside G (on the m_tick path, call
   at 0x833e0, n = 0 and the copy reads no byte of TF); tframe_ok TF is dropped (where m_rx needs it, n <> 0,
   trans_src_ok bounds TF's end below 2 ^ 63: DgnTransportBCg.v trans_src_ok_rd); wmem -> tw_at; g_fail_next B <= 1
   kept as a premise and the post's g_fail_next B' <= 1 kept in X (the code neither reads nor writes g_fail_next, and
   m_rx_m / m_tick_m store no byte of it); timg_plain -> timg_B; the 16-aligned sp, stk, lo + FRAME <= sp and
   w_off_stack -> the journal's window premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv ->
   transport_cg_post (the journal at the return, acall_kept_g over iorecv_wr); wmem -> X's tw_at; rw_cells m' bp
   [CB cap X] /\ firstn (length got) X = got -> X's garr8 of the cap bytes at bp with the same firstn.
   The premises the plain contract does not have (image A's, for the same reasons):
   - cap < 2 ^ 32: __asan_memcpy's contract (YG0d.v aintrin_realizes) asks 0 <= n < 2 ^ 32 of its length, and the
     code copies n = min (g_rx_len, cap) <= cap bytes. Both callers pass 1514.
   - iorecv_rx_in TF Bw: when g_rx Bw is not 0, TCb.v frame_from TF (g_rx Bw) is not None. The code calls
     __asan_memcpy (buf, g_rx, n) on the m_tick path too, where n = 0 (0x833f0), and aintrin_realizes asks of the
     source, for every n, 0 <= x, x + n <= 2 ^ 63 and amem_range x n. For n <> 0 the model places g_rx in TF
     (frame_read F (g_rx B2) n = Some _); for n = 0 frame_read answers Some [] without a test, so the premise places
     g_rx in TF's range, where trans_tframe_at's trans_src_ok gives the three bounds for every length of TF, the empty
     one included. Its source is the harness: receive (fuzz_transport.c:1012) stores g_rx = frame, its heap block and
     the tf_addr of its TF, before diginet_session_poll and NULL after (:1017), and LLVMFuzzerTestOneInput stores NULL
     at :1158; these are the program's only stores of g_rx, so no function that runs inside diginet_session_poll
     stores a byte of it. diginet_session_poll carries it on its own Bw to both of its calls; receive's walk
     discharges it by TCb.v frame_from_base. Like the run invariants the callers carry (diginet_session_rx_cg.v,
     diginet_session_poll_cg.v) it is a premise per call.
   - trans_rom_view_rd W memc: m_rx's premise, taken at io_recv's entry memory. It still holds at the call at
     0x833d0: before it io_recv stores only g_rx_times (.bss, a byte of G) and its own frame, and no byte of
     TRANS_RO_RD (the read-only image and RELRO) is among them.
   - decode_in_fake and the buffer apart from G (above): the post's acall_kept_g keeps every byte at or above
     alloc_ceiling outside the call's window, and the world relation fixes every byte of G, so the bytes the copy
     writes must lie in a side-stack frame (below alloc_ceiling) and outside G: diginet_session_poll's buf, at offset
     32 of its class-5 frame (below).
   Run invariants: none carried and none needed. m_rx_cg.v and m_tick_cg.v carry none of the five run invariants, and
   io_recv's own code reads only g_rx_fail, g_rx, g_rx_times and g_rx_len at constant
   addresses inside their payloads; the copy's destination lies in the buffer (n <= cap) and, for n <> 0, its source
   in TF (the model).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 168 code bytes are equal in both files), 42
   words:
     0x83368 - 0x83378 sp = sp - 32; ra, s0, s1, s2 at sp + 24, sp + 16, sp + 8, sp + 0, loaded back at 0x833f8 -
                      0x83404 (sp = sp + 32 at 0x83408, return at 0x8340c). No side-stack frame, no frame pointer.
     0x8337c - 0x83384 a3 = the 4-byte signed load of g_rx_fail (0x5f2c80 = TB_g_rx_fail); 0 goes to 0x83394.
     0x83388 - 0x83390 the 4-byte store of 0 at g_rx_fail; s1 = -5 (-EIO); to 0x833f4 (:910-913).
     0x83394 - 0x8339c s2 = 0x5df394 (kept for the load again at 0x833e4); a0 = the 8-byte load of g_rx (0x5df620 =
                      TB_g_rx, s2 + 0x28c); 0 goes to 0x833d8 (:914-915).
     0x833a0          s0 = a1 (bp).
     0x833a4 - 0x833ac a3 = the 4-byte signed load of g_rx_times (0x5f2ca0 = TB_g_rx_times); 0 goes to 0x833d8.
     0x833b0 - 0x833bc s1 = the 8-byte load of g_rx_len (0x5f2cc0 = TB_g_rx_len); a3 = a3 - 1 (64-bit), its low 32
                      bits stored at g_rx_times (:916). No UBSan check guards the decrement.
     0x833c0 - 0x833c4 g_rx_len < cap (unsigned) keeps s1 = g_rx_len; else s1 = cap (a2): n = min (g_rx_len, cap)
                      (:917).
     0x833c8          n = 0 goes to 0x833e0.
     0x833cc - 0x833d4 a1 = n (a0 = g_rx since 0x83398); call of m_rx (0x84c1c = transportb_sigma TB_m_rx) at 0x833d0,
                      return address 0x833d4; to 0x833e4 (:923-924).
     0x833d8 - 0x833dc s1 = 0; to 0x833f4.
     0x833e0          call of m_tick (0x8383c = transportb_sigma TB_m_tick) at 0x833e0, return address 0x833e4 (:926).
     0x833e4 - 0x833f0 a1 = the 8-byte load of g_rx again (through s2); a0 = s0 (bp); a2 = s1 (n); call of
                      checked_memcpy (__asan_memcpy, 0x523ec = transportb_sigma TB___asan_memcpy) at 0x833f0, return
                      address 0x833f4 (:927), for n = 0 too.
     0x833f4 - 0x8340c a0 = s1 sign-extended from bit 31 (`sext.w`: -5, 0 or the 32-bit n, :928); ra, s0 .. s2
                      loaded back, sp = sp + 32, return. a1 .. a7 at the return are not stated.
   No tail jump: every call is a jal with link, every j is inside the function, and the function ends with ret.
   The model and the code: every test is io_recv_m's, read through tw_at: truth (g_rx_fail Bw) (the code tests the
   32-bit value against 0), g_rx =? 0 (64-bit), g_rx_times =? 0 (32-bit), int_dec (the code wraps at INT_MIN, where
   the model is None), and g_rx_len B1 <? cap, which the unsigned compare decides for 0 <= g_rx_len < 2 ^ 64 (an
   8-byte unsigned read) and 0 <= cap < 2 ^ 32; the stores are set_g_rx_fail 0 and set_g_rx_times t (put 4 of the low
   32 bits). m_rx's frame is frame_from TF (g_rx B1), with g_rx B1 = g_rx Bw (B1 differs from Bw only at g_rx_times,
   world offsets 0xfde4 .. 0xfde7; g_rx is 0xfdf0 .. 0xfdf7); the copy reads TF at g_rx B2, the value the load at
   0x833e4 reads (m_rx and m_tick store no byte of g_rx); r = bv_swrap 32 n. The model's None cases: int_dec at
   INT_MIN, m_rx's and m_tick's, and frame_read outside TF.
   The trap: none of its own (no branch to a trap word, no call of __asan_handle_no_return or abort).
   Error paths: none. The code makes no instrumented check (it loads no shadow byte: each of its accesses is at a
   constant address of a global or in its own frame) and calls no error path.
   Writes: its own frame (the four saved registers); g_rx_fail and g_rx_times (bytes of G); m_rx's (mrx_wr) or
   m_tick's (mtick_wr B1) stores; the copy's n bytes at bp, inside the buffer. iorecv_wr names them.
   Callee texts assumed (pc order), each a premise of the holds statement:
     m_rx as m_rx_cg.v transport_m_rx_cg at transportb_sigma TB_m_rx (call at 0x833d0; a G-form callee composed in the
       same G journal, no gx_call_cg). Its premises at the call: the journal at the call state; ra = 0x833d4 (ret_ok,
       4096 <= ra); gp, tp as at entry; a0 = g_rx Bw = tf_addr fr, where frame_from TF (g_rx B1) = Some fr (TF = Some
       f, off = g_rx Bw - tf_addr f with 0 <= off <= length (tf_bytes f): frame_read's Some for n <> 0, through
       g_rx B2 = g_rx B1); a1 = n; sp - 32 16-aligned, sp0 - STK <= sp - 32 - MRX_STK (IORECV_STK = 32 + MRX_STK),
       sp - 32 <= sp0; trans_tframe_at (Some fr) at MRX_STK: 0 < g_rx Bw, garr8 of skipn off (tf_bytes f) at g_rx
       (part of TF's garr8, kept: the store at g_rx_times is not a byte of TF by iorecv_apart, the saves lie in the
       window), trans_src_ok and decode_off_win of the sub-range (DgnTransportBCg.v trans_src_ok_sub,
       decode_off_win_sub; MRX_STK = IORECV_STK - 32), read at the call memory by trans_src_ok_view; tf_addr fr + n <
       2 ^ 64: g_rx + n <= tf_addr f + length (tf_bytes f) (frame_read's Some) < 2 ^ 63 (trans_src_ok_rd); mrx_apart
       fr: mrx_wr lies in iorecv_wr and fr's range in TF's (iorecv_apart); trans_rom_view_rd: the entry premise, kept
       (above); tw_at at B1 (the store at 0x833bc, tw_write); m_rx_m timg_B (Some fr) B1 n = Some (B2, _): io_recv_m;
       st_nev S + k + MRX_EV <= EV_MAX: MRX_EV = 0.
     m_tick as m_tick_cg.v transport_m_tick_cg at transportb_sigma TB_m_tick (call at 0x833e0; G-form, the same
       journal): ra = 0x833e4; sp - 32 (MTICK_STK = MSET_STK = 16 <= MRX_STK); tw_at at B1 = iorecv_w1 Bw;
       m_tick_m B1 = Some (B2, tt): io_recv_m; MTICK_EV = 0.
     __asan_memcpy as aintrin_realizes .. OCpy (transportb_sigma TB___asan_memcpy), call at 0x833f0, through
       TransportGCg.v gx_intrin_at (gx_ok; gx_rw by TransportGRwB.v): d = bp, x = g_rx B2, n with 0 <= n <= cap <
       2 ^ 32. The destination [bp, bp + n) inside the buffer: d + n <= 2 ^ 63 and amem_range from decode_rd_ok;
       dest_ok from transport_twr_ok_g (the bytes are outside [sp - 32 - ESTACK, sp - 32) by decode_off_win at
       IORECV_STK); range_addressable and shadow_hull_vis from decode_rd_ok, kept through the callee's acall_kept_g
       (its written range lies in G, the buffer outside G; the frame clause keeps the buffer's bytes and the frames'
       shadow bytes: DgnTransportBCg.v decode_rd_ok_fake_kept). The source, n <> 0: [g_rx, g_rx + n) inside TF's
       range (frame_read), TF's bytes and trans_src_ok carried across the callee (DgnTransportBCg.v
       trans_src_ok_kept over the clauses of its acall_kept_g, with trans_ro_rd_unowned and trans_rom_no_errno: a
       heap block, a frame, the machine stack (outside the callee's window by decode_off_win at IORECV_STK) or a
       TRANS_RO_RD range, outside the callee's written range by iorecv_apart; not a range of G, by trans_tf_off_g,
       since acall_kept_g's image clause leaves G out and the callee's X ties G to the model world only) gives src_ok,
       amem_range, range_addressable and shadow_hull_vis; apart from [bp, bp + n) (the buffer is in iorecv_wr:
       iorecv_apart). The source, n = 0: 0 <= g_rx and g_rx <= 2 ^ 63 and amem_range g_rx 0 from iorecv_rx_in and
       trans_src_ok of TF, for every length of TF; src_ok, range_addressable and the overlap test hold for the empty
       range.
   A G-form callee keeps the caller's block and frame bytes outside its written range, the bytes at or above
   alloc_ceiling outside its window and the image bytes outside G (acall_kept_g), and ties the bytes of G only to the
   model world of its post, so TF's bytes read after it (the copy's source) are the entry's: TF lies outside the
   written range (iorecv_apart) and outside G (trans_tf_off_g).
   Stack: 32 bytes of its own; every call runs from sp - 32, and the largest callee window is m_rx's MRX_STK (m_tick's
   MTICK_STK = 16, __asan_memcpy's ESTACK = 4096, MRX_STK = 112 + HOFF_STK = 192 + 2 * ESTACK): IORECV_STK =
   32 + MRX_STK.

   The callers (each through g_s.io.recv, the 8-byte load at g_s + 80 through s6 = s + 80, by jalr):
   diginet_session_poll 0x8acd4 (return 0x8acd8; the pointer loaded at 0x8acc0) and 0x8ad50 (return 0x8ad54; loaded at
   0x8ad40): a0 = s->io.ctx (the 8-byte load at g_s + 64, 0x8acbc / 0x8ad3c), a1 = s9 = s2 + 32 (0x8acc4; its buf,
   offset 32 of the class-5 side-stack frame __asan_stack_malloc_5 returns at 0x8ab08 for a0 = 0x6a0, description
   string 0x1d8b3 "1 32 1514 7 buf:507"; before the calls __asan_set_shadow_00 at 0x8abe4 marks 189 shadow bytes from
   the buf's first usable and the store at 0x8abec writes the shadow byte 2: 1514 bytes), a2 = 1514, a3 = the timeout
   (sign-extended at 0x8acc8) or 0 (0x8ad4c). Each supplies the G journal of its own walk, the world relation,
   g_fail_next, the model call (call_recv's branch of diginet_session_poll_m), the buffer's facts, trans_tframe_at,
   iorecv_apart and trans_tf_off_g of TF (the last two from its plain tframe_at's off_world clause), iorecv_rx_in and
   trans_rom_view_rd.

   Against image A's statement (lib/A/Prog/io_recv_cg.v): the same definitions, premises, post and holds statement,
   at image B's names (TMAP_B, timg_B, TB_g_rx_fail, TB_g_rx, TB_g_rx_times, TB_g_rx_len, transportb_sigma,
   G_HARNESS_B, lib/B/Prog/DgnTransportBCg.v, lib/B/Prog/m_set_cg.v twb_fld). Image B's code is image A's
   instruction for instruction (the same 42 words but the auipc offsets and the call targets); UBSan adds no check to
   it (the decrement of g_rx_times at 0x833b8 wraps, as image A's, where the model is None). What differs is below
   the calls: image B's m_rx calls spec_read_frame and host_offset (its window MRX_STK = 112 + HOFF_STK, image A's
   144 + DNAMED_STK) and image B's m_tick tail-jumps to m_set (MTICK_STK = MSET_STK); IORECV_STK = 32 + MRX_STK
   holds on both images. No premise is added or dropped. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBList.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_rx_cg m_tick_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* io_recv's entry: the value the model's call_recv tests the session's recv pointer against, and the listing's
   offset of io_recv from the entry function. *)
Lemma io_recv_at :
  TI.ti_io_recv timg_B = 0x83368 /\ TI.ti_io_recv timg_B = transportb_text + DgnTransportBList.AF_io_recv.
Proof. split; reflexivity. Qed.

(* io_recv's frame (`sp = sp - 32` at its entry; no realignment). Every call runs from sp - 32: m_rx (MRX_STK),
   m_tick (MTICK_STK), __asan_memcpy (ESTACK); m_rx's is the largest. *)
Definition IORECV_FRAME : Z := 32.
Definition IORECV_STK : Z := IORECV_FRAME + Z.max (Z.max MRX_STK MTICK_STK) ESTACK.
Lemma iorecv_stk_eq : IORECV_STK = IORECV_FRAME + MRX_STK.
Proof. reflexivity. Qed.
(* No allocator event: io_recv calls neither malloc nor free and takes no side-stack frame, and m_rx and m_tick
   record none. *)
Definition IORECV_EV : Z := 0.
Lemma iorecv_ev_eq : MRX_EV = 0 /\ MTICK_EV = 0.
Proof. split; reflexivity. Qed.
(* The image-B addresses of the four globals the code reads. *)
Lemma iorecv_globals_at :
  TB_g_rx_fail = 0x5f2c80 /\ TB_g_rx = 0x5df620 /\ TB_g_rx_times = 0x5f2ca0 /\ TB_g_rx_len = 0x5f2cc0.
Proof. repeat split; reflexivity. Qed.

(* The world after the store at 0x833bc on the paths that reach m_rx or m_tick (io_recv_m's B1 with
   t = g_rx_times Bw - 1). *)
Definition iorecv_w1 (Bw : list byte) : list byte := TW.set_g_rx_times Bw (TW.g_rx_times Bw - 1).

(* The bytes some path of the call stores outside its own frame: g_rx_fail, g_rx_times, m_rx's (m_rx_cg.v mrx_wr),
   m_tick's at the world it is handed (m_tick_cg.v mtick_wr (iorecv_w1 Bw)), and the buffer (the copy writes its
   first n bytes, n <= cap). *)
Definition iorecv_wr (Bw : list byte) (bp cap a : Z) : Prop :=
  twb_fld TW.OFF_g_rx_fail TB_g_rx_fail TW.OFF_g_rx_fail TW.SZ_g_rx_fail a \/
  twb_fld TW.OFF_g_rx_times TB_g_rx_times TW.OFF_g_rx_times TW.SZ_g_rx_times a \/
  mrx_wr a \/
  mtick_wr (iorecv_w1 Bw) a \/
  bp <= a < bp + cap.

(* No byte the call may store is a byte of the current heap frame TF: m_rx reads TF after the store of g_rx_times,
   the copy reads it after m_rx's or m_tick's stores, and the copy's source must lie apart from its destination. The
   plain contract's tframe_at puts TF off the world, and its io_recv_sep puts the buffer apart from TF's block. *)
Definition iorecv_apart (TF : option TI.tframe) (Bw : list byte) (bp cap : Z) : Prop :=
  forall x, iorecv_wr Bw bp cap x ->
    forall fr, TF = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* g_rx, when it is not 0, points into the current heap frame TF (its offset in [0, length]): the copy's source
   pointer, which the model leaves free when n = 0. *)
Definition iorecv_rx_in (TF : option TI.tframe) (Bw : list byte) : Prop :=
  TW.g_rx Bw <> 0 -> TC.frame_from TF (TW.g_rx Bw) <> None.

Section iorecv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   iorecv_wr Bw bp cap, no meter charge, and X: a0 = r (sign-extended), the world relation at the model's world Bw',
   g_fail_next Bw' <= 1, and the cap bytes at bp agreeing with got on its length. *)
Definition transport_io_recv_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (bp cap : Z) (Bw Bw' : list byte) (r : Z) (got : list byte)
    : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs IORECV_STK IORECV_EV 0 (iorecv_wr Bw bp cap)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 r /\
       tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1 /\
       (exists X : list byte, length X = Z.to_nat cap /\
          garr8 segs (mrestrict (w_H W2) mem2) bp (TW.zs X) /\
          firstn (length got) X = got)).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_io_recv_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bp cap r : Z) (got : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 11 = w64 bp -> YK11.getr regs 12 = w64 cap ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - IORECV_STK -> spZ regs <= sp0 ->
    0 <= cap < 2 ^ 32 ->
    decode_in_fake lyc Sc bp cap ->
    transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs) bp cap ->
    decode_rd_ok W memc bp cap ->
    decode_off_win regs IORECV_STK bp cap ->
    (forall x, bp <= x < bp + cap -> ~ inG TG.G_HARNESS_B x) ->
    trans_tframe_at B lyc Sc W memc regs IORECV_STK TF ->
    trans_tf_off_g TF ->
    iorecv_apart TF Bw bp cap ->
    iorecv_rx_in TF Bw ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TC.io_recv_m timg_B TF Bw cap = Some (Bw', r, got) ->
    st_nev S + k + IORECV_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_io_recv_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bp cap Bw Bw' r got).

(* The statement the walk will prove: the runtime cells (every statement of the unit takes them; io_recv's own code
   reads none), the TRANS_RO_RD bytes outside the owned statics and errno (they carry the bytes and the trans_src_ok
   of a read-only TF across m_rx and m_tick: acall_kept_g's image clause with DgnTransportBCg.v trans_ro_rd_scoped,
   then trans_src_ok_kept), the allocator and meter laws, G inside the image and outside the allocator's statics,
   and the contracts of m_rx, m_tick and __asan_memcpy (pc order of their calls) give the contract at io_recv's
   entry. *)
Definition transport_io_recv_cg_holds_stmt : Prop :=
  transport_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_m_rx_cg fx' rc B MT (transportb_sigma TB_m_rx)) ->
  (forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  transport_io_recv_cg (TI.ti_io_recv timg_B).
End iorecv.
