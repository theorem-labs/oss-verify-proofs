(* m_rx_cg: the ASan walk contract of m_rx (fuzz/fuzz_transport.c:280-375, spec_read_frame and host_offset inlined;
   model lib/TModel/TCb.v m_rx_m) on fuzz_transport.asan (e89be137db17) at 0x8488c = transport_sigma TS_m_rx, size
   1716, as STATEMENTS only (no proof). It stores into M and OW, two harness globals, and calls m_lost, desk_named,
   m_wake, m_maybe_online, m_tick, the bcmp wrapper and __asan_memcpy, so it is a G-form caller-journal walk: the
   caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0,
   OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS).

   The contract. a0 = tf_addr fr, a1 = n: fr is the received frame (the bytes tf_bytes fr at tf_addr fr; TImg.v tframe),
   read as n bytes. The frame is given in check_state_data_cg.v trans_tframe_at form at this call's window MRX_STK
   (0 < tf_addr fr, garr8 of its bytes, trans_src_ok and decode_off_win of [tf_addr fr, + length tf_bytes)), it ends
   below 2 ^ 64 at n (tf_addr fr + n < 2 ^ 64), and no byte the call may store is a byte of it (mrx_apart). The
   read-only bytes the code and desk_named compare (HOST, SPEC_BCAST, SPEC_OUI, the two names) read as the image's
   (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v
   TMAP_A, read through aview), and m_rx_m timg_A (Some fr) Bw n = Some (Bw', r). The function returns to ra with
   a0 = r (0 or 1), the callee-saved registers kept, no allocator event and no meter charge, the caller's side-stack
   frames and blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - MRX_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block
   and frame bytes outside mrx_wr), and the world relation at Bw'.
   This is what the plain contract (lib/Prog/T/m_rx_c.v) says: a0 = r; wmem rsegs m' B' with B' the model's world;
   munch of the frame and the world only. Its premises become: a0 / a1 -> getr 10 / 11;
   tframe_at m sp m_rx_FRAME (Some fr) -> trans_tframe_at at MRX_STK (bytes_at -> garr8, the heap block -> trans_src_ok,
   off_window -> decode_off_win; its off_world clause -> mrx_apart: the frame apart from every byte the call stores);
   tf_addr fr + n < 2 ^ 64 kept as it is (the plain contract keeps it equal to the ubsan twin's; here it gives the
   frame addresses the code forms without wrap); wmem -> tw_at; timg_plain -> timg_A; the stack premises -> the
   journal's window premises; mem_inv dropped. The premise the plain contract does not have: trans_rom_view_rd W memc
   (the plain build reads HOST, SPEC_BCAST, SPEC_OUI through rsegs' read-only segment; here they are TRANS_RO_RD bytes
   read through the journal's view, as check_sent_frame_cg.v and desk_named_cg.v take it).
   Run invariants: none carried and none needed. The callees' contracts (m_lost_cg.v, desk_named_cg.v, m_wake_cg.v,
   m_maybe_online_cg.v, m_tick_cg.v) carry none of the four run invariants (check_inflight_retry,
   check_latest_queue, check_state_data, check_latest_sent), and m_rx's own code reads past no global's payload: every
   instrumented access and every range handed to the bcmp wrapper or __asan_memcpy is either a frame byte below
   tf_addr fr + n (n <= length tf_bytes: the model), a read-only constant (HOST, SPEC_BCAST, SPEC_OUI), at a constant
   offset of M or OW, or at OW.dn[k] with 0 <= k <= 1 (the code's test k <= 1 and the model's None at k < 0); the
   memcpy and bcmp lengths are constants (6 or 3).

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1716 code bytes are equal in both files), 429 words. fa = tf_addr fr.
     0x8488c - 0x848c0 sp = sp - 144; ra, s0 .. s11 at sp + 136 .. sp + 40, loaded back at 0x8496c - 0x8499c (sp = sp +
                      144 at 0x849a0, return at 0x849a4). No side-stack frame, no frame pointer. Spill slots sp + 8 .. sp +
                      32 (stores at 0x84a94 - 0x84a9c of the frame bytes fa + 25, fa + 24, fa + 21, at 0x84b08 of fa + 18;
                      loads back at 0x84c1c, 0x84c24, 0x84c88, 0x84ce0).
     0x848c4 - 0x848c8 n < 30 (unsigned) goes to 0x84968: a0 = 0, return (spec_read_frame's SPEC_E_SHORT).
     0x848cc - 0x848d8 s0 = fa; s2 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the
                      shadow base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an m-byte access
                      (m < 8), ((a & 7) + m - 1) < k (signed) goes on; else the error path; an 8-byte store goes on only
                      at k = 0. No check guards an access at a constant address of M, OW, g_now or g_cfg.
     0x848dc - 0x84964 the checks of the 1-byte loads at fa + 12 .. fa + 15 and the loads: ethertype (fa + 12, fa + 13,
                      big-endian) <> 0x885f, numbytes (fa + 14, fa + 15, big-endian) = s4 < 16, or n - 14 < numbytes
                      (unsigned) goes to 0x84968 (return 0).
     0x849a8 - 0x84ab8 the checks of the 1-byte loads at fa + 18 .. fa + 28 and the loads (send fa + 18 .. 21, ack
                      fa + 22 .. 25, retry fa + 26 .. 27, all big-endian; s9 = cmd = the byte at fa + 28).
     0x84abc - 0x84b04 s1 = fa + 6 (src). bcmp (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp) at 0x84ad0
                      with (fa + 6, HOST = 0x21040 = TRANS_HOST, 6): 0 returns 0 (:285); bcmp at 0x84ae8 with (fa, HOST,
                      6): 0 goes to 0x84b08; else bcmp at 0x84b00 with (fa, SPEC_BCAST = 0x21080 = TRANS_SPEC_BCAST, 6):
                      not 0 returns 0 (:286-287).
     0x84b08 - 0x84b30 s3 = &M = 0x5df160 (TA_M); M.desk_known (the 4-byte load at M + 0) <> 0: bcmp at 0x84b28 with
                      (fa + 6, M + 4 (M.desk), 6), not 0 returns 0 (:288-290); 0 goes to 0x84b70.
     0x84b34 - 0x84b6c (no desk known) cmd & 0xfe <> 0xe0 returns 0 (:292-293); bcmp at 0x84b50 with (fa + 6,
                      SPEC_OUI = 0x210a0 = TRANS_SPEC_OUI, 3): not 0 returns 0 (:294-295); __asan_memcpy (0x523b0 =
                      transport_sigma TS___asan_memcpy, checked_memcpy) at 0x84b64, return address 0x84b68, with (M + 4,
                      fa + 6, 6): M.desk = src; the 4-byte store of 1 at M + 0 (M.desk_known, :296-297).
     0x84b70 - 0x84b78 a5 = M.state (M + 12); 3 (S_CLOSED) returns 0 (:299-300).
     0x84b7c - 0x84b90 a0 = the 8-byte load of g_now (0x5df100); s0 = fa + 30 (f.body); s4 = numbytes - 16 (body_len);
                      the 8-byte store of g_now at M + 32 (M.last_rx, :301).
     0x84b94 - 0x84bb8 the switch on cmd (:302): cmd < 0xe0 goes to 0x84bf8; cmd - 0xe0 >= 2 goes to 0x84c68; e0 / e1
                      with body_len < 33 (SPEC_ANN_MIN) goes to 0x84e1c (:305-306); s7 = M.state; s4 = -1; cmd <> 0xe1
                      goes to 0x84da8.
     0x84bbc - 0x84bf4 host_offset (:256-262, e1 only): s1 = HOST, s2 = fa + 30 + i (the shadow base in s2 is not used
                      again on this path); for i = 0 .. 9 bcmp at 0x84bdc with (fa + 30 + i, HOST, 6); 0 gives s4 = i
                      (0x84da4); ten unequal leave s4 = -1. Then 0x84da8.
     0x84bf8 - 0x84c64 cmd = 0 (SPEC_CMD_DATA) goes to 0x84c88; cmd <> 0xa0 (SPEC_CMD_ACK) goes to 0x84e1c. ACK
                      (:332-341): M.fly.on (M + 96) = 0 or ack <> M.fly.counter (M + 104) goes to 0x84e1c; a2 = &OW =
                      0x5f3060 (TA_OW); the 4-byte stores of OW.acked + 1 at OW + 216, of ack at OW + 224
                      (acked_counter), of M.fly.retries (M + 108) at OW + 228 (acked_retry), of 0 at M + 96 (fly.on);
                      M.state <> 1 (S_WAKING) goes to 0x84e1c; else the 4-byte store of 1 at M + 16 (e2_acked) and to
                      0x84e18.
     0x84c68 - 0x84c84 cmd <> 0xe3 goes to 0x84e1c; e3 (:366-368): M.state - 1 > 1 (unsigned) goes to 0x84e1c; a0 = 7
                      (R_DESK_DISCONNECT); call of m_lost (0x85004) at 0x84c80, return address 0x84c84; to 0x84e1c.
     0x84c88 - 0x84d9c DATA (:344-364): a2 = &OW; the 4-byte stores of OW.acks + 1 at OW + 204 and of 0 at M + 88
                      (fail); retry <> 0: the 8-byte store of g_cfg.backoff_ms (the 4-byte unsigned load at 0x5df0a4) *
                      1000 + g_now at M + 56 (backoff_until); M.desk_counter_valid (M + 76) <> 0, retry <> 0 and send =
                      M.desk_counter (M + 80) goes to 0x84e1c; the 4-byte stores of 1 at M + 76 and of send at M + 80;
                      body_len = 1: the check of the 1-byte load at fa + 30 and the load; 0 goes to 0x84e1c; k = OW.ndata
                      (the 4-byte signed load at OW + 220); 1 < k (signed) goes to 0x84d98; else for x = OW + 256 +
                      24 k: the checks and the 8-byte store of fa + 30 at x (OW.dn[k].body), the 8-byte store of
                      body_len at x + 8 (len), the 4-byte store of send at x + 16 (counter), the 2-byte store of retry at
                      x + 20 (retry); 0x84d98: the 4-byte store of k + 1 at OW + 220 (ndata); to 0x84e1c.
     0x84da8 - 0x84dd0 e0 / e1 (:307-311): s1 = &OW; the 4-byte stores of OW.desk + 1 at OW + 208 and of s4 at OW + 232
                      (desk_off); a0 = fa + 30; call of desk_named (0x84f40) at 0x84dc4, return address 0x84dc8; the
                      8-byte stores of its result at OW + 240 (desk_p) and of fa + 30 at OW + 248 (desk_body).
     0x84dd4 - 0x84e04 cmd = 0xe0 (:312-318): the 4-byte store of 0 at M + 24 (foreign); the old M.state = 2
                      (S_ONLINE): a0 = 3 (R_DESK_OFFLINE), call of m_lost at 0x84de8, return address 0x84dec;
                      M.state (M + 12) <> 0 or g_cfg.auto_wake (the 4-byte load at 0x5df090) = 0 goes to 0x84e1c; else
                      call of m_wake (0x83d00) at 0x84e00, return address 0x84e04 (its a0 not used); to 0x84e1c.
     0x84e08 - 0x84e18 cmd = 0xe1, s4 >= 0 (:319-322): the 4-byte stores of 1 at M + 20 (e1_us) and of 0 at M + 24
                      (foreign); call of m_maybe_online (0x850f0) at 0x84e18, return address 0x84e1c.
     0x84e28 - 0x84e48 cmd = 0xe1, s4 < 0 (:324-328): the 4-byte stores of 1 at M + 24 (foreign) and of OW.foreign + 1 at
                      OW + 212; the old M.state - 1 > 1 (unsigned) goes to 0x84e1c; else a0 = 5 (R_FOREIGN) and to the
                      call of m_lost at 0x84c80.
     0x84e1c - 0x84e24 call of m_tick (0x83c34) at 0x84e1c from sp - 144, return address 0x84e20 (a call, not a tail
                      jump); a0 = 1; to the return at 0x8496c (:373-374).
   The model and the code: every test is m_rx_m's (spec_read_frame's code, src / dst against HOST and SPEC_BCAST,
   M.desk_known, the desk and OUI tests, S_CLOSED, the switch, the counters' tests), read through garr8 of the frame,
   trans_rom_view_rd and tw_at; each store is the model's set_* (put of the low bytes); a bcmp result is 0 exactly
   when the bytes agree (abcmp_realizes). The code has no trap of its own: the model's None cases are n outside
   [0, length tf_bytes] (the frame reads), the increments at INT_MAX (the code wraps), OW.dn[k] with k < 0 (the code
   tests only 1 < k and stores the 22 bytes at OW + 256 + 24 k: for -10 <= k <= -1 inside OW's own payload, over its
   other fields, with no error path; for k <= -11 at least partly outside it), and the callees' Nones; each callee's
   model premise is the one m_rx_m's branch supplies.
   Error paths (20 calls; no trap path) and the facts that rule them out:
     errpath_load1 (TS___asan_report_load1, 0x594c8) at 0x84e54, 0x84e60, 0x84e6c, 0x84e78 (fa + 12 .. fa + 15), 0x84e84,
       0x84e90, 0x84e9c, 0x84ea8, 0x84eb4, 0x84ec0, 0x84ecc, 0x84ed8, 0x84ee4, 0x84ef0, 0x84efc (fa + 18 .. fa + 28) and
       0x84f0c (fa + 30, body_len = 1): each byte lies in [fa, fa + n) (n >= 30, and n >= 31 when body_len = 1), inside
       the frame, which trans_src_ok marks usable (a heap block: AR_laws' block shadow; else decode_rd_ok's
       range_addressable).
     errpath_store8 (TS___asan_report_store8, 0x599c8) at 0x84f34 (x) and 0x84f3c (x + 8), errpath_store4
       (TS___asan_report_store4, 0x59928) at 0x84f20 (x + 16), errpath_store2 (TS___asan_report_store2, 0x59888) at
       0x84f30 (x + 20): 0 <= k <= 1 on this path, so [x, x + 22) lies in [OW + 256, OW + 302), inside OW's payload,
       each store aligned to its width inside one granule; trans_mrx_cells: OW's shadow is 0.
     The bcmp wrapper keeps every byte outside its stack window [sp - 144 - 2 * ESTACK, sp - 144) and the frame lies
     outside it (decode_off_win at MRX_STK); __asan_memcpy keeps every byte outside its destination [M + 4, M + 10)
     and its ESTACK window, and mrx_apart puts the frame apart from the destination. No frame byte is read after the
     call of desk_named or of a G-form callee (m_lost, m_wake, m_maybe_online, m_tick): after each of these calls the
     code reads only M, OW, g_cfg.auto_wake (0x5df090) and its own saved registers, and calls only G-form callees.
     So the frame bytes read after a call are the bytes at entry, and the walk needs no fact that a G-form callee
     keeps a frame byte (its acall_kept_g keeps no byte of G, and trans_tframe_at admits a frame in G).
   Callee texts assumed (pc order), every one a premise of the holds statement:
     the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma TS___interceptor_trampoline_bcmp (calls at 0x84ad0,
       0x84ae8, 0x84b00, 0x84b28, 0x84b50, 0x84bdc; through gx_call_leaf). Its ranges: [fa + 6, + 6), [fa, + 6),
       [fa + 6, + 3), [fa + 30 + i, + 6) (i <= 9; body_len >= 33 gives n >= 63 > 45), inside the frame; HOST =
       [0x21040, + 6), SPEC_BCAST = [0x21080, + 6), SPEC_OUI = [0x210a0, + 3) in TRANS_RO_RD, visible through the
       journal by trans_ro_rd_unowned and trans_rom_no_errno; [M + 4, + 6) in M. Besides each range's own shadow bytes,
       abcmp_realizes asks every shadow byte of the aligned group of 8 around them to be visible (YG0d.v
       shadow_hull_vis). HOST's group [0x7fffc208, 0x7fffc210): transport_cells gives 0x7fffc208 (6) and 0x7fffc20c
       (DESK's, 6), trans_mrx_cells HOST's and DESK's guard bytes (0xf9). SPEC_BCAST's and SPEC_OUI's group
       [0x7fffc210, 0x7fffc218): transport_cells gives 0x7fffc210 (6) and 0x7fffc214 (3), trans_mrx_cells their guard
       bytes (0xf9). M + 4's group [0x800b3e28, 0x800b3e30): trans_mrx_cells gives M's zero shadow (0x800b3e2c ..) and
       g_last_counter's last granule (4) and guard bytes (0xf9). The frame ranges: a heap block's shadow by AR_laws,
       else decode_rd_ok's shadow_hull_vis of the whole frame range.
     __asan_memcpy as aintrin_realizes ... OCpy (YG0d.v) at transport_sigma TS___asan_memcpy (call at 0x84b64; through
       TransportGCg.v gx_intrin_at, the destination [M + 4, M + 10) a range of G, gx_rw by TransportGRwA.v
       G_HARNESS_rw). Source [fa + 6, + 6) inside the frame; the two ranges apart by mrx_apart (M.desk is in mrx_wr);
       the destination's group is M + 4's above.
     m_lost as m_lost_cg.v transport_m_lost_cg at transport_sigma TS_m_lost (calls at 0x84c80, a0 = 7 or 5, and 0x84de8,
       a0 = 3; a G-form callee on the same journal). Its premises: why in [-2^31, 2^31) (the constant in a0);
       m_lost_m at the world of the call (m_rx_m's branch); tw_at at that world (the walk's stores, tw_write).
     desk_named as desk_named_cg.v transport_desk_named_cg at transport_sigma TS_desk_named (call at 0x84dc4; a
       donor-form callee lifted with TransportGCg.v gx_call_cg, hence gx_noerrno; it keeps G, so the world relation
       after it is the one it was handed). Its premises: p = fa + 30 = tf_addr fr + sf_body (spec_read_frame's body
       offset), 0 < p; body = the frame bytes from p to the end of tf_bytes (TCb.v m_rx_m's body), garr8 of them and
       trans_src_ok of [p, + length body) (sub-ranges of the frame's, from trans_tframe_at), decode_off_win at
       DNAMED_STK from sp - 144 (from the frame's decode_off_win at MRX_STK >= 144 + DNAMED_STK), trans_rom_view_rd
       (the contract's; no store reaches TRANS_RO_RD), desk_named_m timg_A at the world of the call (m_rx_m's branch).
     m_wake as m_wake_cg.v transport_m_wake_cg at transport_sigma TS_m_wake (call at 0x84e00); m_wake_m at the world of
       the call.
     m_maybe_online as m_maybe_online_cg.v transport_m_maybe_online_cg at transport_sigma TS_m_maybe_online (call at
       0x84e18); m_maybe_online_m at the world of the call.
     m_tick as m_tick_cg.v transport_m_tick_cg at transport_sigma TS_m_tick (call at 0x84e1c); m_tick_m at the world of
       the call.
     Each G-form callee is entered with ra = its return address in m_rx, sp = m_rx's sp - 144, gp / tp as at entry; its
     written range (mlost_wr / mwake_wr / monline_wr / mtick_wr at the world of its call) lies in mrx_wr.
   Stack: 144 bytes of its own; below sp - 144 the largest callee window, desk_named's DNAMED_STK = 16 + 2 * ESTACK (the
   bcmp wrapper 2 * ESTACK, __asan_memcpy ESTACK, m_lost / m_wake / m_maybe_online / m_tick 16): MRX_STK.

   The callers: io_recv (the call at 0x8352c, return address 0x83530): a0 = the 8-byte load of g_rx, a1 = min (g_rx_len,
   cap); its frame is TCb.v frame_from F (g_rx): the bytes of receive's heap block from g_rx to its end, a sub-range of
   the block (decode_in_block). receive (the call at 0x83a20, return address 0x83a24): a0 = s0, its block from the
   malloc wrapper (0x83814), a1 = s2 = n; its frame is the block (decode_in_block). Each supplies the G journal of its
   own walk, the world relation, the frame facts and the model call. *)
From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* m_rx's frame (`sp = sp - 144` at its entry; no realignment). Every call runs from sp - 144: the bcmp wrapper
   (2 * ESTACK, abcmp_realizes), __asan_memcpy (ESTACK, aintrin_realizes' ecall_pre), m_lost, desk_named, m_wake,
   m_maybe_online and m_tick (their STK); desk_named's is the largest. *)
Definition MRX_FRAME : Z := 144.
Definition MRX_STK : Z :=
  MRX_FRAME + Z.max (Z.max (2 * ESTACK) ESTACK)
                    (Z.max (Z.max MLOST_STK DNAMED_STK) (Z.max (Z.max MWAKE_STK MONLINE_STK) MTICK_STK)).
Lemma mrx_stk_eq : MRX_STK = MRX_FRAME + DNAMED_STK.
Proof. reflexivity. Qed.
(* No allocator event: neither m_rx nor a callee calls malloc or free or takes a side-stack frame. *)
Definition MRX_EV : Z := 0.

(* The bytes the code and its callees may store into G, field by field over every path (as check_latest_sent_cg.v
   cls_wr): m_rx's own stores (M.desk_known, M.desk, M.last_rx, M.e2_acked, M.e1_us, M.foreign, M.backoff_until,
   M.desk_counter_valid, M.desk_counter, M.fail, M.fly.on; OW.acks, OW.desk, OW.foreign, OW.acked, OW.ndata,
   OW.acked_counter, OW.acked_retry, OW.desk_off, OW.desk_p, OW.desk_body and the 22 stored bytes of an OW.dn entry),
   m_lost's (M.desk_counter_valid, M.fly.on, M.state, OW.n, an OW.t entry), m_wake's (M.e2_acked with M.e1_us,
   M.wake_sent, M.fail, OW.e2 and m_set's) and m_maybe_online's (M.next_ka and m_set's). The two entries indexed by a
   world count are named by their array: OW.t by OW.n, which up to three inlined m_set calls (m_lost, m_wake, m_tick's
   m_lost) advance in one call, and OW.dn by OW.ndata. *)
Definition mrx_wr (a : Z) : Prop :=
  twa_fld TW.OFF_M TA_M TW.A_M_desk_known 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_desk 6 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_state 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_e2_acked 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_foreign 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_last_rx 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_wake_sent 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_next_ka 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_backoff_until 8 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_desk_counter_valid 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_desk_counter 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fail 4 a \/
  twa_fld TW.OFF_M TA_M TW.A_M_fly_on 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_n 4 a \/
  (exists i, 0 <= i < TC.TRANS_MAX /\ twa_fld TW.OFF_OW TA_OW (TW.A_OW_t_state i) TW.OW_t_ESZ a) \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_e2 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_acks 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_desk 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_foreign 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_acked 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_ndata 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_acked_counter 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_acked_retry 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_desk_off 4 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_desk_p 8 a \/
  twa_fld TW.OFF_OW TA_OW TW.A_OW_desk_body 8 a \/
  (exists k, 0 <= k < TW.OW_dn_N /\ twa_fld TW.OFF_OW TA_OW (TC.A_OW_dn_body k) 22 a).

(* The shadow facts of the record (lib/A/AF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) that the code's
   instrumented checks and its runtime calls' ranges need beyond transport_cells: OW's payload (304 bytes, 38 whole
   granules) has shadow 0 (the checks of the stores at OW.dn[k]); M's payload (1648 bytes, 206 whole granules) has
   shadow 0 (the memcpy destination and the bcmp range M + 4); and the rest of the aligned groups of 8 shadow bytes
   the bcmp ranges touch: HOST's (0x21040, payload 6) and DESK's (0x21060) guard granules, SPEC_BCAST's (0x21080,
   payload 6) and SPEC_OUI's (0x210a0, payload 3) guard granules, and g_last_counter's (0x5df140, payload 4) last
   granule and guard granules, which share M + 4's group. *)
Definition trans_mrx_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_OW (TA_OW + TW.SZ_OW) /\
  decode_zshadow_at B TA_M (TA_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (ACells.shadow_addr (TRANS_HOST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_HOST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_HOST + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_DESK + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_DESK + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_DESK + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_SPEC_BCAST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_SPEC_BCAST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_SPEC_BCAST + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_SPEC_OUI + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_SPEC_OUI + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TRANS_SPEC_OUI + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr TA_g_last_counter)) 4) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_last_counter + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_last_counter + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (ACells.shadow_addr (TA_g_last_counter + 24))) 0xf9) (as_const B ly).
Lemma trans_mrx_cells_rows :
  map ACells.shadow_addr [TRANS_HOST + 8; TRANS_HOST + 16; TRANS_HOST + 24; TRANS_DESK + 8; TRANS_DESK + 16;
                          TRANS_DESK + 24; TRANS_SPEC_BCAST + 8; TRANS_SPEC_BCAST + 16; TRANS_SPEC_BCAST + 24;
                          TRANS_SPEC_OUI + 8; TRANS_SPEC_OUI + 16; TRANS_SPEC_OUI + 24; TA_g_last_counter;
                          TA_g_last_counter + 8; TA_g_last_counter + 16; TA_g_last_counter + 24; TA_M; TA_OW] =
  [0x7fffc209; 0x7fffc20a; 0x7fffc20b; 0x7fffc20d; 0x7fffc20e; 0x7fffc20f; 0x7fffc211; 0x7fffc212; 0x7fffc213;
   0x7fffc215; 0x7fffc216; 0x7fffc217; 0x800b3e28; 0x800b3e29; 0x800b3e2a; 0x800b3e2b; 0x800b3e2c; 0x800b660c].
Proof. reflexivity. Qed.

Section mrx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* No byte the call may store is a byte of the frame fr: the code and desk_named read frame bytes after stores (the
   body byte at fa + 30, desk_named's name bytes, host_offset's ranges), and the memcpy's source must lie apart from
   its destination. The plain contract's tframe_at puts the frame off the world. *)
Definition mrx_apart (fr : TI.tframe) : Prop :=
  forall x, mrx_wr x -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range mrx_wr, no
   meter charge, and X: a0 = r and the world relation at the model's world Bw'. *)
Definition transport_mrx_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MRX_STK MRX_EV 0 mrx_wr
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_rx_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fr : TI.tframe) (n r : Z) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 (TI.tf_addr fr) -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MRX_STK -> spZ regs <= sp0 ->
    trans_tframe_at B lyc Sc W memc regs MRX_STK (Some fr) ->
    TI.tf_addr fr + n < 2 ^ 64 ->
    mrx_apart fr ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.m_rx_m timg_A (Some fr) Bw n = Some (Bw', r) ->
    st_nev S + k + MRX_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mrx_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, the read-only
   globals' shadow), OW's and M's shadow and the rest of the bcmp ranges' shadow groups (trans_mrx_cells), the two
   read-only facts of the record (they keep HOST, SPEC_BCAST and SPEC_OUI visible through the journal), the allocator
   and meter laws, G inside the image, outside the allocator's statics and outside errno (a donor callee keeps G:
   gx_call_cg), and the contracts of the bcmp wrapper, __asan_memcpy and the five callees give the contract at
   TS_m_rx. *)
Definition transport_m_rx_cg_holds_stmt : Prop :=
  transport_cells B -> trans_mrx_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost)) ->
  (forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named)) ->
  (forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake)) ->
  (forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online)) ->
  (forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick)) ->
  transport_m_rx_cg (transport_sigma TS_m_rx).
End mrx.
