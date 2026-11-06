(* m_rx_cg: image B's ASan walk contract of m_rx (fuzz/fuzz_transport.c:280-375, spec_read_frame and host_offset
   CALLED, m_lost :210-215 inlined; model lib/TModel/TCb.v m_rx_m) on fuzz_transport.asan-ubsan (41113a03c82f) at
   0x84c1c = transportb_sigma TB_m_rx, size 1060, as STATEMENTS only (no proof). It stores into M and OW, two harness
   globals, and calls spec_read_frame, host_offset, m_set, desk_named, m_wake, m_maybe_online, m_tick, the bcmp
   wrapper and __asan_memcpy, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B). Image B's twin of
   lib/A/Prog/m_rx_cg.v; the differences image B's code forces are listed at the end of this comment.

   The contract. a0 = tf_addr fr, a1 = n: fr is the received frame (the bytes tf_bytes fr at tf_addr fr; TImg.v tframe),
   read as n bytes. The frame is given in check_state_data_cg.v trans_tframe_at form at this call's window MRX_STK
   (0 < tf_addr fr, garr8 of its bytes, trans_src_ok and decode_off_win of [tf_addr fr, + length tf_bytes)), it ends
   below 2 ^ 64 at n (tf_addr fr + n < 2 ^ 64), and no byte the call may store is a byte of it (mrx_apart). The
   read-only bytes the bcmp calls, host_offset and desk_named compare (HOST, SPEC_BCAST, SPEC_OUI, the two names) read
   as the image's (trans_rom_view_rd). The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at
   at TWorldB.v TMAP_B, read through aview), and m_rx_m timg_B (Some fr) Bw n = Some (Bw', r). The function returns to
   ra with a0 = r (0 or 1), the callee-saved registers kept, no allocator event and no meter charge, the caller's
   side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling
   outside the call's stack window [sp - MRX_STK, sp), the image bytes outside G, the owned statics and errno, the
   caller's block and frame bytes outside mrx_wr), and the world relation at Bw'.
   This is what the plain contract (lib/Prog/T/m_rx_c.v) says: a0 = r; wmem rsegs m' B' with B' the model's world;
   munch of the frame and the world only. Its premises become: a0 / a1 -> getr 10 / 11;
   tframe_at m sp m_rx_FRAME (Some fr) -> trans_tframe_at at MRX_STK (bytes_at -> garr8, the heap block -> trans_src_ok,
   off_window -> decode_off_win; its off_world clause -> mrx_apart: the frame apart from every byte the call stores);
   tf_addr fr + n < 2 ^ 64 kept as it is (the plain contract keeps it equal to the ubsan twin's); wmem -> tw_at;
   timg_plain -> timg_B; the stack premises -> the journal's window premises; mem_inv dropped. The premise the plain
   contract does not have: trans_rom_view_rd W memc (the plain build reads HOST, SPEC_BCAST, SPEC_OUI through rsegs'
   read-only segment; here they are TRANS_RO_RD bytes read through the journal's view, as check_sent_frame_cg.v,
   host_offset_cg.v and desk_named_cg.v take it).
   Run invariants: none carried and none needed. The callees' contracts (spec_read_frame_cg.v, host_offset_cg.v,
   m_set_cg.v, desk_named_cg.v, m_wake_cg.v, m_maybe_online_cg.v, m_tick_cg.v) carry none of the four run invariants
   (check_inflight_retry, check_latest_queue, check_state_data, check_latest_sent), and m_rx's own
   code reads past no global's payload: every instrumented access and every range handed to the bcmp wrapper or
   __asan_memcpy is either a frame byte below tf_addr fr + n (n <= length tf_bytes: the model), a read-only constant
   (HOST, SPEC_BCAST, SPEC_OUI), at a constant offset of M or OW, or at OW.dn[k] with 0 <= k <= 1 (the code's test
   k <= 1 and the model's None at k < 0); the memcpy and bcmp lengths are constants (6 or 3).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 1060 code bytes are equal in both files), 265
   words. fa = tf_addr fr; f is the struct spec_frame at m_rx's sp + 0.
     0x84c1c - 0x84c2c sp = sp - 112; ra, s0, s1, s2 at sp + 104 .. sp + 80, loaded back at 0x84c4c - 0x84c58 (sp =
                      sp + 112 at 0x84c5c, return at 0x84c60). No side-stack frame, no frame pointer. Own frame cells:
                      sp + 0 .. sp + 80 (f, 80 bytes, written by spec_read_frame).
     0x84c30 - 0x84c38 s2 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     0x84c3c - 0x84c48 a0 = fa, a1 = n (m_rx's own arguments), a2 = sp; call of spec_read_frame (0x839c0 =
                      transportb_sigma TB_spec_read_frame) at 0x84c40, return address 0x84c44 (:283); a result not 0
                      goes to 0x84c48: a0 = 0 and the return (:283-284).
     0x84c64 - 0x84cb0 s0 = f.src (the 8-byte load at sp + 16: fa + 6). bcmp (0x42d34 = transportb_sigma
                      TB___interceptor_trampoline_bcmp) at 0x84c78 with (fa + 6, HOST = 0x20fe0 = TRANS_HOST, 6): 0
                      returns 0 (:285); s1 = f.dst (sp + 8: fa); bcmp at 0x84c94 with (fa, HOST, 6): 0 goes to
                      0x84cb4; else bcmp at 0x84cac with (fa, SPEC_BCAST = 0x21020 = TRANS_SPEC_BCAST, 6): not 0
                      returns 0 (:286-287).
     0x84cb4 - 0x84cd8 s1 = &M = 0x5dede0 (TB_M); M.desk_known (the 4-byte load at M + 0) = 0 goes to 0x84cdc; else
                      bcmp at 0x84cd0 with (fa + 6, M + 4 (M.desk), 6), not 0 returns 0 (:288-290); 0 goes to
                      0x84d1c.
     0x84cdc - 0x84d18 (no desk known) f.cmd (the 1-byte load at sp + 40) & 0xfe <> 0xe0 returns 0 (:292-293); bcmp
                      at 0x84cfc with (fa + 6, SPEC_OUI = 0x21040 = TRANS_SPEC_OUI, 3): not 0 returns 0 (:294-295);
                      __asan_memcpy (0x523ec = transportb_sigma TB___asan_memcpy, checked_memcpy) at 0x84d10, return
                      address 0x84d14, with (M + 4, fa + 6, 6): M.desk = src; the 4-byte store of 1 at M + 0
                      (M.desk_known, :296-297).
     0x84d1c - 0x84d24 a0 = M.state (M + 12); 3 (S_CLOSED) returns 0 (:299-300).
     0x84d28 - 0x84d38 a1 = the 8-byte load of g_now (0x5ded80); a2 = f.cmd; the 8-byte store of g_now at M + 32
                      (M.last_rx, :301).
     0x84d3c - 0x84d6c the switch on cmd (:302): cmd <= 0xdf goes to 0x84d70; cmd - 0xe0 >= 2 goes to 0x84dc8; e0 / e1
                      with f.body_len (sp + 56) < 33 (SPEC_ANN_MIN) goes to 0x84fc0 (:305-306); cmd <> 0xe1 goes to
                      0x84f2c; e1: a0 = f.body (sp + 48); call of host_offset (0x85040 = transportb_sigma
                      TB_host_offset) at 0x84d64, return address 0x84d68; s0 = its result (:307); to 0x84f30.
     0x84d70 - 0x84dc4 cmd = 0 (SPEC_CMD_DATA) goes to 0x84df4; cmd <> 0xa0 (SPEC_CMD_ACK) goes to 0x84fc0. ACK
                      (:332-341): M.fly.on (M + 96) = 0 or f.ack (sp + 36) <> M.fly.counter (M + 104) goes to 0x84fc0;
                      a2 = &OW = 0x5f2ce0 (TB_OW); a3 = OW.acked (OW + 216) + 1 (32-bit, sign-extended); a3 below
                      OW.acked (signed: OW.acked = INT_MAX) goes to the trap word (0x84da0); the 4-byte stores of
                      OW.acked + 1 at OW + 216, of f.ack at OW + 224 (acked_counter), of M.fly.retries (M + 108) at
                      OW + 228 (acked_retry), of 0 at M + 96 (fly.on); M.state <> 1 (S_WAKING) goes to 0x84fc0; else
                      the 4-byte store of 1 at M + 16 (e2_acked) and to 0x84fbc (the call of m_maybe_online).
     0x84dc8 - 0x84df0 cmd <> 0xe3 goes to 0x84fc0; e3 (:366-368): M.state - 1 > 1 (unsigned) goes to 0x84fc0; m_lost
                      inlined: the 4-byte stores of 0 at M + 76 (desk_counter_valid) and at M + 96 (fly.on); a0 = 0
                      (S_IDLE), a1 = 7 (R_DESK_DISCONNECT); call of m_set (0x85224 = transportb_sigma TB_m_set) at
                      0x84dec, return address 0x84df0; to 0x84fc0.
     0x84df4 - 0x84f28 DATA (:344-364): a2 = &OW; OW.acks (OW + 204) + 1, the same overflow branch to the trap word
                      (0x84e04); a3 = f.retry (sp + 30); the 4-byte stores of OW.acks + 1 at OW + 204 and of 0 at
                      M + 88 (fail); retry <> 0: the 8-byte store of g_cfg.backoff_ms (the 4-byte unsigned load at
                      0x5ded24 = g_cfg + 36) * 1000 + g_now at M + 56 (backoff_until); M.desk_counter_valid (M + 76)
                      <> 0, retry <> 0 and f.send (sp + 32) = M.desk_counter (M + 80) goes to 0x84fc0; the 4-byte
                      stores of 1 at M + 76 and of f.send at M + 80; f.body_len = 1: a0 = f.body, 0 goes to the trap
                      word (0x84e64), the instrumented check of the 1-byte load at f.body (the shadow byte k (signed)
                      at (a >> 3) + 0x7fff8000; k = 0 goes on; else (a & 7) < k goes on; else the error path 0x8500c),
                      body[0] = 0 goes to 0x84fc0; k = OW.ndata (the 4-byte signed load at OW + 220); 1 < k (signed)
                      goes to 0x84f1c; else x = OW + 256 + 24 k: x = 0 goes to the trap word (0x84e9c);
                      (x < OW + 256, unsigned) <> (k < 0) goes to the trap word (0x84eb0); the check of the 8-byte
                      store at x (k = 0 goes on, else the error path) and the store of f.body at x (OW.dn[k].body),
                      the check and the 8-byte store of f.body_len at x + 8 (len), the check (for a 4-byte access:
                      ((a & 7) + 3) < k goes on) and the 4-byte store of f.send at x + 16 (counter), the check (2-byte:
                      ((a & 7) + 1) < k goes on) and the 2-byte store of retry at x + 20 (retry); 0x84f1c: k + 1, the
                      overflow branch to the trap word (0x84f20), the 4-byte store of k + 1 at OW + 220 (ndata); to
                      0x84fc0.
     0x84f2c - 0x84f68 e0 / e1 (:307-312): s0 = -1 for e0 (0x84f2c); s2 = &OW (the shadow base in s2 is not used again
                      on this path); OW.desk (OW + 208) + 1, the overflow branch to the trap word (0x84f40); the 4-byte
                      stores of OW.desk + 1 at OW + 208 and of s0 at OW + 232 (desk_off); a0 = f.body; call of
                      desk_named (0x85100 = transportb_sigma TB_desk_named) at 0x84f50, return address 0x84f54; the
                      8-byte stores of its result at OW + 240 (desk_p) and of f.body at OW + 248 (desk_body); cmd <>
                      0xe0 goes to 0x84fac.
     0x84f6c - 0x84fa8 e0 (:312-318): the 4-byte store of 0 at M + 24 (foreign); the old M.state = 2 (S_ONLINE): m_lost
                      inlined (the 4-byte stores of 0 at M + 76 and M + 96; a0 = 0, a1 = 3 (R_DESK_OFFLINE); call of
                      m_set at 0x84f8c, return address 0x84f90; M.state loaded again); M.state <> 0 or g_cfg.auto_wake
                      (the 4-byte load at 0x5ded10 = g_cfg + 16) = 0 goes to 0x84fc0; else call of m_wake (0x83914 =
                      transportb_sigma TB_m_wake) at 0x84fa4, return address 0x84fa8 (its a0 not used); to 0x84fc0.
     0x84fac - 0x84fbc e1, s0 >= 0 (:319-322): the 4-byte stores of 1 at M + 20 (e1_us) and of 0 at M + 24 (foreign);
                      call of m_maybe_online (0x851d4 = transportb_sigma TB_m_maybe_online) at 0x84fbc, return address
                      0x84fc0.
     0x84fcc - 0x84ffc e1, s0 < 0 (:324-328): the 4-byte store of 1 at M + 24 (foreign); OW.foreign (OW + 212) + 1,
                      the overflow branch to the trap word (0x84fdc), stored at OW + 212; the old M.state - 1 > 1
                      (unsigned) goes to 0x84fc0; else m_lost inlined (the 4-byte stores of 0 at M + 76 and M + 96;
                      a1 = 5 (R_FOREIGN)) and to 0x84de8 (a0 = 0, the call of m_set at 0x84dec).
     0x84fc0 - 0x84fc8 call of m_tick (0x8383c = transportb_sigma TB_m_tick) at 0x84fc0 from sp - 112, return address
                      0x84fc4 (a call, not a tail jump); a0 = 1; to the return at 0x84c4c (:373-374).
     0x85000          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x85004 - 0x8503c the slow paths of the checks and the five error calls.
   The model and the code: every test is m_rx_m's (spec_read_frame's code, which the callee returns; src / dst
   against HOST and SPEC_BCAST, M.desk_known, the desk and OUI tests, S_CLOSED, the switch, the counters' tests), read
   through the struct f (spec_read_frame's X: TContract.sf_bytes fa f with f = DgnSpec spec_read_frame (zs tf_bytes) n,
   m_rx_m's f), garr8 of the frame, trans_rom_view_rd and tw_at; each store is the model's set_* (put of the low
   bytes); a bcmp result is 0 exactly when the bytes agree (abcmp_realizes); each inlined m_lost is TCb.v m_lost_m:
   the stores of M.fly.on and M.desk_counter_valid, then m_set_m at S_IDLE. The model's None cases are n outside
   [0, length tf_bytes] (the frame reads), the increments at INT_MAX (the code goes to the trap word), OW.dn[k] with
   k < 0 (the code tests only 1 < k; for -10 <= k <= -1 the 22 bytes at OW + 256 + 24 k lie inside OW's own payload,
   over its other fields, with no error path), and the callees' Nones; each callee's model premise is the one m_rx_m's
   branch supplies.
   Trap path (the unimp word at 0x85000, from 8 branches) and the fact that refutes each:
     0x84da0, 0x84e04, 0x84f20, 0x84f40, 0x84fdc (OW.acked / OW.acks / OW.ndata / OW.desk / OW.foreign = INT_MAX):
       int_inc is None there, so the model premise rules them out.
     0x84e64 (f.body = 0 on the DATA path with body_len = 1): the code is SPEC_OK on every path past 0x84c44, so f.body
       = TContract.sf_ptr fa f (sf_body f) = fa + 30 (spec_read_frame's X) and 0 < fa.
     0x84e9c (x = 0), 0x84eb0 (the pointer-overflow test of OW.dn[k]): reached with k <= 1, and the model is None at
       k < 0, so k is 0 or 1 and x is OW + 256 or OW + 280: not 0, no wrap, and x >= OW + 256.
   Error paths (5 calls) and the facts that rule them out:
     __asan_report_load1 (0x59504) at 0x8500c (fa + 30, body_len = 1): the byte lies in [fa, fa + n) (body_len =
       numbytes - 16 = 1 gives n >= numbytes + 14 = 31), inside the frame, which trans_src_ok marks usable (a heap
       block: AR_laws' block shadow; else decode_rd_ok's range_addressable), kept through the earlier calls
       (DgnTransportBCg.v trans_src_ok_kept; the memcpy writes M.desk, apart from the frame by mrx_apart).
     __asan_report_store8 (0x59a04) at 0x85034 (x) and 0x8503c (x + 8), __asan_report_store4 (0x59964) at 0x85020
       (x + 16), __asan_report_store2 (0x598c4) at 0x85030 (x + 20): 0 <= k <= 1 on this path, so [x, x + 22) lies in
       [OW + 256, OW + 302), inside OW's payload, each store aligned to its width inside one granule
       (OW = 0x5f2ce0); trans_mrx_cells: OW's shadow is 0.
     The bcmp wrapper keeps every byte outside its stack window [sp - 112 - 2 * ESTACK, sp - 112) and the frame lies
     outside it (decode_off_win at MRX_STK); __asan_memcpy keeps every byte outside its destination [M + 4, M + 10)
     and its ESTACK window, and mrx_apart puts the frame apart from the destination. The frame bytes read after
     spec_read_frame (the bcmp and memcpy ranges, the byte at fa + 30, the bodies handed to host_offset and
     desk_named; the struct's pointers are X's garr8, not frame bytes) are kept by its post, although it is a G-form
     callee: its X's gx_kept keeps every
     byte of G, and its acall_kept_g every image byte outside G and every caller byte outside srf_wr sp, which the
     frame lies outside (it lies outside m_rx's window); host_offset and desk_named are donor-form callees lifted by
     gx_call_cg, which keep every byte of G too. No frame byte is read after the call of a G-form callee that writes
     G (m_set, m_wake, m_maybe_online, m_tick): after each of these calls the code reads only M, g_cfg.auto_wake
     (0x5ded10) and its own saved registers, and calls only m_wake and m_tick. So the frame bytes read after a call
     are the bytes at entry, and the walk needs no fact that a callee that writes G keeps a frame byte (its
     acall_kept_g keeps no byte of G, and trans_tframe_at admits a frame in G).
   Callee texts assumed (pc order), every one a premise of the holds statement:
     spec_read_frame as spec_read_frame_cg.v transport_spec_read_frame_cg at transportb_sigma TB_spec_read_frame (call
       at 0x84c40; G form, the same journal; its post, TransportGCg.v transport_cg_post_out [(sp, 80)], is used as
       written). Its premises: b = fa (0 < fa: trans_tframe_at), len = n (0 <= n <= length tf_bytes: m_rx_m is None
       otherwise), garr8 of TW.zs (tf_bytes fr) (trans_tframe_at's garr8 of map DSpec.bz, the same list);
       trans_src_ok and decode_off_win (SRF_STK <= MRX_STK - 112) of [fa, fa + n): sub-ranges of the frame's
       (trans_src_ok_sub, decode_off_win_sub; the empty range at n = 0 by the same placement); the frame apart from
       srf_wr sp: the frame lies outside m_rx's window, the struct inside it; fp = sp: fp mod 8 = 0 (sp mod 16 = 0),
       transport_twr_ok_g (window bytes above the call's ESTACK window, present by the journal), decode_rd_ok
       (CanKit.v can_stack_addressable / can_stack_hull; amem_range: a stack range), decode_off_win (sp >= sp - 112),
       not in G (the stack lies above G). Its X: a0 = sf_code f, the 80 bytes at sp = sf_bytes fa f, and gx_kept (G
       as it was, so the world relation at Bw holds after it).
     the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma TB___interceptor_trampoline_bcmp (calls at
       0x84c78, 0x84c94, 0x84cac, 0x84cd0, 0x84cfc; through gx_call_leaf). Its ranges: [fa + 6, + 6), [fa, + 6),
       [fa + 6, + 3), inside the frame (n >= 30 on SPEC_OK); HOST = [0x20fe0, + 6), SPEC_BCAST = [0x21020, + 6),
       SPEC_OUI = [0x21040, + 3) in TRANS_RO_RD, visible through the journal by trans_rom_view_rd (kept through
       spec_read_frame's acall_kept_g by trans_ro_rd_scoped: trans_ro_rd_unowned, trans_rom_no_errno); [M + 4, + 6) in
       M. Besides each range's own shadow bytes, abcmp_realizes asks every shadow byte of the aligned group of 8
       around them to be visible (YG0d.v shadow_hull_vis). HOST's group [0x7fffc1f8, 0x7fffc200) (the shadow of
       [0x20fc0, 0x21000)): transport_cells gives 0x7fffc1fc (HOST, 6), trans_mrx_cells SCALE's guard bytes
       0x7fffc1f8 - 0x7fffc1fb and HOST's 0x7fffc1fd - 0x7fffc1ff (0xf9). SPEC_BCAST's group [0x7fffc200,
       0x7fffc208): transport_cells gives 0x7fffc200 (DESK, 6) and 0x7fffc204 (SPEC_BCAST, 6), trans_mrx_cells their
       guard bytes (0xf9). SPEC_OUI's group [0x7fffc208, 0x7fffc210): transport_cells gives 0x7fffc208 (SPEC_OUI, 3),
       0x7fffc20c (TRANS_STR_C24's whole granule, 0) and 0x7fffc20d (1), trans_mrx_cells SPEC_OUI's guard bytes
       0x7fffc209 - 0x7fffc20b and TRANS_STR_C24's 0x7fffc20e, 0x7fffc20f (0xf9). M + 4's group [0x800b3db8,
       0x800b3dc0): trans_mrx_cells gives g_last_counter's last granule (4) and guard bytes (0xf9) and M's zero shadow
       (0x800b3dbc ..). The frame ranges: a heap block's shadow by AR_laws, else decode_rd_ok's shadow_hull_vis of the
       whole frame range.
     __asan_memcpy as aintrin_realizes ... OCpy (YG0d.v) at transportb_sigma TB___asan_memcpy (call at 0x84d10; through
       TransportGCg.v gx_intrin_at, the destination [M + 4, M + 10) a range of G, gx_rw by lib/B/Prog/TransportGRwB.v).
       Source [fa + 6, + 6) inside the frame; the two ranges apart by mrx_apart (M.desk is in mrx_wr); the
       destination's group is M + 4's above.
     host_offset as host_offset_cg.v transport_host_offset_cg at transportb_sigma TB_host_offset (call at 0x84d64; a
       donor-form callee lifted with TransportGCg.v gx_call_cg, hence gx_noerrno; it keeps G, so the world relation
       after it is the one it was handed). Its premises: p = f.body = fa + 30 (0 < p); body = the frame bytes from p to
       the end of tf_bytes (TCb.v m_rx_m's body), garr8 of them and trans_src_ok of [p, + length body) (sub-ranges of
       the frame's, from trans_tframe_at), decode_off_win at HOFF_STK from sp - 112 (from the frame's decode_off_win at
       MRX_STK = 112 + HOFF_STK), trans_rom_view_rd (kept, above), host_offset_m at the world of the call (m_rx_m's
       branch).
     m_set as m_set_cg.v transport_m_set_cg at transportb_sigma TB_m_set (calls at 0x84dec, a1 = 7 or 5, and 0x84f8c,
       a1 = 3; a0 = 0; a G-form callee on the same journal), after the two stores of the inlined m_lost. Its premises:
       st = 0 and why in [-2^31, 2^31) (the constants); tw_at at the world after those stores (tw_write); m_set_m at
       that world S_IDLE why = Some _: TCb.v m_lost_m, from m_rx_m's branch.
     desk_named as desk_named_cg.v transport_desk_named_cg at transportb_sigma TB_desk_named (call at 0x84f50; a
       donor-form callee lifted with gx_call_cg). Its premises: p = fa + 30 (0 < p); body = the frame bytes from p to
       the end of tf_bytes, garr8 of them and trans_src_ok of [p, + length body) (sub-ranges of the frame's),
       decode_off_win at DNAMED_STK from sp - 112 (MRX_STK >= 112 + DNAMED_STK), trans_rom_view_rd (no store reaches
       TRANS_RO_RD; kept through the G-form posts by trans_ro_rd_scoped), desk_named_m timg_B at the world of the call
       (m_rx_m's branch).
     m_wake as m_wake_cg.v transport_m_wake_cg at transportb_sigma TB_m_wake (call at 0x84fa4); m_wake_m at the world of
       the call.
     m_maybe_online as m_maybe_online_cg.v transport_m_maybe_online_cg at transportb_sigma TB_m_maybe_online (call at
       0x84fbc); m_maybe_online_m at the world of the call.
     m_tick as m_tick_cg.v transport_m_tick_cg at transportb_sigma TB_m_tick (call at 0x84fc0); m_tick_m at the world of
       the call.
     Each G-form callee is entered with ra = its return address in m_rx, sp = m_rx's sp - 112, gp / tp as at entry; its
     written range (mset_st_wr / mwake_wr / monline_wr / mtick_wr at the world of its call) lies in mrx_wr.
   Stack: 112 bytes of its own; below sp - 112 the largest callee window, host_offset's HOFF_STK = 80 + 2 * ESTACK
   (spec_read_frame 48 + ESTACK, desk_named 16 + 2 * ESTACK, the bcmp wrapper 2 * ESTACK, __asan_memcpy ESTACK, m_wake
   32, m_set / m_maybe_online / m_tick 16): MRX_STK.

   The callers: io_recv (the call at 0x833d0, return address 0x833d4): a0 = the 8-byte load of g_rx (0x5df620),
   a1 = s1 = min (g_rx_len, cap) (0x833b4 - 0x833c4); its frame is TCb.v frame_from F (g_rx): the bytes of receive's
   heap block from g_rx to its end, a sub-range of the block (decode_in_block). receive (the call at 0x837dc, return
   address 0x837e0): a0 = s0, its block from the malloc wrapper (the call at 0x836dc), a1 = s1 = n; its frame is the
   block (decode_in_block). Each supplies the G journal of its own walk, the world relation, the frame facts and the
   model call.

   Against image A's statement (lib/A/Prog/m_rx_cg.v): the same premises and post, at image B's names (TMAP_B,
   timg_B, TB_M, TB_OW, transportb_sigma, lib/B/Prog/DgnTransportBCg.v, lib/B/Prog/m_set_cg.v twb_fld). What image B's
   code forces: (1) spec_read_frame and host_offset are called, not inlined: m_rx's own code reads no frame byte but
   body[0] (image A's reads fa + 12 .. fa + 28 with instrumented checks and keeps four spill slots), its struct f is
   filled by spec_read_frame, and its bcmp calls are five (host_offset makes the sixth family); the frame is 112 bytes
   (A: 144) and MRX_STK is 112 + HOFF_STK (A: 144 + DNAMED_STK). (2) m_lost is inlined (image B has no m_lost
   function): m_rx makes its two stores and calls m_set (0, why), so the holds statement takes m_set's contract in
   place of m_lost's; mrx_wr is unchanged (it already names those fields and m_set's). (3) Eight branches to the
   unimp word (the five OW counters' overflow checks, where image A's code wraps; the null check of f.body; the null
   and pointer-overflow checks of OW.dn[k]), each refuted by the model premise or the struct's fields, so no contract
   premise is added. (4) trans_mrx_cells names the rows image B's layout puts in the bcmp ranges' shadow groups:
   HOST's group holds SCALE's guard bytes (image A: DESK's), SPEC_BCAST's holds DESK's (image A: SPEC_OUI's), and
   SPEC_OUI's holds TRANS_STR_C24's. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  m_set_cg m_wake_cg m_maybe_online_cg m_tick_cg spec_read_frame_cg host_offset_cg desk_named_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* m_rx's frame (`sp = sp - 112` at its entry; no realignment). Every call runs from sp - 112: spec_read_frame
   (SRF_STK), the bcmp wrapper (2 * ESTACK, abcmp_realizes), __asan_memcpy (ESTACK, aintrin_realizes' ecall_pre),
   host_offset, m_set, desk_named, m_wake, m_maybe_online and m_tick (their STK); host_offset's is the largest. *)
Definition MRX_FRAME : Z := 112.
Definition MRX_STK : Z :=
  MRX_FRAME + Z.max (Z.max (Z.max SRF_STK (2 * ESTACK)) ESTACK)
                    (Z.max (Z.max HOFF_STK DNAMED_STK) (Z.max (Z.max MSET_STK MWAKE_STK) (Z.max MONLINE_STK MTICK_STK))).
Lemma mrx_stk_eq : MRX_STK = MRX_FRAME + HOFF_STK.
Proof. reflexivity. Qed.
(* No allocator event: neither m_rx nor a callee calls malloc or free or takes a side-stack frame. *)
Definition MRX_EV : Z := 0.

(* The bytes the code and its callees may store into G, field by field over every path (as check_latest_sent_cg.v
   cls_wr): m_rx's own stores (M.desk_known, M.desk, M.last_rx, M.e2_acked, M.e1_us, M.foreign, M.backoff_until,
   M.desk_counter_valid, M.desk_counter, M.fail, M.fly.on; OW.acks, OW.desk, OW.foreign, OW.acked, OW.ndata,
   OW.acked_counter, OW.acked_retry, OW.desk_off, OW.desk_p, OW.desk_body and the 22 stored bytes of an OW.dn entry;
   the inlined m_lost's M.desk_counter_valid and M.fly.on), m_set's (M.state, OW.n, an OW.t entry), m_wake's
   (M.e2_acked with M.e1_us, M.wake_sent, M.fail, OW.e2 and m_set's), m_maybe_online's (M.next_ka and m_set's) and
   m_tick's (M.desk_counter_valid, M.fly.on and m_set's). The two entries indexed by a world count are named by their
   array: OW.t by OW.n, which up to three m_set calls (the inlined m_lost's, m_wake's, m_tick's) advance in one call,
   and OW.dn by OW.ndata. *)
Definition mrx_wr (a : Z) : Prop :=
  twb_fld TW.OFF_M TB_M TW.A_M_desk_known 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_desk 6 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_state 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_e2_acked 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_foreign 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_last_rx 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_wake_sent 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_next_ka 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_backoff_until 8 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_desk_counter_valid 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_desk_counter 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fail 4 a \/
  twb_fld TW.OFF_M TB_M TW.A_M_fly_on 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_n 4 a \/
  (exists i, 0 <= i < TC.TRANS_MAX /\ twb_fld TW.OFF_OW TB_OW (TW.A_OW_t_state i) TW.OW_t_ESZ a) \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_e2 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_acks 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_desk 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_foreign 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_acked 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_ndata 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_acked_counter 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_acked_retry 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_desk_off 4 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_desk_p 8 a \/
  twb_fld TW.OFF_OW TB_OW TW.A_OW_desk_body 8 a \/
  (exists k, 0 <= k < TW.OW_dn_N /\ twb_fld TW.OFF_OW TB_OW (TC.A_OW_dn_body k) 22 a).

(* The shadow facts of the record (lib/B/YF0m.v Tfib_zero_shadow and Tfib_const_shadow rows) that the code's
   instrumented checks and its runtime calls' ranges need beyond transport_cells: OW's payload (304 bytes, 38 whole
   granules) has shadow 0 (the checks of the stores at OW.dn[k]); M's payload (1648 bytes, 206 whole granules) has
   shadow 0 (the memcpy destination and the bcmp range M + 4); and the rest of the aligned groups of 8 shadow bytes
   the bcmp ranges touch: SCALE's (0x20fa0, payload 32) guard granules and HOST's (0x20fe0, payload 6), DESK's
   (0x21000, payload 6) and SPEC_BCAST's (0x21020, payload 6) guard granules, SPEC_OUI's (0x21040, payload 3) guard
   granules and TRANS_STR_C24's (0x21060, payload 9), and g_last_counter's (0x5dedc0, payload 4) last granule and
   guard granules, which share M + 4's group. *)
Definition trans_mrx_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_OW (TB_OW + TW.SZ_OW) /\
  decode_zshadow_at B TB_M (TB_M + TW.SZ_M) /\
  forall ly,
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 32))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 40))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 48))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SCALE + 56))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_HOST + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_DESK + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_DESK + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_DESK + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_BCAST + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_BCAST + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_BCAST + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_OUI + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_OUI + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_SPEC_OUI + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_STR_C24 + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TRANS_STR_C24 + 24))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr TB_g_last_counter)) 4) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_g_last_counter + 8))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_g_last_counter + 16))) 0xf9) (as_const B ly) /\
    In (z1 (ANum (BCells.shadow_addr (TB_g_last_counter + 24))) 0xf9) (as_const B ly).
Lemma trans_mrx_cells_rows :
  map BCells.shadow_addr [TRANS_SCALE + 32; TRANS_SCALE + 40; TRANS_SCALE + 48; TRANS_SCALE + 56; TRANS_HOST + 8;
                          TRANS_HOST + 16; TRANS_HOST + 24; TRANS_DESK + 8; TRANS_DESK + 16; TRANS_DESK + 24;
                          TRANS_SPEC_BCAST + 8; TRANS_SPEC_BCAST + 16; TRANS_SPEC_BCAST + 24; TRANS_SPEC_OUI + 8;
                          TRANS_SPEC_OUI + 16; TRANS_SPEC_OUI + 24; TRANS_STR_C24 + 16; TRANS_STR_C24 + 24;
                          TB_g_last_counter; TB_g_last_counter + 8; TB_g_last_counter + 16; TB_g_last_counter + 24;
                          TB_M; TB_OW] =
  [0x7fffc1f8; 0x7fffc1f9; 0x7fffc1fa; 0x7fffc1fb; 0x7fffc1fd; 0x7fffc1fe; 0x7fffc1ff; 0x7fffc201; 0x7fffc202;
   0x7fffc203; 0x7fffc205; 0x7fffc206; 0x7fffc207; 0x7fffc209; 0x7fffc20a; 0x7fffc20b; 0x7fffc20e; 0x7fffc20f;
   0x800b3db8; 0x800b3db9; 0x800b3dba; 0x800b3dbb; 0x800b3dbc; 0x800b659c].
Proof. reflexivity. Qed.

Section mrx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* No byte the call may store is a byte of the frame fr: the code and its callees read frame bytes after stores (the
   body byte at fa + 30, host_offset's and desk_named's body bytes), and the memcpy's source must lie apart from its
   destination. The plain contract's tframe_at puts the frame off the world. *)
Definition mrx_apart (fr : TI.tframe) : Prop :=
  forall x, mrx_wr x -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range mrx_wr, no
   meter charge, and X: a0 = r and the world relation at the model's world Bw'. *)
Definition transport_mrx_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs MRX_STK MRX_EV 0 mrx_wr
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_m_rx_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fr : TI.tframe) (n r : Z) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 (TI.tf_addr fr) -> YK11.getr regs 11 = w64 n ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MRX_STK -> spZ regs <= sp0 ->
    trans_tframe_at B lyc Sc W memc regs MRX_STK (Some fr) ->
    TI.tf_addr fr + n < 2 ^ 64 ->
    mrx_apart fr ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.m_rx_m timg_B (Some fr) Bw n = Some (Bw', r) ->
    st_nev S + k + MRX_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_mrx_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word, the read-only
   globals' shadow), OW's and M's shadow and the rest of the bcmp ranges' shadow groups (trans_mrx_cells), the two
   read-only facts of the record (they keep HOST, SPEC_BCAST and SPEC_OUI visible through the journal), the allocator
   and meter laws, G inside the image, outside the allocator's statics and outside errno (a donor callee keeps G:
   gx_call_cg), and the contracts of spec_read_frame, the bcmp wrapper, __asan_memcpy and the six program callees
   (pc order of their first call) give the contract at TB_m_rx. *)
Definition transport_m_rx_cg_holds_stmt : Prop :=
  transport_cells B -> trans_mrx_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_spec_read_frame_cg fx' rc B MT (transportb_sigma TB_spec_read_frame)) ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @transport_host_offset_cg fx' rc B MT (transportb_sigma TB_host_offset)) ->
  (forall fx' : YK11.FPState, @transport_m_set_cg fx' rc B MT (transportb_sigma TB_m_set)) ->
  (forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transportb_sigma TB_desk_named)) ->
  (forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transportb_sigma TB_m_wake)) ->
  (forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transportb_sigma TB_m_maybe_online)) ->
  (forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transportb_sigma TB_m_tick)) ->
  transport_m_rx_cg (transportb_sigma TB_m_rx).
End mrx.
