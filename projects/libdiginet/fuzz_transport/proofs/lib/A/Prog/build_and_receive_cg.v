(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SendctlCut.v, with its module names changed; 358 of its 430 lines of code are new or changed and 371 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickCut.v, with its module paths and module names changed; 203 of its 254 lines of code are new or changed and 379 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_tick_cg.v, with its module paths and module names changed; 82 of its 134 lines of code are new or changed and 202 lines of the source are left out. *)
(* build_and_receive_cg: the ASan walk contract of build_and_receive (fuzz/fuzz_transport.c:1027-1033, with
   spec_build_frame (fuzz/spec.h:228-247), spec_put16, spec_put32 and spec_sum inlined; model lib/TModel/TOps.v
   build_and_receive_m, with lib/TModel/TNeed.v spec_build_frame and TOps.v receive_m) on fuzz_transport.asan
   (e89be137db17) at 0x857e0 = transport_sigma TS_build_and_receive, size 804, as STATEMENTS only (no proof). It
   builds a frame in a class-5 side-stack frame (its one local, uint8_t frame[SPEC_MAX_FRAME]) and hands it to receive,
   a G-form callee that allocates (the malloc and free wrappers), so it is a G-form caller-journal walk in the
   allocator-calling form of lib/A/Prog/receive_cg.v: the caller's journal is lib/A/W_journalG.v ajournal_gx over
   G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS) with receive's two allocator events and receive's meter charge,
   and the statement is stated for call contexts CTX (receive's trace facts name them). The side-stack frame is
   diginet_session_tick_cg.v's: released by a CALL of __asan_stack_free_5, its local marked out of scope and in scope
   by calls of __asan_set_shadow_f8 / _00 (lib/A/Prog/TransportRtCg.v aset_shadow_realizes, astack_free_cls_realizes).
   build_and_receive itself stores no byte of G: every G byte the call changes is receive's.

   The contract. a0 = dstp, a1 = srcp (6-byte MACs), a2 = send and a3 = ack (their low 32 bits), a4 = retry,
   a5 = cmd, a6 = bodyp, a7 = len = the length of body. The 6 bytes at dstp and at srcp are dst and src (garr8), and
   both ranges are placed by trans_src_ok (the callers pass registered read-only globals: HOST, OTHER, SPEC_BCAST,
   DESK, DESK2, NOTDD, a TRANS_RO_RD range with trans_sh_any) outside this call's stack window; the len bytes at bodyp
   are body, and when len is not 0 they are placed by trans_src_ok (a heap block of the caller, a caller's side-stack
   frame, ...) outside this call's stack window. The memory relates to the world Bw by image A's world relation
   (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), g_fail_next Bw <= 1, and build_and_receive_m timg_A Bw
   a dst src send ack retry cmd body is not None for every address a the malloc can return (receive_cg.v
   recv_addr_ok). The read-only bytes receive's callees read are the image's (trans_rom_view_rd). The function returns
   to ra with the callee-saved registers kept, at most RECV_EV = 2 allocator events, the caller's blocks up to
   permutation (receive frees what it allocates), its side-stack frame released (the caller's frames exactly), the
   meter charged at most recv_cost n for the frame's length n, the bytes acall_kept_g G_HARNESS keeps (the bytes at
   or above alloc_ceiling outside the call's stack window [sp - BAR_STK, sp), the image bytes outside G, the owned
   statics and errno, the caller's block and frame bytes outside receive_cg.v recv_wr of the frame), and X: for the
   address a the malloc returned (recv_addr_ok a), build_and_receive_m timg_A Bw a dst src send ack retry cmd body =
   Some (Bw', tt), the world relation at Bw' and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/build_and_receive_c.v, an SR contract with the allocator
   state; the allocator part as receive_cg.v translates receive_c.v): h_binds, call_pre_k /
   call_post_k -> the G journal and transport_cg_post (receive's allocator call rules are receive's holds premises);
   bar_args: a0 = dstp, a1 = srcp, the low 32 bits of a2 = send with 0 <= send < 2 ^ 16, the low 32 bits of a3 = ack
   with 0 <= ack < 2 ^ 32, a4 = retry with 0 <= retry < 2 ^ 8, a5 = cmd with 0 <= cmd < 2 ^ 8, a6 = bodyp,
   a7 = length body, all kept; h_mac_at mem p mac (length 6, blk_data, read-only) -> length mac = 6, garr8 of mac at p,
   trans_src_ok of [p, p + 6) and decode_off_win at BAR_STK (the read-only part is the TRANS_RO_RD disjunct of
   trans_src_ok; the walk reads dst and src once each, by __asan_memcpy, whose own checks read their shadow hulls,
   hence trans_sh_any inside that disjunct); blk_data B mem bodyp body -> garr8 of body at bodyp; h_src -> when
   0 < len, trans_src_ok and decode_off_win at BAR_STK; the model premise (forall a, h_addr_ok a ->
   build_and_receive_m timg_plain Bw a ... <> None) verbatim at timg_A with recv_addr_ok; wmem -> tw_at;
   g_fail_next Bw <= 1 kept (receive's statement asks it and gives it back) and given back in X; relro_img ->
   trans_rom_view_rd; res_ok_slots / room_slots -> st_nev S + k + BAR_EV <= EV_MAX,
   blocks_bytes Sc + RECV_LIVE <= LIVE_MAX and mo_ok MT Sc T with recv_cost n <= T; the stack premises -> the
   journal's window premises; frm_zero is not needed. The post's bar_ret: the address a with h_addr_ok a and
   build_and_receive_m ... = Some (Bw', tt) -> X; the footprint (the world, the freed frame, the allocator's ctx) ->
   acall_kept_g over recv_wr of the frame (receive_cg.v's reading of the same footprint); wmem -> X's tw_at.
   Premises the plain contract does not have:
   - the call context: the frame-pointer chain ch at entry (YCbq.v achain at sp and s0) and raZ regs :: spine ch in
     CTX. At the call of receive, s0 = this function's entry sp (0x8581c), whose frame-pointer record holds the entry
     ra at s0 - 8 and the entry s0 at s0 - 16 (the prologue's stores at sp + 184 and sp + 176): receive's chain is that
     record followed by ch, or [] when the entry sp lies within 16 bytes of ly_top (YCbq.v achain's first case), so
     receive's contexts are BAR_RA_RECV :: c for c in CTX, and [BAR_RA_RECV] (bar_recv_ctx CTX).
   - the five frame counts: receive asks count_cid 5 (frames) + 1 < fs_frames 5 at its call state, where the frames
     are this function's own class-5 frame :: frames Sc, hence count_cid 5 (frames Sc) + 2 < fs_frames 5 here; the other
     four (classes 1, 4, 0 and 2 + 2) are receive's, unchanged since the own frame is of class 5.
   - the four run invariants on its own Bw: (1) TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <=
     TC.SPEC_MAX_FRAME, (2) TW.S_queue_len Bw i <= DIGINET_CMD_MAX_LEN for i < TW.S_queued Bw, (4) every PENDING
     command g_cmd[s], s < g_ncmd Bw, has Cmd_len <= SPEC_CMD_MAX, (5) 1 <= TW.S_cfg_max_cmds Bw and 1 <=
     TW.S_cfg_max_body Bw; and (3), receive_cg.v recv_dn_each at the frame's bytes (by_poll = 0, pf = 0). receive asks
     them at its call world, which is Bw: this function stores no byte of G before the call (its stores go to its own
     machine frame, its own side-stack frame and that frame's shadow). Beside (2) and (4) go their bounds,
     TW.S_queued Bw <= QUEUE_MAX and TW.g_ncmd Bw <= CMDS_MAX (without them an index i or s past the queue or g_cmd
     makes the accessors read other world bytes, which a callee may write); receive asks them beside (2) and (4) too,
     and this function passes them on to receive at the same world.
   - in the holds statement: the record facts trans_g_unowned, trans_g_no_errno, trans_ro_rd_unowned and
     trans_rom_no_errno (they carry the placement of dst, src and body across the stack malloc: DgnTransportCg.v
     trans_src_ok_inner, the stack malloc adding the own frame and keeping the blocks, the ranges' bytes kept by its
     acall_kept and their decode_rd_ok by trans_rd_ok_sh, the ranges apart from the fresh frame and that frame's
     shadow: trans_src_ok_disj_own; the TRANS_RO_RD bytes and G across the stack malloc, the shadow fills, the
     memcpys and the memset: trans_ro_rd_scoped, gx_kept_of_acall_kept with G_HARNESS_gx_ok and G_HARNESS_gx_noerrno),
     and the allocator, meter and side-stack laws.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   804 code bytes are equal in both files), 201 words:
     0x857e0 - 0x85818 sp = sp - 192; 0x857e4 stores 8 zero bytes at sp; ra at sp + 184, s0 .. s11 at sp + 176 ..
                      sp + 88, loaded back at 0x85ac8 - 0x85af8.
     0x8581c          s0 = sp + 192 (the entry sp, kept to 0x85ac4).
     0x85820 - 0x85824 sp = sp & -32 (at most 0x10 below entry - 192); s1 = the realigned sp.
     0x85828 - 0x85830 s3 = a7 (len); the 8-byte store of a6 (bodyp) at s1 + 56; s7 = a3 (ack).
     0x85834 - 0x85848 a3 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), a6 = the 8-byte load of the
                      GOT word 0xa4090 (it holds 0xac9f8); the 4-byte load of the flag word at 0xaca00; s5 = the 8-byte
                      load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7.
     0x8584c - 0x8585c s6 = a0 (dstp); the 8-byte stores of a5 (cmd) at s1 + 48, a4 (retry) at s1 + 40, a2 (send) at
                      s1 + 32 and a1 (srcp) at s1 + 24 (its own machine frame).
     0x85860 - 0x85874 the flag word = 0 goes to 0x85874 (s4 = 0); transport_cells row 6 gives 1. a0 = 0x6a0 = 1696 and
                      the call of __asan_stack_malloc_5 (frame_alloc_5, 0x3dd04 = transport_sigma
                      TS___asan_stack_malloc_5) at 0x85868, return address 0x8586c: a class-5 side-stack frame
                      (fs_frame_bytes 5 = 2048 bytes); s4 = the result.
     0x85878 - 0x85898 s2 = s4; s4 <> 0 goes to 0x8589c. The real-stack arm (s4 = 0): s2 = (sp - 1696) & -32 and a probe
                      loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s2), then sp = s2. With
                      count_cid 5 (frames Sc) + 2 < fs_frames 5 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s2 = s4.
     0x8589c - 0x858a0 the 8-byte store of frame at s1 + 80 (its own machine frame); s10 = frame + 32 (frame[]).
     0x858a4 - 0x858c8 the frame header: 0x41b58ab3 at frame, the description string 0x17eea ("1 32 1514 10
                      frame:1030": one variable, 1514 bytes at frame + 32) at frame + 8, the function's address 0x857e0
                      at frame + 16. s9 = (frame >> 3) + 0x7fff8000 (0x858b0, 0x858d0).
     0x858cc - 0x858e0 the frame's shadow bytes 0..3 = 0xf1 (the left guard) by plain stores.
     0x858e4 - 0x858f0 s11 = s9 + 4 (the shadow byte of frame + 32), a0 = s11, a1 = 0xbe = 190; the call of
                      __asan_set_shadow_f8 (meta_fill_f8, 0x55390 = transport_sigma TS___asan_set_shadow_f8) at 0x858f0,
                      return address 0x858f4: shadow bytes 4..193 = 0xf8 (frame[] out of scope).
     0x858f4 - 0x8593c shadow bytes 194..211 = 0xf3 (the right guard; plain stores at s9 + 0xc2 .. s9 + 0xd3).
     0x85940 - 0x85948 a1 = 0xbd = 189, a0 = s11; the call of __asan_set_shadow_00 (meta_fill_00, 0x55270 =
                      transport_sigma TS___asan_set_shadow_00) at 0x85948, return address 0x8594c: shadow bytes
                      4..192 = 0 (frame[0 .. 1512) in scope).
     0x8594c - 0x85954 shadow byte 193 = 2 (the plain store at s9 + 0xc1: frame[1512 .. 1514) in scope).
     0x85958 - 0x85960 s8 = len when 30 < len (unsigned), else 30: s8 = max (len, 30), so s8 + 30 = n, the frame's
                      length (TNeed.v spec_build_frame, :232).
     0x85964 - 0x85970 a0 = frame + 32, a1 = dstp, a2 = 6; the call of __asan_memcpy (checked_memcpy, 0x523b0 =
                      transport_sigma TS___asan_memcpy) at 0x85970, return address 0x85974: frame[0 .. 6) = dst (:234).
     0x85974 - 0x85984 s6 = frame + 38 (frame[6]); a0 = frame + 44 (frame[12]), a1 = 0, a2 = s8 + 18 = n - 12; the call
                      of __asan_memset (checked_memset, 0x5284c = transport_sigma TS___asan_memset) at 0x85984, return
                      address 0x85988: frame[12 .. n) = 0 (:233, the bytes the two MAC memcpys do not cover; the body
                      memcpy at 0x85a74 writes frame[30 .. 30 + len) after it).
     0x85988 - 0x85994 a0 = frame + 38, a1 = srcp (the 8-byte load at s1 + 24), a2 = 6; the call of __asan_memcpy at
                      0x85994, return address 0x85998: frame[6 .. 12) = src (:235).
     0x85998 - 0x859b4 plain 1-byte stores: frame[12] = 0x88, frame[13] = 0x5f (:236, SPEC_ETHERTYPE big-endian),
                      frame[14] = bits 8 .. 15 and frame[15] = bits 0 .. 7 of len + 16 (:237).
     0x859b8 - 0x859bc a7 = 0 (the sum); len = 0 goes to 0x85a08.
     0x859c0 - 0x859f8 the sum of body (spec_sum, :238), one byte at a time: a1 = bodyp (the 8-byte load at s1 + 56),
                      a2 = a0 = bodyp, a3 = len; at each byte the instrumented check of the 1-byte load at a0 (the
                      shadow byte k at (a0 >> 3) + 0x7fff8000, a signed 1-byte load; k = 0 goes on; else (a0 & 7) < k
                      (signed) goes on; else the error path at 0x85a04), the 1-byte load at a2 added to a7, a3 - 1,
                      a0 + 1, a2 + 1, until a3 = 0; then to 0x85a0c.
     0x85a08          a1 = bodyp (the len = 0 path).
     0x85a0c - 0x85a64 plain 1-byte stores into frame[16 .. 30) (s10 + 0x10 .. s10 + 0x1d): frame[16] = bits 8 .. 15 and
                      frame[17] = bits 0 .. 7 of the sum (put16 of spec_sum body, which is the sum cut to 16 bits);
                      frame[18] = frame[19] = 0, frame[20] = bits 8 .. 15 and frame[21] = bits 0 .. 7 of send (the
                      8-byte load at s1 + 32) (:239: put32 send, whose two high bytes are 0 since send < 2 ^ 16);
                      frame[22 .. 26) = the four bytes of ack (s7), high first (:240); frame[26] = 0, frame[27] = the low
                      byte of retry (the load at s1 + 40) (:241: put16 retry, retry < 2 ^ 8); frame[28] = the low byte
                      of cmd (the load at s1 + 48) (:242); frame[29] = 1 (:243, ncmds = 1).
     0x85a68 - 0x85a74 len = 0 goes to 0x85a78; else a0 = frame + 62 (frame[30]), a1 = bodyp, a2 = len; the call of
                      __asan_memcpy at 0x85a74, return address 0x85a78: frame[30 .. 30 + len) = body (:244-245).
     0x85a78 - 0x85a88 a1 = s8 + 30 = n, a0 = frame + 32, a2 = 0, a3 = 0; the call of receive (0x837d0 =
                      transport_sigma TS_receive) at 0x85a88, return address 0x85a8c = BAR_RA_RECV (:1032).
     0x85a8c - 0x85a94 a1 = 190, a0 = s11; the call of __asan_set_shadow_f8 at 0x85a94, return address 0x85a98: shadow
                      bytes 4..193 = 0xf8 (frame[] out of scope).
     0x85a98 - 0x85aa0 the header word 0x45e0360e stored at frame.
     0x85aa4          s4 = 0 goes to 0x85ab8 (the real-stack arm; not taken).
     0x85aa8 - 0x85ab0 a1 = 0x6a0 = 1696, a0 = s4 = frame; the call of __asan_stack_free_5 (frame_release_5, 0x3df10 =
                      transport_sigma TS___asan_stack_free_5) at 0x85ab0, return address 0x85ab4: the frame's 256
                      shadow bytes = 0xf5, its flag byte left out of the bytes kept (TransportRtCg.v
                      astack_free_cls_realizes); to 0x85ac4.
     0x85ab8 - 0x85ac0 the real-stack arm's release: a1 = 0xd4 = 212, a0 = s9, the call of __asan_set_shadow_00 at
                      0x85ac0 (not taken).
     0x85ac4 - 0x85b00 sp = s0 - 192, ra and s0 .. s11 loaded back, sp = sp + 192, return. a0 .. a7 at the return are not
                      stated (build_and_receive returns void).
   No tail jump: the calls are jal with link (the stack malloc at 0x85868, the shadow fills at 0x858f0 and 0x85a94 to
   __asan_set_shadow_f8 and at 0x85948 and 0x85ac0 to __asan_set_shadow_00, the memcpys at 0x85970, 0x85994 and
   0x85a74, the memset at 0x85984, the error-path call at 0x85a04, receive at 0x85a88, the stack free at 0x85ab0);
   there is no jalr; every j is inside the function, and the function's own return is the ret at 0x85b00.
   The model and the code: the frame's n bytes at frame + 32 when receive is called are bar_frame dst src send ack
   retry cmd body = the bytes of TNeed.v spec_build_frame dst src send ack retry cmd 1 body 0, written statement by
   statement as above (the memset of :233 is cut to the bytes the two memcpys do not write; frame[n .. 1514) is not
   read); receive is called with them, by_poll = 0 and poll_flags = 0, as build_and_receive_m calls receive_m
   (bar_model). The model's None case SPEC_MAX_BODY < len is ruled out by the model premise (it is not None for the
   addresses recv_addr_ok names), so len <= 1484 and n <= 1514 = SPEC_MAX_FRAME: every frame store and the memset and
   the body memcpy stay inside frame[0 .. 1514).
   Error path (1 call; no abort) and the facts that rule it out:
     TS___asan_report_load1 0x594c8 (errpath_load1) at 0x85a04, the check of each body byte's 1-byte load (bodyp + i,
     i < len): when 0 < len the range [bodyp, bodyp + len) is placed by trans_src_ok, which gives decode_rd_ok at the
     call state (its shadow says every byte addressable), carried to the loop across the stack malloc (the record facts
     above: trans_src_ok_inner, trans_rd_ok_sh, trans_src_ok_disj_own), the shadow fills and the memcpys / memset
     (they write only this function's frame and its shadow, and the ESTACK bytes below sp, which decode_off_win keeps
     the body out of).
     The three memcpys' and the memset's own checks (aintrin_realizes' pre, through TransportGCg.v gx_intrin_at): each
     destination lies in frame[0 .. 1514) of the frame this function took, whose shadow is 0 since the fill at 0x85948
     and the store at 0x8594c, with its hull visible (astack_malloc_realizes' zero_shadow and the frame's shadow
     bytes), and each destination byte is a byte of the journal's own frame list after the stack malloc
     (transport_twr_ok_g), not owned, not in the ESTACK bytes below sp; the sources [dstp, dstp + 6), [srcp, srcp + 6)
     and [bodyp, bodyp + len) are readable by trans_src_ok (decode_rd_ok, with trans_sh_any for a read-only global) at
     the call state and lie apart from the destination (a caller's range is not a byte of a frame taken after it) and
     outside the ESTACK window (decode_off_win); each length is below 2 ^ 32.
     The shadow fills' own premise (aset_shadow_realizes; the calls at 0x858f0, 0x85948 and 0x85a94, and the one at
     0x85ac0 that the count premise excludes): the range [shadow_addr frame + 4, + 190) (or + 189) lies inside
     [shadow_addr frame, shadow_addr frame + fs_frame_bytes 5 / 8) = the frame's 256 shadow bytes, and the frame is a
     live frame of the state.
     The stack free's own premise (astack_free_cls_realizes): a0 = frame, the frame is live, and the word at
     frame + 2040 still holds the flag byte's address (astack_malloc_realizes' rdword; no store of this function or of
     receive writes it: frame[] ends at frame + 1546, the shadow stores go to the shadow band, and receive's
     acall_kept_g keeps the bytes of this frame outside its written range recv_wr, by its frame clause).
   Writes: its own machine frame (the 8 zero bytes at entry sp - 192 (0x857e4), ra and s0 .. s11 at sp + 88 ..
   sp + 184, and s1 + 24 .. s1 + 80 after the realignment); its own side-stack frame (the header and frame[0 .. n)),
   that frame's shadow bytes and its flag byte; receive's (receive_cg.v recv_wr of the frame: bytes of G). No byte of
   a caller's frame or block is written, so recv_wr (bar_frame ...) is the written range. The G kit for the own frame
   is diginet_session_tick_cg.v's (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g for the
   callee, dkg_frame_al64, gx_intrin_at for the memcpys and the memset, dk_kept_frame_byte_g; CanKit.v
   can_stack_malloc_at read inside the G journal through gx_lift), with the shadow fills and the stack free as steps
   whose written bytes are the own frame's shadow bytes and its flag byte.
   Callee texts assumed (pc order of their first call), and what supplies each premise:
     __asan_stack_malloc_5 as astack_malloc_realizes ... BAR_CID (with pc_stack_malloc (as_code B) BAR_CID =
       transport_sigma TS___asan_stack_malloc_5): count_cid 5 (frames Sc) < fs_frames 5 from the count premise.
     __asan_set_shadow_f8 as TransportRtCg.v aset_shadow_realizes (transport_sigma TS___asan_set_shadow_f8) 0xf8,
       calls at 0x858f0 and 0x85a94: ecall_pre from the journal; the own frame is live; a0 = shadow_addr frame + 4,
       a1 = 190, and 4 + 190 <= fs_frame_bytes 5 / 8 = 256.
     __asan_set_shadow_00 as TransportRtCg.v aset_shadow_realizes (transport_sigma TS___asan_set_shadow_00) 0, the call
       at 0x85948 (a0 = shadow_addr frame + 4, a1 = 189). The call at 0x85ac0 is on the real-stack arm, which the
       count premise excludes.
     __asan_memcpy as aintrin_realizes ... OCpy (transport_sigma TS___asan_memcpy), calls at 0x85970, 0x85994 and
       0x85a74 (above).
     __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset), the call at 0x85984 (above).
     receive as receive_cg.v transport_receive_cg at transport_sigma TS_receive for the contexts bar_recv_ctx CTX (the
       call at 0x85a88; a G-form callee in the same G journal): the journal at the call state (the own frame live);
       ra = 0x85a8c (ret_ok, 4096 <= ra); gp, tp kept; a0 = p = frame + 32, a1 = n = the length of bar_frame (s8 + 30),
       a2 = by_poll = 0 (-2 ^ 31 <= 0 < 2 ^ 31), the low 32 bits of a3 = pf = 0; achain at the call's sp and s0 =
       the entry sp (above) and its context in bar_recv_ctx CTX; sp' = s1 is 32-aligned, sp0 - STK <= sp' - RECV_STK
       (BAR_STK = 208 + RECV_STK), sp' <= sp0; n <= 1514 <= 65535; garr8 of bar_frame at p (the stores above);
       trans_src_ok of [p, p + n) by decode_in_fake at the call state (inside the 2048 bytes of the own frame) with
       decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4 .. 193 of the frame 0, .., 0, 2 since
       0x85948 - 0x85954, their hull visible), decode_off_win at RECV_STK (the frame lies below alloc_ceiling,
       receive's window above it); tw_at at Bw and g_fail_next Bw <= 1 (no store of G before the call:
       gx_kept_of_acall_kept across the stack malloc, and the fills, memcpys and memset write only the own frame);
       forall a, recv_addr_ok a -> receive_m timg_A Bw a (bar_frame ...) 0 0 <> None: the model premise through
       bar_model (len <= SPEC_MAX_BODY on the Some side); trans_rom_view_rd at the call memory (the stack malloc's
       acall_kept, the fills, the memcpys and the memset keep every TRANS_RO_RD byte: trans_ro_rd_scoped); the four
       run invariants with the two bounds and recv_dn_each at Bw (the premises); the five counts (above);
       st_nev S + k + RECV_EV <= EV_MAX (BAR_EV = RECV_EV; the stack malloc records no event); blocks_bytes Sc +
       RECV_LIVE <= LIVE_MAX (the stack malloc keeps the blocks); mo_ok MT at the call state with the cost: the
       premise, carried across the stack malloc's st_fs change (ameter_fs_laws). Its post: at most two events, the
       blocks up to permutation, the frames of the call state, acall_kept_g over recv_wr of the frame, mo_le of
       recv_cost n, and X: an address a with recv_addr_ok a, receive_m timg_A Bw a (bar_frame ...) 0 0 =
       Some (Bw', tt) (so build_and_receive_m ... = Some (Bw', tt) by bar_model), tw_at at Bw' and
       g_fail_next Bw' <= 1.
     __asan_stack_free_5 as TransportRtCg.v astack_free_cls_realizes (transport_sigma TS___asan_stack_free_5)
       BAR_CID, the call at 0x85ab0 (above).
   Each callee's own record facts are premises of its holds statement.
   Stack: 192 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the shadow fills, the memcpys, the memset, the stack free) or receive's
   RECV_STK: BAR_STK = 208 + RECV_STK (bar_stk_eq).

   The callers (each with the return address after its jal): LLVMFuzzerTestOneInput only, at two sites, each an
   inlined copy of op_frame (:1035-1050) or op_announce (:1052-1066); LLVMFuzzerTestOneInput_cg.v names the two
   return addresses (CTX_build_and_receive) and the arguments. Each supplies its G journal, the chain and its context
   in CTX, the placement of dst, src and body, tw_at, g_fail_next, the model premise, trans_rom_view_rd, the run
   invariants, recv_dn_each, the five frame counts (it holds a class-2 frame of its own) and the allocator budget. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg on_announce_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TNeed TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* build_and_receive's entry, a direct call target. *)
Lemma build_and_receive_at : transport_sigma TS_build_and_receive = 0x857e0.
Proof. reflexivity. Qed.

(* build_and_receive's frame (`sp = sp - 192` at its entry), the at most 0x10 bytes of `sp = sp & -32` (0x85820) below
   it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_5,
   __asan_set_shadow_f8 / _00, __asan_memcpy, __asan_memset and __asan_stack_free_5 (YG0d.v ecall_pre), receive's
   RECV_STK. *)
Definition BAR_FRAME : Z := 192.
Definition BAR_ALIGN : Z := 0x10.
Definition BAR_STK : Z := BAR_FRAME + BAR_ALIGN + Z.max ESTACK RECV_STK.
Lemma bar_stk_eq : BAR_STK = BAR_FRAME + BAR_ALIGN + RECV_STK.
Proof. reflexivity. Qed.
(* The allocator events: receive's malloc and free; the class-5 stack malloc, the shadow fills and the stack free
   record none (YG00.v stack_malloc, stack_free). *)
Definition BAR_EV : Z := RECV_EV.
Lemma bar_ev_eq : BAR_EV = 2.
Proof. reflexivity. Qed.
(* The side-stack class (a0 = 1696 at 0x85864, the call of __asan_stack_malloc_5 at 0x85868): the class
   diginet_session_poll and diginet_session_tick take below it, inside receive; the classes of receive's other count
   premises are others. *)
Definition BAR_CID : Z := 5.
Lemma bar_cid_callees :
  BAR_CID = POLL_CID /\ SRX_CID = 1 /\ ONANN_CID = 4 /\ SENDDATA_CID = 0 /\ ONDATA_CID = 2.
Proof. repeat split; reflexivity. Qed.
(* The return address of its call of receive (the jal at 0x85a88, 0x2a8 bytes after the entry). *)
Definition BAR_RA_RECV : Z := transport_sigma TS_build_and_receive + 0x2ac.
Lemma bar_ra_recv_at : BAR_RA_RECV = 0x85a8c.
Proof. reflexivity. Qed.
(* The length of each MAC it copies (dst and src, :234-235). *)
Definition BAR_MAC : Z := 6.

(* The n bytes spec_build_frame writes into frame[] (:1031, TNeed.v), the bytes receive is handed. *)
Definition bar_frame (dst src : list byte) (send ack retry cmd : Z) (body : list byte) : list byte :=
  fst (TN.spec_build_frame dst src send ack retry cmd 1 body 0).

(* The model, as the code runs it: the body bound, then receive_m of the frame's bytes with by_poll = 0 and
   poll_flags = 0 (TOps.v build_and_receive_m, :1031-1032). *)
Lemma bar_model : forall (I : TI.timg) (Bw : list byte) (a : Z) (dst src : list byte) (send ack retry cmd : Z)
    (body : list byte),
  TOP.build_and_receive_m I Bw a dst src send ack retry cmd body =
  if TC.SPEC_MAX_BODY <? Z.of_nat (length body) then None
  else TOP.receive_m I Bw a (bar_frame dst src send ack retry cmd body) 0 0.
Proof. intros. reflexivity. Qed.

(* receive's call contexts: the return address BAR_RA_RECV followed by this function's frame-pointer record's return
   address (the entry's ra) and the entry chain's (c in CTX), or by nothing when the entry sp lies within 16 bytes of
   ly_top. *)
Definition bar_recv_ctx (CTX : list (list Z)) : list (list Z) := [BAR_RA_RECV] :: map (cons BAR_RA_RECV) CTX.

Section bar. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with at most BAR_EV events, the written range
   receive_cg.v recv_wr of the frame's bytes, the meter charged at most recv_cost of the frame's length, and X: for
   the address a receive's malloc returned, the model's world Bw' of build_and_receive_m at a, the world relation at it
   and g_fail_next Bw' <= 1. transport_cg_post states the caller's blocks up to permutation and frames S2 = frames Sc:
   the frame this function takes is released (by the call of __asan_stack_free_5). *)
Definition transport_bar_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw : list byte) (dst src : list byte) (send ack retry cmd : Z) (body : list byte)
    : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    BAR_STK BAR_EV (recv_cost MT (Z.of_nat (length (bar_frame dst src send ack retry cmd body))))
    (recv_wr (bar_frame dst src send ack retry cmd body))
    (fun regs2 W2 mem2 =>
       exists (a : Z) (Bw' : list byte),
         recv_addr_ok a /\ TOP.build_and_receive_m timg_A Bw a dst src send ack retry cmd body = Some (Bw', tt) /\
         tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a0, for call contexts CTX (the entry's return address followed by the
   frame-pointer chain's), in the G-form caller-journal form. *)
Definition transport_build_and_receive_cg (a0 : Z) (CTX : list (list Z)) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (dstp srcp bodyp send ack retry cmd T : Z) (dst src body : list byte) (Bw : list byte) ch,
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 dstp -> YK11.getr regs 11 = w64 srcp ->
    bv_unsigned (YK11.getr regs 12) mod 2 ^ 32 = send -> bv_unsigned (YK11.getr regs 13) mod 2 ^ 32 = ack ->
    YK11.getr regs 14 = w64 retry -> YK11.getr regs 15 = w64 cmd ->
    YK11.getr regs 16 = w64 bodyp -> YK11.getr regs 17 = w64 (Z.of_nat (length body)) ->
    @achain rc lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - BAR_STK -> spZ regs <= sp0 ->
    0 <= send < 2 ^ 16 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 8 -> 0 <= cmd < 2 ^ 8 ->
    length dst = 6%nat -> garr8 segs (mrestrict (w_H W) memc) dstp (TW.zs dst) ->
    trans_src_ok B lyc Sc W memc dstp BAR_MAC -> decode_off_win regs BAR_STK dstp BAR_MAC ->
    length src = 6%nat -> garr8 segs (mrestrict (w_H W) memc) srcp (TW.zs src) ->
    trans_src_ok B lyc Sc W memc srcp BAR_MAC -> decode_off_win regs BAR_STK srcp BAR_MAC ->
    garr8 segs (mrestrict (w_H W) memc) bodyp (TW.zs body) ->
    ((0 < length body)%nat ->
       trans_src_ok B lyc Sc W memc bodyp (Z.of_nat (length body)) /\
       decode_off_win regs BAR_STK bodyp (Z.of_nat (length body))) ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    (forall a, recv_addr_ok a -> TOP.build_and_receive_m timg_A Bw a dst src send ack retry cmd body <> None) ->
    trans_rom_view_rd W memc ->
    (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    TW.S_queued Bw <= TC.QUEUE_MAX ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    TW.g_ncmd Bw <= TC.CMDS_MAX ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    recv_dn_each timg_A Bw (bar_frame dst src send ack retry cmd body) 0 0 ->
    count_cid BAR_CID (frames Sc) + 2 < fs_frames BAR_CID ->
    count_cid SRX_CID (frames Sc) < fs_frames SRX_CID ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID ->
    st_nev S + k + BAR_EV <= EV_MAX -> blocks_bytes Sc + RECV_LIVE <= LIVE_MAX ->
    mo_ok MT Sc T -> recv_cost MT (Z.of_nat (length (bar_frame dst src send ack retry cmd body))) <= T ->
    SRr segs W (@cfg_at fx segs a0 regs memc mdc)
      (transport_bar_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw dst src send ack retry cmd body).

(* The statement the walk will prove: the class-5 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the record facts that no byte of G and no TRANS_RO_RD byte is an
   owned static or errno (they carry the placement of dst, src and body across the stack malloc's acall_kept, and G
   and the TRANS_RO_RD bytes across it, the shadow fills, the memcpys and the memset; DgnTransportCg.v
   G_HARNESS_gx_ok / G_HARNESS_gx_noerrno give gx_ok and gx_noerrno from the first two), the allocator, meter and
   side-stack laws (frame_flag_lawP: the stack free's flag byte is an owned static; astack_free_law is not taken, since
   this function releases its frame by the call, not by an inline flag store), and the contracts of
   __asan_stack_malloc_5, __asan_set_shadow_f8, __asan_set_shadow_00, __asan_memcpy, __asan_memset, receive (at the
   contexts bar_recv_ctx CTX) and __asan_stack_free_5 (pc order of their first call: 0x85868, 0x858f0, 0x85948,
   0x85970, 0x85984, 0x85a88, 0x85ab0) give the contract at TS_build_and_receive for the contexts CTX. *)
Definition transport_build_and_receive_cg_holds_stmt (CTX : list (list Z)) : Prop :=
  pc_stack_malloc (as_code B) BAR_CID = transport_sigma TS___asan_stack_malloc_5 ->
  transport_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B BAR_CID) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_f8) 0xf8) ->
  (forall fx' : YK11.FPState,
     @aset_shadow_realizes fx' rc segs B (transport_sigma TS___asan_set_shadow_00) 0) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_receive_cg fx' rc B MT (transport_sigma TS_receive) (bar_recv_ctx CTX)) ->
  (forall fx' : YK11.FPState,
     @astack_free_cls_realizes fx' rc segs B (transport_sigma TS___asan_stack_free_5) BAR_CID) ->
  transport_build_and_receive_cg (transport_sigma TS_build_and_receive) CTX.
End bar.
