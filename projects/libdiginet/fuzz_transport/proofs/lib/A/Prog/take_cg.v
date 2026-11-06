(* take_cg: the ASan walk contract of take (transport/src/diginet_session.c:353-386; model lib/TModel/TSess0.v take_m,
   take_loop_m, take_tail_m) on fuzz_transport.asan (e89be137db17) at 0x8a508 = transport_sigma TS_take, size 1228, as
   STATEMENTS only (no proof). It stores into g_s (queue entries and queued), a harness global, and calls
   __asan_memcpy and diginet_body_check, so it is a G-form caller-journal walk: the caller's journal is
   lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the
   post is lib/A/Prog/TransportGCg.v transport_cg_post_out with the two out cells [(blp, 8); (hdp, 4)] (below), the
   form check_latest_sent_cg.v's post takes with its one out cell.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = bp, the caller's uint8_t body[1484]; a2 = blp, the
   caller's size_t body_len (8 bytes); a3 = allow, the int allow_display; a4 = hdp, the caller's int has_display (4
   bytes). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read
   through aview), and take_m Bw allow = Some (Bw', (body, len, hd, taken)). The function returns to ra with
   a0 = Z_to_bv 64 (bv_swrap 32 taken) (the 32-bit taken, sign-extended), the callee-saved registers kept, no allocator
   event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS keeps
   (read at the memory with the 12 bytes at blp and hdp put back), the world relation at Bw', g_fail_next Bw' <= 1,
   the 1484 bytes X at bp with firstn len X = firstn len body, the 8 bytes at blp holding len and the 4 bytes at hdp
   holding hd (little-endian).
   The translation from the plain contract (lib/Prog/T/take_c.v): a0 = W_BASE_PLAIN + OFF_g_s ->
   a0 = TA_g_s; rw_cells m bp [CB 1484 J] and arg_blk sp FRAME bp 1484 -> 0 < bp, decode_in_fake (bp lies in a live
   side-stack frame of the caller), the write right transport_twr_ok_g, decode_rd_ok (the bytes visible, the range
   marked usable: __asan_memcpy's destination check and diginet_body_check's reads), decode_off_win (off_window) and
   the range apart from G (off_world); rw_cells / arg_blk of blp and of hdp -> transport_twr_ok_g, decode_rd_ok (the
   instrumented checks of blp and hdp read their shadow bytes), decode_off_win and the range apart from G; blp mod 8 = 0
   and hdp mod 4 = 0 kept; the three blk_sep -> the three disjunctions; -2^31 <= allow < 2^31 kept; wmem -> tw_at;
   g_fail_next B <= 1 kept (take neither reads nor stores it; its caller diginet_session_tick needs it after the call,
   for send_data); take_m verbatim. Dropped: the contents J, JL, JH (the code reads no byte of them before it stores
   it: hdp is stored at 0x8a56c before its load at 0x8a6ec; blp is only stored; diginet_body_check reads [bp, bp + len
   + c->len), whose first len bytes the earlier taken rounds copied and the rest this round's copy); 0 < blp, 0 < hdp
   (the code never compares them with 0; decode_rd_ok gives 0 <= q and amem_range) and p + n < 2^64 (decode_rd_ok:
   q + n <= 2^63); stk / lo / w_off_stack become the journal's window premises; mem_inv is dropped. The post: munch ->
   acall_kept_g with the written range take_wr; wmono / stk / mem_inv -> the journal; wmem -> tw_at at Bw'; the
   rw_cells of bp, blp and hdp -> garr8 at mem2.

   Premises the plain contract does not have:
   - count_cid 2 (frames Sc) < fs_frames 2: diginet_body_check's statement asks it (it takes a class-2 side-stack
     frame). take takes no side-stack frame and __asan_memcpy keeps the allocator state, so the frames at 0x8a68c are
     Sc.
   - every queued command has len <= 24 (DIGINET_CMD_MAX_LEN, the size of its bytes array), as check_latest_queue_cg.v
     states it: forall i, 0 <= i < S_queued Bw -> S_queue_len Bw i <= 24. The __asan_memcpy at 0x8a67c copies c->len
     bytes from &g_s.queue[i] (memcpy (body + len, c->bytes, c->len), :365), after the three fits tests pass. The model
     bounds i (< 512: None at i >= 512) and len + c->len (<= 1484: None when the fits tests pass and 1484 < len +
     c->len), but not c->len against the entry, and reads the plain world, where the bytes after g_s are g_cmd's. On
     image A g_s's payload (18264 bytes) is followed by bytes the runtime marks unusable, so for i >= 508 a c->len that
     leaves the payload (above 152 for g_s.queue[511]: 1760 + 32 * 511 + 152 = 18264) makes the copy's source check fail
     (the error path); with c->len <= 24 the source lies inside the entry's 32 bytes. diginet_body_check, take's only
     program callee, carries none of the run invariants (check_inflight_retry's, check_latest_queue's,
     check_state_data's, check_latest_sent's). The fields the premise reads are those of take's entry world: the code
     reads g_s.queue[i] in round i only, every store before round i is to g_s.queue[kept] with kept < i (the refusal
     copy) and queued is stored only at the end (0x8a8dc), so the len byte of entry i at round i is S_queue_len Bw i,
     and the loop bound is S_queued Bw. The plain side's run invariant has it: lib/TSim/TickTakeQ.v tt_sq_ok (from
     lib/TSim/Agree.v agree_q: d1_entry, d2_cmd, d4 for the raw mode) gives 1 <= len <= 24 for every entry below
     g_s.queued; the caller supplies it from that invariant.
   - g_s.cfg.max_cmds >= 1 and g_s.cfg.max_body >= 1 (1 <= S_cfg_max_cmds Bw, 1 <= S_cfg_max_body Bw). The tail copy
     at 0x8a888 moves queue[j] to queue[kept], j = i + 1 at its first turn, and kept = i + 1 when every round 0 .. i
     was refused; then source and destination are the same 32 bytes, which aintrin_realizes OCpy (YG0d.v) excludes
     (d + n <= x or x + n <= d). take_m allows it: the break test (taken1 = max_cmds or len1 = max_body) holds after
     refused rounds only when max_cmds = 0, or max_body = 0 with len still 0. With both fields >= 1 the break needs a
     taken round, so kept <= i < j, and each tail turn adds 1 to both. take stores no byte of g_s.cfg, so the fields
     are Bw's in every world of the walk. The plain side's run invariant has it: lib/TSim/Agree.v agree_cfg
     a1_max_cmds (1 <= Cfg_max_cmds <= 255) and a1_max_body (24 <= Cfg_max_body <= 1484), read at g_s.cfg by
     lib/TSim/TickTakeW.v tk_cfg_max_cmds / tk_cfg_max_body; the caller supplies it from that invariant.
   - The bound of the body copy: [bp + len, bp + len + c->len) lies in [bp, bp + 1484) by the model (the None case
     above), so the destination check of the copy at 0x8a67c and the range diginet_body_check reads are inside the
     1484 bytes; no premise is added for it.

   The post is TransportGCg.v transport_cg_post_out with the two out cells [(blp, 8); (hdp, 4)] (check_latest_sent_cg.v
   uses it with one): blp and hdp lie in the caller's MACHINE frame (diginet_session_tick passes its realigned sp + 80
   and sp + 76, below), above this call's stack window, where acall_kept_g's first clause keeps every byte at or above
   alloc_ceiling whatever the written range is. transport_cg_post_out reads acall_kept_g at the memory with the 8 bytes
   at blp and the 4 bytes at hdp put back as they were at the call (W_journalG.v gover [(blp, 8); (hdp, 4)] mem2
   memc): every byte acall_kept_g keeps is kept but those 12, and X says what they hold. The journal already allows
   the stores (awr_ok_x: transport_twr_ok_g). bp lies in the caller's class-5 side-stack frame (decode_in_fake), below
   alloc_ceiling, so acall_kept_g's frame clause admits its writes through the written range take_wr; it is not an
   out cell.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1228 code bytes are equal in both files), 307 words:
     0x8a508 - 0x8a53c sp = sp - 224; ra at sp + 216, s0 .. s11 at sp + 208 .. sp + 120, loaded back at 0x8a8fc -
                      0x8a92c (sp = sp + 224 at 0x8a930, return at 0x8a934). No side-stack frame, no frame pointer, no
                      realignment. 0x8a540 / 0x8a544 allow at sp + 64, bp at sp + 48.
     0x8a548 - 0x8a550 a7 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte access
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; for the 8-byte store at blp any k <> 0 goes to
                      the error path; else the error path.
     0x8a554 - 0x8a56c the check of the 4-byte store at hdp (its shadow address kept at sp + 24); s7 = s; the 4-byte
                      store of 0 at hdp (:357).
     0x8a570 - 0x8a594 s1 = s + 18144 (&queued, 0x5e40a0), s9 = its shadow address; the check of the 4-byte load at
                      s1; blp at sp + 40; a0 = queued (4-byte load); 0 goes to 0x8a8b8 (kept = len = taken = 0, then
                      0x8a8d4).
     0x8a598 - 0x8a600 hdp at sp + 16; s6 = 32 i = 0, a5 = taken = 0, a6 = len = 0, s5 = kept = 0; sp + 72 = s + 1760
                      (&queue[0], 0x5e00a0); a4 = s + 52 (cfg.max_cmds, 0x5df9f4), t0 = s + 56 (cfg.max_body,
                      0x5df9f8); s3 = 1; s4, t1 = their shadow addresses, sp + 8 / sp + 0 = (a & 7) + 3 of each; spills
                      of a7, a4, t0, s4, t1, s7 at sp + 112, 104, 96, 88, 80, 32 (own frame); a0 = 1.
     0x8a604 - 0x8a624 round i (s0 = i + 1): s2 = &queued; the check of the 4-byte load at s + 52; a0 = max_cmds;
                      s8 = s + 32 i, s9 = &queue[i] = s8 + 1760; taken >= max_cmds (unsigned) goes to 0x8a720 (:360).
     0x8a628 - 0x8a650 s10 = &queue[i].len (s8 + 1784); the check of the 1-byte load at s10 and of the 4-byte load at
                      s + 56; a0 = c->len (1-byte load), a1 = max_body (4-byte unsigned load); max_body < len + c->len
                      (unsigned) goes to 0x8a720 (:361).
     0x8a654 - 0x8a658 allow (sp + 64) = 0 goes to 0x8a704: the check of the 1-byte load at s8 + 1785; c->display <> 0
                      goes to 0x8a720, else 0x8a65c (:362).
     0x8a65c - 0x8a67c taken at sp + 56; the check of c->len again; a0 = bp + len, a1 = &queue[i], a2 = c->len; call of
                      checked_memcpy (__asan_memcpy, 0x523b0 = transport_sigma TS___asan_memcpy) at 0x8a67c, return
                      address 0x8a680: memcpy (body + len, c->bytes, c->len) (:365).
     0x8a680 - 0x8a68c a1 = len + c->len (c->len loaded again, no check), a0 = bp; call of diginet_body_check (0x8c530
                      = transport_sigma TS_diginet_body_check) at 0x8a68c, return address 0x8a690 (:366).
     0x8a690 - 0x8a6b0 the spills loaded back; a result <> 0 goes to 0x8a720.
     0x8a6b4 - 0x8a700 (taken, :368-371) the checks of c->len and c->display; the check of the 4-byte access at hdp
                      (shadow address from sp + 24); a2 = the 4-byte load at hdp; len = len + c->len; taken = taken + 1
                      (32-bit add, sign-extended); the 4-byte store of *has_display | c->display at hdp; to 0x8a774.
     0x8a720 - 0x8a770 (refused, :373-375) i = kept (kept zero-extended from 32 bits) skips the copy; else a0 = s + 1760
                      + 32 kept, a1 = &queue[i], a2 = 32; call of checked_memcpy at 0x8a74c, return 0x8a750:
                      queue[kept] = *c (:374); kept = kept + 1.
     0x8a774 - 0x8a7b4 (:377) the check of s + 52; taken = max_cmds goes to 0x8a84c; the check of s + 56; len =
                      max_body goes to 0x8a84c; the check of the 4-byte load at &queued; i + 1 < queued (unsigned) goes
                      back to 0x8a604; else to 0x8a8d4.
     0x8a84c - 0x8a8a8 (:378-380, the tail) the check of &queued; i + 1 >= queued goes to 0x8a8d4; for j = i + 1 ..
                      queued - 1: a0 = s + 1760 + 32 kept, a1 = &queue[j], a2 = 32; call of checked_memcpy at 0x8a888,
                      return 0x8a88c: queue[kept] = queue[j]; the check of &queued; queued reloaded; kept = kept + 1.
     0x8a8d4 - 0x8a8f4 the check of the 4-byte store at &queued; the 4-byte store of kept at &queued (:383); a0 = blp
                      (sp + 40); the check of the 8-byte store at blp; the 8-byte store of len at blp (:384).
     0x8a8f8          a0 = taken (a5, kept sign-extended from 32 bits by every add); return (:385).
   Stores: own frame (the saves and spills above, all in [sp - 224, sp)); the caller's cells at hdp (0x8a56c,
   0x8a6fc) and blp (0x8a8f4); bp + len .. bp + len + c->len by the copy at 0x8a67c; G: g_s.queued (0x8a8dc) and
   g_s.queue[kept] by the copies at 0x8a74c and 0x8a888 (kept < i by the test at 0x8a72c, kept < j by the cfg
   premise: source and destination do not overlap).
   Loads of G: queued (0x8a590, 0x8a7a0, 0x8a854, 0x8a894), max_cmds (0x8a618, 0x8a780), max_body (0x8a648, 0x8a790),
   queue[i].len (0x8a640, 0x8a668, 0x8a680, 0x8a6cc), queue[i].display (0x8a6dc, 0x8a718); every one inside g_s's
   payload. Each test is the model's: take_loop_m's fits0 (taken <? max_cmds, len + clen <=? max_body, allow or
   display), body_check of the joined body (diginet_body_check's result), the refusal copy when kept <> i, the
   break test (taken1 = max_cmds or len1 = max_body) with take_tail_m, and take_m's set_S_queued; the copies are tw_fill
   of g_s's queue (upd of sub Bw (A_S_queue_bytes i) 32), the store at queued tw_write of put 4 kept.
   No trap: the code has no call of TS___asan_handle_no_return or TS_abort. The model's None cases are an index >= 512
   (the code would read past the queue) and the copy past body[1484] (the copy's destination check fails at the guard
   bytes after the body in the caller's frame); take_m Bw allow = Some _ rules out both.
   Error paths (17 calls) and the facts that rule them out:
     TS___asan_report_store4 0x8a948 (hdp, 0x8a56c) and TS___asan_report_load4 0x8a848 (hdp, 0x8a6ec / 0x8a6fc):
       decode_rd_ok's range_addressable of [hdp, hdp + 4) and hdp mod 4 = 0 (one granule).
     TS___asan_report_store8 0x8a988 (blp, 0x8a8f4): decode_rd_ok's range_addressable of [blp, blp + 8) and
       blp mod 8 = 0 (one whole granule, so k = 0).
     TS___asan_report_load4 0x8a95c, 0x8a9b8, 0x8a984, 0x8a8b4 and TS___asan_report_store4 0x8a970 (&queued, 0x5e40a0),
       TS___asan_report_load4 0x8a998, 0x8a990 (s + 52), 0x8a9a8, 0x8a9b0 (s + 56), TS___asan_report_load1 0x8a9a0,
       0x8a9c0, 0x8a9cc (queue[i].len), 0x8a9c4, 0x8a9d0 (queue[i].display): each address lies in g_s's payload (i <
       512 by the model), whose shadow is 0 (trans_take_cells); the copies keep every byte outside their destination
       and their stack window, and diginet_body_check every byte outside its window, so the shadow bytes stay 0.
   Callee texts assumed (pc order): __asan_memcpy as aintrin_realizes ... OCpy (transport_sigma TS___asan_memcpy) at
   0x8a67c, 0x8a74c and 0x8a888, which the walk applies from its G journal through TransportGCg.v gx_intrin_at:
     0x8a67c: destination [bp + len, + c->len), inside the body (the model), writable by transport_twr_ok_g, addressable
       with its shadow hull visible by decode_rd_ok, outside the copy's ESTACK window by decode_off_win; source
       [&queue[i], + c->len), inside the entry's 32 bytes (the premise), visible (tw_at), apart from the destination
       (bp apart from G), in g_s's zero shadow (trans_take_cells; g_s starts on a 64-byte boundary and the queue array
       [s + 1760, s + 18144) lies in it, so the aligned group of 8 shadow bytes around any range in it (YG0d.v
       shadow_hull_vis) ends at or before the shadow byte of s + 18176, inside g_s's 2283 zero shadow bytes).
     0x8a74c, 0x8a888: 32 bytes from &queue[i] / &queue[j] to &queue[kept], kept < i (0x8a72c skips kept = i) / kept
       < j (the cfg premise), i, j < 512 (the model): both in the queue array, apart from each other, the destination
       a byte of G (transport_twr_ok_g_intro's inG case; gx_rw of G is TransportGRwA.v G_HARNESS_rw).
   diginet_body_check as diginet_body_check_cg.v transport_diginet_body_check_cg at transport_sigma
   TS_diginet_body_check (call at 0x8a68c; a donor-form callee, through TransportGCg.v gx_call_cg: gx_ok and
   gx_noerrno, so the world relation after it is the one it was handed). Its premises at the call, from this statement
   and the code: the donor journal (gx_call_cg opens the G journal); ra = 0x8a690; gp, tp as at entry; a0 = bp, a1 =
   len + c->len = the length of the joined body (take_loop_m's cand); sp - 224 16-aligned, sp - 224 - TRANS_BC_STK >=
   sp0 - STK (TAKE_STK = 224 + TRANS_BC_STK); body <> 0 from 0 < bp; trans_src_ok of [bp, bp + len + c->len) by its
   decode_in_fake disjunct (a sub-range of bp's frame range, len + c->len <= 1484 by the model) with decode_rd_ok (the
   copy and the stores before the call change no shadow byte and keep bp's bytes visible); decode_off_win at
   TRANS_BC_STK from bp's at TAKE_STK; garr8 of the joined body at bp (the earlier taken rounds' copies, kept by the
   later stores, which go to G, blp, hdp or the own frame, and this round's copy of sub Bw (A_S_queue_bytes i) c->len
   through tw_at); count_cid 2 (frames Sc) < fs_frames 2 (the premise; the frames are Sc); st_nev S + k <= EV_MAX.
   No other program function is called.
   Stack: 224 bytes of its own, and below sp - 224 the larger of ESTACK (__asan_memcpy) and diginet_body_check's
   TRANS_BC_STK (4400): TAKE_STK = 4624 (take_stk_eq).

   The caller is diginet_session_tick (the call at 0x89c54, return address 0x89c58): a0 = s4 (its first argument,
   &g_s), a1 = s9 = s11 + 384 (body: offset 384 of its class-5 side-stack frame, the frame of 2048 bytes
   __asan_stack_malloc_5 returns at 0x89328; the frame description string at 0x1f183 names body80 at 384, 1484 bytes,
   and no other variable of take's), a2 = s1 + 80 (body_len) and a4 = s1 + 76 (has_display), both in its machine frame
   (s1 = its sp after the realignment `sp = sp & -32` at 0x892f8, written only at 0x892fc; so blp mod 8 = 0 and
   hdp mod 4 = 0), a3 = s10 (allow_display: 1 from 0x89c24 or the 0 / 1 of 0x89b88). Before the call it marks the body
   usable (TS___asan_set_shadow_00 at 0x89c34: 185 shadow bytes from the body's first, and the shadow byte 4 at
   0x89c3c for the last 4 bytes). It supplies the G journal of its own walk, the world relation, the model call, the
   three ranges' facts, the class-2 frame count, the queue-length invariant and the two cfg bounds. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* take's frame (`sp = sp - 224` at its entry; no realignment), and below sp - 224 the larger of the ESTACK
   __asan_memcpy uses (YG0d.v aintrin_realizes' ecall_pre) and diginet_body_check's window TRANS_BC_STK. *)
Definition TAKE_FRAME : Z := 224.
Definition TAKE_STK : Z := TAKE_FRAME + Z.max ESTACK TRANS_BC_STK.
Lemma take_stk_eq : TAKE_STK = TAKE_FRAME + TRANS_BC_STK /\ TAKE_STK = 4624.
Proof. split; reflexivity. Qed.
(* No allocator event: take calls neither malloc nor free and takes no side-stack frame; diginet_body_check records
   none (TRANS_BC_EV). *)
Definition TAKE_EV : Z := 0.
(* Its first argument, g_s's base in image A, and the length of the caller's body buffer (DIGINET_MAX_BODY_LEN). *)
Definition TAKE_S : Z := TA_g_s.
Definition TAKE_BODY : Z := 1484.
(* The image-A addresses the code reads and stores: g_s.cfg.max_cmds, g_s.cfg.max_body, g_s.queue[0], g_s.queued. *)
Lemma take_args_at :
  TAKE_S = 0x5df9c0 /\ TAKE_S + (TW.A_S_cfg_max_cmds - TW.OFF_g_s) = 0x5df9f4 /\
  TAKE_S + (TW.A_S_cfg_max_body - TW.OFF_g_s) = 0x5df9f8 /\ TAKE_S + (TW.A_S_queue_bytes 0 - TW.OFF_g_s) = 0x5e00a0 /\
  TAKE_S + (TW.A_S_queued - TW.OFF_g_s) = 0x5e40a0 /\ TAKE_BODY = TS0.DIGINET_MAX_BODY_LEN.
Proof. repeat split; reflexivity. Qed.

(* The bytes the code may store outside its frame, from take_m: the queue entries g_s.queue[q] (32 bytes) the refusal
   copy and the tail move entries into (q = kept < i < S_queued Bw, q < 512), g_s.queued, the caller's body buffer
   (the copy at 0x8a67c writes [bp + len, bp + len + c->len) inside it), and the cells at blp and hdp. *)
Definition take_wr (Bw : list byte) (bp blp hdp a : Z) : Prop :=
  (exists q, 0 <= q < TW.S_queue_N /\ q < TW.S_queued Bw /\
     twa_fld TW.OFF_g_s TA_g_s (TW.A_S_queue_bytes q) TW.S_queue_ESZ a) \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_queued 4 a \/
  bp <= a < bp + TAKE_BODY \/
  blp <= a < blp + 8 \/
  hdp <= a < hdp + 4.

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of queued, cfg.max_cmds, cfg.max_body, queue[i].len and queue[i].display, and the three copies'
   ranges in the queue, read it. *)
Definition trans_take_cells (B : asyms) : Prop := decode_zshadow_at B TA_g_s (TA_g_s + TW.SZ_g_s).

Section take. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post_out over G_HARNESS with the out cells [(blp, 8); (hdp, 4)],
   no event, the written range take_wr Bw bp blp hdp, no meter charge, and X: a0 = the 32-bit taken sign-extended,
   the world relation at the model's world Bw', g_fail_next Bw' <= 1, the 1484 bytes at bp agreeing with body on the
   first len, len at blp and hd at hdp. *)
Definition transport_take_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (bp blp hdp : Z) (Bw Bw' body : list byte) (len hd taken : Z)
    : world segs -> config -> Prop :=
  @transport_cg_post_out fx rc tfib_sink_head segs B MT TG.G_HARNESS [(blp, 8); (hdp, 4)] STK sp0 FP ly S W0 mem0
    md0 own lyc Sc W memc k regs TAKE_STK TAKE_EV 0 (take_wr Bw bp blp hdp)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (bv_swrap 32 taken) /\
       tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1 /\
       (exists X : list byte, length X = Z.to_nat TAKE_BODY /\
          garr8 segs (mrestrict (w_H W2) mem2) bp (TW.zs X) /\
          firstn (Z.to_nat len) X = firstn (Z.to_nat len) body) /\
       garr8 segs (mrestrict (w_H W2) mem2) blp (TW.zs (TW.put 8 len)) /\
       garr8 segs (mrestrict (w_H W2) mem2) hdp (TW.zs (TW.put 4 hd))).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_take_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bp blp hdp allow len hd taken : Z) (body : list byte) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 TAKE_S -> YK11.getr regs 11 = w64 bp -> YK11.getr regs 12 = w64 blp ->
    YK11.getr regs 13 = w64 allow -> YK11.getr regs 14 = w64 hdp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TAKE_STK -> spZ regs <= sp0 ->
    - 2 ^ 31 <= allow < 2 ^ 31 ->
    0 < bp ->
    decode_in_fake lyc Sc bp TAKE_BODY ->
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs) bp TAKE_BODY ->
    decode_rd_ok W memc bp TAKE_BODY ->
    decode_off_win regs TAKE_STK bp TAKE_BODY ->
    (forall x, bp <= x < bp + TAKE_BODY -> ~ inG TG.G_HARNESS x) ->
    blp mod 8 = 0 ->
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs) blp 8 ->
    decode_rd_ok W memc blp 8 ->
    decode_off_win regs TAKE_STK blp 8 ->
    (forall x, blp <= x < blp + 8 -> ~ inG TG.G_HARNESS x) ->
    hdp mod 4 = 0 ->
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs) hdp 4 ->
    decode_rd_ok W memc hdp 4 ->
    decode_off_win regs TAKE_STK hdp 4 ->
    (forall x, hdp <= x < hdp + 4 -> ~ inG TG.G_HARNESS x) ->
    bp + TAKE_BODY <= blp \/ blp + 8 <= bp ->
    bp + TAKE_BODY <= hdp \/ hdp + 4 <= bp ->
    blp + 8 <= hdp \/ hdp + 4 <= blp ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TS0.take_m Bw allow = Some (Bw', (body, len, hd, taken)) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    1 <= TW.S_cfg_max_cmds Bw -> 1 <= TW.S_cfg_max_body Bw ->
    count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID ->
    st_nev S + k + TAKE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_take_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bp blp hdp Bw Bw' body len hd taken).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_s,
   the allocator and meter laws, G inside the image, outside the allocator's statics and outside errno (the donor
   callee keeps G: gx_call_cg), and the contracts of __asan_memcpy and diginet_body_check give the contract at
   TS_take. *)
Definition transport_take_cg_holds_stmt : Prop :=
  transport_cells B -> trans_take_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  (forall fx' : YK11.FPState,
     @transport_diginet_body_check_cg fx' rc B MT (transport_sigma TS_diginet_body_check)) ->
  transport_take_cg (transport_sigma TS_take).
End take.
