(* maybe_online_cg: the ASan walk contract of maybe_online (transport/src/diginet_session.c:176-182, with ms (:77) and
   set_state (:79-86) inlined; model lib/TModel/TSess.v maybe_online_m and set_state_m) on fuzz_transport.asan
   (e89be137db17) at 0x8b170 = transport_sigma TS_maybe_online, size 1056, as STATEMENTS only (no proof). It stores
   into g_s, a harness global, takes a class-2 side-stack frame for set_state's struct diginet_notice and calls notice
   through the session's notify pointer, so it is a G-form caller-journal walk: the caller's journal is
   lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the
   post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS). Its form is session_lost_cg.v's,
   whose inlined set_state is the same code: a G walk with a side-stack frame of its own.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s). TF is the current heap frame (check_state_data_cg.v
   trans_tframe_at at this call's window); the read-only bytes notice's callees read are the image's
   (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v
   TMAP_A, read through aview), g_fail_next Bw <= 1, and maybe_online_m timg_A TF Bw = Some (Bw', tt). No byte the
   call stores is a byte of TF (maybeon_apart). Class 2 of the side stack has a free frame. The function returns to
   ra with the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame changes the
   state's st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the caller's
   blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the call's stack
   window [sp - MAYBEON_STK, sp), the image bytes outside G, the owned statics and errno, the caller's block and frame
   bytes outside maybeon_wr Bw), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/maybe_online_c.v): a0 = W_BASE_PLAIN + OFF_g_s -> a0 = TA_g_s;
   wmem -> tw_at; g_fail_next B <= 1 kept as a premise, and the post's g_fail_next B' <= 1 kept in X (the code neither
   reads nor writes g_fail_next; the walk takes the post fact from the model and the premise, as session_lost_cg.v
   does; the callers carry it on toward io_send, whose code tests the byte's bit 0); timg_plain -> timg_A; tframe_at
   -> trans_tframe_at at MAYBEON_STK, and its off_world clause -> maybeon_apart, the part of it this call needs: no
   byte the call stores is a byte of TF (notice_cg.v notice_apart's form; trans_src_ok alone admits a range of G, so
   trans_tframe_at does not give it); relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and
   w_off_stack -> the journal's window premises; mem_inv is dropped. The post's munch, wmono,
   stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g over maybeon_wr); wmem -> X's tw_at.
   Premises the plain contract does not have: count_cid 2 (frames Sc) < fs_frames 2 (the side-stack frame, as
   session_lost_cg.v takes it); maybeon_apart (above); in the holds statement, trans_maybeon_cells, the record fact the
   instrumented checks of the g_s accesses read, the side-stack laws, and trans_ro_rd_unowned, trans_rom_no_errno and
   gx_noerrno (they carry the TRANS_RO_RD bytes and G through the stack malloc's acall_kept, below).
   Run invariants: none is carried. The one program callee, notice, carries check_state_data's run invariant (the
   OW.dn[GOT.ndata].body range window-safe, with n_body_len < 2 ^ 32) only for a notice of kind N_DATA; maybe_online's
   notice has kind N_STATE (the store of 2 at p by 0x8b388; maybeon_ntc), so that premise of notice holds vacuously.
   maybe_online's own accesses are at fixed offsets of g_s (s + 24 .. s + 191) and its one memset fills 56 bytes of its
   own frame, so its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   1056 code bytes are equal in both files), 264 words:
     0x8b170 - 0x8b1a4 sp = sp - 96; 0x8b174 stores 8 zero bytes at sp; ra at sp + 88, s0 .. s9 at sp + 80 .. sp + 8,
                      loaded back at 0x8b4f4 - 0x8b51c; s0 = sp + 96 (the entry sp, kept to 0x8b4f0).
     0x8b1a8 - 0x8b1ac sp = sp & -32 (at most 0x10 below entry - 96); s1 = the realigned sp.
     0x8b1b0 - 0x8b1c8 a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s8 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x8b1cc - 0x8b1e0 the flag word = 0 goes to 0x8b1e0 (s2 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d99c = transport_sigma
                      TS___asan_stack_malloc_2) at 0x8b1d4, return address 0x8b1d8: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s2 = the result.
     0x8b1e4 - 0x8b204 s7 = s2; s2 <> 0 goes to 0x8b208. The real-stack arm (s2 = 0): s7 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s7), then sp = s7. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s7 = s2.
     0x8b208 - 0x8b238 the frame header: 0x41b58ab3 at frame, the description string 0x1fa69 ("1 32 72 6 n.i:83": one
                      variable, 72 bytes at frame + 32; session_lost's frame names the same string) at frame + 8, the
                      function's address 0x8b170 at frame + 16.
     0x8b214, 0x8b240 - 0x8b294 s6 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1, 4..12 = 0xf8
                      (the notice's 72 bytes at frame + 32, marked out of scope), 13..19 = 0xf3 (guard bytes).
     0x8b23c, 0x8b254, 0x8b298 s4 = s + 112, s9 = the address of its shadow byte.
     0x8b2a0          the 8-byte store of frame at s1 + 0 (its own machine frame).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x8b29c, 0x8b2a4 - 0x8b2b0 the check of the 4-byte load at s + 112 (its shadow byte loaded at 0x8b29c); a0 = the
                      4-byte signed load at s + 112 (S_state Bw); <> 1 (S_WAKING) goes to 0x8b400 (:178).
     0x8b2b4 - 0x8b2cc the check of the 4-byte load at s + 144; the 4-byte load (S_wake_acked Bw) = 0 goes to 0x8b400.
     0x8b2d0 - 0x8b2e8 the check of the 4-byte load at s + 140; the 4-byte load (S_e1_named_us Bw) = 0 goes to 0x8b400.
                      Past 0x8b2e8, maybeon_go Bw holds.
     0x8b2ec - 0x8b2fc the check of the 8-byte load at s + 176.
     0x8b300 - 0x8b314 the check of the 4-byte load at s + 24; a1 = the 8-byte load at s + 176 (S_last_rx_us Bw, at
                      0x8b310).
     0x8b318 - 0x8b328 the check of the 8-byte store at s + 184.
     0x8b32c - 0x8b340 a2 = the 4-byte unsigned load at s + 24 (S_cfg_keepalive_ms Bw); s5 = frame + 32 = p, the
                      struct diginet_notice; a1 = a2 * 1000 + a1 (mod 2 ^ 64; ms_m, u64); the 8-byte store of a1 at
                      s + 184 (S_next_keepalive_us, :179). The world is now maybeon_w1 Bw.
     0x8b344 - 0x8b364 shadow bytes 4..12 = 0 (the notice's 72 bytes marked usable).
     0x8b368 - 0x8b374 a0 = p + 16, a1 = 0, a2 = 56; the call of __asan_memset (checked_memset, 0x5284c =
                      transport_sigma TS___asan_memset) at 0x8b374, return address 0x8b378: the notice's bytes
                      16 .. 71 set to 0 (:83).
     0x8b378 - 0x8b38c plain stores into the frame: the 8 bytes 0x0000000200000002 at p (kind = N_STATE = 2 at p,
                      state = S_ONLINE = 2 at p + 4) and the 8 bytes 0x0000000200000001 at p + 8 (old = 1 at p + 8, the
                      constant S_WAKING, which is S_state (maybeon_w1 Bw) = S_state Bw on this path; reason = R_ONLINE = 2
                      at p + 12). The 72 bytes at p are then maybeon_ntc Bw as trans_ntc_at reads them: every field from
                      p + 16 on is 0 (the announce pointer 0, n_ann = None; the body pointer 0 and body_len 0, n_body =
                      []).
     0x8b390 - 0x8b3a0 the check of the 4-byte store at s + 112 (its shadow byte read again through s9), then the
                      store of 2 at s + 112 (S_state = S_ONLINE, :84). The world is now maybeon_w2 Bw.
     0x8b39c - 0x8b3c4 the checks of the 8-byte loads at s + 96 and at s + 104.
     0x8b3c8 - 0x8b3d4 a2 = the 8-byte load at s + 96 (S_notify (maybeon_w2 Bw): tw_read, and the model's call_notify
                      gives TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice
                      does not read); a1 = p; the indirect call (jalr a2) at 0x8b3d4, return address 0x8b3d8 (:85;
                      struct diginet_session + 96, notify -> notice).
     0x8b3d8 - 0x8b3fc shadow bytes 4..12 = 0xf8 (the notice out of scope again).
     0x8b400 - 0x8b408 the header word 0x45e0360e stored at frame (every path).
     0x8b40c          s2 = 0 goes to 0x8b4a0 (the real-stack arm; not taken).
     0x8b410 - 0x8b49c the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load at
                      s2 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x8b4f0.
     0x8b4a0 - 0x8b4ec the real-stack arm's release: shadow bytes 0..19 = 0.
     0x8b4f0 - 0x8b524 sp = s0 - 96, ra and s0 .. s9 loaded back, sp = sp + 96, return. a0 .. a7 at the return are
                      not stated (void).
   No tail jump: the calls are jal with link (the stack malloc, the memset) and one jalr with link (notice); every j
   is inside the function, and the function ends with ret.
   The model and the code: the three tests at 0x8b2b0, 0x8b2cc, 0x8b2e8 are maybe_online_m's (maybeon_go: S_state Bw =?
   S_WAKING, S_wake_acked Bw and S_e1_named_us Bw against 0, each a 32-bit signed read), the store at s + 184 is
   set_S_next_keepalive_us with u64 (S_last_rx_us Bw + ms_m (S_cfg_keepalive_ms Bw)) (a 4-byte unsigned read, so
   the product is below 2 ^ 42), the store at s + 112 is set_state_m's set_S_state (put 4 of 2), each a tw_write
   inside g_s's payload; set_state_m's test S_state B =? S_ONLINE at maybeon_w1 Bw is false on this path (the state is
   S_WAKING, and the store at s + 184 does not touch it), and the code makes no such test; the call is call_notify at
   maybeon_w2 Bw with maybeon_ntc Bw (maybeon_model). The code has no trap of its own; the model's None cases are
   call_notify's (S_notify <> ti_notice timg_A) and notice's, both ruled out by the model premise.
   Error paths (9 calls; no abort) and the facts that rule them out:
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x8b538 (s + 112), 0x8b548 (s + 144), 0x8b558 (s + 140),
       0x8b568 (s + 24);
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x8b57c (s + 112);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x8b580 (s + 176), 0x8b588 (s + 96), 0x8b58c (s + 104);
     TS___asan_report_store8 0x599c8 (errpath_store8) at 0x8b584 (s + 184).
     Each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules), whose
     shadow bytes are 0 (trans_maybeon_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so k = 0.
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [p + 16, p + 72) lies in the frame this function took; its shadow bytes 6 .. 12 are 0 since
     0x8b364 and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the
     journal's own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned,
     not in the ESTACK bytes below sp.
   Writes: g_s's two fields (bytes of G); its own machine frame; its own side-stack frame, that frame's shadow bytes
   and its flag byte; notice's stores (notice_wr, bytes of GOT). No byte of a caller's frame or block is written, so
   maybeon_wr (g_s's fields and notice_wr) is the written range. The G kit for the own frame is session_lost_cg.v's
   (TransportGCg.v dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g, dkg_frame_al64, gx_intrin_at,
   dk_kept_frame_byte_g; CanKit.v can_stack_malloc_at and can_flag_store_pi read inside the G journal through
   gx_lift).
   Callee texts assumed: __asan_stack_malloc_2 as astack_malloc_realizes ... MAYBEON_CID (with
   pc_stack_malloc (as_code B) MAYBEON_CID = transport_sigma TS___asan_stack_malloc_2); __asan_memset as
   aintrin_realizes ... OSet (transport_sigma TS___asan_memset); notice as notice_cg.v transport_notice_cg at
   TI.ti_notice timg_A (= 0x83578 = transport_obj 10, notice_cg.v notice_at), a G-form callee composed in the same G
   journal (no gx_call_cg). Each premise of transport_notice_cg at the call, and where it comes from:
     the journal: maybe_online's G journal at the call state (the own frame live); ra = 0x8b3d8 (ret_ok,
       4096 <= ra); gp, tp kept; a1 = p;
     sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 112 and
       MAYBEON_STK = 112 + NOTICE_STK (maybeon_stk_eq); sp' <= sp0;
     trans_ntc_at p (maybeon_ntc Bw): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of its frames) with
       decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their hull visible);
       decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at
       0x8b374 - 0x8b38c, whose fields are maybeon_ntc's; the body: pointer 0, length 0, garr8 of [], trans_src_ok of
       the empty range at 0 (DgnTransportCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK); the
       announce: n_ann = None with the pointer 0;
     trans_tframe_at TF at NOTICE_STK: maybe_online's trans_tframe_at at MAYBEON_STK, carried: TF's bytes and their
       shadow are unchanged (maybeon_apart for the g_s stores; the own frame is a fresh frame, apart from TF's
       placement), and notice's window lies inside maybe_online's;
     trans_rom_view_rd at the call memory: no store of maybe_online reaches a read-only byte, the memset keeps every
       byte outside its destination and ESTACK bytes (gx_intrin_at), and the stack malloc's acall_kept keeps every
       TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno);
     tw_at at maybeon_w2 Bw: G kept through the stack malloc (gx_kept_of_acall_kept: gx_ok, gx_noerrno), then the two
       tw_writes;
     notice_m timg_A TF (maybeon_w2 Bw) (maybeon_ntc Bw) = Some (Bw', tt): the model premise through maybeon_model (on
       this path maybeon_go Bw holds and the state of maybeon_w1 Bw is S_WAKING, not S_ONLINE; call_notify's test is
       the indirect target's value);
     notice_apart: a byte of notice_wr is a byte of GOT (kind N_STATE), a byte of G, so not a byte of p's frame (a
       frame byte is outside the image: AR_laws' al_client_img); the body range is empty and n_ann = None; TF's range:
       maybeon_apart, since on this path notice_wr (maybeon_w2 Bw) (maybeon_ntc Bw) lies inside maybeon_wr Bw;
     the N_DATA premise: vacuous (n_kind = N_STATE);
     st_nev S + k + NOTICE_EV <= EV_MAX: MAYBEON_EV = NOTICE_EV, and the stack malloc records no event.
   notice's own record facts (notice_cg.v trans_notice_cells, gx_noerrno) are premises of notice's holds statement.
   maybe_online lifts no donor callee, but the stack malloc's journal step (can_stack_malloc_at) leaves acall_kept,
   whose image clause keeps no owned-static or errno byte: G kept through it takes gx_noerrno, and the TRANS_RO_RD
   bytes take trans_ro_rd_unowned and trans_rom_no_errno, so the holds statement takes all three.
   Stack: 96 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset) or notice's NOTICE_STK: MAYBEON_STK = 112 + NOTICE_STK
   (maybeon_stk_eq).

   The callers: on_announce at 0x87ff8 (return address 0x87ffc): a0 = s4 (its own a0, &g_s, since 0x87adc), after its
   store of 1 at s + 140 (S_e1_named_us, 0x87ff0); on_ack at 0x886ac (return address 0x886b0): a0 = s3 (its own a0,
   &g_s, since 0x88490), after its store of 1 at s + 144 (S_wake_acked, 0x886a4). Each takes a side-stack frame of
   its own and calls maybe_online while it is live: on_announce a class-4 frame, on_ack a class-2 frame, so on_ack's
   class-2 count must leave room for this call's frame. Each supplies its G journal, tw_at, g_fail_next, the model
   premise (its branch of on_announce_m / on_ack_m), trans_tframe_at and maybeon_apart of its TF, trans_rom_view_rd,
   and count_cid 2 (frames Sc) < fs_frames 2. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* maybe_online's frame (`sp = sp - 96` at TS_maybe_online), the at most 0x10 bytes of `sp = sp & -32` (0x8b1a8)
   below it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2 and
   __asan_memset (YG0d.v ecall_pre), notice's NOTICE_STK. *)
Definition MAYBEON_FRAME : Z := 96.
Definition MAYBEON_ALIGN : Z := 0x10.
Definition MAYBEON_STK : Z := MAYBEON_FRAME + MAYBEON_ALIGN + Z.max ESTACK NOTICE_STK.
Lemma maybeon_stk_eq : MAYBEON_STK = MAYBEON_FRAME + MAYBEON_ALIGN + NOTICE_STK.
Proof. reflexivity. Qed.
(* No allocator event: notice records none, and the class-2 stack malloc and its release record none (YG00.v
   stack_malloc, stack_free). *)
Definition MAYBEON_EV : Z := NOTICE_EV.
(* The side-stack class (a0 = 160 at 0x8b1d0, the call of __asan_stack_malloc_2 at 0x8b1d4). *)
Definition MAYBEON_CID : Z := 2.
(* Its argument: g_s's base in image A. *)
Definition MAYBEON_S : Z := TA_g_s.
(* The addresses of the eight g_s fields the code reads or writes (s + 112, s + 144, s + 140, s + 176, s + 24,
   s + 184, s + 96, s + 104). *)
Lemma maybeon_addrs :
  MAYBEON_S = 0x5df9c0 /\
  MAYBEON_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  MAYBEON_S + (TW.A_S_wake_acked - TW.OFF_g_s) = 0x5dfa50 /\
  MAYBEON_S + (TW.A_S_e1_named_us - TW.OFF_g_s) = 0x5dfa4c /\
  MAYBEON_S + (TW.A_S_last_rx_us - TW.OFF_g_s) = 0x5dfa70 /\
  MAYBEON_S + (TW.A_S_cfg_keepalive_ms - TW.OFF_g_s) = 0x5df9d8 /\
  MAYBEON_S + (TW.A_S_next_keepalive_us - TW.OFF_g_s) = 0x5dfa78 /\
  MAYBEON_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  MAYBEON_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v maybe_online_m, set_state_m): the test of :178, the world after the store of :179,
   the world after set_state's store of the state (:84), and set_state's notice (:83). *)
Definition maybeon_go (Bw : list byte) : bool :=
  (TW.S_state Bw =? TS0.DIGINET_S_WAKING) && negb (TW.S_wake_acked Bw =? 0) && negb (TW.S_e1_named_us Bw =? 0).
Definition maybeon_w1 (Bw : list byte) : list byte :=
  TW.set_S_next_keepalive_us Bw (TS0.u64 (TW.S_last_rx_us Bw + TS0.ms_m (TW.S_cfg_keepalive_ms Bw))).
Definition maybeon_w2 (Bw : list byte) : list byte := TW.set_S_state (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE.
Definition maybeon_ntc (Bw : list byte) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_STATE TS0.DIGINET_S_ONLINE (TW.S_state (maybeon_w1 Bw)) TS0.DIGINET_R_ONLINE 0 0 0 0 None [] 0.
Lemma maybeon_model : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte),
  TSS.maybe_online_m I F Bw =
  if maybeon_go Bw then
    (if TW.S_state (maybeon_w1 Bw) =? TS0.DIGINET_S_ONLINE then Some (maybeon_w1 Bw, tt)
     else TSS.call_notify I F (maybeon_w2 Bw) (maybeon_ntc Bw))
  else Some (Bw, tt).
Proof. intros I F Bw. reflexivity. Qed.

(* The bytes the code stores into G, exactly: when the test of :178 holds, g_s's next_keepalive_us (8 bytes) and,
   when the state changes, g_s's state (4 bytes) and notice's stores at the world maybeon_w2 Bw (notice_cg.v
   notice_wr: for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and GOT.n). *)
Definition maybeon_wr (Bw : list byte) (a : Z) : Prop :=
  maybeon_go Bw = true /\
  (twa_fld TW.OFF_g_s TA_g_s TW.A_S_next_keepalive_us 8 a \/
   (TW.S_state (maybeon_w1 Bw) <> TS0.DIGINET_S_ONLINE /\
    (twa_fld TW.OFF_g_s TA_g_s TW.A_S_state 4 a \/ notice_wr (maybeon_w2 Bw) (maybeon_ntc Bw) a))).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after the g_s stores and after its own (notice_cg.v notice_apart). *)
Definition maybeon_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, maybeon_wr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 24 .. s + 191 read it. *)
Definition trans_maybeon_cells (B : asyms) : Prop := decode_zshadow_at B MAYBEON_S (MAYBEON_S + TW.SZ_g_s).

Section maybeon. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range
   maybeon_wr Bw, no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the model's
   world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this function takes
   is released. *)
Definition transport_maybeon_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    MAYBEON_STK MAYBEON_EV 0 (maybeon_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_maybe_online_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 MAYBEON_S ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MAYBEON_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.maybe_online_m timg_A TF Bw = Some (Bw', tt) ->
    trans_tframe_at B lyc Sc W memc regs MAYBEON_STK TF ->
    trans_rom_view_rd W memc ->
    maybeon_apart TF Bw ->
    count_cid MAYBEON_CID (frames Sc) < fs_frames MAYBEON_CID ->
    st_nev S + k + MAYBEON_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_maybeon_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the TRANS_RO_RD bytes outside the owned
   statics and errno (DgnTransportCg.v trans_ro_rd_scoped: they stay the image's through the stack malloc's
   acall_kept), the allocator, meter and side-stack laws, G inside the image, outside the allocator's statics and
   outside errno (G kept through the stack malloc's acall_kept: TransportGCg.v gx_kept_of_acall_kept), and the
   contracts of __asan_stack_malloc_2, __asan_memset and notice (at the value the session's notify pointer holds)
   give the contract at TS_maybe_online. *)
Definition transport_maybe_online_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) MAYBEON_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_maybeon_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B MAYBEON_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  transport_maybe_online_cg (transport_sigma TS_maybe_online).
End maybeon.
