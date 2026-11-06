(* set_state_cg: image B's ASan walk contract of set_state (transport/src/diginet_session.c:79-86; model
   lib/TModel/TSess.v set_state_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x872cc = transportb_sigma
   TB_set_state, size 892, as STATEMENTS only (no proof). Image B only: image A inlines set_state into session_lost
   (lib/A/Prog/session_lost_cg.v) and into its other callers, so no image-A statement of this function exists; the
   ubsan image has it as a function, and its plain contract lib/U/Prog/T/set_state_c.v is the text this statement
   translates. It stores into g_s, a harness global, takes a class-2 side-stack frame for its struct diginet_notice
   and calls notice through the session's notify pointer, so it is a G-form caller-journal walk: the caller's journal
   is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0, OUT = []), and
   the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B). Form: image A's
   session_lost_cg.v for the part of it that is set_state (the realignment, the stack malloc, the frame header and
   shadow, the notice, the state store, the notify call, the release), at image B's names; session_lost's own two
   stores (S_inflight, S_desk_counter_valid) are not here (on image B the callers that inline session_lost make them,
   below), and the new state st is an argument (image A's session_lost fixes S_IDLE).

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s), a1 = st, a2 = why, 0 <= st < 2 ^ 31 and
   0 <= why < 2 ^ 31 (the enum arguments; the plain contract's bounds). TF is the current heap frame
   (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes notice's callees read are the
   image's (trans_rom_view_rd). The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at
   TWorldB.v TMAP_B, read through aview), g_fail_next Bw <= 1, and set_state_m timg_B TF Bw st why = Some (Bw', tt).
   No byte the call stores is a byte of TF (sstate_apart). Class 2 of the side stack has a free frame. The function
   returns to ra with the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame
   changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the
   caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - SSTATE_STK, sp), the image bytes outside G, the owned statics and errno, the caller's
   block and frame bytes outside sstate_wr Bw st why), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/U/Prog/T/set_state_c.v): a0 = W_BASE_UBSAN + OFF_g_s -> a0 = TB_g_s;
   a1 = st, a2 = why with 0 <= st, why < 2 ^ 31, kept (the code compares the sign-extended S_state with st and stores
   the low 32 bits of st and why as the notice's state and reason, which trans_ntc_at reads back as s32_at NB 4 = st
   and s32_at NB 12 = why); wmem -> tw_at; g_fail_next B <= 1, kept as a premise, and the post's g_fail_next B' <= 1,
   kept in X (the code neither reads nor writes g_fail_next, and notice's N_STATE stores are GOT's; the callers carry
   it on toward io_send, whose code tests the byte's bit 0); timg_ubsan -> timg_B; tframe_at -> trans_tframe_at at
   SSTATE_STK, and its off_world clause -> sstate_apart, the part of it this call needs (session_lost_cg.v
   slost_apart's form); relro_img -> trans_rom_view_rd; the 16-aligned sp, stk, lo + FRAME <= sp and w_off_stack ->
   the journal's window premises; mem_inv is dropped. The post's munch, wmono, stk and mem_inv ->
   transport_cg_post (the journal at the return, acall_kept_g over sstate_wr); wmem -> X's tw_at.
   Premises the plain contract does not have: count_cid 2 (frames Sc) < fs_frames 2 (the side-stack frame, as
   session_lost_cg.v takes it); sstate_apart (above); in the holds statement, trans_sstate_cells, the record fact the
   instrumented checks of the g_s accesses read, the side-stack laws, and trans_ro_rd_unowned, trans_rom_no_errno and
   gx_noerrno (they carry the TRANS_RO_RD bytes and G through the stack malloc's acall_kept, below).
   Run invariants: none is carried. The one program callee, notice, carries check_state_data's run invariant only for
   a notice of kind N_DATA; set_state's notice has kind N_STATE (the store of 2 at 0x87460; sstate_ntc), so that
   premise of notice holds vacuously. set_state's own accesses are at fixed offsets of g_s (s + 96 .. s + 115) and its
   one memset fills 56 bytes of its own frame, so its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 892 code bytes are equal in both files), 223 words:
     0x872cc - 0x87308 sp = sp - 160; 0x872d0 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 ..
                      sp + 56, loaded back at 0x875d4 - 0x87604; s0 = sp + 160 (the entry sp, kept to 0x875d0).
     0x8730c - 0x87318 sp = sp & -32 (at most 0x10 below entry - 160); s1 = the realigned sp; s2 = why, s3 = st.
     0x8731c - 0x87334 a2 = the 8-byte load of the GOT word 0xa3d48 (it holds 0xac680), then the 4-byte load of the
                      flag word at 0xac680; a1 = the 8-byte load of the GOT word 0xa3cf0 (it holds 0xac678), s10 = the
                      8-byte load at 0xac678 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s4 = s.
     0x87338 - 0x87348 the flag word = 0 goes to 0x87348 (a0 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d9f8 = transportb_sigma
                      TB___asan_stack_malloc_2) at 0x87340, return address 0x87344: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes).
     0x8734c - 0x8736c s9 = a0; a0 <> 0 goes to 0x87370. The real-stack arm (a0 = 0): s9 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s9), then sp = s9. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s9 = a0.
     0x87370          the 8-byte store of frame at s1 + 48 (its own machine frame).
     0x87374 - 0x873a0 the frame header: 0x41b58ab3 at frame, the description string 0x13745 ("1 32 72 4 n:83": one
                      variable, 72 bytes at frame + 32) at frame + 8, the function's address 0x872cc at frame + 16.
     0x87380 - 0x873fc s8 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1, 4..12 = 0xf8 (the
                      notice's 72 bytes at frame + 32, marked out of scope), 13..19 = 0xf3 (guard bytes).
     0x87400          s & 7 <> 0 (a1 = s & 7 at 0x873bc) goes to the trap word at 0x87610.
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x87404 - 0x87418 s6 = s + 112, s11 = the address of its shadow byte; the check of the 4-byte load; s5 = the
                      4-byte signed load at s + 112 (S_state Bw).
     0x8741c          s5 = st goes to 0x874e0 with a0 = frame: set_state's :81-82, no notice and no state store
                      (sstate_model's first branch).
     0x87420 - 0x87448 the 8-byte store of frame at s1 + 24; s7 = frame + 32 = p, the struct diginet_notice; shadow
                      bytes 4..12 = 0 (its 72 bytes marked usable).
     0x8744c - 0x87458 a0 = p + 16, a1 = 0, a2 = 56; the call of __asan_memset (checked_memset, 0x52888 =
                      transportb_sigma TB___asan_memset) at 0x87458, return address 0x8745c: the notice's bytes
                      16 .. 71 set to 0 (:83).
     0x8745c - 0x8746c plain stores into the frame: the 4 bytes of 2 at p (kind = N_STATE), the low 32 bits of st at
                      p + 4 (state), of s5 at p + 8 (old), of why at p + 12 (reason). The 72 bytes at p are then
                      sstate_ntc Bw st why as trans_ntc_at reads them: every field from p + 16 on is 0 (the announce
                      pointer 0, n_ann = None; the body pointer 0 and body_len 0, n_body = []).
     0x87470 - 0x87478 the check of the 4-byte store at s + 112 (its shadow byte read again through s11; slow path
                      0x87628), then the store of st at s + 112 (S_state = st, :84). The world is now sstate_w Bw st.
     0x8747c - 0x874a0 the checks of the 8-byte loads at s + 96 and at s + 104.
     0x874a4 - 0x874b0 a2 = the 8-byte load at s + 96 (S_notify (sstate_w Bw st): tw_read, and the model's call_notify
                      gives TI.ti_notice timg_B = 0x8341c); a0 = the 8-byte load at s + 104 (notify_ctx, which notice
                      does not read); a1 = p; the indirect call (jalr a2) at 0x874b0, return address 0x874b4 (:85).
     0x874b4 - 0x874dc shadow bytes 4..12 = 0xf8 (the notice out of scope again); a0 = frame (loaded back from
                      s1 + 24).
     0x874e0 - 0x874e8 the header word 0x45e0360e stored at frame.
     0x874ec          a0 = 0 goes to 0x87580 (the real-stack arm; not taken).
     0x874f0 - 0x8757c the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load at
                      frame + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x875d0.
     0x87580 - 0x875cc the real-stack arm's release: shadow bytes 0..19 = 0.
     0x875d0 - 0x8760c sp = s0 - 160, ra and s0 .. s11 loaded back, sp = sp + 160, return. a0 .. a7 at the return are
                      not stated (void).
     0x87610          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x87614 - 0x87644 the slow paths of the checks and the 4 error calls.
   The model and the code: the test at 0x8741c is set_state_m's S_state B =? st (the sign-extended 4-byte load against
   st, 0 <= st < 2 ^ 31, with S_state the signed 4-byte field); the store at 0x87478 is set_S_state (put 4 of st), a
   tw_write inside g_s's payload; the call is call_notify at sstate_w Bw st with sstate_ntc Bw st why (sstate_model).
   The model covers every path of the code: its None cases are call_notify's (S_notify <> ti_notice timg_B) and
   notice's, both ruled out by the model premise; the code's one trap branch and its real-stack arm are ruled out by
   facts outside the model (the constant s, the side-stack premises).
   Trap path (the unimp word at 0x87610, from 1 branch) and the fact that refutes it: 0x87400 (s & 7 <> 0): s =
   0x5df640, a multiple of 8. (Image A's inlined copy in session_lost has no such check.)
   Error paths (4 calls; no abort) and the facts that rule them out:
     __asan_report_load4 (0x59644) at 0x87624 (s + 112); __asan_report_store4 (0x59964) at 0x87638 (s + 112);
     __asan_report_load8 (0x596e4) at 0x8763c (s + 96) and 0x87644 (s + 104).
     Each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
     shadow bytes are 0 (trans_sstate_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so k = 0.
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [p + 16, p + 72) lies in the frame this function took; its shadow bytes 6 .. 12 are 0 since 0x87448
     and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the journal's
     own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned, not in the
     ESTACK bytes below sp.
   Writes: g_s's state field (bytes of G); its own machine frame; its own side-stack frame, that frame's shadow bytes
   and its flag byte; notice's stores (notice_wr, bytes of GOT). No byte of a caller's frame or block is written, so
   sstate_wr (g_s's state and notice_wr, when the state changes) is the written range. The G kit for the own frame
   (TransportGCg.v): dk_kept_own_g with dkg_nf and dkg_nf_sep, dk_kept_trans_nf_g (notice's acall_kept_g is stated at
   the call state, whose frames are the own frame :: frames Sc; notice_wr (sstate_w Bw st) (sstate_ntc Bw st why)
   lies inside sstate_wr Bw st why), dkg_frame_al64 (the frame starts on 64 bytes), gx_intrin_at (the memset) and
   dk_kept_frame_byte_g; the stack malloc's and the release's journal steps are image B's CanKit.v
   can_stack_malloc_at and can_flag_store_pi, read inside the G journal through gx_lift.
   Callee texts assumed: __asan_stack_malloc_2 as astack_malloc_realizes ... SSTATE_CID (with
   pc_stack_malloc (as_code B) SSTATE_CID = transportb_sigma TB___asan_stack_malloc_2); __asan_memset as
   aintrin_realizes ... OSet (transportb_sigma TB___asan_memset); notice as notice_cg.v transport_notice_cg at
   TI.ti_notice timg_B (= 0x8341c, notice_cg.v notice_at), a G-form callee composed in the same G journal (no
   gx_call_cg). Each premise of transport_notice_cg at the call, and where it comes from:
     the journal: set_state's G journal at the call state (the own frame live); ra = 0x874b4 (ret_ok,
       4096 <= ra); gp, tp kept; a1 = p;
     sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 176 and
       SSTATE_STK = 176 + NOTICE_STK (sstate_stk_eq); sp' <= sp0;
     trans_ntc_at p (sstate_ntc Bw st why): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of its frames) with
       decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their hull visible);
       decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at
       0x87458 - 0x8746c, whose fields are sstate_ntc's; the body: pointer 0, length 0, garr8 of [], trans_src_ok of
       the empty range at 0 (DgnTransportBCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK); the
       announce: n_ann = None with the pointer 0;
     trans_tframe_at TF at NOTICE_STK: set_state's trans_tframe_at at SSTATE_STK, carried: TF's bytes and their
       shadow are unchanged (sstate_apart for the g_s store; the own frame is a fresh frame, apart from TF's
       placement), and notice's window lies inside set_state's;
     trans_rom_view_rd at the call memory: no store of set_state reaches a read-only byte, the memset keeps every
       byte outside its destination and ESTACK bytes (gx_intrin_at), and the stack malloc's acall_kept keeps every
       TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno);
     tw_at at sstate_w Bw st: G kept through the stack malloc (gx_kept_of_acall_kept: gx_ok, gx_noerrno), then the
       tw_write of the state;
     notice_m timg_B TF (sstate_w Bw st) (sstate_ntc Bw st why) = Some (Bw', tt): the model premise through
       sstate_model (the state differed from st on this path; call_notify's test is the indirect target's value);
     notice_apart: a byte of notice_wr is a byte of GOT (kind N_STATE), a byte of G, so not a byte of p's frame (a
       frame byte is outside the image: AR_laws' al_client_img); the body range is empty and n_ann = None; TF's range:
       sstate_apart, since on this path notice_wr (sstate_w Bw st) (sstate_ntc Bw st why) lies inside
       sstate_wr Bw st why;
     the N_DATA premise: vacuous (n_kind = N_STATE);
     st_nev S + k + NOTICE_EV <= EV_MAX: SSTATE_EV = NOTICE_EV, and the stack malloc records no event.
   notice's own record facts (notice_cg.v trans_notice_cells, gx_noerrno) are premises of notice's holds statement.
   set_state lifts no donor callee, but the stack malloc's journal step (can_stack_malloc_at) leaves acall_kept,
   whose image clause keeps no owned-static or errno byte: G kept through it takes gx_noerrno, and the TRANS_RO_RD
   bytes take trans_ro_rd_unowned and trans_rom_no_errno, so the holds statement takes all three.
   Stack: 160 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset) or notice's NOTICE_STK: SSTATE_STK = 176 + NOTICE_STK
   (sstate_stk_eq).

   The callers (7 sites; DgnTransportBList.v PCall TB_set_state / the tail jump), each with a0 = s (its own &g_s):
     diginet_session_wake, the call at 0x86d2c (return address 0x86d30): st = 1 (S_WAKING), why = 1 (R_WAKE);
     diginet_session_close, the call at 0x876f8 (return address 0x876fc): st = 3 (S_CLOSED), why = 8 (R_CLOSED), after
       its checked store of 0 at s + 212 (S_inflight, 0x876e8);
     diginet_session_rx, the call at 0x87c08 (return address 0x87c0c): st = 0 (S_IDLE), why = 7 (R_DESK_DISCONNECT);
     on_announce, the calls at 0x88128 (return address 0x8812c; why = 3, R_DESK_OFFLINE) and 0x882b8 (return address
       0x882bc; why = 5, R_FOREIGN): st = 0;
     diginet_session_tick, the call at 0x8951c (return address 0x89520): st = 0, why = 4 (R_SILENCE, a2 at 0x89510)
       or 6 (R_WAKE_TIMEOUT, a2 at 0x892d8, whose path jumps to 0x89514);
     maybe_online, the tail jump at 0x8af64 (from its entry sp, ra loaded back at 0x8af5c): st = 2 (S_ONLINE),
       why = 2 (R_ONLINE), after its store of S_next_keepalive_us (s + 184, 0x8af58).
   The four st = 0 call sites are image B's inlined session_lost (image A's session_lost_cg.v: one function, called by
   diginet_session_rx, and four inlined copies): before the call each path makes session_lost's two checked 4-byte
   stores of 0, at s + 212 (S_inflight) and s + 168 (S_desk_counter_valid) (diginet_session_rx 0x87be0 / 0x87bf8,
   on_announce 0x88100 / 0x88118 and 0x88290 / 0x882a8, diginet_session_tick 0x894f4 / 0x8950c for R_SILENCE and
   0x892bc / 0x892d4 for R_WAKE_TIMEOUT), so session_lost_m's first two steps land in the caller's walk and its
   set_state_m step is this statement. Each caller supplies its G journal, tw_at, g_fail_next, the model premise (that
   branch of its model), trans_tframe_at and sstate_apart of its TF, trans_rom_view_rd, and the free class-2 frame. *)
From Stdlib Require Import ZArith List Lia Permutation.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* set_state's frame (`sp = sp - 160` at TB_set_state), the at most 0x10 bytes of `sp = sp & -32` (0x8730c) below
   it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2 and
   __asan_memset (YG0d.v ecall_pre), notice's NOTICE_STK. *)
Definition SSTATE_FRAME : Z := 160.
Definition SSTATE_ALIGN : Z := 0x10.
Definition SSTATE_STK : Z := SSTATE_FRAME + SSTATE_ALIGN + Z.max ESTACK NOTICE_STK.
Lemma sstate_stk_eq : SSTATE_STK = SSTATE_FRAME + SSTATE_ALIGN + NOTICE_STK.
Proof. reflexivity. Qed.
(* No allocator event: notice records none, and the class-2 stack malloc and its release record none (YG00.v
   stack_malloc, stack_free). *)
Definition SSTATE_EV : Z := NOTICE_EV.
(* The side-stack class (a0 = 160 at 0x8733c, the call of __asan_stack_malloc_2 at 0x87340). *)
Definition SSTATE_CID : Z := 2.
(* Its first argument: g_s's base in image B. *)
Definition SSTATE_S : Z := TB_g_s.
(* The addresses of the three g_s fields the code reads or writes (s + 112, s + 96, s + 104). *)
Lemma sstate_addrs :
  SSTATE_S = 0x5df640 /\
  SSTATE_S + (TW.A_S_state - TW.OFF_g_s) = 0x5df6b0 /\
  SSTATE_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5df6a0 /\
  SSTATE_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5df6a8.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v set_state_m): the world after the store of the state (:84), and the notice (:83). *)
Definition sstate_w (Bw : list byte) (st : Z) : list byte := TW.set_S_state Bw st.
Definition sstate_ntc (Bw : list byte) (st why : Z) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_STATE st (TW.S_state Bw) why 0 0 0 0 None [] 0.
Lemma sstate_model : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (st why : Z),
  TSS.set_state_m I F Bw st why =
  if TW.S_state Bw =? st then Some (Bw, tt)
  else TSS.call_notify I F (sstate_w Bw st) (sstate_ntc Bw st why).
Proof. intros I F Bw st why. reflexivity. Qed.

(* The bytes the code stores into G, exactly: when the state changes, g_s's state (4 bytes) and notice's stores at
   the world sstate_w Bw st (notice_cg.v notice_wr: for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX,
   and GOT.n); none otherwise. *)
Definition sstate_wr (Bw : list byte) (st why a : Z) : Prop :=
  TW.S_state Bw <> st /\
  (twb_fld TW.OFF_g_s TB_g_s TW.A_S_state 4 a \/ notice_wr (sstate_w Bw st) (sstate_ntc Bw st why) a).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after the g_s store and after its own (notice_cg.v notice_apart). *)
Definition sstate_apart (Fr : option TI.tframe) (Bw : list byte) (st why : Z) : Prop :=
  forall x, sstate_wr Bw st why x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 96 .. s + 115 read it. *)
Definition trans_sstate_cells (B : asyms) : Prop := decode_zshadow_at B SSTATE_S (SSTATE_S + TW.SZ_g_s).

Section sstate. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   sstate_wr Bw st why, no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the
   model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released. *)
Definition transport_sstate_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (st why : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs SSTATE_STK SSTATE_EV 0 (sstate_wr Bw st why)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_set_state_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (st why : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SSTATE_S -> YK11.getr regs 11 = w64 st -> YK11.getr regs 12 = w64 why ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SSTATE_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.set_state_m timg_B TF Bw st why = Some (Bw', tt) ->
    0 <= st < 2 ^ 31 -> 0 <= why < 2 ^ 31 ->
    trans_tframe_at B lyc Sc W memc regs SSTATE_STK TF ->
    trans_rom_view_rd W memc ->
    sstate_apart TF Bw st why ->
    count_cid SSTATE_CID (frames Sc) < fs_frames SSTATE_CID ->
    st_nev S + k + SSTATE_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_sstate_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' st why).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the TRANS_RO_RD bytes outside the owned
   statics and errno (DgnTransportBCg.v trans_ro_rd_scoped: they stay the image's through the stack malloc's
   acall_kept), the allocator, meter and side-stack laws, G inside the image, outside the allocator's statics and
   outside errno (G kept through the stack malloc's acall_kept: TransportGCg.v gx_kept_of_acall_kept), and the
   contracts of __asan_stack_malloc_2, __asan_memset and notice (at the value the session's notify pointer holds)
   give the contract at TB_set_state. *)
Definition transport_set_state_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) SSTATE_CID = transportb_sigma TB___asan_stack_malloc_2 ->
  transport_cells B -> trans_sstate_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SSTATE_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_B)) ->
  transport_set_state_cg (transportb_sigma TB_set_state).
End sstate.
