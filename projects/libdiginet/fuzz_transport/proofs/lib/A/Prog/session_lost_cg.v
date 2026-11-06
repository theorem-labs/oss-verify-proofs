(* session_lost_cg: the ASan walk contract of session_lost (transport/src/diginet_session.c:160-165, with set_state
   (:79-86) inlined; model lib/TModel/TSess.v session_lost_m and set_state_m) on fuzz_transport.asan (e89be137db17) at
   0x88f08 = transport_sigma TS_session_lost, size 944, as STATEMENTS only (no proof). It stores into g_s, a harness
   global, takes a class-2 side-stack frame for set_state's struct diginet_notice and calls notice through the
   session's notify pointer, so it is a G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v
   ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell (XO = 0, OUT = []), and the post is
   lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS). It is the first G-form statement that
   takes a side-stack frame of its own: the G form is diginet_session_init_cg.v's and notice_cg.v's, the side-stack
   premises are diginet_body_check_cg.v's.

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = why, 0 <= why < 2 ^ 31. TF is the current heap
   frame (check_state_data_cg.v trans_tframe_at at this call's window); the read-only bytes notice's callees read are
   the image's (trans_rom_view_rd). The memory relates to the world Bw by image A's world relation (TWorldG.v tw_at at
   TWorldA.v TMAP_A, read through aview), g_fail_next Bw <= 1, and session_lost_m timg_A TF Bw why = Some (Bw', tt).
   No byte the call stores is a byte of TF (slost_apart). Class 2 of the side stack has a free frame. The function
   returns to ra with the callee-saved registers kept, no allocator event and no meter charge (its side-stack frame
   changes the state's st_fs only: ameter_fs_laws), its side-stack frame released (the caller's frames exactly), the
   caller's blocks exactly, the bytes acall_kept_g G_HARNESS keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - SLOST_STK, sp), the image bytes outside G, the owned statics and errno, the caller's
   block and frame bytes outside slost_wr Bw why), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/session_lost_c.v): a0 = W_BASE_PLAIN + OFF_g_s -> a0 = TA_g_s;
   a1 = why with 0 <= why < 2 ^ 31, kept (the code stores the low 32 bits of a1 as the notice's reason, and
   trans_ntc_at reads it back as s32_at NB 12 = why); wmem -> tw_at; g_fail_next B <= 1, kept as a premise, and the
   post's g_fail_next B' <= 1, kept in X (the code neither reads nor writes g_fail_next; the walk takes the post fact
   from the model and the premise, as the plain walk does with TNotifyFacts.v notice_state_acked_fail_next; the
   callers carry it on toward io_send, whose code tests the byte's bit 0); timg_plain -> timg_A; tframe_at ->
   trans_tframe_at at SLOST_STK, and its off_world clause -> slost_apart, the part of it this call needs: no byte the
   call stores is a byte of TF (notice_cg.v notice_apart's form; trans_src_ok alone admits a range of G, so
   trans_tframe_at does not give it); relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp, sp mod 16 and
   w_off_stack -> the journal's window premises; mem_inv is dropped. The post's munch, wmono,
   stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g over slost_wr); wmem -> X's tw_at.
   Premises the plain contract does not have: count_cid 2 (frames Sc) < fs_frames 2 (the side-stack frame, as
   diginet_body_check_cg.v takes it); slost_apart (above); in the holds statement, trans_slost_cells, the record fact
   the instrumented checks of the g_s accesses read, the side-stack laws, and trans_ro_rd_unowned, trans_rom_no_errno
   and gx_noerrno (they carry the TRANS_RO_RD bytes and G through the stack malloc's acall_kept, below).
   Run invariants: none is carried. The one program callee, notice, carries check_state_data's run invariant (the
   OW.dn[GOT.ndata].body range window-safe) only for a notice of kind N_DATA; session_lost's notice has kind N_STATE
   (the store of 2 at 0x890c0; slost_ntc), so that premise of notice holds vacuously. session_lost's own accesses are
   at fixed offsets of g_s (s + 96 .. s + 215) and its one memset fills 56 bytes of its own frame, so its code needs
   no bound that the model does not give.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   944 code bytes are equal in both files), 236 words:
     0x88f08 - 0x88f44 sp = sp - 128; 0x88f0c stores 8 zero bytes at sp; ra at sp + 120, s0 .. s11 at sp + 112 ..
                      sp + 24, loaded back at 0x8922c - 0x8925c; s0 = sp + 128 (the entry sp, kept to 0x89228).
     0x88f48 - 0x88f50 sp = sp & -32 (at most 0x10 below entry - 128); s1 = the realigned sp; s4 = why (a1).
     0x88f54 - 0x88f6c a2 = the 8-byte load of the GOT word 0xa40e8 (it holds 0xaca00), then the 4-byte load of the
                      flag word at 0xaca00; a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8), s9 = the
                      8-byte load at 0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1, 2, 6, 7. s3 = s.
     0x88f70 - 0x88f84 the flag word = 0 goes to 0x88f84 (s2 = 0); transport_cells row 6 gives 1. a0 = 160 and the
                      call of __asan_stack_malloc_2 (frame_alloc_2, 0x3d99c = transport_sigma
                      TS___asan_stack_malloc_2) at 0x88f78, return address 0x88f7c: a class-2 side-stack frame
                      (fs_frame_bytes 2 = 256 bytes); s2 = the result.
     0x88f88 - 0x88fa8 s8 = s2; s2 <> 0 goes to 0x88fac. The real-stack arm (s2 = 0): s8 = (sp - 160) & -32 and a
                      probe loop (sp = sp - 4096, 8 zero bytes stored at sp, until sp <= s8), then sp = s8. With
                      count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame
                      (astack_malloc_realizes), so this arm is not taken. Below, frame = s8 = s2.
     0x88fac - 0x88fd8 the frame header: 0x41b58ab3 at frame, the description string 0x1fa69 ("1 32 72 6 n.i:83": one
                      variable, 72 bytes at frame + 32) at frame + 8, the function's address 0x88f08 at frame + 16.
     0x88fb8 - 0x89034 s7 = (frame >> 3) + 0x7fff8000; the frame's shadow bytes 0..3 = 0xf1, 4..12 = 0xf8 (the
                      notice's 72 bytes at frame + 32, marked out of scope), 13..19 = 0xf3 (guard bytes).
     0x89044          the 8-byte store of frame at s1 + 16 (its own machine frame).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x89038 - 0x8904c the check of the 4-byte store at s + 212, then the store of 0 there (S_inflight, :162).
     0x89050 - 0x89064 the check of the 4-byte store at s + 168, then the store of 0 there (S_desk_counter_valid,
                      :163). The world is now slost_w1 Bw.
     0x89068 - 0x8907c s5 = s + 112, s10 = the address of its shadow byte; the check of the 4-byte load; s11 = the
                      4-byte signed load at s + 112 (S_state (slost_w1 Bw)).
     0x89080          s11 = 0 (S_IDLE) goes to 0x89138: set_state's :81-82, no notice and no state store
                      (slost_model's first branch).
     0x89084 - 0x890a8 s6 = frame + 32 = p, the struct diginet_notice; shadow bytes 4..12 = 0 (its 72 bytes marked
                      usable).
     0x890ac - 0x890b8 a0 = p + 16, a1 = 0, a2 = 56; the call of __asan_memset (checked_memset, 0x5284c =
                      transport_sigma TS___asan_memset) at 0x890b8, return address 0x890bc: the notice's bytes
                      16 .. 71 set to 0 (:83).
     0x890bc - 0x890c8 plain stores into the frame: the 8 bytes of 2 at p (kind = N_STATE = 2 at p, state = S_IDLE = 0
                      at p + 4), the low 32 bits of s11 at p + 8 (old), the low 32 bits of why at p + 12 (reason). The
                      72 bytes at p are then slost_ntc Bw why as trans_ntc_at reads them: every field from p + 16 on is
                      0 (the announce pointer 0, n_ann = None; the body pointer 0 and body_len 0, n_body = []).
     0x890cc - 0x890d4 the check of the 4-byte store at s + 112 (its shadow byte read again through s10), then the
                      store of 0 at s + 112 (S_state = S_IDLE, :84). The world is now slost_w2 Bw.
     0x890d8 - 0x890fc the checks of the 8-byte loads at s + 96 and at s + 104.
     0x89100 - 0x8910c a2 = the 8-byte load at s + 96 (S_notify (slost_w2 Bw): tw_read, and the model's call_notify
                      gives TI.ti_notice timg_A = 0x83578); a0 = the 8-byte load at s + 104 (notify_ctx, which notice
                      does not read); a1 = p; the indirect call (jalr a2) at 0x8910c, return address 0x89110 (:85;
                      struct diginet_session + 96, notify -> notice).
     0x89110 - 0x89134 shadow bytes 4..12 = 0xf8 (the notice out of scope again).
     0x89138 - 0x89140 the header word 0x45e0360e stored at frame.
     0x89144          s2 = 0 goes to 0x891d8 (the real-stack arm; not taken).
     0x89148 - 0x891d4 the release: the frame's 32 shadow bytes (256 bytes) = 0xf5 (released); a0 = the 8-byte load at
                      s2 + 248 (the frame's last word, which holds the flag byte's address: astack_malloc_realizes'
                      rdword), then the store of one zero byte at a0 (YG0d.v astack_free_law); to 0x89228.
     0x891d8 - 0x89224 the real-stack arm's release: shadow bytes 0..19 = 0.
     0x89228 - 0x89264 sp = s0 - 128, ra and s0 .. s11 loaded back, sp = sp + 128, return. a0 .. a7 at the return are
                      not stated (void).
   The model and the code: the three g_s stores are the model's set_S_inflight, set_S_desk_counter_valid and
   set_S_state (put 4 of 0), each a tw_write inside g_s's payload; the test at 0x89080 is set_state_m's
   S_state B =? S_IDLE; the call is call_notify at slost_w2 Bw with slost_ntc Bw why (slost_model). The code has no
   trap of its own; the model's None cases are call_notify's (S_notify <> ti_notice timg_A) and notice's, both ruled
   out by the model premise.
   Error paths (6 calls; no abort) and the facts that rule them out:
     TS___asan_report_store4 0x59928 (errpath_store4) at 0x89274 (s + 212), 0x89284 (s + 168), 0x892ac (s + 112);
     TS___asan_report_load4 0x59608 (errpath_load4) at 0x89298 (s + 112);
     TS___asan_report_load8 0x596a8 (errpath_load8) at 0x892b0 (s + 96) and 0x892b4 (s + 104).
     Each guards a naturally aligned access inside g_s's payload [0x5df9c0, 0x5e4118) (2283 whole granules), whose
     shadow bytes are 0 (trans_slost_cells, read at each AR state by DgnTransportCg.v decode_zshadow_rd), so k = 0.
     The memset's own check (aintrin_realizes' pre, from the G journal through TransportGCg.v gx_intrin_at): the
     destination [p + 16, p + 72) lies in the frame this function took; its shadow bytes 6 .. 12 are 0 since
     0x890a8 and their hull is visible (astack_malloc_realizes' zero_shadow); each destination byte is a byte of the
     journal's own frame list after the stack malloc (YCbq.v awr_byte's in_frames: transport_twr_ok_g), not owned,
     not in the ESTACK bytes below sp.
   Writes: g_s's three fields (bytes of G); its own machine frame; its own side-stack frame, that frame's shadow bytes
   and its flag byte; notice's stores (notice_wr, bytes of GOT). No byte of a caller's frame or block is written, so
   slost_wr (g_s's fields and notice_wr) is the written range. The G kit for the own frame (TransportGCg.v):
   dk_kept_own_g with dkg_nf and dkg_nf_sep (a step that writes the own frame, its shadow bytes or its flag byte keeps
   acall_kept_g: they are apart from the caller's frames, blocks and the image), dk_kept_trans_nf_g (notice's
   acall_kept_g is stated at the call state, whose frames are the own frame :: frames Sc; notice_wr (slost_w2 Bw)
   (slost_ntc Bw why) lies inside slost_wr Bw why), dkg_frame_al64 (the frame starts on 64 bytes), gx_intrin_at (the
   memset) and dk_kept_frame_byte_g; the stack malloc's and the release's journal steps are CanKit.v
   can_stack_malloc_at and can_flag_store_pi (YCbq.v's own-frame rules without model_laws and api_env: the donor
   journal with (cid, pos) :: own, and back), read inside the G journal through gx_lift.
   Callee texts assumed: __asan_stack_malloc_2 as astack_malloc_realizes ... SLOST_CID (with
   pc_stack_malloc (as_code B) SLOST_CID = transport_sigma TS___asan_stack_malloc_2); __asan_memset as
   aintrin_realizes ... OSet (transport_sigma TS___asan_memset); notice as notice_cg.v transport_notice_cg at
   TI.ti_notice timg_A (= 0x83578 = transport_obj 10, notice_cg.v notice_at), a G-form callee composed in the same G
   journal (no gx_call_cg). Each premise of transport_notice_cg at the call, and where it comes from:
     the journal: session_lost's G journal at the call state (the own frame live); ra = 0x89110 (ret_ok,
       4096 <= ra); gp, tp kept; a1 = p;
     sp mod 16 = 0: the realigned sp is 32-aligned; sp0 - STK <= sp' - NOTICE_STK: sp' >= sp - 144 and
       SLOST_STK = 144 + NOTICE_STK (slost_stk_eq); sp' <= sp0;
     trans_ntc_at p (slost_ntc Bw why): 0 < p and p mod 8 = 0 (p = frame + 32, dkg_frame_al64); trans_src_ok by
       decode_in_fake at the call state ([frame + 32, frame + 104) inside the 256 bytes of a frame of its frames) with
       decode_rd_ok (the bytes present by astack_malloc_realizes, shadow bytes 4..12 = 0, their hull visible);
       decode_off_win (the frame lies below alloc_ceiling, notice's window above it); NB = the 72 bytes stored at
       0x890b8 - 0x890c8, whose fields are slost_ntc's; the body: pointer 0, length 0, garr8 of [], trans_src_ok of
       the empty range at 0 (DgnTransportCg.v trans_src_ok_null), decode_off_win of it (0 <= sp' - NOTICE_STK); the
       announce: n_ann = None with the pointer 0;
     trans_tframe_at TF at NOTICE_STK: session_lost's trans_tframe_at at SLOST_STK, carried: TF's bytes and their
       shadow are unchanged (slost_apart for the g_s stores; the own frame is a fresh frame, apart from TF's
       placement), and notice's window lies inside session_lost's;
     trans_rom_view_rd at the call memory: no store of session_lost reaches a read-only byte, the memset keeps every
       byte outside its destination and ESTACK bytes (gx_intrin_at), and the stack malloc's acall_kept keeps every
       TRANS_RO_RD byte (trans_ro_rd_scoped, from trans_ro_rd_unowned and trans_rom_no_errno);
     tw_at at slost_w2 Bw: G kept through the stack malloc (gx_kept_of_acall_kept: gx_ok, gx_noerrno), then the three
       tw_writes;
     notice_m timg_A TF (slost_w2 Bw) (slost_ntc Bw why) = Some (Bw', tt): the model premise through slost_model (the
       state was not S_IDLE on this path; call_notify's test is the indirect target's value);
     notice_apart: a byte of notice_wr is a byte of GOT (kind N_STATE), a byte of G, so not a byte of p's frame (a
       frame byte is outside the image: AR_laws' al_client_img); the body range is empty and n_ann = None; TF's range:
       slost_apart, since on this path notice_wr (slost_w2 Bw) (slost_ntc Bw why) lies inside slost_wr Bw why;
     the N_DATA premise: vacuous (n_kind = N_STATE);
     st_nev S + k + NOTICE_EV <= EV_MAX: SLOST_EV = NOTICE_EV, and the stack malloc records no event.
   notice's own record facts (notice_cg.v trans_notice_cells, gx_noerrno) are premises of notice's holds statement.
   session_lost lifts no donor callee, but the stack malloc's journal step (can_stack_malloc_at) leaves acall_kept,
   whose image clause keeps no owned-static or errno byte: G kept through it takes gx_noerrno, and the TRANS_RO_RD
   bytes take trans_ro_rd_unowned and trans_rom_no_errno, so the holds statement takes all three.
   Stack: 128 bytes of its own, the at most 0x10 bytes of the realignment, and below the realigned sp the largest
   callee window: ESTACK (the stack malloc, the memset) or notice's NOTICE_STK: SLOST_STK = 144 + NOTICE_STK
   (slost_stk_eq).

   The caller: diginet_session_rx at 0x879d8 (return address 0x879dc): a0 = s4 (its own a0, &g_s, since 0x87600),
   a1 = 7 (DIGINET_R_DESK_DISCONNECT), when the S_state it loaded at 0x87910, minus 1, is at most 1 unsigned (WAKING
   or ONLINE: diginet_session_rx_m's test, TSess.v:383-384). It supplies its G journal, tw_at, g_fail_next, the model
   premise (that branch of diginet_session_rx_m), trans_tframe_at and slost_apart of its TF, trans_rom_view_rd, and
   count_cid 2 (frames Sc) < fs_frames 2 (its own side-stack frame is of class 1). The image also has 4 inlined copies
   of session_lost (in diginet_session_tick and on_announce): those are walked inside their
   functions, not by this statement. *)
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

(* session_lost's frame (`sp = sp - 128` at TS_session_lost), the at most 0x10 bytes of `sp = sp & -32` (0x88f48)
   below it, and the largest stack a callee uses below the realigned sp: ESTACK for __asan_stack_malloc_2 and
   __asan_memset (YG0d.v ecall_pre), notice's NOTICE_STK. *)
Definition SLOST_FRAME : Z := 128.
Definition SLOST_ALIGN : Z := 0x10.
Definition SLOST_STK : Z := SLOST_FRAME + SLOST_ALIGN + Z.max ESTACK NOTICE_STK.
Lemma slost_stk_eq : SLOST_STK = SLOST_FRAME + SLOST_ALIGN + NOTICE_STK.
Proof. reflexivity. Qed.
(* No allocator event: notice records none, and the class-2 stack malloc and its release record none (YG00.v
   stack_malloc, stack_free). *)
Definition SLOST_EV : Z := NOTICE_EV.
(* The side-stack class (a0 = 160 at 0x88f74, the call of __asan_stack_malloc_2 at 0x88f78). *)
Definition SLOST_CID : Z := 2.
(* Its first argument: g_s's base in image A. *)
Definition SLOST_S : Z := TA_g_s.
(* The addresses of the five g_s fields the code reads or writes (s + 212, s + 168, s + 112, s + 96, s + 104). *)
Lemma slost_addrs :
  SLOST_S = 0x5df9c0 /\
  SLOST_S + (TW.A_S_inflight - TW.OFF_g_s) = 0x5dfa94 /\
  SLOST_S + (TW.A_S_desk_counter_valid - TW.OFF_g_s) = 0x5dfa68 /\
  SLOST_S + (TW.A_S_state - TW.OFF_g_s) = 0x5dfa30 /\
  SLOST_S + (TW.A_S_notify - TW.OFF_g_s) = 0x5dfa20 /\
  SLOST_S + (TW.A_S_notify_ctx - TW.OFF_g_s) = 0x5dfa28.
Proof. repeat split; reflexivity. Qed.

(* The model's steps (TSess.v session_lost_m, set_state_m): the world after the stores of :162-163, the world after
   set_state's store of the state (:84), and set_state's notice (:83). *)
Definition slost_w1 (Bw : list byte) : list byte := TW.set_S_desk_counter_valid (TW.set_S_inflight Bw 0) 0.
Definition slost_w2 (Bw : list byte) : list byte := TW.set_S_state (slost_w1 Bw) TS0.DIGINET_S_IDLE.
Definition slost_ntc (Bw : list byte) (why : Z) : TI.ntc :=
  TI.Ntc TS0.DIGINET_N_STATE TS0.DIGINET_S_IDLE (TW.S_state (slost_w1 Bw)) why 0 0 0 0 None [] 0.
Lemma slost_model : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte) (why : Z),
  TSS.session_lost_m I F Bw why =
  if TW.S_state (slost_w1 Bw) =? TS0.DIGINET_S_IDLE then Some (slost_w1 Bw, tt)
  else TSS.call_notify I F (slost_w2 Bw) (slost_ntc Bw why).
Proof. intros I F Bw why. reflexivity. Qed.

(* The bytes the code stores into G, exactly: g_s's inflight and desk_counter_valid (4 bytes each); when the state
   changes, g_s's state (4 bytes) and notice's stores at the world slost_w2 Bw (notice_cg.v notice_wr: for an N_STATE
   notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and GOT.n). *)
Definition slost_wr (Bw : list byte) (why a : Z) : Prop :=
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_inflight 4 a \/
  twa_fld TW.OFF_g_s TA_g_s TW.A_S_desk_counter_valid 4 a \/
  (TW.S_state (slost_w1 Bw) <> TS0.DIGINET_S_IDLE /\
   (twa_fld TW.OFF_g_s TA_g_s TW.A_S_state 4 a \/ notice_wr (slost_w2 Bw) (slost_ntc Bw why) a)).

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after the g_s stores and after its own (notice_cg.v notice_apart). *)
Definition slost_apart (Fr : option TI.tframe) (Bw : list byte) (why : Z) : Prop :=
  forall x, slost_wr Bw why x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow. The
   instrumented checks of the accesses at s + 96 .. s + 215 read it. *)
Definition trans_slost_cells (B : asyms) : Prop := decode_zshadow_at B SLOST_S (SLOST_S + TW.SZ_g_s).

Section slost. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range
   slost_wr Bw why, no meter charge (the side-stack frame changes st_fs only), and X: the world relation at the
   model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame this
   function takes is released. *)
Definition transport_slost_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) (why : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    SLOST_STK SLOST_EV 0 (slost_wr Bw why)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_session_lost_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (why : Z) (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SLOST_S -> YK11.getr regs 11 = w64 why ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SLOST_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.session_lost_m timg_A TF Bw why = Some (Bw', tt) ->
    0 <= why < 2 ^ 31 ->
    trans_tframe_at B lyc Sc W memc regs SLOST_STK TF ->
    trans_rom_view_rd W memc ->
    slost_apart TF Bw why ->
    count_cid SLOST_CID (frames Sc) < fs_frames SLOST_CID ->
    st_nev S + k + SLOST_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_slost_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' why).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells (the flag word
   and the shadow base through their GOT words), the shadow of g_s's payload, the TRANS_RO_RD bytes outside the owned
   statics and errno (DgnTransportCg.v trans_ro_rd_scoped: they stay the image's through the stack malloc's
   acall_kept), the allocator, meter and side-stack laws, G inside the image, outside the allocator's statics and
   outside errno (G kept through the stack malloc's acall_kept: TransportGCg.v gx_kept_of_acall_kept), and the
   contracts of __asan_stack_malloc_2, __asan_memset and notice (at the value the session's notify pointer holds)
   give the contract at TS_session_lost. *)
Definition transport_session_lost_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) SLOST_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B -> trans_slost_cells B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  gx_ok segs B TG.G_HARNESS -> gx_noerrno B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SLOST_CID) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @transport_notice_cg fx' rc B MT (TI.ti_notice timg_A)) ->
  transport_session_lost_cg (transport_sigma TS_session_lost).
End slost.
