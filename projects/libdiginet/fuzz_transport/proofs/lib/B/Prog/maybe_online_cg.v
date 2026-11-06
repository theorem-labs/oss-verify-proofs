(* maybe_online_cg: image B's ASan walk contract of maybe_online (transport/src/diginet_session.c:176-182, with ms
   (:77) inlined and set_state (:79-86) CALLED by a tail jump; model lib/TModel/TSess.v maybe_online_m and
   set_state_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x8ae8c = transportb_sigma TB_maybe_online, size 332,
   as STATEMENTS only (no proof). It stores into g_s, a harness global, and tail-jumps to set_state, a G-form walk
   (set_state_cg.v) that takes the class-2 side-stack frame for the struct diginet_notice and calls notice, so it is a
   G-form caller-journal walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v
   G_HARNESS_B with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post
   (acall_kept_g over G_HARNESS_B). Image B's twin of lib/A/Prog/maybe_online_cg.v, with image A's definitions,
   premises and post; its code is image B's own (a 16-byte frame and a tail jump, where image A inlines set_state),
   so the walk's form for the tail jump is lib/B/Prog/m_tick_cg.v's (m_tick tail-jumps to the G-form m_set). The
   differences are listed at the end of this comment.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s). TF is the current heap frame (check_state_data_cg.v
   trans_tframe_at at this call's window); the read-only bytes notice's callees read are the image's
   (trans_rom_view_rd). The memory relates to the world Bw by image B's world relation (TWorldG.v tw_at at TWorldB.v
   TMAP_B, read through aview), g_fail_next Bw <= 1, and maybe_online_m timg_B TF Bw = Some (Bw', tt). No byte the
   call stores is a byte of TF (maybeon_apart). Class 2 of the side stack has a free frame (set_state's). The function
   returns to ra with the callee-saved registers kept, no allocator event and no meter charge (set_state's side-stack
   frame changes the state's st_fs only), set_state's side-stack frame released (the caller's frames exactly), the
   caller's blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at or above alloc_ceiling outside the
   call's stack window [sp - MAYBEON_STK, sp), the image bytes outside G, the owned statics and errno, the caller's
   block and frame bytes outside maybeon_wr Bw), the world relation at Bw', and g_fail_next Bw' <= 1.

   The translation from the plain contract (lib/Prog/T/maybe_online_c.v) is image A's: a0 = W_BASE_PLAIN + OFF_g_s ->
   a0 = TB_g_s; wmem -> tw_at; g_fail_next B <= 1 kept as a premise, and the post's g_fail_next B' <= 1 kept in X (the
   code neither reads nor writes g_fail_next; set_state's statement asks the premise at the world of the jump and
   gives the post fact; the callers carry it on toward io_send, whose code tests the byte's bit 0); timg_plain ->
   timg_B; tframe_at -> trans_tframe_at at MAYBEON_STK, and its off_world clause -> maybeon_apart, the part of it
   this call needs: no byte the call stores is a byte of TF (notice_cg.v notice_apart's form; trans_src_ok alone
   admits a range of G, so trans_tframe_at does not give it); relro_img -> trans_rom_view_rd; stk, lo + FRAME <= sp,
   sp mod 16 and w_off_stack -> the journal's window premises; mem_inv is dropped. The post's
   munch, wmono, stk and mem_inv -> transport_cg_post (the journal at the return, acall_kept_g over maybeon_wr); wmem
   -> X's tw_at.
   Premises the plain contract does not have (image A's): count_cid 2 (frames Sc) < fs_frames 2 (on image B the
   class-2 frame is set_state's, which its statement asks at the jump state, whose frames are frames Sc: maybe_online
   takes no side-stack frame); maybeon_apart (above).
   Run invariants: none is carried. The one program callee, set_state, carries none (its notice has kind N_STATE, so
   notice's N_DATA premise holds vacuously: set_state_cg.v). maybe_online's own accesses are at fixed offsets of g_s
   (s + 24 .. s + 191), so its code needs no bound that the model does not give.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and this function's 332 code bytes are equal in both files), 83
   words:
     0x8ae8c - 0x8ae90 sp = sp - 16; ra at sp + 8, loaded back at 0x8af5c (the tail-jump path) and 0x8af68 (the return
                      path). No side-stack frame, no realignment, no frame pointer, no other register saved.
     0x8ae94 - 0x8ae98 s & 7 <> 0 (a1 = s & 7) goes to the trap word at 0x8af74.
     0x8ae9c - 0x8aea4 a3 = the 8-byte load of the GOT word 0xa3cf0, then the 8-byte load at the cell 0xac678 it holds:
                      the shadow base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for a 4-byte access,
                      ((a & 7) + 3) < k (signed) goes on; for an 8-byte access any k <> 0 goes to the error path.
     0x8aea8 - 0x8aeb8, 0x8af78 - 0x8af88 the check of the 4-byte load at s + 112.
     0x8aebc - 0x8aec4 a1 = the 4-byte signed load at s + 112 (S_state Bw); <> 1 (S_WAKING) goes to 0x8af68 (:178).
     0x8aec8 - 0x8aed8, 0x8af8c - 0x8af9c the check of the 4-byte load at s + 144.
     0x8aedc - 0x8aee0 the 4-byte load (S_wake_acked Bw) = 0 goes to 0x8af68.
     0x8aee4 - 0x8aef4, 0x8afa0 - 0x8afb0 the check of the 4-byte load at s + 140.
     0x8aef8 - 0x8aefc the 4-byte load (S_e1_named_us Bw) = 0 goes to 0x8af68. Past 0x8aefc, maybeon_go Bw holds.
     0x8af00 - 0x8af10, 0x8afc8 - 0x8afcc the check of the 8-byte load at s + 176.
     0x8af14 - 0x8af28, 0x8afb4 - 0x8afc4 the check of the 4-byte load at s + 24 (its shadow byte loaded at 0x8af20,
                      tested at 0x8af28); a4 = the 8-byte load at s + 176 (S_last_rx_us Bw, at 0x8af24).
     0x8af2c - 0x8af3c, 0x8afd0 - 0x8afd4 the check of the 8-byte store at s + 184.
     0x8af40 - 0x8af58 a1 = the 4-byte unsigned load at s + 24 (S_cfg_keepalive_ms Bw); a2 = a1 * 1000; a4 = a2 + a4
                      (mod 2 ^ 64; ms_m, u64); a1 = 2 (S_ONLINE), a2 = 2 (R_ONLINE); the 8-byte store of a4 at s + 184
                      (S_next_keepalive_us, :179) at 0x8af58. The world is now maybeon_w1 Bw.
     0x8af5c - 0x8af64 ra loaded back, sp = sp + 16; the jump (no link) to set_state at 0x872cc = transportb_sigma
                      TB_set_state (:180), with a0 = s, a1 = st = 2, a2 = why = 2, and ra, sp and the callee-saved
                      registers of maybe_online's entry.
     0x8af68 - 0x8af70 ra loaded back, sp = sp + 16, return. a0 .. a7 at the return are not stated (void).
     0x8af74          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x8af78 - 0x8afd4 the slow paths of the 4-byte checks and the 6 error calls.
   One tail jump (0x8af64, to set_state); every other j is inside the function, the error calls are jal with link, and
   the return path ends with ret.
   The model and the code: the three tests at 0x8aec4, 0x8aee0, 0x8aefc are maybe_online_m's (maybeon_go: S_state Bw
   =? S_WAKING, S_wake_acked Bw and S_e1_named_us Bw against 0, each a 32-bit signed read); the store at s + 184 is
   set_S_next_keepalive_us with u64 (S_last_rx_us Bw + ms_m (S_cfg_keepalive_ms Bw)) (a 4-byte unsigned read, so the
   product is below 2 ^ 42), a tw_write inside g_s's payload; the tail jump is maybe_online_m's set_state_m step at
   maybeon_w1 Bw with st = S_ONLINE and why = R_ONLINE (maybeon_model_sstate). set_state_m's test S_state B =?
   S_ONLINE is set_state's own (its 0x8741c), false on this path (S_state (maybeon_w1 Bw) = S_state Bw = S_WAKING).
   The model's None cases are set_state's (call_notify's and notice's), ruled out inside set_state's statement by the
   model premise.
   Trap path (the unimp word at 0x8af74, from 1 branch) and the fact that refutes it: 0x8ae98 (s & 7 <> 0): s =
   0x5df640, a multiple of 8.
   Error paths (6 calls; no abort) and the facts that rule them out:
     __asan_report_load4 (0x59644) at 0x8af88 (s + 112), 0x8af9c (s + 144), 0x8afb0 (s + 140), 0x8afc4 (s + 24);
     __asan_report_load8 (0x596e4) at 0x8afcc (s + 176);
     __asan_report_store8 (0x59a04) at 0x8afd4 (s + 184).
     Each guards a naturally aligned access inside g_s's payload [0x5df640, 0x5e3d98) (2283 whole granules), whose
     shadow bytes are 0 (trans_maybeon_cells, read at each AR state by DgnTransportBCg.v decode_zshadow_rd), so k = 0.
   Writes: g_s's next_keepalive_us (bytes of G) and its own machine frame (ra at sp - 8), then set_state's
   (set_state_cg.v sstate_wr (maybeon_w1 Bw) S_ONLINE R_ONLINE: g_s's state and notice's stores, when the state
   changes; its own frames). No byte of a caller's frame or block is written, so maybeon_wr (A's text: g_s's two
   fields and notice_wr; maybeon_wr_sstate reads it as the store at s + 184 and set_state's range) is the written
   range.
   Callee text assumed: set_state as set_state_cg.v transport_set_state_cg at transportb_sigma TB_set_state (tail
   jump at 0x8af64; a G-form callee entered on the same journal with maybe_online's ra, sp and callee-saved
   registers, so its post is maybe_online's post: the same journal, the same stack window, its written range inside
   maybeon_wr Bw). Each premise of transport_set_state_cg at the jump, and where it comes from:
     the journal: maybe_online's G journal at the jump state (the store at s + 184 a G byte, transport_twr_ok_g's
       inG case; ra's save at sp - 8 a window byte); ra, gp, tp as at entry (ret_ok, 4096 <= ra); a0 = SSTATE_S = s,
       a1 = st = 2, a2 = why = 2, 0 <= st, why < 2 ^ 31;
     sp mod 16 = 0, sp0 - STK <= sp - SSTATE_STK, sp <= sp0: the entry sp, and MAYBEON_STK = SSTATE_STK
       (maybeon_stk_eq);
     tw_at at maybeon_w1 Bw: the tw_write of S_next_keepalive_us; g_fail_next (maybeon_w1 Bw) = g_fail_next Bw <= 1;
     set_state_m timg_B TF (maybeon_w1 Bw) S_ONLINE R_ONLINE = Some (Bw', tt): the model premise through
       maybeon_model_sstate on this path (maybeon_go Bw);
     trans_tframe_at TF at SSTATE_STK: maybe_online's at MAYBEON_STK, carried: TF's bytes and their shadow are
       unchanged (maybeon_apart for the store at s + 184; ra's save lies in the window, which decode_off_win puts
       apart from TF), and the window is the same;
     trans_rom_view_rd at the jump memory: maybe_online's two stores are a G byte and a window byte, neither a
       TRANS_RO_RD byte;
     sstate_apart TF (maybeon_w1 Bw) S_ONLINE R_ONLINE: maybeon_apart, since on this path sstate_wr (maybeon_w1 Bw)
       S_ONLINE R_ONLINE lies inside maybeon_wr Bw (maybeon_wr_sstate);
     count_cid SSTATE_CID (frames Sc) < fs_frames SSTATE_CID: the premise (MAYBEON_CID = SSTATE_CID, frames unchanged
       at the jump);
     st_nev S + k + SSTATE_EV <= EV_MAX: MAYBEON_EV = SSTATE_EV.
   set_state's own record facts (the stack-malloc entry, the side-stack laws, its cells, gx_noerrno,
   trans_ro_rd_unowned, trans_rom_no_errno) are premises of set_state's holds statement, not of this one.
   Stack: 16 bytes of its own below the entry sp (no call runs from it but the refuted error calls); set_state's
   window SSTATE_STK below the entry sp: MAYBEON_STK = Z.max 16 SSTATE_STK = SSTATE_STK.

   The callers: on_announce at 0x881a4 (return address 0x881a8): a0 = s4 (its own a0, &g_s, since 0x87d30), after its
   store of 1 at s + 140 (S_e1_named_us, 0x8819c); on_ack at 0x8881c (return address 0x88820): a0 = s3 (its own a0,
   &g_s, since 0x885f0), after its store of 1 at s + 144 (S_wake_acked, 0x88814). Each takes a side-stack frame of its
   own and calls maybe_online while it is live: on_announce a class-3 frame (__asan_stack_malloc_3 at 0x87d3c), on_ack
   a class-2 frame (__asan_stack_malloc_2 at 0x885fc), so on_ack's class-2 count must leave room for set_state's
   frame. Each supplies its G journal, tw_at, g_fail_next, the model premise (its branch of on_announce_m / on_ack_m),
   trans_tframe_at and maybeon_apart of its TF, trans_rom_view_rd, and count_cid 2 (frames Sc) < fs_frames 2.

   Against image A's statement (lib/A/Prog/maybe_online_cg.v): the same definitions (maybeon_go, maybeon_w1,
   maybeon_w2, maybeon_ntc, maybeon_model, maybeon_wr, maybeon_apart), premises and post, at image B's names (TMAP_B,
   timg_B, TB_g_s, transportb_sigma, G_HARNESS_B, lib/B/Prog/DgnTransportBCg.v, lib/B/Prog/m_set_cg.v twb_fld). What
   image B's code forces: (1) set_state is a function, reached by a tail jump (0x8af64) after maybe_online's 16-byte
   frame is given back, where image A's maybe_online inlines it (its own 96-byte frame, realignment, class-2 stack
   malloc, memset, notice call and release): the holds statement takes set_state's contract in place of the
   contracts of __asan_stack_malloc_2, __asan_memset and notice, and of the side-stack and read-only record facts
   only set_state's walk uses; MAYBEON_STK = SSTATE_STK (image A: 112 + NOTICE_STK), MAYBEON_EV = SSTATE_EV,
   MAYBEON_CID = SSTATE_CID, and the count premise is set_state's at the jump state; three lemmas read A's
   definitions as set_state's (maybeon_model_sstate, maybeon_sstate, maybeon_wr_sstate). (2) One UBSan branch to the
   trap word 0x8af74 (the alignment check of s), refuted by the constant s. (3) 6 error calls of its own (image A's 9
   include the state store's and the notify loads' checks, which on image B are set_state's). No premise of the
   contract is added or dropped; the holds statement takes set_state's contract in place of the inlined callees'. *)
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
  m_set_cg check_state_data_cg notice_cg set_state_cg.
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

(* maybe_online's frame (`sp = sp - 16` at TB_maybe_online; no realignment), given back before the tail jump to
   set_state at 0x8af64, which runs from the entry sp: its window SSTATE_STK is the call's. *)
Definition MAYBEON_FRAME : Z := 16.
Definition MAYBEON_STK : Z := Z.max MAYBEON_FRAME SSTATE_STK.
Lemma maybeon_stk_eq : MAYBEON_STK = SSTATE_STK.
Proof. reflexivity. Qed.
(* No allocator event: maybe_online calls no allocator and takes no side-stack frame, and set_state records none. *)
Definition MAYBEON_EV : Z := SSTATE_EV.
(* The side-stack class of the frame set_state takes (its a0 = 160 at 0x8733c, the call of __asan_stack_malloc_2 at
   0x87340): the class of the count premise. *)
Definition MAYBEON_CID : Z := SSTATE_CID.
(* Its argument: g_s's base in image B. *)
Definition MAYBEON_S : Z := TB_g_s.
(* The addresses of the six g_s fields maybe_online's own code reads or writes (s + 112, s + 144, s + 140, s + 176,
   s + 24, s + 184); s + 96 and s + 104 (notify) are set_state's. *)
Lemma maybeon_addrs :
  MAYBEON_S = 0x5df640 /\ MAYBEON_S = SSTATE_S /\
  MAYBEON_S + (TW.A_S_state - TW.OFF_g_s) = 0x5df6b0 /\
  MAYBEON_S + (TW.A_S_wake_acked - TW.OFF_g_s) = 0x5df6d0 /\
  MAYBEON_S + (TW.A_S_e1_named_us - TW.OFF_g_s) = 0x5df6cc /\
  MAYBEON_S + (TW.A_S_last_rx_us - TW.OFF_g_s) = 0x5df6f0 /\
  MAYBEON_S + (TW.A_S_cfg_keepalive_ms - TW.OFF_g_s) = 0x5df658 /\
  MAYBEON_S + (TW.A_S_next_keepalive_us - TW.OFF_g_s) = 0x5df6f8.
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
(* Image B's code makes the set_state_m step a tail jump to set_state at maybeon_w1 Bw (st = S_ONLINE, why =
   R_ONLINE), whose steps are maybeon_w2 and maybeon_ntc. *)
Lemma maybeon_model_sstate : forall (I : TI.timg) (F : option TI.tframe) (Bw : list byte),
  TSS.maybe_online_m I F Bw =
  if maybeon_go Bw then TSS.set_state_m I F (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE
  else Some (Bw, tt).
Proof. intros I F Bw. reflexivity. Qed.
Lemma maybeon_sstate : forall (Bw : list byte),
  maybeon_w2 Bw = sstate_w (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE /\
  maybeon_ntc Bw = sstate_ntc (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE.
Proof. intros Bw. split; reflexivity. Qed.

(* The bytes the code stores into G, exactly: when the test of :178 holds, g_s's next_keepalive_us (8 bytes) and,
   when the state changes, g_s's state (4 bytes) and notice's stores at the world maybeon_w2 Bw (notice_cg.v
   notice_wr: for an N_STATE notice, GOT.t[GOT.n] when 0 <= GOT.n < TRANS_MAX, and GOT.n). *)
Definition maybeon_wr (Bw : list byte) (a : Z) : Prop :=
  maybeon_go Bw = true /\
  (twb_fld TW.OFF_g_s TB_g_s TW.A_S_next_keepalive_us 8 a \/
   (TW.S_state (maybeon_w1 Bw) <> TS0.DIGINET_S_ONLINE /\
    (twb_fld TW.OFF_g_s TB_g_s TW.A_S_state 4 a \/ notice_wr (maybeon_w2 Bw) (maybeon_ntc Bw) a))).
(* The same range as image B's code makes it: the store at s + 184, then set_state's written range at the world of
   the tail jump. *)
Lemma maybeon_wr_sstate : forall (Bw : list byte) (a : Z),
  maybeon_wr Bw a <->
  maybeon_go Bw = true /\
  (twb_fld TW.OFF_g_s TB_g_s TW.A_S_next_keepalive_us 8 a \/
   sstate_wr (maybeon_w1 Bw) TS0.DIGINET_S_ONLINE TS0.DIGINET_R_ONLINE a).
Proof. intros Bw a. split; intros H; exact H. Qed.

(* No byte the call stores is a byte of the current heap frame TF: the plain contract's tframe_at puts TF off the
   world. notice reads TF after the g_s stores and after its own (notice_cg.v notice_apart). *)
Definition maybeon_apart (Fr : option TI.tframe) (Bw : list byte) : Prop :=
  forall x, maybeon_wr Bw x ->
    forall fr, Fr = Some fr -> ~ (TI.tf_addr fr <= x < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr))).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of the accesses at
   s + 24 .. s + 191 read it. *)
Definition trans_maybeon_cells (B : asyms) : Prop := decode_zshadow_at B MAYBEON_S (MAYBEON_S + TW.SZ_g_s).

Section maybeon. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   maybeon_wr Bw, no meter charge (set_state's side-stack frame changes st_fs only), and X: the world relation at the
   model's world Bw' and g_fail_next Bw' <= 1. transport_cg_post states frames S2 = frames Sc: the frame set_state
   takes is released. *)
Definition transport_maybeon_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs MAYBEON_STK MAYBEON_EV 0 (maybeon_wr Bw)
    (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1).

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_maybe_online_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (TF : option TI.tframe) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 MAYBEON_S ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MAYBEON_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.maybe_online_m timg_B TF Bw = Some (Bw', tt) ->
    trans_tframe_at B lyc Sc W memc regs MAYBEON_STK TF ->
    trans_rom_view_rd W memc ->
    maybeon_apart TF Bw ->
    count_cid MAYBEON_CID (frames Sc) < fs_frames MAYBEON_CID ->
    st_nev S + k + MAYBEON_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_maybeon_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_s's
   payload, the allocator and meter laws, G inside the image and outside the allocator's statics, and the contract
   of set_state (the tail jump's target) give the contract at TB_maybe_online. *)
Definition transport_maybe_online_cg_holds_stmt : Prop :=
  transport_cells B -> trans_maybeon_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_set_state_cg fx' rc B MT (transportb_sigma TB_set_state)) ->
  transport_maybe_online_cg (transportb_sigma TB_maybe_online).
End maybeon.
