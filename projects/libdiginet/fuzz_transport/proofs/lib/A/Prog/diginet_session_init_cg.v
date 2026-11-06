(* diginet_session_init_cg: the ASan walk contract of diginet_session_init (transport/src/diginet_session.c:56-75;
   model lib/TModel/TSess0.v diginet_session_init_m) on fuzz_transport.asan (e89be137db17) at 0x864ec =
   transport_sigma TS_diginet_session_init, size 528, as STATEMENTS only (no proof). It is a G-form caller-journal
   walk: the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS (the payloads of
   the 18 harness globals) with no out cell (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v
   transport_cg_post (acall_kept_g over G_HARNESS).

   The contract. a0 = s = &g_s = 0x5df9c0 (TWorldA.v TA_g_s), a1 = cfg = &g_cfg = 0x5df080 (TA_g_cfg), a2 = io = iop,
   the address of the caller's struct diginet_io (32 bytes: ctx, send, recv, now_us, each 8 bytes little-endian),
   a3 = notify = ntf, a4 = ctx (fuzz_transport.c:1165). io is 8-byte aligned, not 0, and lies where a callee may read
   (DgnTransportCg.v trans_src_ok: in the machine stack (a caller's machine frame), in a caller's side-stack frame,
   in a heap block, in G or in the read-only bytes), outside this call's stack window (decode_off_win) and
   outside g_s's payload (the bytes the call stores); its 32 bytes hold the four fields (garr8). The memory relates
   to the world Bw by the world relation of image A (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), and
   (Bw', r) is the model's result (diginet_session_init_m Bw io_ctx io_send io_recv io_now ntf ctx = Some (Bw', r)).
   The function returns to ra with a0 = r (sign-extended: 0 or -1), the callee-saved registers kept, no allocator
   event and no meter charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS
   keeps (the bytes at or above alloc_ceiling outside the call's stack window [sp - 64 - ESTACK, sp), the image bytes
   outside G, the owned statics and errno, the caller's block and frame bytes outside sinit_wr r), and the world
   relation at Bw'. This is what the plain contract (lib/Prog/T/diginet_session_init_c.v) says: a0 = r;
   wmem rsegs m' B' with B' the model's world; munch of the frame and the world only. Its bytes_at / arg_blk / iop mod
   8 facts about io become garr8 / trans_src_ok / decode_off_win / iop mod 8; iop <> 0
   and the disjointness from g_s are what arg_blk gave on the plain side.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this
   function's 528 code bytes are equal in both files):
     0x864ec - 0x86508 sp = sp - 64: the frame is 64 bytes; ra at sp + 56, s0 .. s5 at sp + 48 .. sp + 8, loaded back
                      at 0x8666c - 0x86684. No side-stack frame, no frame pointer.
     0x8650c - 0x86524 s0 = s, a0 = -1; s = 0, cfg = 0 or io = 0 goes to 0x8666c (return -1, :58): not taken, since
                      s = 0x5df9c0, cfg = 0x5df080 and iop <> 0. s1 = cfg, s4 = io.
     0x86528 - 0x86530 a1 = the 8-byte load of the GOT word 0xa4090 (it holds 0xac9f8); s5 = the 8-byte load at
                      0xac9f8 (0x7fff8000, the shadow base): transport_cells rows 1-2.
     0x86534 - 0x86554 the instrumented check of the 8-byte load at io + 8 (the shadow byte k at
                      ((io + 8) >> 3) + 0x7fff8000; k <> 0 goes to the error path); s3 = notify; notify = 0 returns -1;
                      a1 = io->send (the 8-byte load at io + 8); io->send = 0 returns -1 (:58-59). s2 = ctx.
     0x8655c - 0x865a0 the instrumented check of the 4-byte load at cfg + 52 (k = 0 goes on; else (a & 7) + 3 < k
                      (signed) goes on; else the error path), a2 = cfg->max_cmds (signed load); 0 returns -1; the same
                      check at cfg + 56; max_cmds > 255 (unsigned) returns -1; a1 = (cfg->max_body - 1485) mod 2^32,
                      sign-extended; a1 < 2^64 - 1461 (unsigned), that is max_body outside [24, 1484], returns -1
                      (:60-62).
     0x865a4 - 0x865b4 a0 = s, a1 = 0, a2 = 18264; call of checked_memset (__asan_memset, 0x5284c = transport_sigma
                      TS___asan_memset) at 0x865b4, return address 0x865b8: g_s's 18264 bytes set to 0 (:63).
     0x865b8 - 0x865c4 a0 = s, a1 = cfg, a2 = 60; call of checked_memcpy (__asan_memcpy, 0x523b0 = transport_sigma
                      TS___asan_memcpy) at 0x865c4, return 0x865c8: s->cfg = *cfg (:64).
     0x865c8 - 0x865d4 a0 = s + 64, a1 = io, a2 = 32; call of checked_memcpy at 0x865d4, return 0x865d8: s->io = *io
                      (:65).
     0x865d8 - 0x8661c the instrumented check and the 8-byte store of notify at s + 96 (k <> 0: the error path); the
                      same for ctx at s + 104; the instrumented check (k = 0, or (a & 7) + 3 < k) and the 4-byte store
                      of 0 (DIGINET_S_IDLE) at s + 112 (:66-68).
     0x86620 - 0x86638 the instrumented check of the 4-byte load at cfg + 12; cfg->desk_mac_set = 0 goes to 0x8666c
                      with a0 = 0 (return 0, :69, :74).
     0x8663c - 0x86668 a0 = s + 120, a1 = cfg + 6, a2 = 6; call of checked_memcpy at 0x86648, return 0x8664c:
                      s->desk_mac = cfg->desk_mac (:70); the instrumented check and the 4-byte store of 1 at s + 116
                      (desk_known, :71); a0 = 0.
     0x8666c - 0x8668c ra, s0 .. s5 loaded back, sp = sp + 64, return. a1 .. a7 at the return are not stated.
   Error paths (8 calls; no trap path) and the fact that rules each out:
     0x866a0 errpath_load4 (cfg + 52), 0x866b4 errpath_load4 (cfg + 56), 0x866d4 errpath_load4 (cfg + 12):
       trans_scfg_cells B (diginet_session_config_default_cg.v; a fact of the record): the shadow bytes of g_cfg's 7
       whole granules [0x5df080, 0x5df0b8) are 0 and the shadow byte of its last granule is 4. cfg + 12 and cfg + 52
       lie in whole granules (k = 0); cfg + 56 is the first byte of the last granule, 0 + 3 < 4.
     0x866c4 errpath_store4 (s + 112), 0x866e8 errpath_store4 (s + 116), 0x866f4 errpath_store8 (s + 96), 0x866f8
       errpath_store8 (s + 104): trans_sinit_cells B (a fact of the record, decided by the closing file): the shadow
       bytes of g_s's 2283 whole granules [0x5df9c0, 0x5e4118) are 0 (a range of as_zero_shadow B; the record's
       Tfib_zero_shadow row (0x5df9c0, 0x5e4118 - 0x5df9c0)), and the 5 shadow bytes after them, 0x800b4823 ..
       0x800b4827 (the first shadow bytes of g_s's guard bytes), are 0xf9 (constant cells of the record;
       Tfib_const_shadow). AR re-reads both facts at every state (YG0n.v ARm am_zshadow, am_const).
     0x866f0 errpath_load8 (io + 8): io is 8-byte aligned, so io + 8 starts a granule inside [io, io + 32), which the
       premises make addressable (trans_src_ok: a heap block of the caller, AR_laws' shadow law; otherwise
       decode_rd_ok's range_addressable), so k = 0.
     The memset's and the memcpys' own checks need the same facts (aintrin_realizes' pre, through gx_intrin_at):
     range_addressable of [s, s + 18264), [s, s + 60), [s + 64, s + 96), [s + 120, s + 126), [cfg, cfg + 60),
     [cfg + 6, cfg + 12), [io, io + 32), and shadow_hull_vis, every shadow byte of the 8-aligned hull of each range
     visible. The hull of [s, s + 18264) is [0x800b3f38, 0x800b4828) (sinit_hull_end): g_s's 2283 zero shadow bytes
     and the 5 guard shadow bytes; the hulls of the three memcpy destinations lie in the zero ones; the hulls of
     [cfg, cfg + 60) and [cfg + 6, cfg + 12) are [0x800b3e10, 0x800b3e18), trans_scfg_cells' 8 bytes; io's is
     decode_rd_ok's shadow_hull_vis (or AR_laws' shadow law for a heap block).
   Callee texts assumed: __asan_memset as aintrin_realizes ... OSet (transport_sigma TS___asan_memset) and
   __asan_memcpy as aintrin_realizes ... OCpy (transport_sigma TS___asan_memcpy), which the walk applies from its G
   journal through TransportGCg.v gx_intrin_at (each destination a range of g_s, a byte of G:
   transport_twr_ok_g_intro; gx_rw of G is TransportGRwA.v G_HARNESS_rw). No program function is called.
   Stack: 64 bytes of its own and the ESTACK __asan_memset / __asan_memcpy use below sp - 64 (YG0d.v
   aintrin_realizes' ecall_pre): SINIT_STK.

   The caller is LLVMFuzzerTestOneInput (0x815f0): a0 = 0x5df9c0, a1 = s5 (&g_cfg), a2 = s4 (its struct diginet_io,
   filled by its __asan_memcpy at 0x813e0 from the 32 bytes at 0xa3d60), a3 = 0x83578 (notice), a4 = 0. It supplies
   the G journal of its own walk, the world relation and the facts about io. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module DL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_init's frame (`sp = sp - 64` at its entry; no realignment) and the ESTACK its callees,
   __asan_memset and __asan_memcpy, use below sp - 64. *)
Definition SINIT_FRAME : Z := 64.
Definition SINIT_STK : Z := SINIT_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition SINIT_EV : Z := 0.
(* Its first two arguments: g_s's and g_cfg's bases in image A; the length of struct diginet_io. *)
Definition SINIT_S : Z := TA_g_s.
Definition SINIT_CFG : Z := TA_g_cfg.
Definition SINIT_IO_LEN : Z := 32.
Lemma sinit_args_at : SINIT_S = 0x5df9c0 /\ TW.SZ_g_s = 18264 /\ SINIT_CFG = 0x5df080.
Proof. split; [|split]; reflexivity. Qed.
(* The 32 bytes of the caller's struct diginet_io (ctx, send, recv, now_us), as the plain contract states them. *)
Definition sinit_io_bytes (io_ctx io_send io_recv io_now : Z) : list byte :=
  TW.put 8 io_ctx ++ TW.put 8 io_send ++ TW.put 8 io_recv ++ TW.put 8 io_now.
(* The bytes the code stores into G, exactly: g_s's 18264-byte payload (the memset, then the stores and copies inside
   it) on the path that returns DIGINET_OK; none on the paths that return DIGINET_E_ARG. *)
Definition sinit_wr (r a : Z) : Prop := r = DL.DIGINET_OK /\ SINIT_S <= a < SINIT_S + TW.SZ_g_s.

(* The shadow of g_s's payload and of the start of its guard bytes, as facts of the record B: the shadow bytes of its
   2283 whole granules are 0 (a range of as_zero_shadow B), and the 5 shadow bytes after them are 0xf9 (constant cells
   of the record). The instrumented checks of the stores at s + 96 .. s + 116 read the first; the memset's check of
   [s, s + 18264) reads its whole shadow hull, which ends 5 bytes after g_s's shadow (sinit_hull_end). *)
Definition trans_sinit_cells (B : asyms) : Prop :=
  decode_zshadow_at B SINIT_S (SINIT_S + TW.SZ_g_s) /\
  forall ly i, 0 <= i < 5 -> In (z1 (ANum (ACells.shadow_addr (SINIT_S + TW.SZ_g_s) + i)) 0xf9) (as_const B ly).
(* The 8-aligned shadow hull of g_s's payload (YG0d.v shadow_hull_vis) starts at g_s's first shadow byte and ends 5
   bytes after its last zero one: [0x800b3f38, 0x800b4828). *)
Lemma sinit_hull_end :
  shadow_addr SINIT_S / 8 * 8 = ACells.shadow_addr SINIT_S /\
  shadow_addr (SINIT_S + TW.SZ_g_s - 1) / 8 * 8 + 8 = ACells.shadow_addr (SINIT_S + TW.SZ_g_s) + 5 /\
  ACells.shadow_addr SINIT_S = 0x800b3f38 /\ ACells.shadow_addr (SINIT_S + TW.SZ_g_s) = 0x800b4823.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section sinit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS with no event, the written range sinit_wr r,
   no meter charge, and X: a0 = r (sign-extended) and the world relation at the model's world Bw'. *)
Definition transport_sinit_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
    SINIT_STK SINIT_EV 0 (sinit_wr r)
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_A (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_init_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (iop io_ctx io_send io_recv io_now ntf ctx r : Z) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SINIT_S -> YK11.getr regs 11 = w64 SINIT_CFG ->
    YK11.getr regs 12 = w64 iop -> YK11.getr regs 13 = w64 ntf -> YK11.getr regs 14 = w64 ctx ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SINIT_STK -> spZ regs <= sp0 ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TS0.diginet_session_init_m Bw io_ctx io_send io_recv io_now ntf ctx = Some (Bw', r) ->
    0 <= io_ctx < 2 ^ 64 -> 0 <= io_send < 2 ^ 64 -> 0 <= io_recv < 2 ^ 64 -> 0 <= io_now < 2 ^ 64 ->
    0 <= ntf < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
    iop <> 0 -> iop mod 8 = 0 ->
    trans_src_ok B lyc Sc W memc iop SINIT_IO_LEN ->
    garr8 segs (mrestrict (w_H W) memc) iop (TW.zs (sinit_io_bytes io_ctx io_send io_recv io_now)) ->
    decode_off_win regs SINIT_STK iop SINIT_IO_LEN ->
    iop + SINIT_IO_LEN <= SINIT_S \/ SINIT_S + TW.SZ_g_s <= iop ->
    st_nev S + k + SINIT_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_sinit_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_cfg
   and of g_s, the allocator and meter laws, G inside the image and outside the allocator's statics, and the
   contracts of __asan_memset and __asan_memcpy give the contract at TS_diginet_session_init. *)
Definition transport_diginet_session_init_cg_holds_stmt : Prop :=
  transport_cells B -> trans_scfg_cells B -> trans_sinit_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) ->
  transport_diginet_session_init_cg (transport_sigma TS_diginet_session_init).
End sinit.
