(* check_latest_queue_cg: the ASan walk contract of check_latest_queue (fuzz/fuzz_transport.c:804-819; model
   lib/TModel/TCb.v check_latest_queue_m) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x86104 =
   transportb_sigma TB_check_latest_queue, size 436, as STATEMENTS only (no proof). It stores into no harness global
   and calls the bcmp wrapper, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post
   over the caller's donor journal ajournal); a G-form caller lifts it with lib/A/Prog/TransportGCg.v gx_call_cg
   (stated over any segments, record and G, so image B's walks use it too). Image B's twin of
   lib/A/Prog/check_latest_queue_cg.v: the same statement at image B's world table, cells and listing; the
   differences image B's code forces are listed at the end of this comment.

   The contract. No argument. The memory relates to the world Bw by image B's world relation (lib/A/Prog/TWorldG.v
   tw_at at lib/B/Prog/TWorldB.v TMAP_B, read through aview), check_latest_queue_m Bw = Some (Bw', tt), and each of
   the g_s.queued commands in the session's queue has len <= 24 (DIGINET_CMD_MAX_LEN, the size of its bytes array).
   The function returns to ra with the callee-saved registers kept, no allocator event, no meter charge, every byte
   outside its stack window kept (it stores nothing outside its own frame: E is empty), and Bw' = Bw. This is what the
   plain contract (lib/Prog/T/check_latest_queue_c.v) says: void; B' = B and wmem rsegs m' B; munch of the frame only.
   Its wmem premise becomes tw_at; mem_inv is dropped.
   The one premise the plain contract does not have: the queue lengths <= 24. The bcmp at 0x8621c compares len bytes
   of g_s.queue[i] and of g_cmd[g_q[i]], len their common length byte (u8); the model bounds the indices (i < 512,
   g_q[i] < 1024) but not len, and reads the plain world, where the bytes after a global are the next global's. On
   image B each global's payload is followed by bytes the runtime marks unusable, so a len that leaves g_cmd's
   payload (above 28 for g_cmd[1023]) makes the wrapper's check fail (the error path). The plain side's run invariant
   has it: lib/TSim/TickTakeQ.v tt_sq_ok (from lib/TSim/Agree.v agree_q: d1_entry, S_queue_len = Cmd_len of the
   queued command, and d2_cmd, 3 <= Cmd_len <= 24; d4 for the raw mode) gives 1 <= len <= 24 for every entry below
   g_s.queued (diginet_session_submit queues only commands of 1 .. 24 bytes, TSess0.v :330-331); the caller supplies
   it from that invariant.

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 436 code bytes of this function are equal in both files),
   109 words:
     0x86104          sp = sp - 112; ra, s0 .. s11 at sp + 104 .. sp + 8 (0x86108 - 0x86138), loaded back at
                      0x8625c - 0x8628c; no side-stack frame, no frame pointer.
     0x8613c - 0x86158  the 4-byte loads of g_s.queued (g_s + 18144 = 0x5e3d20; g_s = 0x5df640) and g_nq (0x5df5e0),
                      no instrumented check; differ goes to the trap.
     0x8615c - 0x861a4  s5 = the 8-byte load at the GOT word 0xa3cf0 (GOT_CELL_K), then at the cell 0xac678 (CELL_K)
                      it holds: the shadow base 0x7fff8000 (transport_cells rows 1-2); a0 = g_s + 1760 (g_s.queue[0]),
                      s0 = g_s + 1784 (g_s.queue[0].len), s9 = (s0 >> 3) + 0x7fff8000 (its shadow byte), s1 = s6 = g_q
                      (0x5f1880), s2 = 1024, s3 = 40, s7 = 2052, s8 = g_cmd (0x5e5080), s10 = 2 ^ 64 - 1 - g_cmd,
                      s4 = queued (zero-extended).
     0x861a8 - 0x8622c  for i = 0 .. queued - 1 (s4 counts down; s4 = 0 goes to the return):
                      the instrumented check of the 4-byte load at g_q + 4 i (the shadow byte k at (a >> 3) +
                      0x7fff8000; k = 0 goes on; else (a & 7) + 3 < k (signed) goes on; else the error path);
                      q = g_q[i] (sign-extended); the ubsan build's checks go to the unimp word at 0x86298:
                      1024 < q (unsigned, 0x861c0: the bounds check of &g_cmd[q]), 2 ^ 64 - 1 - g_cmd < 40 q (unsigned,
                      0x861c8: g_cmd + 40 q wraps), and s7 = s7 - 4 = 0 (0x861d0, at i = 512: the bounds check of
                      g_s.queue[i]);
                      the check of the 1-byte load at g_s + 1784 + 32 i (k = 0, or (a & 7) < k, goes on);
                      a3 = g_cmd + 40 q; the check of the 1-byte load at a3 + 36;
                      queue[i].len (g_s + 1784 + 32 i) <> g_cmd[q].len (a3 + 36) goes to the trap;
                      bcmp (0x42d34 = transportb_sigma TB___interceptor_trampoline_bcmp) at 0x8621c with
                      (g_s + 1760 + 32 i, a3 + 12, queue[i].len); a result not 0 goes to the trap.
                      After the loop, the return at 0x86294 (a0 not stated: void).
   The trap: 0x8629c call of __asan_handle_no_return (0x5a500, TB___asan_handle_no_return), 0x862a0 call of abort
   (0x93390, TB_abort), then 0x862a4 the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal
   instruction that traps); every branch to 0x8629c is ruled out by check_latest_queue_m Bw = Some _: queue_loop's
   tests are the code's tests, read through tw_at (S_queued, g_nq, Q_at, S_queue_len, Cmd_len, and the bytes
   sub Bw (A_S_queue_bytes i) and sub Bw (A_Cmd_bytes q)), and bcmp's result is 0 exactly when the bytes agree
   (abcmp_realizes).
   The unimp word at 0x86298 (the ubsan build's checks) and the facts that rule out each branch to it: 0x861c0:
   queue_loop's CMDS_MAX <=? q is None, so q < 1024 (Q_at is unsigned, so the sign-extended load is q); 0x861c8:
   40 q < 40960 and g_cmd + 40960 < 2 ^ 64; 0x861d0: queue_loop's QUEUE_MAX <=? i is None, so i < 512.
   Error paths (3 calls) and the facts that rule them out: __asan_report_load4 (0x59644) at 0x862b4 (g_q + 4 i),
   __asan_report_load1 (0x59504) at 0x862ac (g_s + 1784 + 32 i) and 0x86258 (g_cmd + 40 q + 36): each address lies in
   the payload of g_q, g_s or g_cmd (the model gives i < 1024 for g_q[i], i < 512 for g_s.queue[i], q < 1024 for
   g_cmd[q]), whose shadow is 0 (trans_clq_cells); bcmp keeps every byte outside its stack window, so the shadow bytes
   stay 0 through the loop.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transportb_sigma
   TB___interceptor_trampoline_bcmp. Its ranges: [g_s + 1760 + 32 i, + len) and [g_cmd + 40 q + 12, + len), len <=
   24 (the premise), inside g_s's and g_cmd's payloads, whose shadow is 0. The aligned group of 8 shadow bytes around
   each range (YG0d.v shadow_hull_vis) is inside the same zero rows: g_s (0x5df640) and g_cmd (0x5e5080) start on a
   64-byte boundary, and the groups end at or before g_s + 18176 and g_cmd + 40960. No program function is called.
   Stack: 112 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 112 (abcmp_realizes): CLQ_STK.

   The caller is settle (the call at 0x838fc, return address 0x83900, when g_raw is 0). It supplies the journal, the
   world relation, the model call and the queue-length invariant from its own walk.

   Against image A's statement (lib/A/Prog/check_latest_queue_cg.v): the same premises, post and holds statement, at
   image B's names (TMAP_B, TB_g_s / TB_g_q / TB_g_cmd, transportb_sigma, lib/B/Prog/DgnTransportBCg.v). What image
   B's code forces: the frame is 112 bytes, not 80 (it keeps s8 .. s11 too: CLQ_FRAME, so CLQ_STK grows by 32); the
   three branches to the unimp word (the ubsan build's checks; image A has none), ruled out by the model call, so no
   premise is added; the error paths are direct calls of the runtime's report entries (image A's file names them
   errpath_load4 and errpath_load1). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_latest_queue's frame (`sp = sp - 112` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use
   below sp - 112 (abcmp_realizes, YG0d.v). *)
Definition CLQ_FRAME : Z := 112.
Definition CLQ_STK : Z := CLQ_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition CLQ_EV : Z := 0.

(* The shadow of the payloads of g_s (18264 bytes), g_q (4096) and g_cmd (40960), all whole granules, is 0: ranges of
   the record's as_zero_shadow. The loop's instrumented loads and its bcmp calls read them. *)
Definition trans_clq_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_g_s (TB_g_s + TW.SZ_g_s) /\
  decode_zshadow_at B TB_g_q (TB_g_q + TW.SZ_g_q) /\
  decode_zshadow_at B TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd).

Section clq. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, no written range, no meter charge, and X: the
   model's world is the world it was given. *)
Definition transport_clq_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw Bw' : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs CLQ_STK CLQ_EV 0
    (fun _ => False) (fun _ _ _ => Bw' = Bw).

(* The contract at entry address a, in the caller-journal form. *)
Definition transport_check_latest_queue_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bw Bw' : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLQ_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.check_latest_queue_m Bw = Some (Bw', tt) ->
    (forall i, 0 <= i < TW.S_queued Bw -> TW.S_queue_len Bw i <= TS0.DIGINET_CMD_MAX_LEN) ->
    st_nev S + k + CLQ_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_clq_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_s,
   g_q and g_cmd, the allocator and meter laws, and the bcmp contract at the listing's trampoline give the contract at
   TB_check_latest_queue. *)
Definition transport_check_latest_queue_cg_holds_stmt : Prop :=
  transport_cells B -> trans_clq_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  transport_check_latest_queue_cg (transportb_sigma TB_check_latest_queue).
End clq.
