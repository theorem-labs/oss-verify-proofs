(* check_latest_sent_cg: the ASan walk contract of check_latest_sent (fuzz/fuzz_transport.c:626-644, with tagged_of
   :609-615 and q_remove :617-624 inlined; model lib/TModel/TCb.v check_latest_sent_m) on fuzz_transport.asan
   (e89be137db17) at 0x84500 = transport_sigma TS_check_latest_sent, size 836, as STATEMENTS only (no proof). It stores
   into g_cmd, g_q and g_nq, three harness globals, and calls the bcmp wrapper, so it is a G-form caller-journal walk:
   the caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/A/TransportG.v G_HARNESS with no out cell
   (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post_out with the one out cell
   [(dp, 4)] (below).

   The contract. a0 = bp, the len bytes body at bp (a1 = len); a2 = dp, the caller's int *display. The memory relates
   to the world Bw by image A's world relation (TWorldG.v tw_at at TWorldA.v TMAP_A, read through aview), and
   check_latest_sent_m Bw body len = Some (Bw', disp). The function returns to ra with the callee-saved registers kept,
   no allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the world relation at
   Bw', and the 4 bytes at dp holding disp (little-endian, its low 32 bits). This is what the plain contract
   (lib/Prog/T/check_latest_sent_c.v) says: void; wmem rsegs m' B' with B' the model's world; rw_cells m' dp
   [C4 disp]; munch of the frame, of [dp, dp + 4) and of the world. Its premises become: bytes_at of the body ->
   garr8 + trans_src_ok + decode_off_win; the body below g_cmd or above the world -> the body apart from every byte
   the call stores (cls_wr); rw_cells / off_world / off_window of dp -> the write right transport_twr_ok_g, decode_rd_ok
   (the instrumented checks of dp read its shadow byte), dp outside G, decode_off_win; wmem -> tw_at; mem_inv is
   dropped.
   The one premise the plain contract does not have: every PENDING command g_cmd[s], s < g_ncmd, has len <=
   SPEC_CMD_MAX (24, the size of its bytes array). The bcmp at 0x84658 compares t->len bytes at g_cmd[s].bytes, and
   runs only after the code found t->st = PENDING; the model bounds s (< CMDS_MAX) but not t->len, and reads the
   plain world, where the bytes after g_cmd are g_q's. On image A g_cmd's payload is followed by bytes the runtime
   marks unusable, so a len that leaves the payload (above 28 for g_cmd[1023]) makes the wrapper's check fail (the
   error path). The loop changes st only from PENDING to SENT and never changes a len, so a command PENDING in a
   round was PENDING in Bw. op_submit records only commands of 3 .. 24 bytes (fuzz_transport.c:1088, :1111); the
   caller supplies it from the plain sim's invariant lib/TSim/Agree.v d2_cmd (3 <= Cmd_len <= 24 for every command
   below g_ncmd whose st is not 0): each caller carries the premise up to LLVMFuzzerTestOneInput, whose walk
   discharges it from that invariant.

   The post is TransportGCg.v transport_cg_post_out with the one out cell [(dp, 4)]: dp lies in the caller's MACHINE
   frame (io_send passes its sp + 4 and takes no side-stack frame), above this call's stack window, where
   acall_kept_g's first clause keeps every byte at or above alloc_ceiling whatever the written range is.
   transport_cg_post_out reads acall_kept_g at the memory with the 4 bytes at dp put back as they were at the call
   (W_journalG.v gover [(dp, 4)] mem2 memc): every byte acall_kept_g keeps is kept but those 4, and X says what they
   hold. The journal already allows the store (awr_ok_x: dp is an awr_byte of the caller's window,
   transport_twr_ok_g).

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's, and this function's
   836 code bytes are equal in both files), 209 words:
     0x84500 - 0x84534 sp = sp - 144; ra, s0 .. s11 at sp + 136 .. sp + 40, loaded back at 0x847b0 - 0x847e0
                      (sp = sp + 144 at 0x847e4, return at 0x847e8); spill slots sp + 8 .. sp + 32. No side-stack frame,
                      no frame pointer. s0 = dp, s1 = len.
     0x84540 - 0x84548 s5 = the 8-byte load at the GOT word 0xa4090, then at the cell 0xac9f8 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte access
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path.
     0x8454c - 0x84564 the check of the 4-byte store at dp (its shadow address kept at sp + 24; bp kept at sp + 32,
                      0x8455c), then the 4-byte store of 0 at dp (:628). 0x84568: len = 0 goes to the return.
     0x8456c - 0x84598 s7 = at = 0; s9 = the 4-byte load of g_nq (0x5df960, no instrumented check); s10 = g_cmd
                      (0x5e5400); sp + 8 = (dp & 7) + 3 (0x8458c); sp + 16 = g_q (0x5f1c00).
     0x8459c - 0x845c8 one round per command (:630): len - at < 3 (unsigned) goes to the trap; the check of the
                      1-byte load at bp + at; that byte <> 0xa0 (TAG) goes to the trap.
     0x845cc - 0x84608 the checks of the 1-byte loads at bp + at + 1 and bp + at + 2; s2 = serial = b[1] | b[2] << 7;
                      the 4-byte load of g_ncmd (0x5df980, no check); serial >= g_ncmd (unsigned) goes to the trap.
     0x8460c - 0x84630 s3 = t = g_cmd + 40 * serial; the check of the 4-byte load at t (t->st); <> 1 (PENDING) goes to
                      the trap.
     0x84634 - 0x8464c the check of the 1-byte load at t + 36; s4 = t->len; len - at < t->len (unsigned) goes to the
                      trap.
     0x84650 - 0x8465c bcmp (0x42cf8 = transport_sigma TS___interceptor_trampoline_bcmp) at 0x84658 with
                      (bp + at, t + 12, t->len); a result not 0 goes to the trap.
     0x84660 - 0x8466c the check of the 4-byte store at t (t's shadow byte loaded again), the 4-byte store of 2 (SENT)
                      at t (:639).
     0x84670          s9 <> 0 goes to q_remove's loop at 0x846b4; else 0x84674.
     0x846b4 - 0x8471c q_remove (:619-622), with k = s9 = 0: for i = 0 .. (s9 at entry, zero-extended) - 1: the check
                      of the 4-byte load at g_q + 4 i; g_q[i] = serial skips; else the check of the 4-byte store at
                      g_q + 4 k, k = k + 1, the store of g_q[i] at g_q + 4 (k - 1). Then 0x84674.
     0x84674          the 4-byte store of s9 (k) at g_nq (:623, no check). s9 carries g_nq from round to round: no
                      other store reaches g_nq.
     0x84678 - 0x846ac the check of the 4-byte load at t + 8 (t->display); the check of the 4-byte load at dp; the
                      4-byte store of *display | t->display at dp (:641); at = at + t->len; at < len (unsigned) goes back
                      to 0x8459c; else the return (a0 .. a7 not stated: void).
   The trap: 0x847ec call of TS___asan_handle_no_return (0x5a4c4), 0x847f0 call of TS_abort (0x93734); every branch to
   it is ruled out by check_latest_sent_m Bw body len = Some _: latest_sent_loop's tests are the code's tests (tagged_of_m:
   len - at < 3, the TAG byte, serial < g_ncmd Bw; Cmd_st Bw s = PENDING; Cmd_len Bw s <= len - at; beq_bytes of the
   body bytes and sub Bw (A_Cmd_bytes s) (Cmd_len Bw s)), read through tw_at and garr8 of the body, and bcmp's result
   is 0 exactly when the bytes agree (abcmp_realizes). A command of length 0 meets itself, now SENT, in the next round:
   the model's None, as the code's trap.
   Error paths (11 calls) and the facts that rule them out:
     TS___asan_report_store4 0x84804 and TS___asan_report_load4 0x847ac (dp): decode_rd_ok's range_addressable of
       [dp, dp + 4) and dp mod 4 = 0 (one granule).
     TS___asan_report_load1 0x84814, 0x8481c, 0x84824 (bp + at, + 1, + 2; at + 3 <= len): inside the body, which
       trans_src_ok marks usable (a heap block: AR's shadow law; else decode_rd_ok).
     TS___asan_report_load4 0x8482c (t), TS___asan_report_load1 0x84834 (t + 36), TS___asan_report_store4 0x8483c (t),
       TS___asan_report_load4 0x84840 (t + 8): t = g_cmd + 40 s with s < CMDS_MAX (tagged_of_m is None at
       s >= CMDS_MAX), inside g_cmd's payload, whose shadow is 0 (trans_cls_cells).
     TS___asan_report_load4 0x84808 (g_q + 4 i), TS___asan_report_store4 0x84810 (g_q + 4 k, k <= i): i < CMDS_MAX
       (q_remove_loop is None at i >= CMDS_MAX), inside g_q's payload, whose shadow is 0 (trans_cls_cells).
     bcmp keeps every byte outside its stack window [sp - 144 - 2 * ESTACK, sp - 144), so the shadow bytes stay as
     they were through the loop.
   Callee texts assumed: the bcmp wrapper as abcmp_realizes (YG0d.v) at transport_sigma
   TS___interceptor_trampoline_bcmp, which the walk applies from its G journal through TransportGCg.v gx_call_leaf.
   Its ranges: [bp + at, + t->len) inside the body (t->len <= len - at), and [t + 12, + t->len) inside g_cmd[s]
   (t->len <= 24, the premise; 12 + 24 <= 40). No program function is called.
   Stack: 144 bytes of its own and the 2 * ESTACK the bcmp wrapper uses below sp - 144 (abcmp_realizes): CLS_STK.

   The caller is io_send (the call at 0x83314, return address 0x83318): a0 = the 8-byte word at io_send's sp + 56
   (f.body of its struct spec_frame at sp + 8), a1 = s2 (the body length), a2 = io_send's sp + 4 (its int display).
   It supplies the G journal of its own walk, the world relation, the body and dp facts, and the command-length
   invariant. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_latest_sent's frame (`sp = sp - 144` at its entry; no realignment) and the 2 * ESTACK its bcmp calls use
   below sp - 144 (abcmp_realizes, YG0d.v). *)
Definition CLS_FRAME : Z := 144.
Definition CLS_STK : Z := CLS_FRAME + 2 * ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition CLS_EV : Z := 0.
(* The bytes the code may store: the st field of a command (g_cmd[s].st, s < CMDS_MAX), g_q's payload (q_remove's
   g_q[k], k < CMDS_MAX), g_nq, and the caller's int at dp. *)
Definition cls_wr (dp a : Z) : Prop :=
  (exists s, 0 <= s < TC.CMDS_MAX /\ twa_fld TW.OFF_g_cmd TA_g_cmd (TW.A_Cmd_st s) 4 a) \/
  twa_fld TW.OFF_g_q TA_g_q TW.OFF_g_q TW.SZ_g_q a \/
  twa_fld TW.OFF_g_nq TA_g_nq TW.OFF_g_nq TW.SZ_g_nq a \/
  dp <= a < dp + 4.

(* The shadow of the payloads of g_q (4096 bytes) and g_cmd (40960), all whole granules, is 0: ranges of the record's
   as_zero_shadow. The instrumented checks of t, t + 8, t + 36 and of g_q[i], g_q[k], and bcmp's second range, read
   them. *)
Definition trans_cls_cells (B : asyms) : Prop :=
  decode_zshadow_at B TA_g_q (TA_g_q + TW.SZ_g_q) /\
  decode_zshadow_at B TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd).

Section cls. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The contract at entry address a, in the G-form caller-journal form. What a call leaves: TransportGCg.v
   transport_cg_post_out over G_HARNESS with the out cell [(dp, 4)], no event, the written range cls_wr dp, no meter
   charge, and X: the world relation at the model's world Bw' and the 4 bytes at dp holding disp. *)
Definition transport_check_latest_sent_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bp len dp disp : Z) (body : list byte) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 bp -> YK11.getr regs 11 = w64 len -> YK11.getr regs 12 = w64 dp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CLS_STK -> spZ regs <= sp0 ->
    0 < bp -> Z.of_nat (length body) = len ->
    garr8 segs (mrestrict (w_H W) memc) bp (TW.zs body) ->
    trans_src_ok B lyc Sc W memc bp len ->
    decode_off_win regs CLS_STK bp len ->
    (forall x, bp <= x < bp + len -> ~ cls_wr dp x) ->
    dp mod 4 = 0 ->
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs) dp 4 ->
    decode_rd_ok W memc dp 4 ->
    decode_off_win regs CLS_STK dp 4 ->
    (forall x, dp <= x < dp + 4 -> ~ inG TG.G_HARNESS x) ->
    tw_at TMAP_A (aview segs (w_H W) memc) Bw ->
    TC.check_latest_sent_m Bw body len = Some (Bw', disp) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    st_nev S + k + CLS_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (@transport_cg_post_out fx rc tfib_sink_head segs B MT TG.G_HARNESS [(dp, 4)] STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc k regs CLS_STK CLS_EV 0 (cls_wr dp)
         (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\
                               garr8 segs (mrestrict (w_H W2) mem2) dp (TW.zs (TW.put 4 disp)))).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_q
   and g_cmd, the allocator and meter laws, G inside the image and outside the allocator's statics, and the bcmp
   contract at the listing's trampoline give the contract at TS_check_latest_sent. *)
Definition transport_check_latest_sent_cg_holds_stmt : Prop :=
  transport_cells B -> trans_cls_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp)) ->
  transport_check_latest_sent_cg (transport_sigma TS_check_latest_sent).
End cls.
