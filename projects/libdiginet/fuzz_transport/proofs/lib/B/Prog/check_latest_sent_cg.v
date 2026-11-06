(* check_latest_sent_cg: image B's ASan walk contract of check_latest_sent (fuzz/fuzz_transport.c:626-644, with
   q_remove :617-624 inlined and tagged_of :609-615 CALLED; model lib/TModel/TCb.v check_latest_sent_m) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x848bc = transportb_sigma TB_check_latest_sent, size 788, as
   STATEMENTS only (no proof). It stores into g_cmd, g_q and g_nq, three harness globals, and calls tagged_of (a
   program function on this image) and the bcmp wrapper, so it is a G-form caller-journal walk: the caller's journal is
   lib/A/W_journalG.v ajournal_gx (image-free) over G = lib/B/TransportGB.v G_HARNESS_B with no out cell (XO = 0,
   OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post_out (image-free) with the one out cell
   [(dp, 4)] (below).

   The contract. a0 = bp, the len bytes body at bp (a1 = len); a2 = dp, the caller's int *display. The memory relates
   to the world Bw by image B's world relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), and
   check_latest_sent_m Bw body len = Some (Bw', disp). The function returns to ra with the callee-saved registers kept,
   no allocator event and no meter charge, the caller's side-stack frames and blocks exactly, the world relation at
   Bw', and the 4 bytes at dp holding disp (little-endian, its low 32 bits). This is what the plain contract
   (lib/Prog/T/check_latest_sent_c.v) says: void; wmem rsegs m' B' with B' the model's world; rw_cells m' dp
   [C4 disp]; munch of the frame, of [dp, dp + 4) and of the world. Its premises become: bytes_at of the body ->
   garr8 + trans_src_ok + decode_off_win; the body below g_cmd or above the world -> the body apart from every byte
   the call stores (cls_wr); rw_cells / off_world / off_window of dp -> the write right transport_twr_ok_g, decode_rd_ok
   (the instrumented checks of dp read its shadow byte), dp outside G, decode_off_win; wmem -> tw_at; mem_inv is
   dropped.
   The premise the plain contract does not have (image A's form has it too): every PENDING command g_cmd[s],
   s < g_ncmd, has len <= SPEC_CMD_MAX (24, the size of its bytes array). The bcmp at 0x849f0 compares t->len bytes at
   g_cmd[s].bytes, and runs only after the code found t->st = PENDING; the model bounds s (< CMDS_MAX) but not t->len,
   and reads the plain world, where the bytes after g_cmd are g_q's. On image B g_cmd's payload [0x5e5080, 0x5ef080)
   is followed by bytes the runtime marks unusable (the symbol g_cmd is 51200 bytes; its asan_globals descriptor's
   payload 40960), so a len that leaves the payload (above 28 for g_cmd[1023]) makes the wrapper's check fail (the
   error path). The loop changes st only from PENDING to SENT and never changes a len, so a command PENDING in a round
   was PENDING in Bw. op_submit records only commands of 3 .. 24 bytes (fuzz_transport.c:1088, :1111); the caller
   supplies it from the plain sim's invariant lib/TSim/Agree.v d2_cmd (3 <= Cmd_len <= 24 for every command below
   g_ncmd whose st is not 0): each caller carries the premise up to LLVMFuzzerTestOneInput, whose walk
   discharges it from that invariant.
   The premise image B's code adds to image A's form: trans_rom_view_rd W memc (DgnTransportBCg.v: the TRANS_RO_RD
   bytes read as the image's). The code loads the 8-byte constant-pool word 0x10338 (DgnTransportBCg.v TRANS_K_SENT,
   a TRANS_RO_RD range; its value 0xcccccccccccccccd) by a plain `ld` at 0x84954, and q_remove's test multiplies by its
   low 32 bits (the inverse of 5 modulo 2^32) to get the serial back from t; image A's code kept the serial in a
   register and reads no such word. Without the premise the walk does not know the word's value at the call memory.
   The post is TransportGCg.v transport_cg_post_out with the one out cell [(dp, 4)]: dp lies in the caller's MACHINE
   frame (io_send passes its sp + 4 and takes no side-stack frame), above this call's stack window, where
   acall_kept_g's first clause keeps every byte at or above alloc_ceiling whatever the written range is.
   transport_cg_post_out reads acall_kept_g at the memory with the 4 bytes at dp put back as they were at the call
   (W_journalG.v gover [(dp, 4)] mem2 memc): every byte acall_kept_g keeps is kept but those 4, and X says what they
   hold. The journal already allows the store (awr_ok_x: dp is an awr_byte of the caller's window,
   transport_twr_ok_g).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; this function's 788 code bytes and the word at
   0x10338 are equal in the pin and the twin), 197 words:
     0x848bc - 0x848f0 sp = sp - 160; ra, s0 .. s11 at sp + 152 .. sp + 56, loaded back at 0x84b4c - 0x84b7c
                      (sp = sp + 160 at 0x84b80, return at 0x84b84); spill slots sp + 8 .. sp + 48. No side-stack
                      frame, no frame pointer. s1 = len (0x848f4).
     0x848f8 - 0x848fc the UBSan alignment check of dp: dp & 3 <> 0 goes to the trap 0x84b88.
     0x84900 - 0x84910 s0 = dp, s2 = bp; s7 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it
                      holds: the shadow base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; k = 0 goes on; for an n-byte access
                      (n < 8), ((a & 7) + n - 1) < k (signed) goes on; else the error path.
     0x84914 - 0x84928 the check of the 4-byte store at dp (its shadow address kept at sp + 48), then the 4-byte store
                      of 0 at dp (:628). 0x8492c: len = 0 goes to the return.
     0x84930 - 0x84970 s9 = at = 0; sp + 40 = (bp <> 0); sp + 32 = g_cmd (0x5e5080); sp + 24 = the 8-byte load of the
                      constant-pool word 0x10338 (0x84954); s11 = 0x5df944, the pc-relative base of g_nq (s11 - 0x364
                      = 0x5df5e0); sp + 8 = (dp & 7) + 3; sp + 16 = g_q (0x5f1880); s10 = 1023.
     0x84974 - 0x84988 one round per command (:630): s5 = bp + at; the UBSan pointer-overflow checks of bp + at:
                      bp + at < bp (unsigned) goes to the trap 0x84b88, and so does (bp <> 0) = (bp + at = 0).
     0x8498c - 0x8499c s6 = len - at; the call of tagged_of (0x846a0 = transportb_sigma TB_tagged_of) at 0x84998 with
                      (bp + at, len - at), return address 0x8499c; its result t = 0 goes to the trap 0x84b8c.
     0x849a0 - 0x849a8 s3 = t; the UBSan alignment check of t: t & 3 <> 0 goes to the trap 0x84b88.
     0x849ac - 0x849c4 s8 = t's shadow address; the check of the 4-byte load at t (t->st); <> 1 (PENDING) goes to the
                      trap 0x84b8c.
     0x849c8 - 0x849e0 the check of the 1-byte load at t + 36; s4 = t->len; len - at < t->len (unsigned) goes to the
                      trap 0x84b8c.
     0x849e4 - 0x849f4 bcmp (0x42d34 = transportb_sigma TB___interceptor_trampoline_bcmp) at 0x849f0 with
                      (bp + at, t + 12, t->len), return address 0x849f4; a result not 0 goes to the trap 0x84b8c.
     0x849f8 - 0x84a04 the check of the 4-byte store at t (t's shadow byte loaded again through s8), the 4-byte store
                      of 2 (SENT) at t (:639).
     0x84a08 - 0x84a0c a3 = the 4-byte unsigned load of g_nq (0x5df5e0, no instrumented check), every round; 0 goes to
                      0x84abc (k = 0) and on to 0x84ac0.
     0x84a10 - 0x84a98 q_remove (:619-622), with k = a2 = 0: a4 = the low 32 bits of ((t - g_cmd) >> 3) times the word
                      at sp + 24, sign-extended: 5 s times the inverse of 5 modulo 2^32, that is the serial s; a5 = 1024;
                      for i = 0 .. g_nq - 1 (a0 = a6 = g_q + 4 i): a5 = 0 (i = 1024, the UBSan index check of g_q[i])
                      goes to the trap 0x84b88; the check of the 4-byte load at g_q + 4 i; g_q[i] = s skips; else
                      1023 < k (unsigned, the index check of g_q[k]) and ~g_q < 4 k (unsigned, the pointer-overflow
                      check of g_q + 4 k) go to the trap 0x84b88, the check of the 4-byte store at g_q + 4 k,
                      k = k + 1, the store of g_q[i] at g_q + 4 (k - 1) (0x84a80). Then 0x84ac0.
     0x84ac0          the 4-byte store of k at g_nq (:623, no check).
     0x84ac4 - 0x84afc the check of the 4-byte load at t + 8 (t->display); the check of the 4-byte load at dp (its shadow
                      byte loaded again through sp + 48, its bound read from sp + 8); the 4-byte store of
                      *display | t->display at dp (:641, 0x84af4); at = at + t->len; at < len (unsigned) goes back to
                      0x84974; else the return (a0 .. a7 not stated: void).
   The differences from image A's code (lib/A/Prog/check_latest_sent_cg.v): the frame is 160 bytes (A: 144);
   tagged_of is called, not inlined, so its tests (len - at < 3, the TAG byte, serial < g_ncmd) and the checks of the
   1-byte loads at bp + at .. bp + at + 2 are tagged_of's, and this code tests only its result; q_remove gets the
   serial back from t through the constant-pool word (above), and reads g_nq in every round (A carried it in a
   register); seven UBSan checks with the trap 0x84b88 are new. Their effect on the form: CLS_FRAME, the tagged_of
   contract among the callee texts, the premise trans_rom_view_rd W memc; every new trap is refuted by a premise A's
   form has (below). cls_wr names a field's bytes by lib/B/Prog/m_set_cg.v twb_fld, image B's twin of
   lib/A/Prog/m_lost_cg.v twa_fld (image B has no m_lost function, so the twin lives in m_set_cg.v).
   The traps:
     0x84b88 (`unimp`, the UBSan trap): from 0x848fc (dp & 3 <> 0): dp mod 4 = 0; from 0x84978 and 0x84988 (bp + at
       wraps, or changes from non-null to null): 0 < bp, at < len, and bp + len <= 2 ^ 64 by the body's placement
       (trans_src_ok: a heap block of the caller ends at or below alloc_ceiling, YG0d.v AR_blocks_law; every other
       placement has decode_rd_ok's q + n <= 2 ^ 63); from 0x849a8 (t & 3 <> 0): t = TB_g_cmd + 40 s (tagged_of's
       result), TB_g_cmd mod 4 = 0; from 0x84a34 (i = CMDS_MAX = 1024 while i < g_nq): q_remove_loop is None there;
       from 0x84a50 and 0x84a64: k <= i < CMDS_MAX.
     0x84b8c call of __asan_handle_no_return (0x5a500 = transportb_sigma TB___asan_handle_no_return), 0x84b90 call of
       abort (0x93390 = transportb_sigma TB_abort): from 0x8499c (t = 0), 0x849c4, 0x849e0, 0x849f4. Every branch to
       it is ruled out by check_latest_sent_m Bw body len = Some _: latest_sent_loop's tests are the code's tests
       (tagged_of_m's Some (_, None), which the callee's statement returns as t = 0; Cmd_st Bw s = PENDING;
       Cmd_len Bw s <= len - at; beq_bytes of the body bytes and sub Bw (A_Cmd_bytes s) (Cmd_len Bw s)), read through
       tw_at and garr8 of the body, and bcmp's result is 0 exactly when the bytes agree (abcmp_realizes). A command of
       length 0 meets itself, now SENT, in the next round: the model's None, as the code's trap.
     The word 0x84b94 after the call of abort (`unimp`) is reached by no branch.
   Error paths (8 calls) and the facts that rule them out:
     __asan_report_store4 0x84ba8 and __asan_report_load4 0x84b48 (dp): decode_rd_ok's range_addressable of
       [dp, dp + 4) and dp mod 4 = 0 (one granule).
     __asan_report_load4 0x84bbc (t), __asan_report_load1 0x84bc0 (t + 36), __asan_report_store4 0x84bc8 (t),
       __asan_report_load4 0x84bcc (t + 8): t = g_cmd + 40 s with s < CMDS_MAX (tagged_of_m is None at
       s >= CMDS_MAX), inside g_cmd's payload, whose shadow is 0 (trans_cls_cells).
     __asan_report_load4 0x84bac (g_q + 4 i), __asan_report_store4 0x84bb4 (g_q + 4 k, k <= i): i < CMDS_MAX
       (q_remove_loop is None at i >= CMDS_MAX), inside g_q's payload, whose shadow is 0 (trans_cls_cells).
     tagged_of and bcmp keep every byte outside their stack windows below sp - 160, so the shadow bytes stay as they
     were through the loop.
   Callee texts assumed (pc order): tagged_of as image B's leaf statement lib/B/Prog/tagged_of_cg.v
     transport_tagged_of_cg (read at this unit's model by DgnTransportBCg.v transport_leaf_at; the call at 0x84998,
     through gx_call_leaf and the leaf bridge), entered with a0 = bp + at, a1 = len - at. What it asks besides the
     journal's facts: 0 < bp + at and 0 <= len - at < 2 ^ 64 (the placement above), the bytes skipn at body at
     bp + at (garr8 of the body; no store of the loop reaches the body), tw_at at csw_view of the call memory (the
     round's world), tagged_of_m of that world, skipn at body and len - at = Some (that world, t) (latest_sent_loop's
     let* of the round), asan_cells (transport_cells rows 1-2), and when 3 <= len - at the 3 bytes at bp + at
     addressable (trans_src_ok: a heap block, AR's shadow law; else decode_rd_ok) and off its frame
     (decode_off_win). It returns 0 for tagged_of_m's None, TB_g_cmd + 40 s for Some s. The bcmp wrapper as
     abcmp_realizes (YG0d.v) at transportb_sigma TB___interceptor_trampoline_bcmp (the call at 0x849f0), which the
     walk applies from its G journal through TransportGCg.v gx_call_leaf. Its ranges: [bp + at, + t->len) inside the
     body (t->len <= len - at), and [t + 12, + t->len) inside g_cmd[s] (t->len <= 24, the premise; 12 + 24 <= 40).
   Stack: 160 bytes of its own, tagged_of's ESTACK and the 2 * ESTACK the bcmp wrapper uses below sp - 160
   (LeafCgKit.v ecall_pre, abcmp_realizes): CLS_STK.

   The caller is io_send (the call at 0x8329c, return address 0x832a0): a0 = the 8-byte word at io_send's sp + 56
   (f.body of its struct spec_frame at sp + 8), a1 = the 8-byte word at its sp + 64 (f.body_len), a2 = io_send's
   sp + 4 (its int display). It supplies the G journal of its own walk, the world relation, the body and dp facts,
   the read-only view and the command-length invariant.
   Form: lib/A/Prog/check_latest_sent_cg.v (the post transport_cg_post_out). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require tagged_of_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_latest_sent's frame (`sp = sp - 160` at its entry; no realignment) and the window its calls use below
   sp - 160: tagged_of's ESTACK (a leaf, LeafCgKit.v ecall_pre) inside the 2 * ESTACK of the bcmp calls
   (abcmp_realizes, YG0d.v). *)
Definition CLS_FRAME : Z := 160.
Definition CLS_STK : Z := CLS_FRAME + 2 * ESTACK.
(* No allocator event: neither it nor tagged_of calls malloc or free or takes a side-stack frame. *)
Definition CLS_EV : Z := 0.
(* The bytes the code may store: the st field of a command (g_cmd[s].st, s < CMDS_MAX), g_q's payload (q_remove's
   g_q[k], k < CMDS_MAX), g_nq, and the caller's int at dp. *)
Definition cls_wr (dp a : Z) : Prop :=
  (exists s, 0 <= s < TC.CMDS_MAX /\ twb_fld TW.OFF_g_cmd TB_g_cmd (TW.A_Cmd_st s) 4 a) \/
  twb_fld TW.OFF_g_q TB_g_q TW.OFF_g_q TW.SZ_g_q a \/
  twb_fld TW.OFF_g_nq TB_g_nq TW.OFF_g_nq TW.SZ_g_nq a \/
  dp <= a < dp + 4.

(* The shadow of the payloads of g_q (4096 bytes) and g_cmd (40960), all whole granules, is 0: ranges of the record's
   as_zero_shadow. The instrumented checks of t, t + 8, t + 36 and of g_q[i], g_q[k], and bcmp's second range, read
   them. *)
Definition trans_cls_cells (B : asyms) : Prop :=
  decode_zshadow_at B TB_g_q (TB_g_q + TW.SZ_g_q) /\
  decode_zshadow_at B TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd).

Section cls. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* The contract at entry address a, in the G-form caller-journal form. What a call leaves: TransportGCg.v
   transport_cg_post_out over G_HARNESS_B with the out cell [(dp, 4)], no event, the written range cls_wr dp, no meter
   charge, and X: the world relation at the model's world Bw' and the 4 bytes at dp holding disp. *)
Definition transport_check_latest_sent_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bp len dp disp : Z) (body : list byte) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
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
    transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs) dp 4 ->
    decode_rd_ok W memc dp 4 ->
    decode_off_win regs CLS_STK dp 4 ->
    (forall x, dp <= x < dp + 4 -> ~ inG TG.G_HARNESS_B x) ->
    trans_rom_view_rd W memc ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TC.check_latest_sent_m Bw body len = Some (Bw', disp) ->
    (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) ->
    st_nev S + k + CLS_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (@transport_cg_post_out fx rc tfib_sink_head segs B MT TG.G_HARNESS_B [(dp, 4)] STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memc k regs CLS_STK CLS_EV 0 (cls_wr dp)
         (fun regs2 W2 mem2 => tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\
                               garr8 segs (mrestrict (w_H W2) mem2) dp (TW.zs (TW.put 4 disp)))).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_q
   and g_cmd, the allocator and meter laws, G inside the image and outside the allocator's statics, the leaf
   statement of tagged_of, and the bcmp contract at the listing's trampoline give the contract at
   TB_check_latest_sent. *)
Definition transport_check_latest_sent_cg_holds_stmt : Prop :=
  transport_cells B -> trans_cls_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx') ->
  (forall fx' : YK11.FPState, @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp)) ->
  transport_check_latest_sent_cg (transportb_sigma TB_check_latest_sent).
End cls.
