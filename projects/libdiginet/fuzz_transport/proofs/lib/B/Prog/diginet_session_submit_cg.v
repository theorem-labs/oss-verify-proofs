(* diginet_session_submit_cg: image B's ASan walk contract of diginet_session_submit (transport/src/diginet_session.c:
   328-349, with coalescable :322-326 inlined; model lib/TModel/TSess0.v diginet_session_submit_m) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x89aec = transportb_sigma TB_diginet_session_submit, size 652, as
   STATEMENTS only (no proof). It stores into g_s, a harness global, so it is a G-form caller-journal walk: the
   caller's journal is lib/A/W_journalG.v ajournal_gx over G = lib/B/TransportGB.v G_HARNESS_B with no out cell
   (XO = 0, OUT = []), and the post is lib/A/Prog/TransportGCg.v transport_cg_post (acall_kept_g over G_HARNESS_B).
   Image B's twin of lib/A/Prog/diginet_session_submit_cg.v: the same statement at image B's world table, cells and
   listing; the differences image B's code forces are listed at the end of this comment.

   The contract. a0 = s = &g_s = 0x5df640 (TWorldB.v TB_g_s), a1 = c = cp, the address of the caller's struct
   diginet_cmd, whose 32 bytes are C (bytes[24], len at 24, display at 25, key, little-endian, at 28). cp is not 0,
   4-aligned, lies where a callee may read (DgnTransportBCg.v trans_src_ok) but not in G and not in TRANS_RO_RD (so
   in a heap block of the caller, in a caller's side-stack frame or in the machine stack), and outside this call's
   stack window (decode_off_win); its 32 bytes hold C (garr8). The memory relates to the world Bw by image B's world
   relation (TWorldG.v tw_at at TWorldB.v TMAP_B, read through aview), and diginet_session_submit_m Bw C =
   Some (Bw', r). Class 2 of the side stack has a free frame (diginet_body_check takes one). The function returns to
   ra with a0 = r (sign-extended: 0, -1, -5 or -10), the callee-saved registers kept, no allocator event and no meter
   charge, the caller's side-stack frames and blocks exactly, the bytes acall_kept_g G_HARNESS_B keeps (the bytes at
   or above alloc_ceiling outside the call's stack window [sp - SSUBMIT_STK, sp), the image bytes outside G, the
   owned statics and errno, the caller's block and frame bytes outside ssubmit_wr), and the world relation at Bw'.
   This is what the plain contract (lib/Prog/T/diginet_session_submit_c.v) says: a0 = r; wmem rsegs m' B' with B'
   the model's world; munch of the frame and the world only. Its premises become: bytes_at of C -> garr8; arg_blk ->
   trans_src_ok, decode_off_win, cp <> 0 and cp outside G and TRANS_RO_RD (arg_blk puts it off the world);
   cp mod 4 = 0 unchanged; wmem -> tw_at; w_off_stack and mem_inv are dropped.
   Why c is kept out of G and TRANS_RO_RD: the code reads c's bytes and their shadow after the call of
   diginet_body_check (the checked load at c + 28, the memcpy source [c, c + 32)). For a heap block, a side-stack
   frame or the machine stack, diginet_body_check's post (decode_cg_post, YCbq.v acall_kept) keeps the bytes, and AR
   (the stack's zero range, the blocks' shadow) or acall_kept's frame clause gives the shadow: DgnTransportBCg.v
   trans_src_ok_kept, with no record fact. A TRANS_RO_RD byte would be kept only with trans_ro_rd_unowned and
   trans_rom_no_errno, which this statement does not take. c outside G also keeps it apart from every byte the call
   stores (ssubmit_wr lies in g_s), so the memcpy's source and destination do not overlap.
   No run invariant: the only program callee, diginet_body_check, carries none, and the model bounds every index the
   code uses (submit_find_m and the append are None at an index >= 512).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 652 code bytes of this function are equal in both files),
   163 words:
     0x89aec - 0x89b00 sp = sp - 48; ra, s0 .. s3 at sp + 40 .. sp + 8, loaded back at 0x89c2c - 0x89c3c (sp = sp + 48
                      at 0x89c40, the return at 0x89c44). No side-stack frame, no frame pointer. These five 8-byte
                      stores into its own frame are its only stores outside g_s.
     0x89b04 - 0x89b14 s1 = s, a0 = -1; s = 0 or c = 0 goes to the return with -1 (:330): not taken, since
                      s = 0x5df640 and cp <> 0. s0 = c.
     0x89b18 - 0x89b1c c & 3 <> 0 goes to the trap word at 0x89d0c.
     0x89b20 - 0x89b28 s3 = the 8-byte load at the GOT word 0xa3cf0, then at the cell 0xac678 it holds: the shadow
                      base 0x7fff8000 (transport_cells rows 1-2).
     each instrumented check below: the shadow byte k at (a >> 3) + 0x7fff8000; for an n-byte access (n < 8), k = 0
                      goes on, else ((a & 7) + n - 1) < k (signed) goes on, else the error path; for an 8-byte access,
                      k = 0 goes on, else the error path.
     0x89b2c - 0x89b4c the check of the 1-byte load at c + 24; a1 = len (zero-extended); len - 25 < 2^64 - 24
                      (unsigned), that is len outside [1, 24], returns -1 (:330-331).
     0x89b50 - 0x89b60 s2 = s + 18144 (&g_s.queued); a0 = c, a1 = len; call of diginet_body_check (0x8c0fc =
                      transportb_sigma TB_diginet_body_check) at 0x89b60, return address 0x89b64 (:332).
     0x89b64 - 0x89b94 a result not 0: s & 7 <> 0 goes to the trap word; the check of the 8-byte access at s + 18256
                      (g_s.stats.refused), the 8-byte load, + 1, the 8-byte store back; a0 = -10; to the return
                      (:333-334).
     0x89b98 - 0x89bc4 the check of the 4-byte load at c + 28; a0 = key (zero-extended); ((key >> 16) | 8) & 0xff = 8,
                      that is the kind byte (key >> 16, the byte at c + 30) is 0 or 8 (DIGINET_KEY_INPUT): to the
                      append at 0x89bc8 (:336); else
     0x89c48 - 0x89c54 key & 0xff0000 = 0x90000, that is kind 9 (DIGINET_KEY_KEEPALIVE): to the append; else the
                      search (:337-343):
     0x89c58 - 0x89c70 s & 7 <> 0 goes to the trap word; the check of the 4-byte load at s + 18144; queued
                      (zero-extended) = 0 goes to the append.
     0x89c74 - 0x89cd4 for j = 0 .. queued - 1 (a6 counts 512 - j down): a6 = 0 (j = 512) goes to the trap word
                      (0x89c88); s + 1760 + 32 j below s + 1760 (unsigned) goes to the trap word (0x89c94); the check
                      of the 4-byte load at s + 1760 + 32 j + 28; queue[j].key (sign-extended) = key (sign-extended)
                      goes to 0x89cd8; after the last j (0x89cbc), to the append.
     0x89cd8 - 0x89d08 s + 1760 + 32 j = 0 goes to the trap word (0x89cd8); a0 = s + 1760 + 32 j, a1 = c, a2 = 32;
                      call of checked_memcpy (__asan_memcpy, 0x523ec = transportb_sigma TB___asan_memcpy) at 0x89ce4,
                      return address 0x89ce8: s->queue[j] = *c (:339); the check of the 8-byte access at s + 18248
                      (g_s.stats.coalesced), whose shadow byte (0 on this path) is left in a0; the 8-byte load, + 1,
                      the 8-byte store back (:340); to the return with a0 = 0.
     0x89bc8 - 0x89bec (the append, :345-348) s & 7 <> 0 goes to the trap word; the check of the 4-byte load at
                      s + 18144; queued = 512 returns -5.
     0x89bf0 - 0x89c28 the check of the 4-byte store at s + 18144 (the same shadow byte, loaded again); the 4-byte
                      store of queued + 1 at s + 18144; queued (the sign-extended 4-byte value) above 512 (unsigned)
                      goes to the trap word (0x89c04); the bitwise not of s + 1760 below 32 queued (unsigned:
                      s + 1760 + 32 queued wraps) goes to the trap word (0x89c14); a0 = s + 1760 + 32 queued,
                      a1 = c, a2 = 32; call of checked_memcpy at 0x89c24, return address 0x89c28:
                      s->queue[queued] = *c; a0 = 0.
     0x89c2c - 0x89c44 ra, s0 .. s3 loaded back, sp = sp + 48, return. a1 .. a7 at the return are not stated.
     0x89d0c          the word 0xc0001073 (unimp: a write of the read-only CSR cycle, an illegal instruction that
                      traps): the trap path.
     0x89d10 - 0x89d74 the slow paths of the checks and the 8 error calls.
   The model and the code: every test is diginet_session_submit_m's (cmd_len_of C in [1, DIGINET_CMD_MAX_LEN];
   body_check (firstn len C) = DIGINET_OK, which the callee's statement returns; coalescable_m (cmd_key_of C);
   submit_find_m over S_queue_key; S_queued = DIGINET_QUEUE_MAX), read through tw_at and garr8 of C (the
   sign-extended keys are equal exactly when their low 32 bits are); each store is the model's set_S_stats_refused /
   set_S_stats_coalesced / set_S_queued (the low 64 / 32 bits) or upd of A_S_queue_bytes with C (the memcpy). The
   model's None cases (an index >= 512) are where the code goes to the trap word or would write past g_s.queue: the
   model premise rules them out.
   Trap path (the unimp word at 0x89d0c, from 9 branches) and the premise that refutes each:
     0x89b1c (c & 3 <> 0): cp mod 4 = 0.
     0x89b6c, 0x89bcc, 0x89c5c (s & 7 <> 0): s = 0x5df640, a multiple of 8.
     0x89c04 (queued above 512 after the test queued = 512): S_queued Bw (TWorld.v: the unsigned 4-byte value; a value
       of 2^31 or more sign-extends to one above 512 as well) >= 513 makes the model's append None
       (S_queue_N <=? q), so the model premise rules it out.
     0x89c14 (s + 1760 + 32 queued wraps): reached only with queued < 512, where s + 1760 + 32 queued < 0x5dfd20 + 2^14.
     0x89c88 (j = 512 while j < queued): submit_find_m is None at i >= S_queue_N: the model premise.
     0x89c94 (s + 1760 + 32 j below s + 1760) and 0x89cd8 (s + 1760 + 32 j = 0): reached only with j < 512, where
       s + 1760 + 32 j lies in [0x5dfd20, 0x5e3d20), with no wrap and not 0.
   Error paths (8 calls) and the facts that rule them out:
     __asan_report_load1 (0x59504) at 0x89d1c (c + 24, before the call of diginet_body_check), __asan_report_load4
       (0x59644) at 0x89d2c (c + 28, after it): the 32 bytes at c are marked usable at entry (trans_src_ok: a heap
       block, AR's shadow law; else decode_rd_ok's range_addressable), and still after the call (c is not in G or
       TRANS_RO_RD: AR's shadow of the heap blocks and of the stack, or acall_kept's clause for the shadow bytes of a
       side-stack frame of the call state); cp mod 4 = 0, so the 4-byte load lies in one granule.
     __asan_report_load4 at 0x89d40 and 0x89d68 (s + 18144), __asan_report_store4 (0x59964) at 0x89d54 (s + 18144),
       __asan_report_load4 at 0x89cd4 (s + 1760 + 32 j + 28, j < 512 by the model), __asan_report_load8 (0x596e4) at
       0x89d6c (s + 18256) and 0x89d74 (s + 18248): each access lies in g_s's payload, in one granule (g_s's base
       0x5df640 is 64-byte aligned; the offsets are 4- or 8-aligned), whose shadow is 0 (trans_ssubmit_cells).
     The memcpy's own checks (aintrin_realizes' pre, through gx_intrin_at): range_addressable of the destination
     [s + 1760 + 32 j, + 32) (j < 512: inside g_s's zero shadow) and of the source [c, c + 32) (as for c + 28 above),
     and shadow_hull_vis of both: the destination's aligned group of 8 shadow bytes lies in g_s's zero ones, the
     source's is decode_rd_ok's kept through the call (or AR's shadow law for a heap block and for the stack).
   Writes into memory: the 8-byte field g_s.stats.refused, the 4-byte field g_s.queued, the 32 bytes of one entry
   g_s.queue[j] (the memcpy), the 8-byte field g_s.stats.coalesced (ssubmit_wr), and its own frame. The journal
   allows each (awr_ok_x: a byte of G), and the memcpy is applied from the G journal through gx_intrin_at
   (transport_twr_ok_g_intro; gx_rw of G is lib/B/Prog/TransportGRwB.v's).
   Callee texts assumed (pc order): diginet_body_check as lib/B/Prog/diginet_body_check_cg.v
   transport_diginet_body_check_cg at transportb_sigma TB_diginet_body_check (the call at 0x89b60; a donor-form callee,
   through TransportGCg.v gx_call_cg: it keeps every byte of G, gx_ok and gx_noerrno, so the world relation after it
   is the one it was handed), entered with a0 = cp and a1 = len, the bytes firstn len C; what it asks of them
   (trans_src_ok, decode_off_win of [cp, cp + len) at its window, garr8) comes from the premises on [cp, cp + 32),
   and count_cid 2 (frames Sc) < fs_frames 2 is this statement's premise; __asan_memcpy as aintrin_realizes ... OCpy
   (transportb_sigma TB___asan_memcpy; the calls at 0x89c24 and 0x89ce4).
   Stack: 48 bytes of its own and below sp - 48 the largest callee window: diginet_body_check's PBC.TRANS_BC_STK, or
   the ESTACK __asan_memcpy uses (YG0d.v aintrin_realizes' ecall_pre): SSUBMIT_STK.

   The caller is LLVMFuzzerTestOneInput (the calls at 0x825cc, return address 0x825d0, and 0x82744, return address
   0x82748): a0 = 0x5df640, a1 = s4 = c, its local command at offset 32 of its class-2 side-stack frame (the call of
   __asan_stack_malloc_2 at 0x81310, the frame kept at its s1 + 136 (0x81374), c = that frame + 32 at 0x817d8; before
   the call at 0x825cc it stores len at c + 24 (0x825b0) and copies the command's bytes into c with __asan_memcpy at
   0x825bc). It supplies the G journal of its own walk, the world relation, the facts about c and the free class-2
   frame.

   Against image A's statement (lib/A/Prog/diginet_session_submit_cg.v): the same premises, post and holds statement,
   at image B's names (TMAP_B, TB_g_s, transportb_sigma, lib/B/Prog/DgnTransportBCg.v, lib/B/Prog/m_set_cg.v twb_fld
   for image A's lib/A/Prog/m_lost_cg.v twa_fld). What image B's code forces: the 9 branches to the unimp word at
   0x89d0c (the ubsan build's checks: c's alignment, s's alignment, the index and pointer checks of s->queue[i];
   image A has none), each refuted by a premise image A's form already has (cp mod 4 = 0, the model premise) or by
   the constant s, so no premise is added; the search loop also keeps a down-counter from 512 for the index check,
   and the append stores queued + 1 before its index and pointer checks; the error paths are direct calls of the
   runtime's report entries. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_body_check_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_session_submit's frame (`sp = sp - 48` at its entry; no realignment) and the largest stack a callee uses
   below sp - 48: diginet_body_check's own window, ESTACK for __asan_memcpy. *)
Definition SSUBMIT_FRAME : Z := 48.
Definition SSUBMIT_STK : Z := SSUBMIT_FRAME + Z.max ESTACK PBC.TRANS_BC_STK.
(* No allocator event: it calls no allocator and takes no side-stack frame; diginet_body_check records none. *)
Definition SSUBMIT_EV : Z := 0.
(* Its first argument, g_s's base in image B, and the length of struct diginet_cmd. *)
Definition SSUBMIT_S : Z := TB_g_s.
Definition SSUBMIT_CMD_LEN : Z := 32.
Lemma ssubmit_args_at : SSUBMIT_S = 0x5df640 /\ TW.A_S_queued - TW.OFF_g_s = 18144 /\
  TW.A_S_stats_coalesced - TW.OFF_g_s = 18248 /\ TW.A_S_stats_refused - TW.OFF_g_s = 18256 /\
  TW.A_S_queue_bytes 0 - TW.OFF_g_s = 1760 /\ TW.A_S_queue_key 0 - TW.OFF_g_s = 1788.
Proof. repeat split; reflexivity. Qed.

(* The bytes the code may store into G: g_s.queued, g_s.stats.coalesced, g_s.stats.refused, and one entry
   g_s.queue[j], j < 512 (32 bytes, the memcpy). *)
Definition ssubmit_wr (a : Z) : Prop :=
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_queued 4 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_coalesced 8 a \/
  twb_fld TW.OFF_g_s TB_g_s TW.A_S_stats_refused 8 a \/
  (exists j, 0 <= j < TW.S_queue_N /\ twb_fld TW.OFF_g_s TB_g_s (TW.A_S_queue_bytes j) TW.S_queue_ESZ a).

(* The shadow of g_s's payload (18264 bytes, 2283 whole granules) is 0: a range of the record's as_zero_shadow
   (lib/B/YF0m.v Tfib_zero_shadow row (0x5df640, 0x5e3d98 - 0x5df640)). The instrumented checks of g_s.queued,
   g_s.stats.*, g_s.queue[j].key and the memcpy's destination read it. *)
Definition trans_ssubmit_cells (B : asyms) : Prop := decode_zshadow_at B TB_g_s (TB_g_s + TW.SZ_g_s).

Section ssubmit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What a call leaves: TransportGCg.v transport_cg_post over G_HARNESS_B with no event, the written range
   ssubmit_wr, no meter charge, and X: a0 = r (sign-extended) and the world relation at the model's world Bw'. *)
Definition transport_ssubmit_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (r : Z) : world segs -> config -> Prop :=
  @transport_cg_post fx rc tfib_sink_head segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
    regs SSUBMIT_STK SSUBMIT_EV 0 ssubmit_wr
    (fun regs2 W2 mem2 => YK11.getr regs2 10 = w64 r /\ tw_at TMAP_B (aview segs (w_H W2) mem2) Bw').

(* The contract at entry address a, in the G-form caller-journal form. *)
Definition transport_diginet_session_submit_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (cp r : Z) (C : list byte) (Bw Bw' : list byte),
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SSUBMIT_S -> YK11.getr regs 11 = w64 cp ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SSUBMIT_STK -> spZ regs <= sp0 ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
    TS0.diginet_session_submit_m Bw C = Some (Bw', r) ->
    length C = 32%nat ->
    cp <> 0 -> cp mod 4 = 0 ->
    trans_src_ok B lyc Sc W memc cp SSUBMIT_CMD_LEN ->
    garr8 segs (mrestrict (w_H W) memc) cp (TW.zs C) ->
    decode_off_win regs SSUBMIT_STK cp SSUBMIT_CMD_LEN ->
    (forall x, cp <= x < cp + SSUBMIT_CMD_LEN -> ~ inG TG.G_HARNESS_B x /\ ~ trans_in_ro_rd x) ->
    count_cid PBC.TRANS_BC_CID (frames Sc) < fs_frames PBC.TRANS_BC_CID ->
    st_nev S + k + SSUBMIT_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (transport_ssubmit_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the shadow of g_s,
   the allocator and meter laws, G inside the image, outside the allocator's statics and outside errno (the donor
   callee keeps G: gx_call_cg), and the contracts of diginet_body_check and __asan_memcpy give the contract at
   TB_diginet_session_submit. *)
Definition transport_diginet_session_submit_cg_holds_stmt : Prop :=
  transport_cells B -> trans_ssubmit_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  gx_ok segs B TG.G_HARNESS_B -> gx_noerrno B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState,
     @PBC.transport_diginet_body_check_cg fx' rc B MT (transportb_sigma TB_diginet_body_check)) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transportb_sigma TB___asan_memcpy)) ->
  transport_diginet_session_submit_cg (transportb_sigma TB_diginet_session_submit).
End ssubmit.
