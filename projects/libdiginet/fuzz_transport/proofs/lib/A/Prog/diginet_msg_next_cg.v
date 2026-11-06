(* diginet_msg_next_cg: the ASan walk contract of diginet_msg_next (src/diginet_msg.c:27-103; plain contract
   lib/Prog/diginet_msg_next_c.v) on fuzz_transport.asan (e89be137db17) at 0x8c9f8 =
   transport_sigma TS_diginet_msg_next, size 0x5c8 (1480), as STATEMENTS only (no proof). It stores into no harness
   global and calls __asan_memset, so it takes decode's caller-journal form (lib/A/Prog/DgnTransportCg.v
   decode_cg_post over the caller's donor journal ajournal).

   Relocated from libdiginet/fuzz_frame lib/A/Prog/diginet_msg_next_cg.v (file sha256 5435decc9434; donor not
   released; fuzz_frame.asan 67d7e481d74e at 0x832d0), the same 1480 code bytes up to the
   pc-relative words (35 pc-relative words differ, no other; re-checked
   here word by word on the two twins: 370 words, the 35 that differ are the GOT-word load at 0x8ca48, the
   __asan_memset call at 0x8cb14 and the 33 error-path calls). Every pc below is frame's + 0x9728 and was read again
   on transport's twin. The names change: frame_cg_post / frame_twr_ok / frame_rd_ok / frame_in_fake / frame_off_win
   / frame_cells / dgnframe_sigma DF_* become this unit's decode_cg_post / decode_twr_ok / decode_rd_ok /
   decode_in_fake / decode_off_win / transport_cells / transport_sigma TS_*, frame_mn_* / FRAME_MN_* become
   trans_mn_* / TRANS_MN_*, and frame_diginet_msg_next_cg{,_holds_stmt} become transport_diginet_msg_next_cg{,_holds_stmt}.
   One premise changes (its placement: DgnTransportCg.v trans_src_ok): frame's `frame_in_block B lyc Sc body
   (length bb)` (the bytes in one of the caller's heap blocks) becomes `trans_src_ok B lyc Sc W memc body
   (length bb)` with `decode_off_win regs TRANS_MN_STK body (length bb)`, both when bb is not empty: transport's
   diginet_body_check passes a body from LLVMFuzzerTestOneInput's local command (submit), take's local body[] or the
   frame diginet_frame_build builds, none of them a heap block. trans_src_ok's non-block cases carry decode_rd_ok
   (every byte visible, the range marked usable), which is what the walk took from the block (AR_laws' block shadow),
   and decode_off_win keeps the range out of this call's stack window, which the block gave by lying below
   alloc_ceiling.

   The contract. The caller's journal is the premise. a0 = c, a struct diginet_cursor whose 25 bytes are
   cursor_cells body (length bb) pos st (lib/Prog/diginet_cursor_init_c.v), with pos <= length bb and st_ok st; a1 =
   m, a struct diginet_msg of 40 bytes mj. c and m are not 0, lie in the caller's live side-stack frames, where the
   caller lets the call write them (decode_twr_ok), their bytes are visible and marked usable (decode_rd_ok), and they
   are outside this call's stack window; c and m do not overlap. The bytes bb at body are placed by trans_src_ok and
   lie outside this call's stack window when bb is not empty, and then do not overlap c or m. Let r = msg_step bb pos
   st (DgnLib). The function returns to ra with a0 = mr_code r, the callee-saved registers kept, no allocator event,
   every byte outside its stack window and outside the bytes of c and m it stores kept, c's 25 bytes = cursor_cells
   body (length bb) (mr_pos r) (mr_st r) and m's 40 bytes = msg_cells body mj r (lib/Prog/diginet_msg_next_c.v). The
   written range E is the bytes any path stores: [c + 16, c + 25) (pos, status) and [m, m + 4), [m + 8, m + 40); it
   never stores c's body and len (c + 0 .. c + 15) or the padding m + 4 .. m + 7. The post states all 25 + 40 bytes,
   so the bytes a path does not store (all of them at the end, pos = length bb) keep their old values.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 370 words:
     0x8c9f8  sp = sp - 128; ra at sp + 120, s0 .. s11 at sp + 112 .. sp + 24; no realignment, no frame pointer;
              spills at sp + 0 (m + 3, 0x8cae0), sp + 8 (its shadow address, 0x8cad4), sp + 16 (c + 16, 0x8cae4);
     0x8ca34 - 0x8ca40  c = 0 or m = 0 returns a0 = -1 (kept unreached: c <> 0, m <> 0);
     0x8ca44 - 0x8ca4c  the shadow base through its GOT word 0xa4090 (cell 0xac9f8: transport_cells rows 1-2);
     0x8ca78 / 0x8ca7c  the 8-byte loads of len (c + 8), pos (c + 16); pos >= len (unsigned, at 0x8ca80) returns 0 and
              stores nothing;
     0x8ca94  the 8-byte load of body (c + 0); 0x8cac0 the 1-byte load of body[pos]; then the 8-byte store of pos at
              m + 24 (0x8cac4), the 1-byte stores of 0 at m + 3 (0x8cae8) and m + 2 (0x8cb04), and 0x8cb14 the call
              of __asan_memset (0x5284c = transport_sigma TS___asan_memset) with (m + 8, 0, 16);
     body[pos] = 0xf0 (0x8cb1c): the search for 0xf7 over body[pos + 1 .. len) (0x8cb30 - 0x8cb54); not found: 0
              stored at c + 24 (0x8cbb8), a0 = -6, len stored at c + 16 (0x8cc68); found: 0 at c + 24 (0x8cbd8), 0xf0 at
              m + 0 (0x8cbf4), 0 at m + 1 (0x8cc08), body + pos + 1 at m + 8 (0x8cc20), m + 16 (0x8cc38), m + 32
              (0x8cc54), a0 = 1, c + 16 (0x8cc68);
     a data byte (bit 7 clear): the 1-byte load of status (c + 24, 0x8cb90); 0 gives pos + 1 stored at c + 16
              (0x8ccb8), a0 = -7;
     0xf1 .. 0xff: pos + 1 stored at c + 16 (0x8cc84), 0 at c + 24 (0x8cc9c), a0 = -8;
     a channel status or a running status: m + 1 stored (0x8ccf0); too few bytes: len stored at c + 16 (0x8cd04), a0
              = -6; a data byte with bit 7 set (loop 0x8cd18 - 0x8cd40): c + 16 stored (0x8cd60), 0 at c + 24
              (0x8cd78), a0 = -6; else status at m + 0 (0x8cd94), d1 at m + 2 (0x8cdbc), d2 at m + 3 (0x8cdf0), m + 32
              (0x8ce0c), c + 16 (0x8ce18), status at c + 24 (0x8ce30), a0 = 1;
     its loads of body lie in [body + pos, body + len) on every path that reaches them.
   Each store and each load of c, m and body follows the instrumented check of its shadow byte at (a >> 3) +
   0x7fff8000. Error paths (33 calls, no trap path): load1 x6 (0x8cb68, 0x8cd50, 0x8ce80, 0x8cf24, 0x8cf60: body
   bytes, kept unreached by trans_src_ok of [body, body + len): a heap block's bytes are marked usable by AR_laws'
   block shadow, every other case carries decode_rd_ok's range_addressable; 0x8cea8: c + 24), load8 x3 (0x8cf68,
   0x8cf6c, 0x8cf74: c + 16, c + 8, c + 0), store1 x13 (0x8ce8c .. 0x8cf54: m + 0 .. m + 3, c + 24), store8 x11
   (0x8cf78 .. 0x8cfbc: m + 8, m + 16, m + 24, m + 32, c + 16), kept unreached by decode_rd_ok's range_addressable of
   [c, c + 25) and [m, m + 40): every byte read or stored is addressable (YG0v.v saddr_ok), which is what each check
   tests; the granule each 8-byte access starts in has its last byte in the range, so its shadow byte is 0. The
   __asan_memset call needs [m + 8, m + 24) addressable and outside its ESTACK (decode_rd_ok, decode_off_win). No
   store reaches a harness global: every store is to c or m (base registers s2 = c, s1 = m and their offsets), in the
   caller's side-stack frame.
   Stack: 128 bytes of its own and the ESTACK __asan_memset uses below sp - 128 (YG0d.v aintrin_realizes' ecall_pre).

   The caller is diginet_body_check at 0x8c6a4 (return address 0x8c6a8), in a loop: a0 = c (s5 = its class-2
   side-stack frame + 32, 0x8c5d8), a1 = m (s6 = frame + 96, 0x8c5dc); body and len are its own arguments. It
   supplies: the cursor bytes (diginet_cursor_init's post at 0x8c688, pos 0 and st 0, for the first call; this
   statement's post for the next ones), m's bytes (the frame's 40 bytes, then this post); decode_in_fake (the frame
   from the stack malloc at 0x8c5a0, a class-2 frame of 256 bytes: 32 + 25 and 96 + 40 inside); decode_twr_ok (the
   frame is in its journal's own list, present and not owned: AR_frames_law); decode_rd_ok (its stores 0x8c610 -
   0x8c674 mark the shadow bytes of c (granules 4 .. 7) and m (12 .. 16) 0); decode_off_win (frames lie below
   alloc_ceiling); c / m disjoint by their offsets; trans_src_ok, decode_off_win and the disjointness of body from its
   own statement (a body outside its frame). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c diginet_msg_next_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PCur := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.
Module PMsg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_msg_next's frame (`sp = sp - 128` at TS_diginet_msg_next; no realignment) and the ESTACK its only callee,
   __asan_memset, uses below sp - 128. *)
Definition TRANS_MN_FRAME : Z := 128.
Definition TRANS_MN_STK : Z := TRANS_MN_FRAME + ESTACK.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition TRANS_MN_EV : Z := 0.
(* The cursor bytes it reads (body, len, pos, status: PCur.cursor_cells) and the struct diginet_msg. *)
Definition TRANS_MN_CUR_SIZE : Z := 25.
Definition TRANS_MN_MSG_SIZE : Z := 40.

(* The bytes of c and m the code stores on some path: c->pos and c->status [c + 16, c + 25); m->status, running,
   d1, d2 [m, m + 4); sysex and sysex_len (the __asan_memset destination, then the sysex stores), offset and len
   [m + 8, m + 40). *)
Definition trans_mn_wr (c m a : Z) : Prop :=
  c + 16 <= a < c + 25 \/ m <= a < m + 4 \/ m + 8 <= a < m + 40.

(* The 25 cursor bytes and the 40 message bytes as values, in the form the walks' image view reads (garr8, YI00.v). *)
Definition trans_mn_cur_bytes (body len : Z) (pos : nat) (st : Z) : list Z :=
  map bz (LC.cells_bytes (PCur.cursor_cells body len pos st)).
Definition trans_mn_msg_bytes (body : Z) (mj : list byte) (r : msg_res) : list Z :=
  map bz (LC.cells_bytes (PMsg.msg_cells body mj r)).

Section mn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no event, the written range trans_mn_wr c m, no meter
   charge, a0 = mr_code r (sign-extended), the cursor at the step's pos and status, and the message bytes. *)
Definition trans_mn_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (c m body : Z) (bb mj : list byte) (pos : nat) (st : Z) :
    world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TRANS_MN_STK TRANS_MN_EV 0
    (trans_mn_wr c m)
    (fun regs2 W2 mem2 =>
       YK11.getr regs2 10 = w64 (mr_code (msg_step bb pos st)) /\
       garr8 segs (mrestrict (w_H W2) mem2) c
         (trans_mn_cur_bytes body (Z.of_nat (length bb)) (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st))) /\
       garr8 segs (mrestrict (w_H W2) mem2) m (trans_mn_msg_bytes body mj (msg_step bb pos st))).

(* The contract at entry address a, in the caller-journal form. c (a0) holds the cursor over the bytes bb at body
   at pos with running status st; m (a1) holds the 40 bytes mj; both inside the caller's live side-stack frames,
   writable by this call, visible, marked usable, outside its stack window and disjoint; bb is placed by trans_src_ok,
   outside this call's stack window and disjoint from c and m, when it is not empty. *)
Definition transport_diginet_msg_next_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (c m body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 c -> YK11.getr regs 11 = w64 m ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRANS_MN_STK -> spZ regs <= sp0 ->
    c <> 0 -> m <> 0 ->
    (pos <= length bb)%nat -> st_ok st ->
    garr8 segs (mrestrict (w_H W) memc) c (trans_mn_cur_bytes body (Z.of_nat (length bb)) pos st) ->
    length mj = 40%nat ->
    garr8 segs (mrestrict (w_H W) memc) m (map bz mj) ->
    garr8 segs (mrestrict (w_H W) memc) body (map bz bb) ->
    ((0 < length bb)%nat -> trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb))) ->
    ((0 < length bb)%nat -> decode_off_win regs TRANS_MN_STK body (Z.of_nat (length bb))) ->
    decode_in_fake lyc Sc c TRANS_MN_CUR_SIZE -> decode_in_fake lyc Sc m TRANS_MN_MSG_SIZE ->
    decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c TRANS_MN_CUR_SIZE ->
    decode_twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) m TRANS_MN_MSG_SIZE ->
    decode_rd_ok W memc c TRANS_MN_CUR_SIZE -> decode_rd_ok W memc m TRANS_MN_MSG_SIZE ->
    decode_off_win regs TRANS_MN_STK c TRANS_MN_CUR_SIZE -> decode_off_win regs TRANS_MN_STK m TRANS_MN_MSG_SIZE ->
    c + TRANS_MN_CUR_SIZE <= m \/ m + TRANS_MN_MSG_SIZE <= c ->
    ((0 < length bb)%nat -> c + TRANS_MN_CUR_SIZE <= body \/ body + Z.of_nat (length bb) <= c) ->
    ((0 < length bb)%nat -> m + TRANS_MN_MSG_SIZE <= body \/ body + Z.of_nat (length bb) <= m) ->
    st_nev S + k + TRANS_MN_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (trans_mn_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c m body bb mj pos st).

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word), the allocator and
   meter laws, and the contract of __asan_memset give the contract at TS_diginet_msg_next. *)
Definition transport_diginet_msg_next_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (transport_sigma TS___asan_memset)) ->
  transport_diginet_msg_next_cg (transport_sigma TS_diginet_msg_next).
End mn.
