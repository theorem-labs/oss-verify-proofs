(* diginet_msg_next_cg (image B): the ASan walk contract of diginet_msg_next (src/diginet_msg.c:27-103; plain
   contract lib/Prog/diginet_msg_next_c.v) on fuzz_transport.asan-ubsan (41113a03c82f) at 0x8c60c =
   transportb_sigma TB_diginet_msg_next, size 0x610 (1552), as STATEMENTS only (no proof). It stores into no harness
   global and calls no function, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v
   decode_cg_post over the caller's donor journal ajournal). Form: lib/A/Prog/diginet_msg_next_cg.v (the same
   definitions, premises and post, but for the differences below).

   RELOCATED from libdiginet/fuzz_decode lib/B/Prog/diginet_msg_next_cg.v (file sha256 0b603bc54c0a; donor not
   released; fuzz_decode.asan-ubsan 1c8e7ec20682 at 0x82328, size 1552; it carries no notice line): the same 1552 code
   bytes up to the pc-relative words (compared word by word with capstone on the two symbol-bearing files: 388 words,
   the 38 that differ are the GOT-word pair at 0x8c648 - 0x8c64c and the 36 error-path calls). Every pc below is
   decode's + 0xa2e4 and was read again on this unit's twin (e217cb0a84f1; its loaded bytes equal the pin's but the
   ELF header's section-table fields and the build-id note, and the 1552 code bytes of this function are equal in
   both files). The names change as image A's text names them:
   decode_mn_wr / decode_mn_cur_bytes / decode_mn_msg_bytes / decode_mn_post / FRAME_MN_* /
   decode_diginet_msg_next_cg{,_holds_stmt} become trans_mn_wr / trans_mn_cur_bytes / trans_mn_msg_bytes /
   trans_mn_post / TRANS_MN_* / transport_diginet_msg_next_cg{,_holds_stmt}; DgnDecodeBSyms / DgnDecodeBAddr
   dgndecb_sigma DDB_ become DgnTransportBSyms / DgnTransportBAddr transportb_sigma TB_; DgnDecodeBCg's decode_cells
   becomes DgnTransportBCg's transport_cells; decodesegsB0 and lib/B DecodeTFIB become lib/B/YB1v.v tfibsegs, and
   lib/B/YE2k.v is this unit's.
   The premises, against decode's image-B text and image A's text:
   - As in image A's text (its placement: DgnTransportBCg.v trans_src_ok), decode's `decode_in_block B lyc Sc body
     (length bb)` (the bytes in one of the caller's heap blocks) becomes `trans_src_ok B lyc Sc W memc body (length bb)`
     with `decode_off_win regs TRANS_MN_STK body (length bb)`, both when bb is not empty: transport's diginet_body_check
     passes a body that is not a heap block. The code does not force this change; transport's callers do.
   - As in decode's image-B text, and not in image A's: c mod 8 = 0 and m mod 8 = 0, forced by this code's UBSan
     alignment checks of c (0x8c640 / 0x8c644) and m (0x8c6c8 / 0x8c6cc), which go to the unimp word at 0x8caa8.
   - No premise for body <> 0, though this code needs it: the UBSan checks of body + pos at 0x8c6a4 - 0x8c6b0 (the
     null-offset rule) and 0x8c6b4 (`beqz t4`, body = 0) go to the unimp word when body = 0, on every path with
     pos < len, so whenever bb is not empty. Decode's text keeps them not taken by decode_in_block (4096 <= body by
     AR_laws al_blocks); here trans_src_ok_place (DgnTransportBCg.v) gives 0 < body from trans_src_ok in every case
     when bb is not empty (a heap block, a side-stack frame, G_HARNESS_B or TRANS_RO_RD at or above 4096; the machine
     stack at or above alloc_ceiling), with AR at the call state (the journal) and AR_laws (the holds statement).
   The 6 UBSan checks of body + x for a wrap (x < length bb) are kept not taken by body + length bb <= 2^63
   (AR_laws al_blocks for a heap block, decode_rd_ok otherwise).
   The stack differs from image A's: image B's code has a 64-byte frame and calls no function (it stores the 16 zero
   bytes of m->sysex and m->sysex_len with two 8-byte stores, 0x8c700 and 0x8c718, where image A calls
   __asan_memset), so TRANS_MN_STK is the frame alone (image A: 128 + ESTACK) and the holds statement takes no
   contract of __asan_memset, as decode's.

   The contract. The caller's journal is the premise. a0 = c, a struct diginet_cursor whose 25 bytes are
   cursor_cells body (length bb) pos st (lib/Prog/diginet_cursor_init_c.v), with pos <= length bb and st_ok st; a1 =
   m, a struct diginet_msg of 40 bytes mj. c and m are not 0 and are multiples of 8, lie in the caller's live
   side-stack frames, where the caller lets the call write them (decode_twr_ok), their bytes are visible and marked
   usable (decode_rd_ok), and they are outside this call's stack window; c and m do not overlap. When bb is not
   empty, the bytes bb at body are placed by trans_src_ok and lie outside this call's stack window, and they do not
   overlap c or m. Let r = msg_step bb pos st (DgnLib). The function returns to ra with
   a0 = mr_code r, the callee-saved registers kept, no allocator event, every byte outside its stack window and
   outside the bytes of c and m it stores kept, c's 25 bytes = cursor_cells body (length bb) (mr_pos r) (mr_st r) and
   m's 40 bytes = msg_cells body mj r (lib/Prog/diginet_msg_next_c.v). The written range E is the bytes any path
   stores: [c + 16, c + 25) (pos, status) and [m, m + 4), [m + 8, m + 40); it never stores c's body and len
   (c + 0 .. c + 15) or the padding m + 4 .. m + 7. The post states all 25 + 40 bytes, so the bytes a path does not
   store (all of them at the end, pos = length bb) keep their old values.
   The code, measured on the symbol-bearing twin (e217cb0a84f1), 388 words:
     0x8c60c  `addi sp,sp,-64`; ra at sp + 56, s0 .. s6 at sp + 48 .. sp + 0; no realignment, no frame pointer, no
              call (no `jal` except the error paths);
     0x8c634 / 0x8c638  c = 0 or m = 0 returns a0 = -1 (kept unreached: c <> 0, m <> 0);
     0x8c640 / 0x8c644  `andi a0,a0,7; bnez a0` to the `unimp` word at 0x8caa8: the UBSan alignment check of c
              (c->pos, src/diginet_msg.c:31), kept not taken by c mod 8 = 0;
     0x8c64c / 0x8c650  the shadow base through its GOT word 0xa3cf0 (cell 0xac678: transport_cells rows 1-2) into t1;
     0x8c67c / 0x8c680  ld len (c + 8), pos (c + 16); pos >= len (`bgeu` at 0x8c684) returns 0 and stores nothing
              (so the body checks below run only when bb is not empty);
     0x8c698  ld body (c + 0); 0x8c69c a4 = body + pos and three UBSan checks of it to 0x8caa8: `bltu a4,t4`
              (0x8c6a0, body + pos wraps), the null-offset rule (0x8c6a4 - 0x8c6b0), `beqz t4` (0x8c6b4, body = 0)
              (src/diginet_msg.c:36), kept not taken by 0 < body (trans_src_ok_place; bb is not empty here) and
              body + length bb <= 2^63 (trans_src_ok: AR_laws al_blocks for a heap block, decode_rd_ok otherwise);
     0x8c6c8 / 0x8c6cc  `andi t6,a1,7; bnez t6` to 0x8caa8: the UBSan alignment check of m (m->offset,
              src/diginet_msg.c:38), kept not taken by m mod 8 = 0;
     0x8c6e4  lbu body[pos]; then sd pos at m + 24 (0x8c6e8), sd 0 at m + 8 (0x8c700) and m + 16 (0x8c718) (m->sysex
              and m->sysex_len: image A calls __asan_memset (m + 8, 0, 16) here), sb 0 at m + 3 (0x8c730) and m + 2
              (0x8c74c);
     body[pos] = 0xf0 (`bne` at 0x8c750): the search for 0xf7 over body[pos + 1 .. len) (0x8c764 - 0x8c790; UBSan
              check `bltu t3,a3` at 0x8c770: body + pos + i wraps); not found: sb 0 at c + 24 (0x8c80c), a0 = -6, sd
              len at c + 16 (0x8c8b0); found: sb 0 at c + 24 (0x8c82c), sb 0xf0 at m + 0 (0x8c848), sb 0 at m + 1
              (0x8c860), UBSan check `beq a4,a3` (0x8c864: body + pos = 2^64 - 1, src/diginet_msg.c:53), sd
              body + pos + 1 at m + 8 (0x8c874), sd at m + 16 (0x8c884), sd at m + 32 (0x8c8a0), a0 = 1, sd at c + 16
              (0x8c8b0);
     a data byte (bit 7 clear, `bltz` at 0x8c7b4 not taken): lbu status (c + 24, 0x8c7cc); 0 gives sd pos + 1 at
              c + 16 (0x8c8fc), a0 = -7; else sb 1 at m + 1 (0x8c7ec) and the channel arm with data at pos;
     0xf1 .. 0xff (0x8c8bc): sd pos + 1 at c + 16 (0x8c8cc), sb 0 at c + 24 (0x8c8e4), a0 = -8;
     a channel status 0x80 .. 0xef: sb 0 at m + 1 (0x8c920), data at pos + 1; the channel arm (0x8c924): too few
              bytes (`bgeu` at 0x8c938 not taken): sd len at c + 16 (0x8c944), a0 = -6; a data byte with bit 7 set
              (loop 0x8c954 - 0x8c97c, UBSan check `bltu t5,s4` at 0x8c954: body + d + i wraps, src/diginet_msg.c:89):
              sd at c + 16 (0x8c99c), sb 0 at c + 24 (0x8c9b4), a0 = -6; else sb status at m + 0 (0x8c9d0), UBSan
              check `bltu t5,a7` (0x8c9d4: body + d wraps, :96), d1 at m + 2 (0x8c9fc), for a two-byte status the
              UBSan check `bltu t5,a4` (0x8ca10: body + d + 1 wraps, :98) and d2 at m + 3 (0x8ca34, 0 for C0 / D0),
              sd at m + 32 (0x8ca50), sd at c + 16 (0x8ca5c), sb status at c + 24 (0x8ca74), a0 = 1;
     its loads of body lie in [body + pos, body + len) on every path that reaches them, so every UBSan wrap check
              of body + x (x < length bb) is kept not taken by body + length bb <= 2^63 (as above).
   Error paths (36 calls, no abort): load1 x6 (0x8c7a4, 0x8c990, 0x8cab8, 0x8cb78, 0x8cbb4: body bytes, kept
   unreached by trans_src_ok of [body, body + len): a heap block's bytes are marked usable by AR_laws' block shadow,
   every other case carries decode_rd_ok's range_addressable; 0x8cae8: c + 24), load8 x3 (0x8cbb8, 0x8cbc0,
   0x8cbc8: c + 16, c + 8, c + 0), store1 x14 (0x8cac8 .. 0x8cba4: m + 0 .. m + 3, c + 24), store8 x13 (0x8cbd0 ..
   0x8cc18: m + 8, m + 16, m + 24, m + 32, c + 16), kept unreached by decode_rd_ok's range_addressable of [c, c + 25)
   and [m, m + 40): every byte read or stored is addressable (YG0v.v saddr_ok), which is what each check tests; the
   granule each 8-byte access starts in has its last byte in the range, so its shadow byte is 0.
   UBSan checks: 10 branches to the `unimp` word at 0x8caa8 (above): 2 alignment checks (c, m: the two premises), 8
   checks of body + x (kept not taken by 0 < body and body + length bb <= 2^63, as above). No store reaches a
   harness global: every store is to [c + 16, c + 25), [m, m + 4) or [m + 8, m + 40) (trans_mn_wr), in the caller's
   side-stack frame.
   Stack: the 64 bytes of its own frame; it calls nothing, so nothing uses stack below sp - 64.

   The caller is diginet_body_check at 0x8c270 (return address 0x8c274; DgnTransportBList.v PCall
   TB_diginet_msg_next; src/diginet_codec.c:53), in a loop: a0 = c (s5 = its class-2 side-stack frame + 32,
   0x8c1a4), a1 = m (s6 = frame + 96, 0x8c1a8); body and len are its own arguments. It supplies: the cursor bytes
   (diginet_cursor_init's post at 0x8c254, pos 0 and st 0, for the first call; this statement's post for the next
   ones), m's bytes (the frame's 40 bytes, then this post); decode_in_fake (the frame from the stack malloc at
   0x8c16c, a class-2 frame of 256 bytes: 32 + 25 and 96 + 40 inside); c mod 8 = 0 and m mod 8 = 0 (a side-stack
   frame is 64-aligned, YG0f.v frame_addr); decode_twr_ok (the frame is in its journal's own list, present and not
   owned: AR_frames_law); decode_rd_ok (its stores 0x8c214 - 0x8c240 mark the shadow bytes of c (granules 4 .. 7)
   and m (12 .. 16) 0); decode_off_win (frames lie below alloc_ceiling); c / m disjoint by their offsets;
   trans_src_ok, decode_off_win and the disjointness of body from its own statement (a body outside its frame). *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
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

(* diginet_msg_next's frame (`addi sp, sp, -64` at TB_diginet_msg_next; no realignment). It calls no function, so
   its stack window is its frame (image A's: 128 + ESTACK, for its __asan_memset call). *)
Definition TRANS_MN_FRAME : Z := 64.
Definition TRANS_MN_STK : Z := TRANS_MN_FRAME.
(* No allocator event: it calls neither malloc nor free and takes no side-stack frame. *)
Definition TRANS_MN_EV : Z := 0.
(* The cursor bytes it reads (body, len, pos, status: PCur.cursor_cells) and the struct diginet_msg. *)
Definition TRANS_MN_CUR_SIZE : Z := 25.
Definition TRANS_MN_MSG_SIZE : Z := 40.

(* The bytes of c and m the code stores on some path: c->pos and c->status [c + 16, c + 25); m->status, running,
   d1, d2 [m, m + 4); sysex and sysex_len (two 8-byte stores of 0, then the sysex stores), offset and len
   [m + 8, m + 40). *)
Definition trans_mn_wr (c m a : Z) : Prop :=
  c + 16 <= a < c + 25 \/ m <= a < m + 4 \/ m + 8 <= a < m + 40.

(* The 25 cursor bytes and the 40 message bytes as values, in the form the walks' image view reads (garr8, YI00.v). *)
Definition trans_mn_cur_bytes (body len : Z) (pos : nat) (st : Z) : list Z :=
  map bz (LC.cells_bytes (PCur.cursor_cells body len pos st)).
Definition trans_mn_msg_bytes (body : Z) (mj : list byte) (r : msg_res) : list Z :=
  map bz (LC.cells_bytes (PMsg.msg_cells body mj r)).

Section mn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no event, the written range trans_mn_wr c m, no meter
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
   at pos with running status st; m (a1) holds the 40 bytes mj; both are multiples of 8 (image B's UBSan checks),
   inside the caller's live side-stack frames, writable by this call, visible, marked usable, outside its stack
   window and disjoint; when bb is not empty, bb is placed by trans_src_ok, outside this call's stack window and
   disjoint from c and m. *)
Definition transport_diginet_msg_next_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (c m body : Z) (bb mj : list byte) (pos : nat) (st : Z),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 c -> YK11.getr regs 11 = w64 m ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRANS_MN_STK -> spZ regs <= sp0 ->
    c <> 0 -> m <> 0 ->
    (* Image B's UBSan premises: 0x8c640 `andi a0,a0,7` / 0x8c644 `bnez a0` (c) and 0x8c6c8 `andi t6,a1,7` /
       0x8c6cc `bnez t6` (m) trap (unimp at 0x8caa8) on a struct pointer that is not 8-aligned. *)
    c mod 8 = 0 -> m mod 8 = 0 ->
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

(* The statement the walk will prove: the runtime cells (the shadow base through its GOT word) and the allocator and
   meter laws give the contract at TB_diginet_msg_next (image B's function calls no function). *)
Definition transport_diginet_msg_next_cg_holds_stmt : Prop :=
  transport_cells B ->
  AR_laws segs B -> ameter_laws MT ->
  transport_diginet_msg_next_cg (transportb_sigma TB_diginet_msg_next).
End mn.
