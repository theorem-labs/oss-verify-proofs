(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame lib/A/Prog/diginet_body_check_cg.v (commit 61bffbb56123): module paths, FrameSpec -> DgnSpec DgnLib, the DgnFrameCg / DgnFrameSyms / DgnFrameAddr names -> DgnDecodeCg / DgnDecodeSyms / DgnDecodeAddr (frame_ -> decode_, dgnframe_sigma DF_ -> dgndec_sigma DD_), image-A addresses by symbol from fuzz_frame.asan to fuzz_decode.asan, the header's image and callers. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame's diginet_body_check in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v:267-317 (cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), with the side-stack frame premises of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cg.v:49-119, at this unit's core names and image A; the shared definitions are lib/A/Prog/DgnFrameCg.v's. *)
(* diginet_body_check_cg (image B): the ASan walk contract of diginet_body_check (src/diginet_codec.c:47-64; plain
   contracts lib/Prog/diginet_body_check_c.v and the wide lib/Prog/diginet_body_check_w_c.v) on
   fuzz_transport.asan-ubsan (41113a03c82f) at 0x8c0fc = transportb_sigma TB_diginet_body_check, size 1112, as
   STATEMENTS only (no proof). It stores into no harness global, takes a class-2 side-stack frame and calls two program
   functions, so it takes decode's caller-journal form (lib/B/Prog/DgnTransportBCg.v decode_cg_post over the caller's
   donor journal ajournal). Form: lib/A/Prog/diginet_body_check_cg.v (the same definitions, premises and post).

   RELOCATED from libdiginet/fuzz_decode's image-B statement lib/B/Prog/diginet_body_check_cg.v (file sha256
   a94e893a459b; donor not released; fuzz_decode.asan-ubsan at 0x82970, size 1112): every pc that text names,
   moved by + 0x978c, was read again on this
   unit's twin and holds the same instruction (the frame, the realignment, the two runtime-cell loads, the stack
   malloc, the frame header and shadow, the two calls, the sysex test, the prefix scan, the release, the 7 UBSan
   branches, the trap word and the 5 error-path calls). The names change: decode_bc_post / FRAME_BC_* /
   decode_diginet_body_check_cg{,_holds_stmt} become trans_bc_post / TRANS_BC_* /
   transport_diginet_body_check_cg{,_holds_stmt} (image A's names, lib/A/Prog/diginet_body_check_cg.v),
   DgnDecodeBSyms / DgnDecodeBAddr dgndecb_sigma DDB_ become DgnTransportBSyms / DgnTransportBAddr transportb_sigma
   TB_, DgnDecodeBCg's decode_cells / decode_leaf_wr_at become DgnTransportBCg's transport_cells /
   transport_leaf_wr_at, decodesegsB0 becomes lib/B/YB1v.v tfibsegs, and the callee statements are this unit's
   image-B lib/B/Prog/diginet_cursor_init_cg.v transport_diginet_cursor_init_cg and lib/B/Prog/diginet_msg_next_cg.v
   transport_diginet_msg_next_cg (with its TRANS_MN_STK).
   Two premises change, the two that image A's text changes for transport's call sites (the code does not force
   them; transport's callers do):
   - decode's `decode_in_block B lyc Sc body (length bb)` (the bytes in one of the caller's heap blocks) becomes
     `trans_src_ok B lyc Sc W memc body (length bb)` with `decode_off_win regs TRANS_BC_STK body (length bb)`,
     both when bb is not empty (DgnTransportBCg.v trans_src_ok): transport's callers pass a command inside
     LLVMFuzzerTestOneInput's side-stack frame, a buffer inside diginet_session_tick's side-stack frame, or the body
     diginet_frame_build is given, none of them a heap block. trans_src_ok's non-block cases carry decode_rd_ok (every
     byte visible, the range marked usable, 0 <= body and body + len <= 2 ^ 63), which is what the walk took from the
     block (AR_laws' block shadow and al_blocks), and decode_off_win keeps the range out of this call's stack window,
     which the block gave by lying below alloc_ceiling. These are the premises diginet_msg_next's statement asks of
     the body.
   - decode's `body <> 0` becomes `body <> 0 \/ length bb = 0%nat`, the wide plain contract's premise
     (diginet_body_check_w_c.v): send_control calls diginet_frame_build with no body (a5 = a6 = 0 at 0x87078 /
     0x8707c), and diginet_frame_build passes them on (a0 = s2 = a5, a1 = s1 = a6 at 0x8b8b4 / 0x8b8b8). Then
     diginet_cursor_init sets the cursor length to 0, the first diginet_msg_next returns 0 before it reads the body
     (its pos >= len test), the prefix scan does not run (len < 4), no byte at body is read, no UBSan branch is
     reached, and a0 = 0 = body_check [].
   No premise is added for image B: each of its 7 UBSan branches is refuted by the premises above (below).

   The contract. The caller's journal is the premise. a0 = body, a1 = len: the len bytes bb at body hold bb and, when
   bb is not empty, lie where trans_src_ok places them, outside this call's stack window; body is not 0 or bb is
   empty; class 2 of the side stack has a free frame. The function returns to ra with a0 = DgnLib.body_check bb
   (lib/Prog/diginet_body_check_c.v: -10 when the cursor loop finds a sysex F0 13 xx 70 .. F7 or the prefix scan finds
   F0 13 xx 70, else 0), the callee-saved registers kept, the caller's journal extended by no allocator event, its
   side-stack frame released, every byte outside its stack window kept (it writes no byte of its caller: the written
   range E is empty), and no meter charge.
   The callers, each supplying every premise from its own statement (the journal, the body premise, the bytes of the
   body, trans_src_ok and decode_off_win of them, count_cid 2 (frames Sc) < fs_frames 2):
   - diginet_session_submit at 0x89b60 (return address 0x89b64): a0 = c (s0, its second argument;
     LLVMFuzzerTestOneInput passes its local command c.i, at offset 32 of its class-2 side-stack frame: s4 = frame + 32
     at 0x817d8, kept in s1 + 144 from 0x81824; the calls at 0x825cc and 0x82744), a1 = the byte at c + 24 (0x89b40),
     1 .. 24 by the test at 0x89b4c;
   - take at 0x8a328 (return address 0x8a32c): a0 = its second argument (s2, the word at sp + 80 stored at 0x8a19c and
     loaded at 0x8a30c), a 1484-byte buffer of diginet_session_tick (at offset 160 of that function's class-5
     side-stack frame: s9 = s11 + 160 at 0x89848, the call of take at 0x89874), a1 = the bytes take has copied into it
     (s8 plus the length byte at s4 + 1784, 0x8a31c - 0x8a320, after the __asan_memcpy call at 0x8a318);
   - diginet_frame_build at 0x8b8bc (return address 0x8b8c0): a0 = its argument body (a5), a1 = body_len (a6), after
     its tests at 0x8b87c - 0x8b888 (a body length that is not 0 with no body returns -1) and 0x8b89c (body_len <=
     1484); send_control passes no body (0, 0), send_data its own (a5 = s6, a6 = the word at s1 + 24, 0x89ef4 /
     0x89ef8; the call at 0x89efc).

   The code, measured on the symbol-bearing twin (e217cb0a84f1; its loaded bytes equal the pin's but the ELF header's
   section-table fields and the build-id note, and the 1112 code bytes of this function are equal in both files),
   symbol diginet_body_check, value 0x8c0fc, size 1112, 278 words:
     0x8c0fc  sp = sp - 160; 0x8c100 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 .. sp + 56;
              0x8c138 s0 = sp + 160 (s0 = the entry sp, kept to 0x8c4f8); 0x8c13c sp = sp & -32 (at most 0x10 more
              below entry - 160); s1 = the realigned sp; it stores len at s1 + 16 (0x8c24c), the stack-malloc result
              at s1 + 24 (0x8c19c) and the frame base at s1 + 48 (0x8c1a0) (all inside its own frame);
     0x8c150 / 0x8c154 load the GOT words 0xa3d48 (GOT_UAR, -> the flag word 0xac680) and 0xa3cf0 (GOT_CELL_K, -> the
              shadow base cell 0xac678); 0x8c158 a2 = the 4-byte load of the flag word, 0x8c15c s9 = the shadow base
              (transport_cells rows 1, 2, 6, 7); the branch on a2 = 0 at 0x8c164 skips the stack-malloc call when the
              flag word is 0 (transport_cells gives 1);
     0x8c168  a0 = 192, 0x8c16c the call of __asan_stack_malloc_2 (0x3d9f8 = transportb_sigma
              TB___asan_stack_malloc_2): a class-2 side-stack frame (fs_frame_bytes 2 = 256 bytes); a 0 result takes
              the real-stack arm (0x8c180 - 0x8c198: a probe loop of 4096-byte steps down to (sp - 192) & -32); with
              count_cid 2 (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame, so that arm
              is not taken;
     0x8c1c8 - 0x8c1d0 the frame header: 0x41b58ab3, the description string 0x16f4c ("2 32 32 4 c:49 96 40 4 m:50"),
              the function address 0x8c0fc; 0x8c1dc - 0x8c240 the frame's shadow bytes at (frame >> 3) + 0x7fff8000:
              0..3 = 0xf1, 4..7 = 0 (c, the struct diginet_cursor, 32 bytes at frame + 32, marked usable),
              8..11 = 0xf2, 12..16 = 0 (m, the struct diginet_msg, 40 bytes at frame + 96, marked usable),
              17..23 = 0xf3 (the right guard bytes: a0 = -13 at 0x8c200, stored to 20..23 at 0x8c204 - 0x8c210 and to
              17..19 at 0x8c218 - 0x8c220; 16 is set to 0 at 0x8c214);
     0x8c254  the call of diginet_cursor_init (0x8c554; a0 = c = frame + 32, a1 = body, a2 = len): the leaf writes 25
              bytes of c; 0x8c258 - 0x8c264 the loop constants s10 = 1, s11 = 0xf0, s2 = 3, s4 = 0x13;
     0x8c268 - 0x8c27c the loop: the call of diginet_msg_next (0x8c60c; a0 = c, a1 = m = frame + 96) at 0x8c270; a
              result of 1 goes to the sysex test, any other nonzero result loops, 0 goes to the prefix scan at
              0x8c2f4. The sysex test reads m.status (frame + 96, 0x8c280), m.sysex_len (frame + 112, 0x8c288) and
              m.sysex (frame + 104, 0x8c290) by plain loads of its own frame, then the bytes at m.sysex (0x8c2a8) and
              m.sysex + 2 (0x8c2cc), each after an instrumented check (error paths at 0x8c544 and 0x8c2f0); 0x13 and
              0x70 there give -10 (0x8c538);
     0x8c2f4 - 0x8c3a0 the prefix scan when len >= 4 (len read back from s1 + 16 at 0x8c2f8): for i < len - 3 (i in
              a2, body in s3) the 1-byte loads of body[i] (0x8c34c), body[i + 1] (0x8c36c) and body[i + 3]
              (0x8c390), each after an instrumented check (error paths at 0x8c548, 0x8c550, 0x8c3c4);
              F0 13 xx 70 gives -10;
     0x8c3cc - 0x8c4f4 the release: shadow bytes 12..16 and 4..7 = 0xf8 (out of scope), header word 0x45e0360e
              (0x8c400); on the side-stack arm all 32 shadow bytes of the 256-byte frame = 0xf5 (released) and the
              8-byte load at a2 + 248 then the store of one zero byte at that address (0x8c48c - 0x8c490) clear the
              flag byte whose address is the frame's last word (frame + 256 - 8; YG0d.v astack_free_law); on the
              real-stack arm (0x8c498 - 0x8c4f4) its 24 shadow bytes = 0;
     0x8c4f8 - 0x8c534 epilogue (sp = s0 - 160, restores, return). The result register a0 is 0 (0x8c3c8) or -10
              (0x8c538), not written after.
   UBSan checks (image B only): 7 branches to the trap word at 0x8c540, all kept not taken by the premises above:
   0x8c294 (m.sysex is 0: m.sysex = body + an index of bb, which diginet_msg_next's statement gives, and body + len <=
   2 ^ 63 with 0 < body, since bb is not empty there), 0x8c2b4 with a1 = -2 at 0x8c2b0 (m.sysex + 2 wraps: m.sysex +
   2 < body + len), and in the prefix scan, where len >= 4 so body <> 0 by the wide premise: 0x8c324 (body + i
   wraps), the null-offset rule at 0x8c328 - 0x8c330 (body + i is 0 while body is not, or the reverse), 0x8c334 (body
   is 0), 0x8c354 with a3 = ~body (0x8c304; body + i + 1 wraps) and 0x8c378 with a1 = i + 3 (body + i + 3 wraps):
   i + 3 < len and body + len <= 2 ^ 63 (trans_src_ok: the block below alloc_ceiling, AR_laws al_blocks, or
   decode_rd_ok).
   Error paths: 5 calls of __asan_report_load1 (0x59504) (0x8c2f0, 0x8c3c4, 0x8c544, 0x8c548, 0x8c550; the last after
   a0 = a1 at 0x8c54c), each before a 1-byte load of a body byte. trans_src_ok gives the shadow bytes of
   [body, body + len) marked usable (the block by AR_laws al_shadow; every other case by decode_rd_ok's
   range_addressable), and m.sysex = body + an index of the body (diginet_msg_next's statement), so no check fails
   and no error path is reached. No abort. Writes into caller memory: none (its real-stack frame lies in its stack
   window; the side-stack frame, its shadow bytes and the flag byte are the frame it takes and releases, as in the
   template). No store reaches a harness global.
   Image B against image A's code (lib/A/Prog/diginet_body_check_cg.v, 263 words): the same frame, saves, header,
   shadow, calls and release; image B adds the 7 UBSan branches and the trap word, and its prefix scan keeps body in
   s3 and counts i up in a2 (image A advances s3); its error paths are laid out after the trap word.
   Stack: the frame (160), the realignment (0x10), and below the realigned sp the largest callee window: ESTACK (the
   stack malloc, the leaf diginet_cursor_init) or diginet_msg_next's PMN.TRANS_MN_STK (image B's diginet_msg_next has
   a 64-byte frame and calls nothing).
   Template: reac-repacer/fuzz_uci lib/A/Prog/check_clamp_cg.v:49-58 (constants), :87-105 (statement), :107-119 (holds
   statement); the post is DgnTransportBCg.v decode_cg_post. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_cursor_init_cg diginet_msg_next_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_cg.
Module PMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_body_check's frame (`sp = sp - 160` at TB_diginet_body_check), the at most 0x10 bytes of `sp = sp & -32`
   (0x8c13c) below it, and the largest stack a callee uses below the realigned sp: ESTACK for the stack malloc and
   the leaf diginet_cursor_init (YG0d.v ecall_pre, LeafCgKit.v), diginet_msg_next's own window. *)
Definition TRANS_BC_FRAME : Z := 160.
Definition TRANS_BC_ALIGN : Z := 0x10.
Definition TRANS_BC_STK : Z := TRANS_BC_FRAME + TRANS_BC_ALIGN + Z.max ESTACK PMN.TRANS_MN_STK.
(* No allocator event: the class-2 stack malloc and its release record none (YG00.v stack_malloc, stack_free). *)
Definition TRANS_BC_EV : Z := 0.
(* The side-stack class (a0 = 192 at 0x8c168, the call of __asan_stack_malloc_2 at 0x8c16c). *)
Definition TRANS_BC_CID : Z := 2.

Section bc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportBCg.v decode_cg_post with no allocator event, no written range (it writes only its
   own frames), no meter charge (the side-stack frame changes st_fs only: ameter_fs_laws), and a0 = body_check bb. *)
Definition trans_bc_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (bb : list byte) : world segs -> config -> Prop :=
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TRANS_BC_STK TRANS_BC_EV 0
    (fun _ => False)
    (fun regs2 _ _ => YK11.getr regs2 10 = w64 (body_check bb)).

(* The contract at entry address a, in the caller-journal form. body (a0) is not 0 or the body is empty; the len
   (a1) bytes bb at body hold bb and, when bb is not empty, are placed by trans_src_ok outside this call's stack
   window; class 2 has a free side-stack frame. *)
Definition transport_diginet_body_check_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (body : Z) (bb : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 body -> YK11.getr regs 11 = w64 (Z.of_nat (length bb)) ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRANS_BC_STK -> spZ regs <= sp0 ->
    body <> 0 \/ length bb = 0%nat ->
    ((0 < length bb)%nat -> trans_src_ok B lyc Sc W memc body (Z.of_nat (length bb))) ->
    ((0 < length bb)%nat -> decode_off_win regs TRANS_BC_STK body (Z.of_nat (length bb))) ->
    garr8 segs (mrestrict (w_H W) memc) body (map bz bb) ->
    count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID ->
    st_nev S + k + TRANS_BC_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (trans_bc_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs bb).

(* The statement the walk will prove: the class-2 stack-malloc entry of the record, the runtime cells, the record's
   facts that no byte of G_HARNESS_B or TRANS_RO_RD is an owned static or errno (with them trans_src_ok_acall carries
   a body in G or TRANS_RO_RD across the call of diginet_msg_next at 0x8c270, before the body loads at 0x8c2a8,
   0x8c2cc and 0x8c34c - 0x8c390), the allocator, meter and side-stack laws (the meter's fs laws too: the frame
   changes the state's st_fs only, and the post charges 0), and the contracts of __asan_stack_malloc_2, the leaf
   diginet_cursor_init (it writes c, inside the frame this function takes) and diginet_msg_next give the contract at
   TB_diginet_body_check. *)
Definition transport_diginet_body_check_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) TRANS_BC_CID = transportb_sigma TB___asan_stack_malloc_2 ->
  transport_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B TRANS_BC_CID) ->
  (forall fx' : YK11.FPState, @transport_leaf_wr_at rc B (@LCI.transport_diginet_cursor_init_cg) fx') ->
  (forall fx' : YK11.FPState,
     @PMN.transport_diginet_msg_next_cg fx' rc B MT (transportb_sigma TB_diginet_msg_next)) ->
  transport_diginet_body_check_cg (transportb_sigma TB_diginet_body_check).
End bc.
