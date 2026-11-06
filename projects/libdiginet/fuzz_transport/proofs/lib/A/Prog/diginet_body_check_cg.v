(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame's diginet_body_check in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v:267-317 (cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), with the side-stack frame premises of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cg.v:49-119, at this unit's core names and image A; the shared definitions are lib/A/Prog/DgnFrameCg.v's. *)
(* diginet_body_check_cg: the ASan walk contract of diginet_body_check (src/diginet_codec.c:47-64; plain contracts
   lib/Prog/diginet_body_check_c.v and the wide lib/Prog/diginet_body_check_w_c.v) on fuzz_transport.asan
   (e89be137db17) at 0x8c530 = transport_sigma TS_diginet_body_check, size 1052, as STATEMENTS only (no proof). It
   stores into no harness global, takes a class-2 side-stack frame and calls two program functions, so it takes
   decode's caller-journal form (lib/A/Prog/DgnTransportCg.v decode_cg_post over the caller's donor journal ajournal).

   Taken from libdiginet/fuzz_frame lib/A/Prog/diginet_body_check_cg.v (file sha256 9cc69adfb06c; donor not
   released; fuzz_frame.asan 67d7e481d74e at 0x82e08): the same 1052 code bytes up to the pc-relative words (10
   pc-relative words differ, no other, and the 28-byte frame description string is equal as a C string; re-checked
   here word by word on the two symbol-bearing twins: 263
   words, the 10 that differ are the two GOT-word loads at 0x8c584 / 0x8c588, the stack-malloc call at 0x8c5a0, the
   description string's address at 0x8c5e4 / 0x8c5f4 and the 5 error-path calls). Every pc below is frame's + 0x9728
   and was read again on transport's twin. The names change: frame_cg_post / frame_cells / frame_leaf_wr_at /
   dgnframe_sigma DF_* become this unit's decode_cg_post / transport_cells / transport_leaf_wr_at / transport_sigma
   TS_*, frame_bc_* / FRAME_BC_* become trans_bc_* / TRANS_BC_*, frame_diginet_body_check_cg{,_holds_stmt} become
   transport_diginet_body_check_cg{,_holds_stmt}, and the callee statements are this unit's
   diginet_cursor_init_cg.v transport_diginet_cursor_init_cg and diginet_msg_next_cg.v
   transport_diginet_msg_next_cg (with its TRANS_MN_STK).
   Two premises change, both for transport's call sites:
   - frame's `frame_in_block B lyc Sc body (length bb)` (the bytes in one of the caller's heap blocks) becomes
     `trans_src_ok B lyc Sc W memc body (length bb)` with `decode_off_win regs TRANS_BC_STK body (length bb)`,
     both when bb is not empty (DgnTransportCg.v trans_src_ok): transport's callers pass a command inside
     LLVMFuzzerTestOneInput's side-stack frame, a buffer inside diginet_session_tick's side-stack frame, or the body
     diginet_frame_build is given, none of them a heap block. trans_src_ok's non-block cases carry decode_rd_ok (every
     byte visible, the range marked usable), which is what the walk took from the block (AR_laws' block shadow), and
     decode_off_win keeps the range out of this call's stack window, which the block gave by lying below
     alloc_ceiling. These are the premises diginet_msg_next's statement asks of the body.
   - frame's `body <> 0` becomes `body <> 0 \/ length bb = 0%nat`, the wide plain contract's premise
     (diginet_body_check_w_c.v): send_control calls diginet_frame_build with no body (a5 = a6 = 0 at 0x86ef8 /
     0x86efc), and diginet_frame_build passes them on (0x8bd94 / 0x8bd98). Then diginet_cursor_init sets the cursor
     length to 0, the first diginet_msg_next returns 0, the prefix scan does not run (len < 4), no byte at body is
     read, and a0 = 0 = body_check [].

   The contract. The caller's journal is the premise. a0 = body, a1 = len: the len bytes bb at body hold bb and, when
   bb is not empty, lie where trans_src_ok places them, outside this call's stack window; body is not 0 or bb is
   empty; class 2 of the side stack has a free frame. The function returns to ra with a0 = DgnLib.body_check bb
   (lib/Prog/diginet_body_check_c.v: -10 when the cursor loop finds a sysex F0 13 xx 70 .. F7 or the prefix scan finds
   F0 13 xx 70, else 0), the callee-saved registers kept, the caller's journal extended by no allocator event, its
   side-stack frame released, every byte outside its stack window kept (it writes no byte of its caller: the written
   range E is empty), and no meter charge.
   The callers, each supplying every premise from its own statement (the journal, the body premise, the bytes of the
   body, trans_src_ok and decode_off_win of them, count_cid 2 (frames Sc) < fs_frames 2):
   - diginet_session_submit at 0x89f5c (return address 0x89f60): a0 = c (its second argument; LLVMFuzzerTestOneInput
     passes its local command, at offset 32 of its class-2 side-stack frame), a1 = the byte at c + 24, 1 .. 24 by
     the test at 0x89f48;
   - take at 0x8a68c (return address 0x8a690): a0 = its second argument, a buffer of diginet_session_tick (at offset
     384 of that function's class-5 side-stack frame), a1 = the bytes take has copied into it (the __asan_memcpy call
     at 0x8a67c);
   - diginet_frame_build at 0x8bd9c (return address 0x8bda0): a0 = its argument body (a5), a1 = body_len (a6), after
     its body_len <= 1484 test; send_control passes no body (0, 0), send_data its own.

   The code, measured on the symbol-bearing twin (86efc3a80314; its loaded bytes equal the pin's), 263 words:
     0x8c530  sp = sp - 160; 0x8c534 stores 8 zero bytes at sp; ra at sp + 152, s0 .. s11 at sp + 144 .. sp + 56;
              0x8c56c s0 = sp + 160 (s0 = the entry sp, kept to 0x8c8f4); 0x8c570 sp = sp & -32 (at most 0x10 more
              below entry - 160); s1 = the realigned sp; it stores len at s1 + 16, the stack-malloc result at
              s1 + 24 and the frame base at s1 + 48 (all inside its own frame);
     0x8c584 / 0x8c588 load the GOT words 0xa40e8 (-> the flag word 0xaca00) and 0xa4090 (-> the shadow base cell
              0xac9f8); 0x8c58c a2 = the 4-byte load of the flag word, 0x8c590 s9 = the shadow base (transport_cells
              rows 1, 2, 6, 7); the branch on a2 = 0 at 0x8c598 skips the stack-malloc call when the flag word is 0
              (transport_cells gives 1);
     0x8c59c  a0 = 192, 0x8c5a0 the call of __asan_stack_malloc_2 (0x3d99c = transport_sigma
              TS___asan_stack_malloc_2): a class-2 side-stack frame (fs_frame_bytes 2 = 256 bytes); a 0 result takes
              the real-stack arm (0x8c5b4-0x8c5cc: a probe loop of 4096-byte steps down to sp - 192); with count_cid 2
              (frames Sc) < fs_frames 2 and stack_malloc_progressP the call returns a frame, so that arm is not taken;
     0x8c5fc-0x8c604 the frame header: 0x41b58ab3, the description string 0x16f72 ("2 32 32 4 c:49 96 40 4 m:50"),
              the function address 0x8c530; 0x8c610-0x8c674 the frame's shadow bytes at (frame >> 3) + 0x7fff8000:
              0..3 = 0xf1, 4..7 = 0 (c, the struct diginet_cursor, 32 bytes at frame + 32, marked usable),
              8..11 = 0xf2, 12..16 = 0 (m, the struct diginet_msg, 40 bytes at frame + 96, marked usable),
              17..23 = 0xf3 (guard bytes; stored at 0x8c638-0x8c644 and 0x8c64c-0x8c654);
     0x8c688  the call of diginet_cursor_init (a0 = c, a1 = body, a2 = len): the leaf writes 25 bytes of c;
     0x8c69c-0x8c6a4 the loop: the call of diginet_msg_next (a0 = c, a1 = m); a result of 1 goes to the sysex test,
              any other nonzero result loops, 0 goes to the prefix scan at 0x8c71c. The sysex test reads m.status
              (frame + 96), m.sysex_len (frame + 112) and m.sysex (frame + 104) by plain loads of its own frame, then
              the bytes at m.sysex and m.sysex + 2, each after an instrumented check (error paths at 0x8c93c and
              0x8c718); 0x13 and 0x70 there give -10 (0x8c934);
     0x8c71c-0x8c798 the prefix scan when len >= 4: for i < len - 3 the 1-byte loads of body[i], body[i + 1] and
              body[i + 3], each after an instrumented check (error paths at 0x8c944, 0x8c948, 0x8c7c0);
              F0 13 xx 70 gives -10;
     0x8c7c8-0x8c8f0 the release: shadow bytes 12..16 and 4..7 = 0xf8 (out of scope), header word 0x45e0360e; on
              the side-stack arm all 32 shadow bytes of the 256-byte frame = 0xf5 (released) and the 8-byte load at
              a2 + 248 then the store of one zero byte at that address (0x8c888-0x8c88c) clear the flag byte whose
              address is the frame's last word (frame + 256 - 8; YG0d.v astack_free_law); on the real-stack arm its
              24 shadow bytes = 0;
     0x8c8f4-0x8c930 epilogue (sp = s0 - 160, restores, return). The result register a0 is 0 (0x8c7c4) or -10
              (0x8c934), not written after.
   Error paths: 5 calls of __asan_report_load1 (0x594c8) (0x8c718, 0x8c7c0, 0x8c93c, 0x8c944, 0x8c948), each before
   a 1-byte load of a body byte. trans_src_ok gives the shadow bytes of [body, body + len) marked usable (the block by
   AR_laws al_shadow; every other case by decode_rd_ok's range_addressable), and m.sysex = body + an index of the body
   (diginet_msg_next's statement), so no check fails and no error path is reached. No abort. Writes into caller
   memory: none (its real-stack frame lies in its stack window; the side-stack frame, its shadow bytes and the flag
   byte are the frame it takes and releases, as in the template). No store reaches a harness global.
   Stack: the frame (160), the realignment (0x10), and below the realigned sp the largest callee window: ESTACK (the
   stack malloc, the leaf diginet_cursor_init) or diginet_msg_next's PMN.TRANS_MN_STK.
   Template: reac-repacer/fuzz_uci lib/A/Prog/check_clamp_cg.v:49-58 (constants), :87-105 (statement), :107-119 (holds
   statement); the post is DgnTransportCg.v decode_cg_post. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_cursor_init_cg diginet_msg_next_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_cursor_init_cg.
Module PMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_msg_next_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* diginet_body_check's frame (`sp = sp - 160` at TS_diginet_body_check), the at most 0x10 bytes of `sp = sp & -32`
   (0x8c570) below it, and the largest stack a callee uses below the realigned sp: ESTACK for the stack malloc and
   the leaf diginet_cursor_init (YG0d.v ecall_pre, LeafCgKit.v), diginet_msg_next's own window. *)
Definition TRANS_BC_FRAME : Z := 160.
Definition TRANS_BC_ALIGN : Z := 0x10.
Definition TRANS_BC_STK : Z := TRANS_BC_FRAME + TRANS_BC_ALIGN + Z.max ESTACK PMN.TRANS_MN_STK.
(* No allocator event: the class-2 stack malloc and its release record none (YG00.v stack_malloc, stack_free). *)
Definition TRANS_BC_EV : Z := 0.
(* The side-stack class (a0 = 192 at 0x8c59c, the call of __asan_stack_malloc_2 at 0x8c5a0). *)
Definition TRANS_BC_CID : Z := 2.

Section bc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* What a call leaves: DgnTransportCg.v decode_cg_post with no allocator event, no written range (it writes only its
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
   facts that no byte of G_HARNESS or TRANS_RO_RD is an owned static or errno (with them trans_src_ok_acall carries a
   body in G or TRANS_RO_RD across diginet_msg_next), the allocator, meter and side-stack laws (the meter's fs laws
   too: the frame changes the state's st_fs only, and the post charges 0), and the contracts of
   __asan_stack_malloc_2, the leaf diginet_cursor_init (it writes c, inside the frame this function takes) and
   diginet_msg_next give the contract at TS_diginet_body_check. *)
Definition transport_diginet_body_check_cg_holds_stmt : Prop :=
  pc_stack_malloc (as_code B) TRANS_BC_CID = transport_sigma TS___asan_stack_malloc_2 ->
  transport_cells B ->
  trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B TRANS_BC_CID) ->
  (forall fx' : YK11.FPState, @transport_leaf_wr_at rc B (@LCI.transport_diginet_cursor_init_cg) fx') ->
  (forall fx' : YK11.FPState,
     @PMN.transport_diginet_msg_next_cg fx' rc B MT (transport_sigma TS_diginet_msg_next)) ->
  transport_diginet_body_check_cg (transport_sigma TS_diginet_body_check).
End bc.
