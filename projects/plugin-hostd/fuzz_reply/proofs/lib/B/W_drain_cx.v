(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane, a Theorem Labs lane's dr_sa_align row): the kit's dr_spec now states SA mod 8 = 0 (W7's A text), so FINDING 1 is closed: dr_sa_align is deleted and dr_all_stmt takes the premise from dr_spec; dr_sa_align_slot moved to lib/B/W_drain_sa.v (W6 72eb36c9efa). The unused Section hypothesis LDSPEC is deleted (a Theorem Labs lane). *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT INTERFACE of the ASan+UBSan walk (image B,
   fuzz_reply.asan-ubsan) of fuzz_reply's drain, 0x83278 .. 0x841fc (993 instructions, nm size 0xf84), the
   lib/B twin of lib/A/W_drain_cx.v (a working branch 42f8ce51aaa).  B is NOT A relocated: UBSan is
   TRAP mode in this pin (no __ubsan_handle_* symbol), so the checks are inline branches to the `unimp` at
   0x84004, the frame is 352 bytes (A: 336), the register allocation differs, and the shadow base lives in a
   frame slot (A keeps it in s5).  Same contract shape, same decomposition, same statement names; a fresh
   walk.  EVERY image-dependent number below is re-derived from fuzz_reply.asan-ubsan's own objdump and nm and
   from lib/B/W_listing.v / lib/B/W_place.v; no A numeral is copied.
   Nothing is proved here: the file fixes the Section hypotheses, the entry context, the cut predicates over
   concrete machine states and the statement of every segment, so that the segments are proved in parallel.

   drain (s) is relay.c:171-224 with gesture_seen (relay.c:89-121) inlined and the harness's fuzz_recv
   (fuzz_reply.c:240-276) with source_of, reference_feed (217-238) and list_drop (153-158); on image B
   list_drop is NOT inlined but CALLED (0x83914 -> 0x85b50), so the DROP stage calls it through the proved
   pb_list_drop_ro_c (lib/B/W_list_drop.v) at the pending list's 16-byte header cell (&h->pending) (NOT at G_DR: gx_rt excludes
   errno's bytes), with AFREE (the _c rule) and HCTX_ld, where lib/A's takes the inlined free and __asan_memmove.
   Its contract is lib/B/W_contract.v Section s7: dr_spec B MT MMAX RG (BASE + AF_fr_drain), post dr_post.
   The functional half is the plain proof's (lib/Prog/drain_b_c.v drain_run and lib/A/W_drain_model.v, the
   image-free copy of lib/Prog/drain_b.v:22-336 of its pure round model, Required by path); the memory half is
   lib/B/W_journal.v's ajournal_gx at G_DR and the allocator's live-state meter MT.

   A -> B CUT POINTS (B pc = 0x83278 + the offset each definition carries; listing slot = (pc - 0x82344) / 4,
   AF_fr_drain = 0xf34, fr_B0 = 0x82344):
     entry            A 0x830dc   B 0x83278  (+0x000)
     DI    dr_top     A 0x831f8   B 0x833c0  (+0x148)  the outer loop's head, in the round state s
     DRB   dr_feed    A 0x8347c   B 0x836fc  (+0x484)  reference_feed's byte loop, after k of the n bytes
     DE    dr_fed     A 0x835ac   B 0x838a0  (+0x628)  the byte loop left
     DLL   dr_line    A 0x836bc   B 0x8399c  (+0x724)  the line [p, q) found in the relay's buffer
     DLN   dr_next    A 0x836f4   B 0x839d4  (+0x75c)  the line done: on to the next
     DGS   dr_seen    A 0x837c8   B 0x83aa4  (+0x82c)  gesture_seen's held-array search
     DLR   dr_rest    A 0x83a4c   B 0x83e34  (+0xbbc)  no further line: the rest of the buffer moved down
     DEND  dr_end     A 0x83bbc   B 0x83e94  (+0xc1c)  no pending text: the closed / EAGAIN tail
     eof store        A 0x83b64   B 0x83fa8  (+0xd30)  s->eof = 1
     epilogue         A 0x83b80   B 0x83fc8  (+0xd50)  13 restores, addi sp,sp,352, ret
   B's line loop re-enters at 0x8395c and both DLL and DLR are reached from the ONE memchr at 0x83990 (A has
   two memchr sites, 0x836a4 for the first line and 0x8372c for the next), so DROP and NEXT join there; the
   cut points and the statements are unchanged by that.

   A -> B CALL SITES:
     realloc #1 (the buffer)     A 0x83248  B 0x83410   -> SIGMA WS_realloc   0x53e48
     __errno_location EBADF      A 0x83b44  B 0x834f8   -> 0x8cf28 (A shares one site for EBADF / EAGAIN)
     __errno_location EINTR      A 0x8333c  B 0x8354c
     __asan_memcpy               A 0x833f4  B 0x8365c   -> 0x52780
     list_push                   A 0x834f0  B 0x837a4   -> BASE + AF_fr_list_push = 0x85324
     free      (list_drop)       A 0x83618  B  --       B calls list_drop instead
     memmove   (list_drop)       A 0x83648  B  --       B calls list_drop instead
     list_drop                   A  --      B 0x83914   -> BASE + AF_fr_list_drop = 0x85b50
     free      (in list_drop)    A  --      B 0x85be8   -> 0x53e40, returns to 0x85bec = BASE + AF_fr_list_drop + 0x9c (HCTX_ld)
     memchr (first line)         A 0x836a4  B 0x83990   -> 0x42208
     memchr (next line)          A 0x8372c  B 0x83990   (one site on B)
     send_line                   A 0x83744  B 0x839f0   -> BASE + AF_fr_send_line = 0x82854
     strrchr                     A 0x83750  B 0x839fc   -> 0x421fc
     strncmp "param_gesture"     A 0x83768  B 0x83a14   -> 0x421f4
     strcmp  "begin"             A 0x837a8  B 0x83a78   -> 0x421f0
     strcmp  "end"               A 0x837c0  B 0x83a9c
     strlen  (held key)          A 0x83850  B 0x83b6c   -> 0x421e4
     strncmp (held key)          A 0x83864  B 0x83b84
     realloc #2 (held array)     A 0x838c0  B 0x83be8
     strndup                     A 0x838e0  B 0x83c08   -> 0x421ec
     free #2 (end of a gesture)  A 0x8394c  B 0x83ccc   -> 0x53e40
     __asan_memmove (the rest)   A 0x83a68  B 0x83e50   -> 0x52e5c
     __errno_location EAGAIN     A 0x83a20  B 0x83eac
     __errno_location (n < 0)    A 0x83a20  B 0x83ed8   (B has four errno sites, A three)

   FRAME.  A: 336 bytes, 13 saves at 232(sp) .. 328(sp).  B: 352 bytes (0x83278 addi sp,sp,-352), 13 saves at
   248(sp) .. 344(sp) in the same order [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra], and 23
   one-time slots the prologue 0x832b0 .. 0x833bc sets and nothing else writes (dr_frame; A has 16):
     8  (SA mod 8) + 3     32  SA + 48          40  (GS + 8) / 8     48  (GS + 56) / 8
     56 (GS + 48) / 8      64  (GS + 40) / 8    72  (GS + 32) / 8    80  (GS + 16) / 8
     88 SA + 40           104  (GS + 24) / 8   120  GS              128  SA + 16
     136 SA + 24          144  SA              152  (GS + 12) / 8   176  SA + 32
     184 6001             200  shadow_addr SA  208  SA + 8          216  shadow_addr (SA + 32)
     224 shadow_addr (SA + 16)                 232  shadow_addr (SA + 24)
     240 SHADOW_OFF
   (A's dr_frame keeps the same facts at 88 / 96 / 104 / 112 / 120 / 128 / 136 / 144 / 152 / 160 / 168 / 176 /
   184 / 208 / 216 / 224 and holds SA, SA + 8 .. SA + 32, GS and the shadow base in registers instead.)
   Slots 0, 16, 24, 96, 112, 160, 168, 192 are scratch: the walk rewrites them per round or per line, so they
   are carried by the cut predicates that need them, never by dr_frame.

   REGISTERS (x-numbers; s0 = x8, s1 = x9, s2 = x18, s3 = x19, s4 = x20, s5 = x21, s6 = x22, s7 = x23,
   s8 = x24, s9 = x25, s10 = x26, s11 = x27, t1 = x6, a5 = x15).
     DI (dregs_top)    B: s5 = SA, s8 = SA + 8, s4 = SA + 16, s6 = SA + 24, s11 = SA + 32, s0 = GS,
                          s1 = GS / 8, s2 = (GS + 4) / 8, s10 = 384 (the scan's bound, 4 * ASRC).
                       A: s6 = SA, s9 = SA + 32, s11 = SA + 24, s10 = SA + 16, s2 = GS, s1 = GS / 8,
                          s0 = (GS + 4) / 8, s5 = SHADOW_OFF, s7 = shadow (SA + 32), s8 = shadow SA.
     the line cuts     B (dregs_line): s5 = SA, s4 = SA + 16, s6 = SA + 24, s11 = SA + 32, s0 = GS,
                          s1 = GS / 8, s2 = (GS + 4) / 8; s3 = s->buf, s8 = buf + p, s7 = buf + q (DLL) or
                          buf + p - 1 (DLN), s9 = |W| - p (DLL / DLR), s10 = 384 (DLL / DLR only: the GS stage
                          uses s10 for the key and 0x839d8 re-loads it just after DLN).
     DRB               B: s11 = p0 (the base), s3 = s8 = p0 + k, t1 = v[0].s, s4 = 1 (the one-time
                          `snez v[0].s`, an atom fact so the runner decides the null traps), s5 = n - k,
                          a5 = n, a6 = shadow (HA + 40), a7 = shadow (HA + 48), s6 = shadow (HA + 56),
                          s7 = HA; 24(sp) = HA + 56, 96(sp) = HA + 16, 160(sp) = HA + 64,
                          112(sp) = shadow (HA + 16), 168(sp) = shadow (HA + 32), 192(sp) = n.
                       A: s9 = n - k, s8 = s10 = p0 + k, s3 = n, s7 = &g_s[j], s4 / s11 / s6 = the shadow
                          bytes of h->partial / h->npartial / h->overlong.
     DE                B: s7 = HA, a5 = n, and the four scratch slots above (s4 / s5 / s6 / s10 / s11 are
                          re-loaded from the frame at 0x838a8 .. 0x838d0, so the cut does not fix them).
     DEND              B: s5 = SA, s7 = HA, s3 = SHADOW_OFF + 12 j (A: s7 = &g_s[j], s8 = shadow base + 12 j).

   OBJECTS (lib/B/W_place.v fr_obj; the labels MOVE between the images, so each is keyed by CONTENT, read out
   of the pinned ELF at the address below):
     A_OBJ 0  = 0x9df50  the GOT slot of __asan_shadow_memory_dynamic_address   (A: A_OBJ 0  = 0x9d9d0)
     A_OBJ 30 = 0xa6638  __asan_shadow_memory_dynamic_address                   (A: A_OBJ 32)
     A_OBJ 19 = 0x5d8e60 g_s                                                    (A: A_OBJ 22)
     A_OBJ 18 = 0x20f20  "param_gesture\0"  (B label .str.6, A label .str.5)    (A: A_OBJ 21)
     A_OBJ 20 = 0x20f40  "begin\0"          (B label .str.7, A label .str.6)    (A: A_OBJ 23)
     A_OBJ 21 = 0x20f60  "end\0"            (B label .str.8, A label .str.7)    (A: A_OBJ 24)
     A_OBJ 9  = 0xa2560  g_client                                               (A: A_OBJ 9)
   g_send_dead (0x5d8e00) and g_send_max (0x5d8dc0) are NOT listing objects of image B (A reaches g_send_dead
   as A_OBJ 12; B's A_OBJ 12 is g_nout, 0x5d8e40 -- copying A's HV12 would build green and be false here), so
   their placement is stated as the image band they lie in (HSD / HSM), which is all aout_at needs to move
   across a store to this frame.  The band's top is image B's own: pa_img_range gives 0x10000 <= a < 0x5fc000
   (A cites 0x5fb000).
   musl memchr's constant window is re-derived from image B: memchr 0x96950 reads 0x10350 and 0x10368
   (0x969ac, 0x969b4), so the window [0x10350, 0x10370) is B's as well as A's.

   TRAP SITES IN drain: 49 decision points, the most of any function of image B, all to the one `unimp` at
   0x84004 (0x839e0 traps on its NOT-TAKEN edge, through the `j 0x84004` at 0x839e4).  Checked branch by
   branch against fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) and agreeing site for site and shape for shape with the published
   census (TRAPS-ALL.md (sha256 c90982171c9b; internal record) rows 60-108: NONNULL 14, ALIGN8 7, PTR_BLTU 6, NULL_XOR 6,
   ALIGN4 3, ADDW1 2, NULL_BEQ 2, PTR_SOVF 2, PTR_NOT 2, NONNULL_LIT 1, PTR_EQK_FT 1, PTR_CONST 1, PTR_EQK 1,
   DECW 1).  The lemma named is lib/B/W_traps.v's (a working branch 6c73ae99620, 48 lemmas
   Qed); "R1" .. "R5" are that file's seat recipe, and a site marked R is decided inside paj_run_tok once the
   cut's atom facts are seated (pointer atoms mkAF 4096 140737479966720 3, errno al2 2, one-time flags
   mkAF 1 1 0), which is what the dinband / `getr regs1 20 = w64 1` conjuncts below are for.  No shape of
   drain is missing from the kit.  Stage = the segment that runs the site.
     PRO   0x832b8  ALIGN8   andi 7; bnez (on SA)        R1; trap_align8              [FINDING 1]
     TOP   0x83468  PTR_BLTU bltu buf+used, buf          R5; trap_ptr_wrap_atom / trap_ptr_bltu
     TOP   0x83478  NULL_XOR snez; seqz; xor; beqz       R1 / R2; trap_null_xor
     TOP   0x834fc  NONNULL  beqz errno                  R1; trap_nonnull
     TOP   0x83504  ALIGN4   andi 3; bnez errno          R1 (al2 2, HERRAL); trap_align4
     TOP   0x83550  NONNULL  beqz errno                  R1; trap_nonnull
     TOP   0x83558  ALIGN4   andi 3; bnez errno          R1 (al2 2, HERRAL); trap_align4
     TOP   0x8357c  NONNULL  beqz errno                  R1; trap_nonnull
     TOP   0x83580  NONNULL_LIT beqz a1, a1 = 1          decided, no stop (literal)
     TOP   0x835dc  NONNULL  beqz v (pending.v)          R1; trap_nonnull
     TOP   0x835e4  ALIGN8   andi 7; bnez v              R1; trap_align8
     TOP   0x83644  PTR_BLTU bltu off+v[0].s, v[0].s     R5; trap_ptr_wrap_atom / trap_ptr_bltu
     TOP   0x83654  NULL_XOR snez; seqz; xor; beqz       R1 / R2; trap_null_xor
     TOP   0x83674  NONNULL  beqz v                      R1; trap_nonnull
     TOP   0x8367c  ALIGN8   andi 7; bnez v              R1; trap_align8
     TOP   0x836ac  PTR_BLTU bltu p0, v[0].s             R5; trap_ptr_wrap_atom / trap_ptr_bltu
     TOP   0x836bc  NULL_XOR snez; seqz; xor; beqz       R1 / R2; trap_null_xor
     FEED  0x836fc  PTR_BLTU bltu p0+k, p0               R5 seated once: trap_seat (trap_ptr_wrap_atom ..)
     FEED  0x83708  NULL_XOR xor (atom snez); beqz       R3 (s4 = 1 at the cut); trap_null_xor_folded
     FEED  0x8370c  NONNULL  beqz t1 (v[0].s)            R1; trap_nonnull
     FEED  0x83808  PTR_BLTU bltu partial+npartial, partial   R5; trap_ptr_wrap_atom
     FEED  0x83818  NULL_XOR snez; seqz; xor; beqz       R1 / R2; trap_null_xor
     FEED  0x8381c  NONNULL  beqz partial                R1; trap_nonnull
     DROP  0x838e0  NONNULL  beqz v                      R1; trap_nonnull
     DROP  0x838e8  ALIGN8   andi 7; bnez v              R1; trap_align8
     DROP  0x83ee4  NONNULL  beqz errno                  R1; trap_nonnull
       the n < 0 arm: 0x83ed8 .. 0x83ee8 is reached ONLY from DROP's `bltz a5` at 0x8392c, which DROP refutes
       from DE's 0 < dnum s1, so no stage walks it; the `j 0x83580` it ends in lands in TOP's shared errno
       tail (0x83574 .. 0x835a0), which on the split of lib/B/W_drain_topb_cx.v is the TAIL half's code.
     NEXT  0x839e0  PTR_EQK_FT li -1; bne nul,-1; j unimp (the NOT-TAKEN edge traps)
                                                         R1; trap_seat (trap_br_eq ..)
     LINEA 0x83a1c  NONNULL  beqz line                   R1; trap_nonnull
     LINEA 0x83a24  PTR_CONST li -13; bgeu line,-13      R1; trap_ptr_wrap_k / trap_br_geu
     LINEA 0x83a64  PTR_EQK  li -1; beq last,-1          R1; trap_br_eq
     GS    0x83b38  PTR_BLTU bltu hp+8i, hp              R5; trap_ptr_wrap_atom
     GS    0x83b44  NULL_XOR xor (atom snez hp); beqz    R3; trap_null_xor_folded
     GS    0x83b4c  NONNULL  beqz the one-time flag 168(sp) (hp aligned and not null)
                                                         R3; trap_w_base_ok / trap_nonnull
     GS    0x83bc4  ADDW1    addiw +1; blt               R4; trap_addw1
     GS    0x83c28  ADDW1    addiw +1; blt               R4; trap_addw1
     GS    0x83c60  NULL_BEQ snez; seqz; beq             R1 / R2; trap_null_beq
     GS    0x83c74  PTR_SOVF sltu; slti; xor; xori 1; beqz   R5; trap_ptr_sovf + trap_U_sltu_ge
     GS    0x83c78  NONNULL  beqz hp                     R1; trap_nonnull
     GS    0x83c80  ALIGN8   andi 7; bnez                R1 / R2; trap_align8
     GS    0x83cbc  PTR_NOT  not hp; bltu ~hp, 8i        R3; trap_ptr_wrap_not
     GS    0x83cfc  DECW     addiw -1; bge               R4; trap_decw
     GS    0x83d20  NULL_BEQ snez; seqz; beq             R1 / R2; trap_null_beq
     GS    0x83d34  PTR_SOVF sltu; slti; xor; xori 1; beqz   R5; trap_ptr_sovf + trap_U_sltu_ge
     GS    0x83d38  NONNULL  beqz hp                     R1; trap_nonnull
     GS    0x83d40  ALIGN8   andi 7; bnez                R1 / R2; trap_align8
     GS    0x83d5c  PTR_NOT  not hp; bltu ~hp, 8i        R3; trap_ptr_wrap_not
     GS    0x83d68  ALIGN8   add; andi 7; bnez           R1 / R2; trap_align8
     END   0x83eb0  NONNULL  beqz errno                  R1; trap_nonnull
     END   0x83eb8  ALIGN4   andi 3; bnez errno          R1 (al2 2, HERRAL); trap_align4
   REST (0x83e34 .. 0x83e90) has no trap.  The three ALIGN4 sites are why HERRAL (errno mod 4 = 0) is a
   Section hypothesis: errno is tp - 164 (HERRNO) and the pin's thread pointer decides it.
   (* The table lists the UBSan trap sites only (49, objdump-exact). ASan shadow side-exits (65 in drain; 39 sites with a decider in the four stages then open) are in the census D1-TRAP-CENSUS.md (sha256 f32bad2bbf4c; internal record). *)

   FINDING 1 (closed): B's prologue traps at 0x832b4-0x832b8 unless SA mod 8 = 0, and the kit's dr_spec on
   67c07b3d6e6 did not state it (its table premises allow any address of the 896-byte block; the kit's own
   alignment report align-B.txt (sha256 e030624aa48b; internal record) found the same gap).  The kit's dr_spec now carries
   `SA mod 8 = 0` (W7's A text, a working branch ccd62d4c6f6 lib/A/W_contract.v:868, twinned to B by
   mkbkit), so DBASE's `dxSA cx mod 8 = 0` comes from dr_spec's own premise.  The corollary a real caller uses
   to supply it (for a table block G of the allocator and any slot index i, (G + AENT * i) mod 8 = 0, from
   AR_blocks_law's G mod 16 = 0) is dr_sa_align_slot in lib/B/W_drain_sa.v (W6 72eb36c9efa).
   FINDING 2 (closed): the five shapes of drain that a Theorem Labs lane's 32-lemma W_traps.v did not cover (ALIGN4,
   PTR_CONST, PTR_EQK, PTR_EQK_FT, PTR_NOT) are all in the published 48-lemma kit
   (a working branch 6c73ae99620) as trap_align4, trap_ptr_wrap_k, trap_br_eq,
   trap_seat (trap_br_eq ..) and trap_ptr_wrap_not, so drain needs no new trap lemma.
   FINDING 3 (none of the above): B's drain CALLS list_drop (0x83914), so the DROP stage calls it through the proved
   pb_list_drop_ro_c (lib/B/W_list_drop.v) at the pending list's 16-byte header cell (&h->pending) (NOT at G_DR: gx_rt excludes
   errno's bytes), with AFREE (the _c rule) and HCTX_ld, where lib/A's takes AFREE and AMEMMOVE for the inlined
   body.  LDROP_STK = 64 + ASTACK
   (B's list_drop frame is 64 bytes) is under DRAIN_STK - DRAIN_FRAME = SL_STK = 144 + ASTACK, so the stack
   budget of the generated DRAIN_STK covers the call.

   KIT.  Written against the B kit head a working branch 416c8ab2a27 (generated from the integrated
   lib/A) and the final trap kit a working branch 6c73ae99620.  On that kit head DRAIN_FRAME = 352
   and DRAIN_STK = DRAIN_FRAME + SL_STK = 352 + (144 + ASTACK) (W_contract.v:941-942), which still dominates B's
   call graph of drain (its deepest callee is send_line, frame 144; list_drop's LDROP_STK = 64 + ASTACK is under
   it).  Every argument trap of the kit's contracts has its premise there EXCEPT dr_spec's SA (FINDING 1).
   aentry_okx below is that W_rep.v's aentry_ok with `re_used e <= APARTIAL` and `~ In 0 (re_U e)` relaxed to
   `re_used e <= re_cap e` (between the memcpy and the move-down the buffer does hold NULs), so it follows the
   ruling-(A) text with no key_slack.  The kit's A_lit_gesture / A_lit_begin / A_lit_end (W_contract.v:1651-
   1547) are A_OBJ 18 / 20 / 21, which is what HLIT5 / HLIT6 / HLIT7 below name.  The callee contracts' caller
   obligations at drain's call sites, and where this interface gives them:
     sl_spec  `forall a, line <= a < line + |Bl| -> ~ inG G_SL a` (W_contract.v:931), owed by LINEA at the
              send_line call 0x839f0: the line lies in the relay's buffer (dinband / aentry_okx at DLL) and HRGD
              keeps G_SL's image cells apart from it;
     lp_spec  `LA mod 8 = 0` (W_contract.v:394), owed by FEED at the list_push call 0x837a4 with
              LA = dHA cx + 64 (DRB's 160(sp)): HGSB gives rg_s RG mod 8 = 0 and ASRC = 96, so it holds for
              every slot; lp_post's errno-view conjunct is what lets FEED re-establish DMEM's aout_at after the
              call (no statement here changes for it);
     ldrop_spec `LA mod 8 = 0`, `azs B LA 16`, `LA` in G (W_contract.v:722), owed by DROP at 0x83914 with
              LA = dHA cx + 16: HGSB, HGSZ and G_DR's (rg_s RG, 4 * ASRC) give them.

   dlit_at (the three literals) is A's current form on a working branch 095dd035a61 verbatim, re-indexed
   for B: the bytes, in_rom, and `ashp B (VAL (A_OBJ i)) (|l|)` (lib/B/W_shadow_pin.v:80).  The older
   `azs B .. /\ shadow_hull_vis ..` pair it had is the form a Theorem Labs lane measured FALSE for ASan globals (their
   shadow cells are pinned, not zero), so it is gone from both images; ashp is the shared replacement and is
   derived from AR, never assumed.

   STATEMENT GAPS of lib/A that this file keeps (they are properties of the model, not of the image): *_concl
   for dr_all / dr_outer, the ds_eintr guard on dr_top's EINTR continuation, and k < dnum s1 at DRB. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Definition A_drain : Z := AF_fr_drain.
Definition A_drainP : Z := BASE + A_drain.
Definition A_dr_top : Z := AF_fr_drain + 0x148.
Definition A_dr_feed : Z := AF_fr_drain + 0x484.
Definition A_dr_fed : Z := AF_fr_drain + 0x628.
Definition A_dr_line : Z := AF_fr_drain + 0x724.
Definition A_dr_next : Z := AF_fr_drain + 0x75c.
Definition A_dr_seen : Z := AF_fr_drain + 0x82c.
Definition A_dr_rest : Z := AF_fr_drain + 0xbbc.
Definition A_dr_end : Z := AF_fr_drain + 0xc1c.
Definition A_dr_eof : Z := AF_fr_drain + 0xd30.
Definition A_dr_epi : Z := AF_fr_drain + 0xd50.

Definition DR_SAVED : list (bv 5) :=
[27%bv; 26%bv; 25%bv; 24%bv; 23%bv; 22%bv; 21%bv; 20%bv; 19%bv; 18%bv; 9%bv; 8%bv; 1%bv].
Definition DR_SAVE_OFF : Z := 248.
Definition DR_SCAN_END : Z := 384.
Definition DCEIL : Z := 0x7fffff800000.
Definition IMG_TOP : Z := 0x5fc000.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Definition dlit_at (i : nat) (l : list Z) : Prop :=
(forall k, (k < length l)%nat ->
   seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ i) + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
(forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + Z.of_nat (length l) -> YG0d.in_rom SEGS x) /\
ashp B (VAL (A_OBJ i)) (Z.of_nat (length l)).
Hypothesis HLIT5 : dlit_at 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

Lemma amem_range_of_in_app : forall a n, in_app a n -> amem_range a n.
Proof.
intros a n (H0 & [H | [H1 H2]]); pose proof (@ASAN_CEIL_range rc) as (Hc & _);
unfold amem_range, in_app, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma amem_range_near_block : forall ly S W mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros ly S W mem md q n a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.
Lemma amem_range_img : forall a n, 0x10000 <= a -> 0 <= n -> a + n <= IMG_TOP -> amem_range a n.
Proof. intros a n H1 H2 H3. unfold amem_range, kLowMemEnd, IMG_TOP in *. left. lia. Qed.

Definition dinband (x n : Z) : Prop := 4096 <= x /\ x + n <= DCEIL /\ x mod 8 = 0.

Definition aentry_okx (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (e : rentry) : Prop :=
(re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
0 <= re_fd e < 2 ^ 31 /\
(re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
Z.of_nat (length (re_U e)) = re_used e /\ re_used e <= re_cap e /\
((re_cap e = 0 /\ re_buf e = 0 /\ re_used e = 0) \/
 (0 < re_cap e /\ In (re_buf e, re_cap e) (ablocks B ly S) /\
  Z.of_nat (length (re_junk e)) = re_cap e - re_used e /\
  garr8 SEGS (arm W mem) (re_buf e) (bzs (re_U e ++ re_junk e)))) /\
re_nheld e < 2 ^ 26 /\
((re_hp e = 0 /\ re_keys e = []) \/
 (re_hp e <> 0 /\ In (re_hp e, re_kh e) (ablocks B ly S) /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e /\
  garr8 SEGS (arm W mem) (re_hp e) (bzs (key_ptrs (re_keys e))))) /\
NoDup (map key_addr (re_keys e)) /\
NoDup (map key_text (re_keys e)) /\
Forall (fun k =>
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (ablocks B ly S) /\
  garr8 SEGS (arm W mem) (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= APARTIAL) (re_keys e).

Lemma aentry_okx_of_ok : forall ly S W mem e,
aentry_ok B ly S W mem e -> aentry_okx ly S W mem e.
Proof.
intros ly S W mem e H. unfold aentry_okx.
assert (HC : re_used e <= re_cap e).
{ destruct H as (_ & _ & _ & _ & _ & H6 & _ & H8 & _ & H10 & _).
  destruct H10 as [(A1 & A2 & A3)|(A1 & _)]; unfold APARTIAL in *; lia. }
unfold aentry_ok in H. tauto.
Qed.

Lemma aentry_ok_of_okx : forall ly S W mem e,
aentry_okx ly S W mem e -> ~ In (Z_to_bv 8 0) (re_U e) -> re_used e <= APARTIAL ->
aentry_ok B ly S W mem e.
Proof.
intros ly S W mem e H HN HU. unfold aentry_ok. unfold aentry_okx in H. tauto.
Qed.

Record dcx : Type := mkDcx {
  dxregs : bvmap 5 word;
  dxly : alayout; dxS : astate; dxW : world SEGS; dxmem : word -> option byte; dxmd : Model;
  dxch : list (Z * Z * Z);
  dxG : Z; dxSA : Z; dxe : rentry; dxj : nat; dxh : hsrc;
  dxc : ctl; dxO : list byte; dxmx : Z; dxno : Z; dxcap : Z; dxout : Z;
  dxrest : list (Z * Z) }.

Definition dHA (cx : dcx) : Z := rg_s RG + ASRC * Z.of_nat (dxj cx).
Definition dsp0 (cx : dcx) : Z := spZ (dxregs cx).
Definition dSTR (cx : dcx) : lstate := hs_state (dxh cx).
Definition dPS (cx : dcx) : list Z := bzs (pending_stream (dxh cx)).
Definition dlive (cx : dcx) : bool := dr_live (dxc cx) (dxh cx).
Definition dFP (cx : dcx) : list (Z * Z) := dr_fp (dxSA cx) (dxe cx) (dxh cx) (dxcap cx) (dxout cx).
Definition dfin (cx : dcx) : drain_b_c.dstate :=
dr_fin (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition dtrc (cx : dcx) : dtrace := dr_tr (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition dcost (cx : dcx) : Z := dr_cost MT (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition ds0 (cx : dcx) : drain_b_c.dstate :=
drain_b_c.drain_init (dxno cx) (dxcap cx) (dxe cx) (dxh cx).
Definition dPOST (cx : dcx) : world SEGS -> config -> Prop :=
dr_post B MT RG (dxregs cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
  (dxSA cx) (dHA cx) (dxe cx) (dxh cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx) (dxout cx).

Definition DBASE (cx : dcx) : Prop :=
afn_pre SEGS B DRAIN_STK (dxly cx) (dxS cx) (dxW cx) (dxregs cx) (dxmem cx) (dxmd cx) (dxch cx) /\
getr (dxregs cx) 10 = w64 (dxSA cx) /\
In (dxG cx, ATABLE) (ablocks B (dxly cx) (dxS cx)) /\
dxG cx <= dxSA cx /\ dxSA cx + AENT <= dxG cx + ATABLE /\
dxSA cx mod 8 = 0 /\
garr8 SEGS (arm (dxW cx) (dxmem cx)) (dxSA cx) (bzs (entry_bytes (dxe cx))) /\
awr (dxW cx) (dxmem cx) (dxSA cx) AENT /\
aentry_ok B (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxe cx) /\
(dxj cx < 4)%nat /\
asrc_at B (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dHA cx) (dxh cx) /\
aothers_at RG (dxW cx) (dxmem cx) (dxj cx) (re_fd (dxe cx)) /\
hs_fd (dxh cx) = re_fd (dxe cx) /\ re_skip (dxe cx) = hs_overlong (dxh cx) /\
(re_skip (dxe cx) = 0 -> bzs (re_U (dxe cx)) = bzs (hs_W (dxh cx))) /\
aout_at B RG (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx) (dxout cx) /\
rom_view SEGS (dxW cx) (dxmem cx) /\
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) /\
Z.of_nat (length (pending_stream (dxh cx))) < 2 ^ 26 /\
hl_cap (hs_expected (dxh cx)) < 2 ^ 26 /\
re_nheld (dxe cx) + Z.of_nat (length (pending_stream (dxh cx))) < 2 ^ 26 /\
tr_max (dtrc cx) < MMAX /\
blocks_bytes (dxS cx) + tr_peak (dtrc cx) <= LIVE_MAX /\
mo_ok MT (dxS cx) (dcost cx).

Definition dlater (cx : dcx) (s1 : drain_b_c.dstate) (jb : nat) (a : drain_b_c.dadr) (tl : dtrace) : Prop :=
exists fuel : nat,
(dneed s1 <= fuel)%nat /\ dwf s1 /\
fst (drain_b_c.drain_run fuel (dlive cx) (dxmx cx) s1 jb a) = tl /\
fst (snd (drain_b_c.drain_run fuel (dlive cx) (dxmx cx) s1 jb a)) = dfin cx.

(* The meter: `spent` is what the walk has charged so far, tl what is still to come.  dr_spec's three resource
   premises, carried forward: the cost fits in dr_cost, the live bytes plus the peak of the requests still to come
   (tr_peak, C3) in LIVE_MAX, every request under MMAX. *)
Definition dbud (cx : dcx) (S1 : astate) (spent : Z) (tl : dtrace) : Prop :=
mo_le MT (dxS cx) S1 spent /\ 0 <= spent /\
spent + tr_cost MT tl <= dcost cx /\
blocks_bytes S1 + tr_peak tl <= LIVE_MAX /\
tr_max tl < MMAX.

Definition danext (a : drain_b_c.dadr) (r : dadrF * dadrF * list dadrF) : drain_b_c.dadr :=
drain_b_c.DA (fst (fst r)) (drain_b_c.da_buf a) (snd (fst r)) (snd r) (drain_b_c.da_pend a)
  (drain_b_c.da_ev a) (drain_b_c.da_erecs a).
Definition dapush (a : drain_b_c.dadr) (vr : dadrF * list dadrF) : drain_b_c.dadr :=
drain_b_c.DA (drain_b_c.da_out a) (drain_b_c.da_buf a) (drain_b_c.da_hp a) (drain_b_c.da_keys a)
  (drain_b_c.da_pend a) (fst vr) (snd vr).

Definition dlfut (cx : dcx) (s2 : drain_b_c.dstate) (ab : drain_b_c.dadr) (no oc : Z) (H : list (list Z)) (ka : Z)
(rl : list (list Z)) (jb : nat) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) : Prop :=
let lr := drain_b_c.lines_run (dlive cx) (dxmx cx) no oc H ka rl jb o ha ks in
exists tl2 : dtrace,
dlater cx s2 (jb + dnret (fst (fst lr)))%nat (danext ab (snd lr)) tl2 /\
tl = fst (fst lr) ++ tl2.

Definition dsfut (cx : dcx) (s2 : drain_b_c.dstate) (ab : drain_b_c.dadr) (H : list (list Z)) (ka : Z)
(l : list Z) (no oc : Z) (rl : list (list Z)) (jb : nat) (o ha : dadrF) (ks : list dadrF) (tl : dtrace) : Prop :=
let sn := drain_b_c.seen_tr H ka l jb ha ks in
exists tl2 : dtrace,
dlfut cx s2 ab no oc (seen_arr H l) (seen_ka H ka l) rl (jb + dnret (fst (fst sn)))%nat o
  (fst (snd sn)) (snd (snd sn)) tl2 /\
tl = fst (fst sn) ++ tl2.

Definition drfut (cx : dcx) (s1 : drain_b_c.dstate) (jb : nat) (a : drain_b_c.dadr) (tl : dtrace) : Prop :=
exists tl2 : dtrace,
dlfut cx (dnext (dlive cx) (dxmx cx) s1)
  (if dwhole s1 then drain_b_c.DA (drain_b_c.da_out a) (drain_b_c.da_buf a) (drain_b_c.da_hp a)
     (drain_b_c.da_keys a) (skipn 1 (drain_b_c.da_pend a)) (drain_b_c.da_ev a) (drain_b_c.da_erecs a) else a)
  (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1) (drain_b_c.ds_ka s1) (drl s1)
  (jb + dnret (ddrop s1 a))%nat (drain_b_c.da_out a) (drain_b_c.da_hp a) (drain_b_c.da_keys a) tl2 /\
tl = ddrop s1 a ++ tl2.

Definition dpfut (cx : dcx) (s1 : drain_b_c.dstate) (k : nat) (jb : nat) (a : drain_b_c.dadr)
(v : dadrF) (rs : list dadrF) (tl : dtrace) : Prop :=
let done := lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)) in
let pu := drain_b_c.pushes_run (drain_b_c.ds_en s1 + Z.of_nat (length done))
            (pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) done)
            (lines (feed (drain_b_c.ds_ref s1) (firstn k (ddata s1))) (skipn k (ddata s1))) jb v rs in
exists tl2 : dtrace,
drfut cx s1 (jb + dnret (fst (fst pu)))%nat (dapush a (snd pu)) tl2 /\
tl = fst (fst pu) ++ tl2.

Definition dctl (cx : dcx) (tot ev : Z) : ctl :=
let off := send_line_c.send_off (ct_cl (dxc cx)) (ct_br (dxc cx)) tot in
CTL (ct_cl (dxc cx)) (if off then ct_br (dxc cx) else ct_dd (dxc cx)) (ct_dd (dxc cx))
  (if off then ct_ei (dxc cx) else 0) ev.

Definition dr_saved (W1 : world SEGS) (m1 : word -> option byte) (spX : Z) (regsE : bvmap 5 word) : Prop :=
forall i, (i < 13)%nat ->
val_mem SEGS (arm W1 m1) (spX + DR_SAVE_OFF + 8 * Z.of_nat i) 8 (bv_unsigned (getr regsE (nth i DR_SAVED 0%bv))).

Definition dr_frame (cx : dcx) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
let spX := dsp0 cx - DRAIN_FRAME in
let SA := dxSA cx in
let GS := rg_s RG in
val_mem SEGS (arm W1 m1) (spX + 8) 8 (SA mod 8 + 3) /\
val_mem SEGS (arm W1 m1) (spX + 32) 8 (SA + 48) /\
val_mem SEGS (arm W1 m1) (spX + 40) 8 ((GS + 8) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 48) 8 ((GS + 56) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 56) 8 ((GS + 48) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 64) 8 ((GS + 40) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 72) 8 ((GS + 32) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 80) 8 ((GS + 16) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 88) 8 (SA + 40) /\
val_mem SEGS (arm W1 m1) (spX + 104) 8 ((GS + 24) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 120) 8 GS /\
val_mem SEGS (arm W1 m1) (spX + 128) 8 (SA + 16) /\
val_mem SEGS (arm W1 m1) (spX + 136) 8 (SA + 24) /\
val_mem SEGS (arm W1 m1) (spX + 144) 8 SA /\
val_mem SEGS (arm W1 m1) (spX + 152) 8 ((GS + 12) / 8) /\
val_mem SEGS (arm W1 m1) (spX + 176) 8 (SA + 32) /\
val_mem SEGS (arm W1 m1) (spX + 184) 8 6001 /\
val_mem SEGS (arm W1 m1) (spX + 200) 8 (shadow_addr SA) /\
val_mem SEGS (arm W1 m1) (spX + 208) 8 (SA + 8) /\
val_mem SEGS (arm W1 m1) (spX + 216) 8 (shadow_addr (SA + 32)) /\
val_mem SEGS (arm W1 m1) (spX + 224) 8 (shadow_addr (SA + 16)) /\
val_mem SEGS (arm W1 m1) (spX + 232) 8 (shadow_addr (SA + 24)) /\
val_mem SEGS (arm W1 m1) (spX + 240) 8 SHADOW_OFF /\
dr_saved W1 m1 spX (dxregs cx).

Definition DMEM (cx : dcx) (ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte)
(md1 : Model) (k1 : Z) (e1 : rentry) (h1 : hsrc) (s1 : drain_b_c.dstate) (out1 ev1 : Z)
(sent : list (list Z)) (LB1 : list byte) : Prop :=
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (dxW cx) (dxmem cx) W1 m1 /\ frames S1 = frames (dxS cx) /\
dr_frame cx W1 m1 /\
garr8 SEGS (arm W1 m1) (dxSA cx) (bzs (entry_bytes e1)) /\ awr W1 m1 (dxSA cx) AENT /\
aentry_okx ly1 S1 W1 m1 e1 /\
asrc_at B ly1 S1 W1 m1 (dHA cx) h1 /\
aothers_at RG W1 m1 (dxj cx) (re_fd (dxe cx)) /\
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA cx <= x < dHA cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m1 x) /\
aout_at B RG ly1 S1 W1 m1 (dctl cx (Z.of_nat (length (with_nul sent))) ev1)
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 /\
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) /\
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).

Definition DLINK (s1 : drain_b_c.dstate) (e1 : rentry) (h1 : hsrc) : Prop :=
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = (if drain_b_c.ds_eintr s1 then 1 else 0) /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\ hs_state h1 = drain_b_c.ds_ref s1 /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 /\ hl_cap (hs_expected h1) = drain_b_c.ds_ecap s1 /\ dwf s1.

Definition DSAME (cx : dcx) (e1 : rentry) (h1 : hsrc) : Prop :=
re_fd e1 = re_fd (dxe cx) /\ re_eof e1 = re_eof (dxe cx) /\
hs_fd h1 = hs_fd (dxh cx) /\ hs_open h1 = hs_open (dxh cx) /\ hs_closed h1 = hs_closed (dxh cx) /\
hl_v (hs_pending h1) = hl_v (hs_pending (dxh cx)) /\
hl_cap (hs_pending h1) = hl_cap (hs_pending (dxh cx)) /\
hs_partial h1 = hs_partial (dxh cx) /\ hs_held h1 = hs_held (dxh cx) /\
((re_hp e1 = re_hp (dxe cx) /\ re_kh e1 = re_kh (dxe cx)) \/ re_kh e1 <= 2 ^ 30).

Definition DHIST (cx : dcx) (s1 : drain_b_c.dstate) (D F : list Z) (sent kl : list (list Z)) (h1 : hsrc)
(LB1 : list byte) (nk : Z) : Prop :=
dPS cx = D ++ pstream s1 /\ drain_b_c.ds_ref s1 = feed (dSTR cx) D /\
map snd (hl_recs (hs_expected h1)) =
  map snd (hl_recs (hs_expected (dxh cx))) ++ map (map (Z_to_bv 8)) (lines (dSTR cx) F) /\
firstn (length (hl_recs (hs_expected (dxh cx)))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected (dxh cx)) /\
hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected (dxh cx))) (2 * hl_n (hs_expected h1))) /\
drain_b_c.ds_no s1 = dxno cx + Z.of_nat (length (with_nul sent)) /\
bzs LB1 = with_nul sent /\
NoDup (drain_b_c.ds_H s1) /\
same_set (drain_b_c.ds_H s1) (upds (drain_b_c.keys_texts (re_keys (dxe cx))) kl) /\
Z.of_nat (length (drain_b_c.ds_H s1)) + nk + Z.of_nat (length (pstream s1)) < 2 ^ 26 /\
drain_b_c.ds_en s1 + Z.of_nat (length (pstream s1)) < 2 ^ 27.

Definition dW (s1 : drain_b_c.dstate) : list Z := drain_b_c.ds_u s1 ++ ddata s1.

Definition dvirt (cx : dcx) (s1 : drain_b_c.dstate) (sk : bool) (H : list (list Z)) (ka no oc : Z)
: drain_b_c.dstate :=
let s2 := dnext (dlive cx) (dxmx cx) s1 in
drain_b_c.DS (drain_b_c.ds_cap s1) (dW s1) sk H ka false
  (drain_b_c.ds_pend s2) (drain_b_c.ds_off s2) (drain_b_c.ds_ref s2) (drain_b_c.ds_en s2)
  (drain_b_c.ds_ecap s2) no oc.

Definition drlp (s1 : drain_b_c.dstate) (p : nat) : list (list Z) :=
snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1))).
Definition dskp (s1 : drain_b_c.dstate) (p : nat) : bool :=
if Nat.eqb p 0 then drain_b_c.ds_skip s1 else false.
Definition drlq (s1 : drain_b_c.dstate) (p : nat) : list (list Z) :=
snd (scan (dskp s1 p) [] (skipn p (dW s1))).
Definition dlrun (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : Z * list (list Z) * Z :=
lrun (dlive cx) (dxmx cx) (drain_b_c.ds_no s1) (drain_b_c.ds_ocap s1) (drain_b_c.ds_H s1)
  (drain_b_c.ds_ka s1) (drlp s1 p).
Definition dlno (s1 : drain_b_c.dstate) (p : nat) : Z :=
drain_b_c.ds_no s1 + Z.of_nat (length (with_nul (drlp s1 p))).
Definition dloc (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : Z := fst (fst (dlrun cx s1 p)).
Definition dlH (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : list (list Z) := snd (fst (dlrun cx s1 p)).
Definition dlka (cx : dcx) (s1 : drain_b_c.dstate) (p : nat) : Z := snd (dlrun cx s1 p).
Definition dbound (s1 : drain_b_c.dstate) (p : nat) : Prop :=
(p <= length (dW s1))%nat /\ (p = 0%nat \/ nth_error (dW s1) (p - 1) = Some 0).
Definition dline (s1 : drain_b_c.dstate) (p q : nat) : list Z := firstn (q - p) (skipn p (dW s1)).

Definition RSTART (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) : Prop :=
drain_b_c.ds_ref s1 = feed (dSTR cx) D /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
4096 <= drain_b_c.ds_cap s1 - ulen s1 /\ dwf s1 /\ dstrict s1 /\
drain_b_c.ds_eintr s1 = false /\ drain_b_c.ds_pend s1 <> [].

Definition LCORE (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (sent kl : list (list Z))
(H : list (list Z)) (ka no oc nk : Z) (sk : bool)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
let sv := dvirt cx s1 sk H ka no oc in
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 sv out1 ev1 sent LB1 /\
DLINK sv e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sv (D ++ ddata s1) (D ++ ddata s1) sent kl h1 LB1 nk /\
RSTART cx s1 D /\ dbud cx S1 spent tl.

Definition dregs_top (cx : dcx) (regs1 : bvmap 5 word) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 21 = w64 (dxSA cx) /\ getr regs1 24 = w64 (dxSA cx + 8) /\
getr regs1 20 = w64 (dxSA cx + 16) /\ getr regs1 22 = w64 (dxSA cx + 24) /\
getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 26 = w64 DR_SCAN_END.

Definition DI (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_top) regs1 m1 md1 /\
dregs_top cx regs1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
(re_cap e1 <> 0 -> dinband (re_buf e1) (re_cap e1)) /\
DLINK s1 e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
dlater cx s1 jb a tl /\ dbud cx S1 spent tl.

Definition DEND (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 21 = w64 (dxSA cx) /\ getr regs1 23 = w64 (dHA cx) /\
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
dr_frame cx W1 m1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK s1 e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
drain_b_c.ds_pend s1 = [] /\ drain_b_c.ds_eintr s1 = false /\ 4096 <= drain_b_c.ds_cap s1 - ulen s1 /\
dlater cx s1 jb a tl /\ dbud cx S1 spent tl.

Definition DRB (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a v rs tl p0 r0 rs0,
c1 = cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 23 = w64 (dHA cx) /\
getr regs1 15 = w64 (dnum s1) /\ getr regs1 21 = w64 (dnum s1 - Z.of_nat k) /\
getr regs1 27 = w64 p0 /\ getr regs1 19 = w64 (p0 + Z.of_nat k) /\ getr regs1 24 = w64 (p0 + Z.of_nat k) /\
getr regs1 6 = w64 (fst r0) /\ getr regs1 20 = w64 1 /\
getr regs1 16 = w64 (shadow_addr (dHA cx + 40)) /\ getr regs1 17 = w64 (shadow_addr (dHA cx + 48)) /\
getr regs1 22 = w64 (shadow_addr (dHA cx + 56)) /\
dr_frame cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (dHA cx + 56) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 (dHA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 160) 8 (dHA cx + 64) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (shadow_addr (dHA cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 (shadow_addr (dHA cx + 32)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (dnum s1) /\
hl_recs (hs_pending h1) = r0 :: rs0 /\ p0 = fst r0 + drain_b_c.ds_off s1 /\
dinband (fst r0) (Z.of_nat (length (snd r0)) + 1) /\ fst r0 <= p0 /\
(Z.of_nat k < dnum s1)%Z /\ 0 < dnum s1 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (firstn k (ddata s1)) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)))) /\
hl_cap (hs_expected h1) =
  pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) /\
DHIST cx s1 D (D ++ firstn k (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
dpfut cx s1 k jb a v rs tl /\ dbud cx S1 spent tl.

Definition DE (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_fed) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 23 = w64 (dHA cx) /\
getr regs1 15 = w64 (dnum s1) /\
dr_frame cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 (dHA cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (shadow_addr (dHA cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 (shadow_addr (dHA cx + 32)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (dnum s1) /\
0 < dnum s1 /\ bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM cx ly1 S1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) /\
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) /\
DHIST cx s1 D (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
drfut cx s1 jb a tl /\ dbud cx S1 spent tl.

Definition dregs_line (cx : dcx) (regs1 : bvmap 5 word) (W1 : world SEGS) (m1 : word -> option byte) : Prop :=
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 21 = w64 (dxSA cx) /\ getr regs1 20 = w64 (dxSA cx + 16) /\
getr regs1 22 = w64 (dxSA cx + 24) /\ getr regs1 27 = w64 (dxSA cx + 32) /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\
dr_frame cx W1 m1.

Definition DLC (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE cx s1 D (lines (dSTR cx) D ++ drlp s1 p) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p) (Z.of_nat (length (drlq s1 p))) (dskp s1 p)
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

Definition DLL (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_line) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 26 = w64 DR_SCAN_END /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (re_buf e1) /\
getr regs1 25 = w64 (Z.of_nat (length (dW s1) - p)) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
DLC cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

Definition DLN (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_next) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat p - 1) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (0 < p)%nat /\
DLC cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

Definition DLR (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_rest) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 26 = w64 DR_SCAN_END /\
getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (Z.of_nat (length (dW s1) - p)) /\
getr regs1 19 = w64 (re_buf e1) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) /\
DLC cx s1 D p ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

Definition DGS (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_seen) regs1 m1 md1 /\
dregs_line cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
getr regs1 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) /\
getr regs1 25 = w64 bg /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat /\
LCORE cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl.

Definition dr_pro_stmt : Prop :=
forall cx,
DBASE cx ->
(forall W2 c2, DI cx (ds0 cx) [] W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS (dxW cx) (cfg_at SEGS A_drainP (dxregs cx) (dxmem cx) (dxmd cx)) (dPOST cx).

Definition dr_top_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DI cx s1 D W1 c1 ->
(drain_b_c.ds_eintr s1 = true -> forall W2 c2, DI cx (dclr (dgrow s1)) D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DEND cx (dgrow s1) D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DRB cx (dgrow s1) D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_feed_stmt : Prop :=
forall cx s1 D k W1 c1,
DBASE cx -> DRB cx s1 D k W1 c1 ->
(forall W2 c2, DRB cx s1 D (S k) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DE cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_drop_stmt : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DE cx s1 D W1 c1 ->
(forall q W2 c2, DLL cx s1 D 0 q W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DLR cx s1 D 0 W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_linea_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE cx -> DLL cx s1 D p q W1 c1 ->
(forall W2 c2, DLN cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DGS cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_gs_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE cx -> DGS cx s1 D p q W1 c1 ->
(forall W2 c2, DLN cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_next_stmt : Prop :=
forall cx s1 D p W1 c1,
DBASE cx -> DLN cx s1 D p W1 c1 ->
(forall q W2 c2, DLL cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
(forall W2 c2, DLR cx s1 D p W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_rest_stmt : Prop :=
forall cx s1 D p W1 c1,
DBASE cx -> DLR cx s1 D p W1 c1 ->
(forall W2 c2, DI cx (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).

Definition dr_epi_stmt : Prop :=
forall cx ly1 S1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
YK0s.ret_ok (getr (dxregs cx) 1) ->
dr_saved W1 m1 (dsp0 cx - DRAIN_FRAME) (dxregs cx) ->
(forall regs' m' md', aregs_preserved (dxregs cx) regs' ->
   (forall x, arm W1 m' x = arm W1 m1 x) ->
   @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m' md' k1 ->
   Q W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md')) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regs1 m1 md1) Q.

Definition dr_end_concl : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DEND cx s1 D W1 c1 ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_end_stmt : Prop := dr_epi_stmt -> dr_end_concl.

Definition dr_feeds_concl : Prop :=
forall cx s1 D k W1 c1,
DBASE cx -> DRB cx s1 D k W1 c1 ->
(forall W2 c2, DE cx s1 D W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_feeds_stmt : Prop := dr_feed_stmt -> dr_feeds_concl.

Definition dr_lines_concl : Prop :=
forall cx s1 D W1 c1,
DBASE cx ->
((exists p q, DLL cx s1 D p q W1 c1) \/ (exists p, DLN cx s1 D p W1 c1) \/ (exists p, DLR cx s1 D p W1 c1)) ->
(forall W2 c2, DI cx (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 -> SRr SEGS W2 c2 (dPOST cx)) ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_lines_stmt : Prop :=
dr_linea_stmt -> dr_gs_stmt -> dr_next_stmt -> dr_rest_stmt -> dr_lines_concl.

Definition dr_outer_concl : Prop :=
forall cx s1 D W1 c1,
DBASE cx -> DI cx s1 D W1 c1 ->
SRr SEGS W1 c1 (dPOST cx).
Definition dr_outer_stmt : Prop :=
dr_top_stmt -> dr_feeds_concl -> dr_drop_stmt -> dr_lines_concl -> dr_end_concl -> dr_outer_concl.

Definition dr_all_stmt : Prop :=
dr_pro_stmt -> dr_outer_concl -> dr_spec B MT MMAX RG A_drainP.

End c.
End b.
End a.
