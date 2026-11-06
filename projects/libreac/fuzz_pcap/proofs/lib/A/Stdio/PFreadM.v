(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the contracts of musl's fread and of the two read-path helpers it calls,
   __toread and the fmemopen cookie read mread, inside libreac/fuzz_pcap (libreac v1.9.0, ASan
   build), stated in cgif_file_fuzzer's vocabulary.

   STATEMENT ONLY. This file holds Definitions and nothing else: no lemma, no proof, no Admitted.

   THE FUNCTIONS, read off fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record) (the
   unstripped twin fuzz_pcap.asan (sha256 36da3052c383) of the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0)):
     fread    0x8ee5c  lines 99500-99579, frame 64
     __toread 0x8e638  lines 98961-98998, frame 16
     mread    0x8ea40  lines 99225-99278, frame 48
   The entry addresses are parameters of the contracts (pc), so the asan-ubsan copy is the same
   statement at its own addresses.

   At ossv/recipes 25e3d17bdb50 (2026-10-29), NO DONOR existed for these functions (rule 24: a Theorem Labs lane's runtime-donors.md (sha256 77e6fad19fb7; internal record) rows 3-4 and section
   6). The step content comes from this worker's own plain proofs lib/Prog/fread_c.v,
   lib/Prog/__toread_c.v, lib/Prog/mread_c.v and the layout model lib/Prog/StdioModel.v; the names
   come from the cgif donor listed at the end.

   WHAT THE STATEMENTS SAY.
   rfread_contract: called inside its caller's journal (THE CALLER-JOURNAL FORM below) with
     a0 = d, a1 = 1, a2 = nm (0 <= nm <= 2^26), a3 = f, where f is a live 1304-byte block carrying a
     read stream on (b, C) at caller position p, b is a live block off the callee's stack window,
     the caller may write every byte of the FILE block, and d .. d+nm is an addressable destination
     in a side-stack frame, on the stack or inside a live block, which the caller may write and
     which is disjoint from the FILE, from b and from the callee's stack window: fread returns
     j = min(nm, |C| - p), the destination holds C[p .. p+j), the stream is at position p + j, its
     orientation word +136 is -1, the layout and the allocator state are as they were, the
     caller's journal is extended with no event, the fd table and the file system are as they
     were, and every byte outside the callee's stack window, the FILE block and d .. d+nm is as it
     was at the call, the shadow band included (THE POSTS below). When nm = 0 every byte of the
     FILE block except the orientation word is as it was.
   rtoread_contract: on an unbuffered stream with flags fl whose data buffer b is a live block off
     the callee's stack window, __toread returns -1 if fl = 24 (EOF) and 0 if fl = 8, leaves the
     stream, its position and its flags as they were, sets the orientation word to -1, puts
     rpos = rend = f + 1304 and leaves the shadow band as it was. Its post is apost_base over the
     FILE block alone (THE FOOTPRINT OF __toread below).
   rmread_contract: in the caller-journal form, on an unbuffered stream at position p with flags 8
     and with fread's premises on b, on the FILE block and on the destination, mread(f, d, l) for
     1 <= l <= 2^26 copies j = min(l, |C| - p) bytes C[p .. p+j) to d and returns j, refills the
     window with the next r = min(|C| - p - j, 1024) bytes at f + 280, moves the cookie position to
     p + j + r, leaves the stream at caller position p + j, sets the EOF flag exactly when
     l > |C| - p, keeps the orientation word, and keeps everything else as fread's post does.

   mread MOVES THE CALLER POSITION. Its first memcpy (0x8eaa4) copies j bytes from c->buf + c->pos
   to its argument a1, which is fread's destination, and adds j to c->pos (0x8eab0) BEFORE it fills
   the window (0x8eac4-0x8eaf0). Those j bytes are delivered to the caller, so the caller position
   moves from p to p + j; only the r window bytes are read ahead (cpos' - (p + j) = r). This
   composes with a Theorem Labs lane's amseek_rewind_spec (PFmopsM.v at 10eaf4540eb) at its p := p + j: the
   rewind by rend - rpos = r returns the cookie to p + j.

   fread WITH nm = 0 (reachable: pcap_source_next 0x81bd4, nm = incl_len, a Theorem Labs lane). fread does
   NOT return before touching the FILE: it reads the lock word (0x8ee8c, `bltz` at 0x8ee94 skips
   __lockfile for lock = -1), then unconditionally stores mode |= mode - 1 at +136
   (0x8eeac-0x8eec0), before any test on the total s6 = size * nmemb (0x8eec4). With an empty
   window (`beq` at 0x8eec8) the zero test is `bnez s6` at 0x8ef90; with a non-empty window it
   calls memcpy(d, rpos, 0) (0x8eee0), stores rpos + 0 (0x8eef0) and tests `beqz s4` at 0x8eef8.
   Either way __toread is NOT reached and 0 is returned (0x8ef2c-0x8ef34). So for nm = 0 the
   stream keeps p, cpos, window and flags, and the orientation word becomes -1 if it was 0; the
   post says exactly that.

   SIZE = 1 ONLY. pcap calls fread at four sites, all with a1 = 1 (`li a1,1` at 0x815e8, 0x819ac,
   0x81ae4, 0x81bc8): nm = 24 at 0x815f8, 16 at 0x819b8, s11 with 0 < s11 < incl_len at 0x81af0,
   incl_len (possibly 0) at 0x81bd4. With size 1 fread returns the byte count (0x8ef5c-0x8ef60
   divides by 1); a general size would need the item-granular result (len - l) / size and its
   remainder bytes, so the statement fixes size = 1, as cgif's afwrite_spec does (YE01.v:176).

   NO ALLOCATOR CALL IS REACHABLE, so these contracts carry no room premise, no meter and no frame
   chain, and record no event. Every call instruction in the three bodies:
     fread    0x8ee9c jal __lockfile   skipped: `bltz a1` at 0x8ee94 on lock +140 = -1 (source_static)
              0x8eee0 jal 0x51510       the memcpy trampoline
              0x8ef00 jal __toread
              0x8ef18 jalr a3           f->read, loaded from +64 = as_read K = mread (source_static)
              0x8ef44, 0x8ef58 jal __unlockfile  skipped: `bnez s5` at 0x8ef38 / 0x8ef50, s5 = 1 (0x8eea8)
     __toread 0x8e674 jalr a3           f->write, skipped: `beq` at 0x8e660, wpos +40 = wbase +56 = 0
     mread    0x8eaa4, 0x8eae4 jal 0x51510  the memcpy trampoline
   The memcpy trampoline's contract is cgif's aintrin_realizes OCpy (YG0d.v:317-335): its post keeps
   ly and S, so it allocates nothing and records nothing; it takes ecall_pre, with no chain.

   Line numbers from here on are of the relocated core under lib/Reusable at this commit, unless a
   ref is named.

   THE CALLER-JOURNAL FORM of rfread and rmread (a Theorem Labs lane's ruling, 22:39Z). WHAT CHANGED: the
   premise is now the CALLER's journal, not afn_pre, and the post extends that journal instead of
   starting a fresh one with apost_base. WHY: the destination d is memory the caller owns, and at
   two of pcap's four call sites it can be on the real stack AT OR ABOVE the callee's stack
   pointer. apost_base (YC20.v:90-96) starts its journal at the call, and that journal keeps every
   byte at or above alloc_ceiling outside the callee's window [sp - STK, sp) (YCbq.v:355-356) and
   every image byte outside the owned statics and errno (YCbq.v:359-360), whatever the footprint.
   For a destination in the caller's frame or on the real stack the old post therefore asked one
   cell to be both unchanged and written: it was unprovable. THE FORM is cgif's tlzw_spec
   (YC20.v:347-365):
     - the caller's journal as premise, ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
       (YC20.v:349);
     - the callee's window inside the caller's, sp0 - STK <= sp - STK_callee and sp <= sp0
       (YC20.v:356);
     - the right to write each byte as a premise the caller supplies, through awr_byte
       (YC20.v:358-359; awr_byte YCbq.v:457-461);
     - the post extends the SAME journal (tlzw_post YC20.v:334) and says, against the state at the
       call, what the call kept (tlzw_kept YC20.v:311-323).
   pcap's own pcap_source_next statement already has this form (a working branch
   3e755b00849, lib/A/Prog/PcapSourceNextDefs.v: nx_wr_ok :324-328, nx_kept :333-350, nx_wrset
   :353, tnext_post :361, tnext_specX :388). rread_wr_ok and rread_kept below are nx_wr_ok and
   nx_kept with the callee's window as a parameter, and rread_call is tnext_specX's call-state
   premises, so pcap has one destination form and not two. afn_pre is not needed: the caller's
   journal gives AR at lyc (YCbq.v:351), the window present (:365), astk_ok (:366) and qtight
   (:369). The frame chain (ch, achain on lyc) stays.
     dest_ok is NOT a premise any more: awr_byte gives apresent and ~ aowned (YCbq.v:1925-1928
   awr_byte_present) and rread_wr_ok gives the window, which is how cgif's intrinsic call derives
   it (lib/A/Prog/YC85.v:244, :271-273). ~ in_img is not a premise either: ajournal_after_write
   derives it for every awr_byte arm (YCbq.v:566-574, blk_img / frm_img / segs_low).
     THE FILE BLOCK needs the same per-byte right (rread_wr_ok over f .. f + 1304), and the form
   FORCES it: fread and mread write the FILE block, and the caller's journal keeps a block that was
   live at its start unless the byte is in the caller's footprint (YCbq.v:357-358). Under the old
   form the footprint was fread's own and held the FILE block.

   THE DESTINATION (rread_dest). Kept from the old statement: disjoint from the FILE and from b,
   0 <= d, amem_range, range_addressable and the shadow hull for a non-empty range
   (aintrin_realizes' own, YG0d.v:318-336). New: rread_wr_ok over d .. d+l, which also holds the
   disjointness from the callee's window that the old interval disjunct stated, and rread_at, a
   disjunction of three arms. The frame arm and the stack arm are tlzw_pR_ok's two arms
   (YC20.v:324-327) widened from 16 bytes to l; the live-block arm is new. The shadow conjuncts of
   tlzw_pR_ok's frame arm are not copied: range_addressable over d .. d+l says the same for any
   length. EVERY ARM IS REACHED BY A REAL CALL SITE (pcap-fread-dest.md (sha256 dc57856b06db; internal record), both images):
     the frame arm and the stack arm: pcap_source_open 0x815f8 (nm 24, d = s6 + 32) and
       pcap_source_next 0x819b8 (nm 16, d = s2 + 32). The local lies in __asan_stack_malloc_1's
       96-byte (open) or __asan_stack_malloc_0's 64-byte (next) side-stack frame when
       __asan_option_detect_stack_use_after_return (0xa18c0, through GOT 0x99888) is non-zero
       (`beqz` at 0x814bc / 0x8188c), and on the real stack when it is 0 (0x814dc-0x814f4 /
       0x818ac-0x818c4). The flag is a run-time cell, so both arms are reachable code;
     the live-block arm: pcap_source_next 0x81af0 and 0x81bd4, d = the incoming a1, the harness's
       wrapper_malloc buffer (LLVMFuzzerTestOneInput, malloc at 0x80ab8, wrapper_free at 0x8110c);
     asan-ubsan: 0x81388 and 0x8176c (frame / stack), 0x81848 and 0x819a4 (block). Only addresses
       and register allocation differ (a1 spilled to 96(s1); next's data pointer is s3 + 32).
   The disjunction is not defensive: no arm can be dropped without dropping a site.

   THE DATA BUFFER b. A post that keeps garr8 b C (inside asource_at) needs b off the callee's
   stack window (a Theorem Labs lane's R1, sent by a Theorem Labs lane: with b = sp0 - 48 mseek's store at
   0x8ec2c writes ra into C). All three pres carry the live-block premise In (b, |C|) (ablocks ...)
   and the explicit disjunct (b + |C| <= sp - STK \/ sp <= b), in the form of PFmopsM.v:133
   (a working branch ece7690b19e). rtoread_pre LACKED the live-block premise
   (a Theorem Labs lane, 22:42Z: with b = sp - 16 __toread's saves at 0x8e63c / 0x8e640 overwrite C and the
   post's asource_unbuffered is false); it has it now. The disjunct also follows from the live
   block: AR_blocks_law (YG0d.v:423-426) puts every block below alloc_ceiling, and astk_ok
   (YCbq.v:331) puts the window at or above ly_stk_lo >= alloc_ceiling. It is stated anyway, so
   that no walk has to derive it.

   THE FOOTPRINT OF __toread is the FILE block alone, rtoread_fp, WITHOUT YI16.sink_token. The
   caller-journal form FORCES this change. fread's walk folds __toread's fresh journal into the
   caller's journal with ajournal_sub (YCbq.v:722-727). Its side condition :726 needs every
   footprint byte to be in a live block that the caller's footprint holds, or in a new block. The
   token is address 0 (YI16.v:15), and no block holds address 0. So with the token the fold is
   impossible. (cgif's ajournal_sub_tok, lib/A/Prog/YC85.v:33-38, would need the caller's
   footprint to contain address 0, and a caller-journal premise does not give that.) __toread
   writes no image byte and makes no call on a read stream, so its own post does not need the
   token. Without the token, aos_step (YCbq.v:34-39, :39) pins m_fd and m_fsys.

   THE POSTS. Two clauses that the fread interceptor's walk needs are now in rfread_post (from
   a Theorem Labs lane's interceptor walk):
     - m_fds and m_fs unchanged. The post's journal is the caller's journal. Its aos_step
       (YCbq.v:34-39) over the caller's footprint PERMITS fds_rel / fs_rel changes when that
       footprint holds the sink token. musl fread, __toread and mread reach no ecall.
       rfmemopen_post states the same clause (PFmemopenM.v:227-233).
     - the shadow band [kLowMemEnd, kHighShadowEnd) (YG0f.v:18, :24) unchanged. The interceptor's
       check after REAL fread (0x43568-0x435bc; region_is_poisoned at 0x436a8) reads the shadow of
       (d, j) on the memory at REAL's return. The band lies below alloc_ceiling (YK06.v:14), and
       there the kept clauses pin only the shadow of frames. Nothing pins the shadow of a
       destination on the caller's stack. fread writes only its window, the FILE block and
       d .. d+nm, and all of them are application memory.
   rmread_post has both clauses, and rtoread_post has the band clause. fread's walk can give its
   own post only what its callees' posts give it. rtoread_post does not need the fd clause,
   because its footprint does not contain address 0, and aos_step's last conjunct (YCbq.v:39) then
   pins m_fd.
     THE WRITE-SET FORM (a Theorem Labs lane's note, 22:51Z) was considered. rread_kept already says, against
   the state at the call, that only the callee's window, the FILE block and d .. d+l change. With
   the band clause it covers the shadow too. But the posts speak through asource_at (a Theorem Labs lane's
   predicate), and asource_at names b's content. A pure write set would restate what asource_at
   gives. So the kept form stays, with b's live-block and window premises.

   THE STACK. COMPOSITION USES THE CALLEE'S CONTRACT BUDGET, NOT THE MACHINE DEPTH. A caller's STK
   must be at least its own frame plus each callee's STK as that callee's contract states it, for
   every callee it calls. These are the conditions sp0 - STK <= sp1 - STK1 of ajournal_sub
   (YCbq.v:725) and sp0 - STK <= sp - STK_callee of rread_call. The measured machine depth only
   checks that a constant covers what the code uses. Example: RFREAD_STK was
   64 + RMREAD_STK = 4208, above the measured need. But fread calls __toread at sp - 64, and
   RTOREAD_STK = 4160, so the composition needs 64 + 4160 = 4224 (a Theorem Labs lane, 22:50Z). 4208 was too
   small, which is the unsound direction. Each constant, with the measured need and the composition
   need:
     RMREAD_STK = 48 + ESTACK = 4144.
       Measured need from mread's entry: 48 + 2160 = 2208 (its frame, then the memcpy interceptor
       through the trampoline 0x51510).
       Composition need: 48 + ESTACK = 4144. aintrin_realizes' window is ESTACK (YG0d.v:313, :335).
     RTOREAD_STK = 16 + RMREAD_STK = 4160.
       Measured need from __toread's entry: 16. Its only call is `jalr a3` at 0x8e674, with
       a3 = FILE+72 = f->write (0x8e664). That call is skipped on a read stream by `beq wpos,wbase`
       at 0x8e660. __toread does NOT call f->read (pcap-fread-dest.md (sha256 dc57856b06db; internal record) Q3); the earlier
       text here, and chain (b) of pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record), said it did.
       Composition need: 16, because there is no callee on the path that the contract covers.
       The constant stays at 4160, which is above both needs.
     RFREAD_STK = 64 + RTOREAD_STK = 4224.
       Measured need from fread's entry: 64 + 48 + 2160 = 2272, through fread's own `jalr` f->read
       at 0x8ef18 to mread and its memcpy interceptor. pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record) counts 2288 through the
       __toread -> mread edge, which does not exist.
       Composition need: max(64 + RTOREAD_STK, 64 + RMREAD_STK, 64 + ESTACK)
       = max(4224, 4208, 4160) = 4224.
   All three are at or below ASTACK = 16384. So rtoread's astk_ok (YCbq.v:330-332) asks its caller
   for nothing beyond the window. The windows of rfread and rmread are placed by rread_call.

   NOT IN THE STATEMENT, for the proof: aintrin_realizes OCpy at the trampoline 0x51510, and
   as_read K equal to mread's entry (fread's jalr at 0x8ef18 goes to whatever +64 holds).

   IMAGE CONSTANTS in the Definitions, all measured on pcap's asan objdump: PFREAD 0x8ee5c,
   PTOREAD 0x8e638, PMREAD 0x8ea40, the frames 64 / 16 / 48 (their first instructions), and the
   orientation word at +136 (fread 0x8eeac / 0x8eec0, __toread 0x8e648 / 0x8e65c), rpos +8 and
   rend +16 (__toread 0x8e6a0 / 0x8e6a4, mread 0x8eacc / 0x8ead0), the flag values 8 (fmemopen's
   store at 0x8e994-0x8e998) and 24 (mread's `ori 16` at 0x8ea88). The other FILE offsets are
   named through PSource.v. ESTACK, SHADOW_OFF, alloc_ceiling, kLowMemEnd and kHighShadowEnd are
   constants of cgif's model, named through the core. The statements do not use the image end,
   the shadow of the image, or the fake-stack floor.

   DONOR VOCABULARY (origin/ossv/recipes c8557374ad2e, proofs/cgif/cgif_file_fuzzer/lib/):
     afn_pre YCbq.v:334-341, ajournal YCbq.v:348-370; apost_base YC20.v:90-96;
     SRr YA0n.v:34-37, world / w_H YA0n.v:17-22;
     cfg_at YG0d.v:212-213, w64 YG0d.v:27, spZ YG0d.v:23, ESTACK YG0d.v:18,
     amem_range YG0d.v:316, shadow_hull_vis YG0d.v:309-310, ablocks YG0d.v:420-421,
     aintrin_realizes YG0d.v:317-335; range_addressable YG0v.v:32-33; SHADOW_OFF YG0f.v:11;
     asyms YG0f.v:154; aview YG0n.v:17; sink_head YI16.v:10; garr8 YI00.v:14-15;
     val_mem YI04.v:140; mrestrict YK04.v:16; getr YK11.v:22;
     the shape of rfread (size-1 argument, disjointness, amem_range, shadow premises) YE01.v:172-187
     afwrite_spec;
     the pre / post split as named Definitions A/ACfn.v:33-59.
   CALLER-JOURNAL VOCABULARY (lib/Reusable at this commit): ajournal YCbq.v:347-369, awr_byte
     YCbq.v:457-461, achain (as afn_pre uses it, YCbq.v:339), ajournal_sub YCbq.v:722-727, aos_step
     YCbq.v:34-39; tlzw_kept / tlzw_pR_ok / tlzw_post / tlzw_spec YC20.v:311-365; in_img
     YG0d.v:471, AR_blocks_law YG0d.v:423-426; kLowMemEnd YG0f.v:18, kHighShadowEnd YG0f.v:24;
     alloc_ceiling YK06.v:14; the caller-journal post's register and config shape YC20.v:332-335.
   PREDICATE (a working branch 58a865eec30, lib/A/Stdio/PSource.v):
     SRC_FILE_BLOCK :49, SRC_BUF_OFF :50, SRC_BUFSIZ :51, SRC_COOKIE_OFF :52, U32M1 :57,
     source_mode :162-163, source_flags :212-213, asource_at :215-231,
     asource_unbuffered :261-262. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ONE STATEMENT TEXT FOR BOTH IMAGES (a Theorem Labs lane, 22:27Z; the precedent is MemmoveDef.v). The
   contracts below are image-generic: no listing is in their context, every entry address is a
   parameter (pc), and every frame and FILE offset they use is identical in the asan and
   asan-ubsan images (measured). NO DEFINITION IN THIS FILE NAMES AN IMAGE ADDRESS (the addresses in
   comments are measurement provenance), so both lib/A and lib/B may Require it (a Theorem Labs lane's lib/B
   closure rule, 01:26Z, if comments are outside it). Each image's walk instantiates the
   contracts at its own entry addresses (asan: fread 0x8ee5c, __toread 0x8e638, mread 0x8ea40;
   asan-ubsan: 0x8ed28, 0x8e504, 0x8e90c; each from that image's own fuzz_pcap.nm.txt (sha256 21120db6ab2e, 49b2ad826669; internal record)). The named
   constants PFREAD / PTOREAD / PMREAD and their _U twins that stood here were removed at
   02:2xZ: a `git grep -w` over 91 live pcap heads found no user of any of them. *)

(* Each is its own frame plus the largest budget of a callee's contract (header, THE STACK). *)
Definition RMREAD_STK  : Z := 48 + ESTACK.
Definition RTOREAD_STK : Z := 16 + RMREAD_STK.
Definition RFREAD_STK  : Z := 64 + RTOREAD_STK.

(* The bytes a read of l at caller position p moves out of a stream of n bytes (plain
   lib/Prog/fread_c.v:5 fread_j, lib/Prog/mread_c.v:5 mread_t). *)
Definition rread_k (l n p : Z) : Z := Z.min l (n - p).
(* The bytes mread reads ahead into the window after delivering rread_k (mread_c.v:6 mread_rem2). *)
Definition rmread_fill (l n p : Z) : Z := Z.min (n - p - rread_k l n p) SRC_BUFSIZ.

(* What __toread may change besides its window: the FILE block, without YI16.sink_token (header,
   THE FOOTPRINT OF __toread). *)
Definition rtoread_fp (f : Z) : list (Z * Z) := [(f, f + SRC_FILE_BLOCK)].

(* What fread and mread may write besides their window: the FILE block and the destination
   (pcap's nx_wrset, PcapSourceNextDefs.v:353). *)
Definition rread_wrset (f d l : Z) (a : Z) : Prop :=
  (f <= a < f + SRC_FILE_BLOCK) \/ (d <= a < d + l).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ajournal (YCbq.v) is stated under cgif's sink-head class, as in YE01.v. *)
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The caller's right to let a call whose stack window is RSTK write [q, q + n): the byte is one
   the caller's own journal may change, and it is not in the callee's window. This is pcap's
   nx_wr_ok (PcapSourceNextDefs.v:324-328) with the window as a parameter (cgif YC20.v:358-359). *)
Definition rread_wr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (RSTK sp q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
    ~ (sp - RSTK <= a < sp).

(* Where the destination lies: in one of the caller's side-stack frames, on the stack (the two arms
   of cgif's tlzw_pR_ok, YC20.v:324-327), or inside a live block. The header names the call sites
   of each arm. *)
Definition rread_at (lyc : alayout) (Sc : astate) (d l : Z) : Prop :=
  (exists cid pos, In (cid, pos) (frames Sc) /\
     (forall a, d <= a < d + l -> in_zr a (frame_rng lyc (cid, pos)))) \/
  (ly_stk_lo lyc <= d /\ d + l <= ly_stk_hi lyc) \/
  (exists bb nn, In (bb, nn) (ablocks B lyc Sc) /\ bb <= d /\ d + l <= bb + nn).

(* The destination d .. d+l of a read from the stream (f, b, n), for a callee whose stack window
   is RSTK below sp: disjoint from the FILE and from b, where it lies, the caller's right to write
   it, and what the memcpy interceptor checks of it (YG0d.v:318-336). *)
Definition rread_dest (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (RSTK sp d l f b n : Z) : Prop :=
  (d + l <= f \/ f + SRC_FILE_BLOCK <= d) /\
  (d + l <= b \/ b + n <= d) /\
  0 <= d /\ amem_range d l /\
  rread_at lyc Sc d l /\
  rread_wr_ok STK sp0 FP ly S lyc Sc own RSTK sp d l /\
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF d l /\
  (0 < l -> shadow_hull_vis (aview segs (w_H W) memc) d l).

(* The call, inside the caller's journal: the call-state premises of pcap's tnext_specX
   (PcapSourceNextDefs.v:388) and cgif's tlzw_spec (YC20.v:349-356), without tlzw's CTX and
   rodata premises, which no allocator event and no rodata read here needs. *)
Definition rread_call (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (k : Z) (RSTK : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : Prop :=
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - RSTK /\ spZ regs <= sp0 /\
  achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch.

(* What a call keeps, against the state at the call: everything but its own stack window and the
   bytes E it may write. This is pcap's nx_kept (PcapSourceNextDefs.v:333-350) with the window as a
   parameter (cgif tlzw_kept, YC20.v:311-323). *)
Definition rread_kept (RSTK : Z) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (W2 : world segs) (mem2 : word -> option byte) (sp : Z)
    (E : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RSTK <= a < sp) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - RSTK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, sp - RSTK <= a < sp -> apresent (w_H W2) mem2 a).

(* The post of a call in the caller-journal form (cgif tlzw_post, YC20.v:328-335): the caller's
   journal extended with no event, the callee-saved registers, and what the call kept; Q states
   the rest, with apost_base's argument order (YC20.v:90-96). *)
Definition rread_post_base (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (RSTK : Z) (regs : bvmap 5 word) (E : Z -> Prop)
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    : world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
  ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
  aregs_preserved regs regs2 /\
  rread_kept RSTK lyc Sc W memc W2 mem2 (spZ regs) E /\
  Q ly2 S2 W2 regs2 mem2 md2.

(* ---------------------------------------------------------------------- *)
(* fread(d, 1, nm, f)                                                      *)
(* ---------------------------------------------------------------------- *)
Definition rfread_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (k : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z))
    (d nm f b p : Z) (C : list Z) : Prop :=
  rread_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k RFREAD_STK regs ch /\
  getr regs 10 = w64 d /\ getr regs 11 = w64 1 /\ getr regs 12 = w64 nm /\ getr regs 13 = w64 f /\
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\ In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
  (b + Z.of_nat (length C) <= spZ regs - RFREAD_STK \/ spZ regs <= b) /\
  asource_at segs K (rd W memc) f b C p /\
  rread_wr_ok STK sp0 FP ly S lyc Sc own RFREAD_STK (spZ regs) f SRC_FILE_BLOCK /\
  0 <= nm <= 2 ^ 26 /\
  rread_dest STK sp0 FP ly S own lyc Sc W memc RFREAD_STK (spZ regs) d nm f b
    (Z.of_nat (length C)).

Definition rfread_post (d nm f b p : Z) (C : list Z) (lyc : alayout) (Sc : astate)
    (W : world segs) (memc : word -> option byte) (mdc : Model)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  let j := rread_k nm (Z.of_nat (length C)) p in
  ly' = lyc /\ S' = Sc /\
  getr regs' 10 = w64 j /\
  garr8 segs (rd W' mem') d (firstn (Z.to_nat j) (skipn (Z.to_nat p) C)) /\
  asource_at segs K (rd W' mem') f b C (p + j) /\
  (* fread always stores mode |= mode - 1 (0x8eeac-0x8eec0) *)
  source_mode segs (rd W' mem') f U32M1 /\
  (* nm = 0: the stream is as it was, except the orientation word +136 *)
  (nm = 0 -> forall a, f <= a < f + SRC_FILE_BLOCK -> ~ (f + 136 <= a < f + 140) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) memc a) /\
  (* musl fread, __toread and mread make no fd and no fs call. The journal below is the caller's,
     and its aos_step (YCbq.v:34-39) only gives fds_rel / fs_rel, which PERMIT a change of the sink
     fd and path when the caller's footprint holds the sink token, so the equality has to be
     stated here or no caller can have it (as rfmemopen_post, PFmemopenM.v:227-233). *)
  m_fds md' = m_fds mdc /\ m_fs md' = m_fs mdc /\
  (* the shadow band is as it was: the interceptor reads the shadow of (d, j) after REAL fread
     returns (0x43568-0x435bc, 0x436a8), and below alloc_ceiling the kept clauses pin only frame
     shadows *)
  (forall s, kLowMemEnd <= s < kHighShadowEnd ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s).

Definition rfread_contract (pc : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (d nm f b p : Z) (C : list Z),
  rfread_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C ->
  SRr segs W (cfg_at segs pc regs memc mdc)
    (rread_post_base STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k RFREAD_STK regs
       (rread_wrset f d nm) (rfread_post d nm f b p C lyc Sc W memc mdc)).

(* ---------------------------------------------------------------------- *)
(* __toread(f), as fread calls it: after the window is drained.            *)
(* ---------------------------------------------------------------------- *)
Definition rtoread_pre (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
    (f b p fl : Z) (C : list Z) : Prop :=
  afn_pre segs B RTOREAD_STK ly S W regs mem md ch /\
  getr regs 10 = w64 f /\
  In (f, SRC_FILE_BLOCK) (ablocks B ly S) /\ In (b, Z.of_nat (length C)) (ablocks B ly S) /\
  (b + Z.of_nat (length C) <= spZ regs - RTOREAD_STK \/ spZ regs <= b) /\
  asource_unbuffered segs K (rd W mem) f b C p /\
  source_flags segs (rd W mem) f fl.

Definition rtoread_post (f b p fl : Z) (C : list Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  ly' = ly /\ S' = S /\
  (* (flags << 59) >> 63: -1 exactly when F_EOF (16) is set (0x8e698, 0x8e6a8) *)
  getr regs' 10 = w64 (if fl =? 24 then -1 else 0) /\
  asource_unbuffered segs K (rd W' mem') f b C p /\
  source_flags segs (rd W' mem') f fl /\
  source_mode segs (rd W' mem') f U32M1 /\
  (* rpos = rend = buf + buf_size (0x8e690-0x8e6a4) *)
  val_mem segs (rd W' mem') (f + 8) 8 (f + SRC_FILE_BLOCK) /\
  val_mem segs (rd W' mem') (f + 16) 8 (f + SRC_FILE_BLOCK) /\
  (* the shadow band is as it was, for rfread_post's band clause *)
  (forall s, kLowMemEnd <= s < kHighShadowEnd ->
     aview segs (w_H W') mem' s = aview segs (w_H W) mem s).

Definition rtoread_contract (pc : Z) : Prop :=
  forall W ly S regs mem md ch (f b p fl : Z) (C : list Z),
  rtoread_pre regs ly S W mem md ch f b p fl C ->
  SRr segs W (cfg_at segs pc regs mem md)
    (apost_base segs B RTOREAD_STK (rtoread_fp f) regs ly S W mem md 0
       (rtoread_post f b p fl C ly S W mem)).

(* ---------------------------------------------------------------------- *)
(* mread(f, d, l), as fread calls it through f->read: after __toread       *)
(* returned 0, so the window is empty and the flags are 8.                  *)
(* ---------------------------------------------------------------------- *)
(* mo is the orientation word, which mread keeps. *)
Definition rmread_pre (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
    (k : Z) (regs : bvmap 5 word) (ch : list (Z * Z * Z))
    (f d l b p mo : Z) (C : list Z) : Prop :=
  rread_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k RMREAD_STK regs ch /\
  getr regs 10 = w64 f /\ getr regs 11 = w64 d /\ getr regs 12 = w64 l /\
  In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\ In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
  (b + Z.of_nat (length C) <= spZ regs - RMREAD_STK \/ spZ regs <= b) /\
  asource_unbuffered segs K (rd W memc) f b C p /\
  source_flags segs (rd W memc) f 8 /\ source_mode segs (rd W memc) f mo /\
  rread_wr_ok STK sp0 FP ly S lyc Sc own RMREAD_STK (spZ regs) f SRC_FILE_BLOCK /\
  1 <= l <= 2 ^ 26 /\
  rread_dest STK sp0 FP ly S own lyc Sc W memc RMREAD_STK (spZ regs) d l f b
    (Z.of_nat (length C)).

Definition rmread_post (f d l b p mo : Z) (C : list Z) (lyc : alayout) (Sc : astate)
    (W : world segs) (memc : word -> option byte) (mdc : Model)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  let n := Z.of_nat (length C) in
  let j := rread_k l n p in
  let r := rmread_fill l n p in
  ly' = lyc /\ S' = Sc /\
  getr regs' 10 = w64 j /\
  (* delivered to the caller (0x8eaa4) *)
  garr8 segs (rd W' mem') d (firstn (Z.to_nat j) (skipn (Z.to_nat p) C)) /\
  (* the caller position moves by j; the window holds C[p+j .. p+j+r) *)
  asource_at segs K (rd W' mem') f b C (p + j) /\
  val_mem segs (rd W' mem') (f + SRC_COOKIE_OFF) 8 (p + j + r) /\
  val_mem segs (rd W' mem') (f + 8) 8 (f + SRC_BUF_OFF) /\
  val_mem segs (rd W' mem') (f + 16) 8 (f + SRC_BUF_OFF + r) /\
  (* F_EOF is set when the request exceeds what is left (0x8ea80-0x8ea8c) *)
  source_flags segs (rd W' mem') f (if l >? n - p then 24 else 8) /\
  source_mode segs (rd W' mem') f mo /\
  (* fread's two post clauses, which fread's walk can only have from here *)
  m_fds md' = m_fds mdc /\ m_fs md' = m_fs mdc /\
  (forall s, kLowMemEnd <= s < kHighShadowEnd ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s).

Definition rmread_contract (pc : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (f d l b p mo : Z) (C : list Z),
  rmread_pre STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f d l b p mo C ->
  SRr segs W (cfg_at segs pc regs memc mdc)
    (rread_post_base STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k RMREAD_STK regs
       (rread_wrset f d l) (rmread_post f d l b p mo C lyc Sc W memc mdc)).

End a.
