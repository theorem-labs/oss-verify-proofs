(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the contract of musl's fmemopen inside libreac/fuzz_pcap (libreac v1.9.0,
   ASan build), stated in cgif_file_fuzzer's vocabulary.

   STATEMENT ONLY. This file holds Definitions and nothing else: no lemma, no proof, no Admitted.

   THE FUNCTION. musl fmemopen at 0x8e870 of the v1.9.0 ASan image (the unstripped twin
   fuzz_pcap.asan (sha256 36da3052c383) of the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0)), read off
   fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record) lines 99107-99223. The malloc
   call inside it returns to 0x8e90c. The asan-ubsan copy is the same statement at its own
   addresses: entry 0x8e73c, malloc return 0x8e7d8 (a Theorem Labs lane's trace-universe.md:132, :411 (sha256 c4f92d11241e; internal record); not
   re-measured here). Both addresses are parameters of the contract (pc, ra), as in cgif's
   afopen_spec, so one statement serves both images.

   At ossv/recipes 25e3d17bdb50 (2026-10-29), NO DONOR existed for this function (rule 24: a Theorem Labs lane's runtime-donors.md (sha256 77e6fad19fb7; internal record) rows 3-4 and section
   6). The step content comes from this worker's own plain proof lib/Prog/fmemopen_c.v and the
   layout model lib/Prog/StdioModel.v; the names come from the cgif donor listed at the end.

   WHAT THE STATEMENT SAYS. Called with a0 = b (a live heap block holding the n bytes C),
   a1 = n (0 <= n < 2^26), a2 = the "rb" literal, with no stream open (asource_none), with room
   for one 1304-byte allocation and one allocator event, and with the frame chain above the entry
   in the caller-supplied context list CTX, musl fmemopen returns res, keeps the callee-saved
   registers, records at most one event and advances the meter by at most one 1304-byte malloc,
   and then, the allocation having succeeded: 4096 <= res, res mod 16 = 0, exactly one new block
   (res, 1304) is appended to the live blocks, and an unbuffered read stream on (res, b, C) is
   open at caller position 0 (asource_unbuffered, PSource.v). The fd and fs tables are unchanged.
   Its writes are confined to its stack window, the fresh block and the open-file list head.

   ONE ARM, AND NO SPLIT ON THE LENGTH. The post states the SUCCESS case only: rfmemopen_contract
   takes amalloc04_rule as a hypothesis, whose 4096 <= res (YC5d.v:72) refutes the malloc-failure
   branch inside the walk (a Theorem Labs lane's ruling of 21:49Z; a disjunct
   in a callee's POST cannot be refuted by its caller, which is why the earlier two-arm form made
   the interceptor's success-only afmemopen_spec unprovable). musl fmemopen has four exits that
   return 0, and each is accounted for rather than stated:
     0x8e910 `j 8e8dc` after the malloc NULL test (`bnez a0,8e920` at 0x8e90c): REFUTED IN THE WALK
             from amalloc04_rule's 4096 <= res. It frees nothing and writes no errno, since 0x8e8dc
             lies after the only errno store at 0x8e8d8.
   The other three zero returns, each excluded by a premise rather than by the walk:
     0x8e8b8 `beqz a0` after strchr("rwa", mode[0]) (0x8e8b4, "rwa" at 0x20026): errno 22
             (0x8e8d0-0x8e8d8). Excluded by a premise: a2 is the "rb" literal (as_mode K), so
             mode[0] = 'r'.
     0x8e8bc `bnez s1` (s1 = buf), then 0x8e8c0 `bgez s2` (s2 = size, a SIGN test, size >
             PTRDIFF_MAX): errno 12 (0x8e8c4-0x8e8d8). Excluded by a premise: b is a live block,
             so b <> 0.
    0x8e90c `bnez a0,8e920` after malloc(1304) at 0x8e908: a non-zero result goes on to the
            FILE set-up at 0x8e920; a zero result falls to 0x8e910 `j 8e8dc`, which returns 0
            (0x8e8dc `li a0,0`, reload, 0x8e8f8 pop, 0x8e8fc `ret`; no free, and no errno store,
            since 0x8e8dc lies after the only errno store at 0x8e8d8). This branch is REAL CODE
            and the walk must step it - but it is REFUTED there, not stated in the post.
   CHOICE (a Theorem Labs lane's ruling of 21:49Z; it reverses the earlier
   two-arm post of d9a18ea6247): the post states the SUCCESS arm only, and rfmemopen_contract
   takes the allocator's grant rule as a HYPOTHESIS - cgif's amalloc04_rule (YC5d.v:56-74), the
   contract of the malloc callee at the trampoline 0x52bd8 - whose post gives 4096 <= res
   (YC5d.v:72). The walk therefore refutes the 0x8e910 branch from that bound. REASON: a
   disjunct in a callee's POST cannot be refuted by its caller, so a two-arm post made the
   interceptor's success-only afmemopen_spec (a working branch e66390898ef)
   unprovable. THE SUCCESS-ONLY FORM IS BY PROOF, NOT BY ASSUMPTION (a Theorem Labs lane's 00:28Z ruling: allowed
   if and only if the spec carries the room premises and cites the grant lemma). The room premises
   are in rfmemopen_pre: st_nev S + 1 <= EV_MAX, blocks_bytes S + SRC_FILE_BLOCK <= LIVE_MAX and
   mo_ok MT S (mo_malloc MT SRC_FILE_BLOCK), with 0 <= 1304 < MALLOC_MAX by YG00.v:38 (see THE ROOM
   PREMISES below). The grant lemma is amalloc04_rule's 4096 <= res (YC5d.v:72), a hypothesis of
   rfmemopen_contract. allocator_may_return_null = 1 on every pcap image does not reopen the arm:
   ASAN_OPTIONS is never read on these images (the GOT word at 0x99870 = 1, a Theorem Labs lane's
   measurement on the original v1.9.0 asan pin), and the refusal paths are proved DEAD under the
   statements' premises by a Theorem Labs lane's lib/Reusable/YRefuse.v (a working branch
   3af7ae3448a; arefuse_primary_dead_agrees / _halts, arefuse_ceiling_dead), which is what
   discharges amalloc04_rule at composition time. This file cites them and does not re-derive them.

   NO SPLIT ON THE LENGTH.
   The length is tested nowhere on the buf <> 0 path: n = 0 takes the same path as n >= 1 and
   returns a FILE for an empty stream. PSource.v's asource_at admits C = [] (then
   p = cpos = 0, the window is empty, +240 = +248 = 0). The NULL return for a zero length is the
   HARNESS's: libreac_fuzz_fopen loads g_file_len at 0x80788, `beqz a1,807b0` at 0x8078c,
   returns 0 at 0x807b0 with no errno store and never calls fmemopen on that path (the plain
   contract lib/Prog/libreac_fuzz_fopen_c.v:50-52 states that split for the caller; the plain musl
   contract lib/Prog/fmemopen_c.v:34 instead assumed 1 <= length Fc).

   WHAT THE CODE WRITES, cross-checked against PSource.v source_static and StdioModel.v:70-80
   mfile_cells (no disagreement found): memset(f, 0, 272) (0x8e924-0x8e92c) zeroes +0..+271,
   so flags, rpos, rend, wend/wpos/mustbezero_1/wbase, prev, mode +136 and cpos +232 start at 0;
   +152 = f+232 (0x8e93c), +88 = f+280 (0x8e944), +96 = 1024 (0x8e948), +120 = -1 (0x8e94c),
   +144 = -1 (0x8e950), +248 = n (0x8e96c), +256 = b (0x8e970), +264 = mode[0] = 114 (0x8e978),
   flags = 8 for "r" without '+' (0x8e994-0x8e998), +240 = n (0x8e9b0), +24/+64/+72/+80 = mclose,
   mread, mwrite, mseek (0x8ea00-0x8ea0c), +140 = -1 when __libc.threaded (0x5f4b21) is 0
   (0x8e9fc-0x8ea18); then the tail jump to __ofl_add (0x8ea3c): next +112 = old head (0x8f230),
   head = f (0x8f23c). The lock calls touch nothing while __libc.need_locks (0x5f4b23) is 0
   (__lock 0x93430-0x93434) and the lock word is 0 (__unlock 0x936b4-0x936b8).

   THE FRAME CHAIN (a Theorem Labs lane's shape, pcaptr-asks.md (sha256 436176c63147; internal record) section 4.2; donor types). CTX is a
   Section parameter: the contexts the caller's frame pointer may have at entry. fmemopen does not
   change s0 before its malloc call (s0 is saved at 0x8e878 and first written at 0x8e920, after
   the call), so the chain the allocator unwinds at 0x8e908 is afn_pre's entry chain ch, and the
   recorded trace is pc0 :: ra :: spine ch (innermost first, YG0d.v:223-224 call_trace, YG00.v:374
   unwind_of_chain), or [pc0] when frame0_ok fails. Hence the three premises: In (spine ch) CTX,
   the [pc0] row, and the donor's per-context row (A/ACeb.v:39). The ASan interceptor restores s0
   and ra before its tail jump (0x4667c-0x46690), so the interceptor passes (CTX, ch) through
   unchanged and adds no return address. Membership is a premise of malloc and free only
   (YG0d.v:253-276); the memset and the two strchr calls take no chain.

   THE ROOM PREMISES, in cgif's form, from the allocator contract this walk calls at 0x8e908
   (amalloc04_rule, YC5d.v:56-74): 0 <= n < MALLOC_MAX holds for 1304 by YG00.v:38 and needs no
   premise; blocks_bytes S + SRC_FILE_BLOCK <= LIVE_MAX and st_nev S + 1 <= EV_MAX (the form of
   YE01.v:216, which implies amalloc04_rule's st_nev Sc < EV_MAX); mo_ok MT S (mo_malloc MT
   SRC_FILE_BLOCK) (the form of YC7x.v:88). They are dischargeable from pcap's constants
   (a Theorem Labs lane: largest request 2^26, live bytes 2.0e8). The refusal branches inside the
   allocator are the ported runtime walk's business, not this file's.

   THE FOOTPRINT is [YI16.sink_token], as cgif's afopen_spec (YE01.v:221). It must contain the
   token: ajournal keeps every image byte outside the owned statics and errno (YCbq.v:360-361)
   unless fp_spares fails, and fp_spares (YCbq.v:86) frees the open-file list head AOFL_HEAD only
   for a footprint that contains address 0 (YI16.v:70 sink_open_fp). The fresh block needs no
   footprint (ajournal protects only the blocks live before the call, YCbq.v:358-359), and b is
   not written.

   THE STACK. RFMEMOPEN_STK = 48 + ASTACK. 48 is fmemopen's frame (`addi sp,sp,-48` at 0x8e870);
   the malloc call sits at offset o = -48, and amalloc04_rule asks ASTACK - o <= STK
   (YC5d.v:60). The other callees need less: the memset trampoline ESTACK (aintrin_realizes'
   ecall_pre, YG0d.v:281), the strchr interceptor a frame of 2144 bytes on pcap's image (measured
   by the parent's lane; a lower bound, its own callees not followed), and __ofl_add runs after
   the frame is popped (16 + __ofl_lock 16). UNVERIFIED as a whole-reach bound until the strchr
   interceptor's own callees are followed on pcap's image.

   NOT IN THE STATEMENT, for the proof: the source analogue of cgif's asink_img_laws (YE01.v:27-40),
   in particular as_ofl_head K = AOFL_HEAD and the interceptor cells; the allocator contract at the
   malloc trampoline 0x52bd8 (cgif's amalloc04_rule, or the ported runtime's contract that admits
   a 0 result), aintrin_realizes (OSet) at the memset trampoline 0x5150c; a pcap strchr walk in the form
   of A/AE2j.v:184 for ("rb", '+') -> 0 and ("rwa", 'r') -> "rwa". No ameta_inv premise: musl
   fmemopen does not touch the interceptor metadata region.

   IMAGE CONSTANTS in the Definitions, all measured on pcap's asan objdump: PFMEMOPEN 0x8e870
   (line 99107), FM_MALLOC_RA 0x8e90c (the instruction after the jal at 0x8e908, line 99146),
   and fmemopen's frame 48 (0x8e870). Everything else is a pcap fact named through PSource.v
   (SRC_FILE_BLOCK) or a constant of cgif's allocator model named through the core (ASTACK, EV_MAX,
   LIVE_MAX, kUnwindMax). The statement does not use the image end, the shadow of the image, or
   the fake-stack floor.

   DONOR VOCABULARY (origin/ossv/recipes c8557374ad2e, proofs/cgif/cgif_file_fuzzer/lib/):
     afn_pre YCbq.v:334-341, ajournal YCbq.v:348-370, spine YCbq.v:220, achain YCbq.v:216-219;
     apost_base YC20.v:90-96 (arodata_okP YC20.v:46-48 is NO LONGER used: PSource.v pins the bytes);
     ameter_ops / mo_ok / mo_le / mo_malloc YC5d.v:16-20, amalloc04_rule YC5d.v:56-74;
     SRr YA0n.v:34-37, world / w_H YA0n.v:17-22;
     cfg_at YG0d.v:212-213, w64 YG0d.v:27, spZ YG0d.v:23, ASTACK YG0d.v:18, ablocks YG0d.v:420-421,
     AR_blocks_law YG0d.v:422-428 (res mod 16 = 0), call_trace YG0d.v:223-224;
     EV_MAX YG00.v:37, kUnwindMax YG00.v:36, st_nev YG00.v:166, blocks_bytes YG01.v:222-223,
     LIVE_MAX YG01.v:224, asyms / pc_malloc_ra0 / as_universe YG0f.v:134-177, aview YG0n.v:17;
     sink_head / sink_token YI16.v:10, :14; garr8 / bytes_ok YI00.v:14-16; mrestrict YK04.v:16;
     getr YK11.v:22;
     the CTX parameter and the per-context row A/ACeb.v:29, :39 (form of YC7x.v:72-75);
     the [pc0] row YCbo.v:221-223 (call_trace_in);
     the pre / post split as named Definitions A/ACfn.v:33-59;
     the success arm's shape (4096 <= res, ablocks ++ [(res, FILE_BLOCK)]) YE01.v:209-228 afopen_spec.
   PREDICATE (a Theorem Labs lane, a working branch 58a865eec30, lib/A/Stdio/PSource.v):
     SRC_FILE_BLOCK :49, asource_syms / as_mode :79-94, asource_unbuffered :261-262,
     asource_none :240-241.
   The cgif core arrives relocated under lib/Reusable; until then this file does not build, and
   its first build is a name check against the list above. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI00 YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20 YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ONE STATEMENT TEXT FOR BOTH IMAGES (a Theorem Labs lane, 22:27Z; the precedent is MemmoveDef.v). The
   contracts below are image-generic: no listing is in their context, every entry address is a
   parameter (pc, ra), the malloc return address comes from the asyms record, and every frame and
   FILE offset they use is identical in the asan and asan-ubsan images (measured). NO DEFINITION IN
   THIS FILE NAMES AN IMAGE ADDRESS, so both lib/A and lib/B may Require it. Each image's walk takes
   its own pcs from its image file: lib/A/Stdio/PStdioImgA.v (asan: PFMEMOPEN fmemopen+0x0 = 0x8e870,
   FM_MALLOC_RA fmemopen+0x9c = 0x8e90c) and lib/B/Stdio/PStdioImgB.v (asan-ubsan). The four
   constants PFMEMOPEN / FM_MALLOC_RA / PFMEMOPEN_U / FM_MALLOC_RA_U that stood here were moved there
   on a Theorem Labs lane's 03:15Z ruling, after every user Required its image file. *)

(* fmemopen's frame (0x8e870) plus the allocator's stack budget (YC5d.v:60). *)
Definition RFMEMOPEN_STK : Z := 48 + ASTACK.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ajournal (YCbq.v) is stated under cgif's sink-head class, as in YE01.v. *)
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
(* The contexts of the frame s0 points to at entry. The program walk sets the list of
   pcap_source_open's contexts (asan: [0x809a0; 0x80634] and its truncation, and the same through
   0x810c8; two Theorem Labs lanes, trace-universe.md:332-338 (sha256 c4f92d11241e; internal record)). *)
Variable CTX : list (list Z).
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* pc: fmemopen's entry; ra: the return address of its malloc call; [mc_lo, mc_hi): the window of
   read-only bytes the strchr callee reads beyond the two mode strings. The bytes of the mode
   strings - musl's own "rwa\0" at 0x20026 and pcap's mode literal "rb\0" at 0x20d40 - are pinned by
   PSource.v's asrc_stdio_env (a Theorem Labs lane, on a Theorem Labs lane's 21:05Z ruling that the predicate is their
   one home), which asource_none below carries. strchr also reads __strchrnul's word constants,
   which AR does not pin (YG0n.v:490; mbyte reads mem before rom, YP09.v:18). Without them
   strchr("rb", '+') could return non-NULL and fmemopen would skip `flags = 8` (a Theorem Labs lane,
   00:04Z-00:12Z). The premise is the DONOR'S form (a Theorem Labs lane, 00:23Z, after
   a Theorem Labs lane's reading of cgif c8557374ad2e): the body of the core's narrow mconsts_view
   (A/AE39.v:28), stated over segs with the window as parameters. pcap's instance is
   [0x10350, 0x10370) = AE39.v's MC_LO / MC_HI (mc_bounds), the constants 0x10350 / 0x10368 that
   strchr reads. The donor's program site derives it from its image-region fact (A/AD1k.v:266
   mconsts_of_IMG, applied at AD1l.v:124) and moves it across calls with mconsts_view_keep
   (AE39.v:42). This replaces rom_view (eaba5a32fed), which is not derivable from fopen's roimg. *)
Definition rfmemopen_pre (ra mc_lo mc_hi : Z) (regs : bvmap 5 word) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
    (b n : Z) (C : list Z) : Prop :=
  afn_pre segs B RFMEMOPEN_STK ly S W regs mem md ch /\
  (* the arguments: the data buffer, its length, the "rb" literal *)
  getr regs 10 = w64 b /\ getr regs 11 = w64 n /\ getr regs 12 = w64 (as_mode K) /\
  (* no stream is open *)
  asource_none segs K (rd W mem) /\
  (* the content: a live block holding C *)
  n = Z.of_nat (length C) /\ n < 2 ^ 26 /\
  In (b, n) (ablocks B ly S) /\ garr8 segs (rd W mem) b C /\ bytes_ok C /\
  (* the read-only constants the strchr calls read beyond the two mode strings *)
  (forall a, mc_lo <= a < mc_hi ->
     aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) /\
  (* the allocator's room premises *)
  st_nev S + 1 <= EV_MAX /\ blocks_bytes S + SRC_FILE_BLOCK <= LIVE_MAX /\
  mo_ok MT S (mo_malloc MT SRC_FILE_BLOCK) /\
  (* the frame chain the 1304-byte malloc event records *)
  In (spine ch) CTX /\
  In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (ra :: c))) (as_universe B)).

Definition rfmemopen_post (b : Z) (C : list Z) (ly : alayout) (S : astate) (md : Model)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) : Prop :=
  exists res : Z,
    getr regs' 10 = w64 res /\
    mo_le MT S S' (mo_malloc MT SRC_FILE_BLOCK) /\
    (* the FILE and its cookie, linked as the open stream; malloc's 0 result is refuted in the
       walk from amalloc04_rule's 4096 <= res, so it has no arm here *)
    4096 <= res /\ res mod 16 = 0 /\
    ablocks B ly' S' = ablocks B ly S ++ [(res, SRC_FILE_BLOCK)] /\
    asource_unbuffered segs K (rd W' mem') res b C 0 /\
    (* musl fmemopen makes no fd and no fs call: it allocates, memsets, reads the mode with
       strchr and links the stream through __ofl_add. The sink token in the journal below only
       gives fds_rel / fs_rel (YI16.v:51-54, through aos_step YCbq.v:34-39), which PERMIT a change
       of the sink fd and path, so the equality has to be stated here or no caller can have it.
       Asked for by the fmemopen interceptor walk, whose tail call takes md' from this post alone
       (afmemopen_spec's obligation at PFmemopenISpec.v:103). *)
    m_fds md' = m_fds md /\ m_fs md' = m_fs md.

Definition rfmemopen_contract (pc ra mc_lo mc_hi : Z) : Prop :=
  amalloc04_rule segs B MT ->
  forall W ly S regs mem md ch (b n : Z) (C : list Z),
  rfmemopen_pre ra mc_lo mc_hi regs ly S W mem md ch b n C ->
  SRr segs W (cfg_at segs pc regs mem md)
    (apost_base segs B RFMEMOPEN_STK [YI16.sink_token] regs ly S W mem md 1
       (rfmemopen_post b C ly S md)).

End a.
