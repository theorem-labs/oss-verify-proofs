(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are
   restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc from
   proofs/libreac/fuzz_knock/lib/A/APgCSpec.v (the Section form of its lines 32-164) and
   proofs/libreac/fuzz_knock/lib/A/ACfn.v (lines 27-71, the harness contract tfib_lib_pre_x / _post_x /
   _contract_x; its lines 72-73, tfib_lib_contract_x_all, are not carried here) at origin/ossv/recipes
   6ebe35ba632, with their module paths changed (h-small-a3). rule 24 (reuse): no function is proved here;
   this file states the three ASan-level contracts only.

   THE QDISC CHANGES, and why each one is there.
   - knock's three callees (reac_knock_init / _heard / _step) write a 40-byte struct in the caller's fake
     frame; qdisc's two callees (reac_qdisc_etf_catchup_slots, check_slots) are register-only leaves that
     write nothing but check_slots' own return-address slot. So kn_post_* 's object clause (obj_at) and
     its FOUR memory conjuncts -- the stack side above alloc_ceiling outside the callee's window, the live
     blocks, the frames and their shadow, and the image -- are replaced by ONE memory clause,
     `aview W2 mem2 a = aview W memc a` outside [sp - STK_f, sp), which implies all four and needs no
     object. Its proof needs no block, separation or frame law of AR either (knock's four conjuncts needed
     AR's block and separation facts to place the object): check_slots' walk takes from the caller's
     journal only its stack-presence clause (`forall a, sp0 - STK <= a < sp0 -> apresent ..`) and astk_ok
     (sp0's alignment and bounds), with the contract's two stack-window premises. Both posts state the
     clause in that same shape, so the text does not depend on
     the value of either STK_f. T_slots_STK is 0 (the leaf has no frame: `addi a2,zero,1` is its first
     instruction in both images, image A 0x7e94c and image B 0x7e984, no sp move; at 0 the excluded window
     is empty and the clause holds at every address), T_check_STK is 16 (image A 0x7e870 and image B
     0x7e8a4 `addi sp,sp,-0x10`, then `sd ra,8(sp)`).
   - both leaves divide by 10^6 with the 8-byte constant 0x431BDE82D7B634DB = ceil(2 ^ 82 / 10 ^ 6)
     (lib/Prog/qdisc_div.v:7-10). The load is NOT shadow-checked in either image (image A
     `auipc a1,0xfff92` 0x7e8b4 + `ld a1,-0x564(a1)` 0x7e8b8 -> 0x10350, and the same cell 0x10350 in the
     asan-ubsan image from 0x7e8e8 / -0x598; capstone 5.0.7 over the pinned bytes). The cell is .rodata, so
     its value is not derivable from an abstract `segs`: the contract takes its ADDRESS as a parameter `am`
     and its value as the premise `val_mem segs .. am 8 QD_MAGIC`. Each image discharges that premise from
     its own read-only-data fact. The constant is image-shared: the 8 bytes at 0x10350 are
     0x431BDE82D7B634DB in both fuzz_qdisc.asan (980e2b845852) and fuzz_qdisc.asan-ubsan (eb657d77bd4b),
     read out of the pinned files by this lane and checked independently by h-small-a3; only `am` could
     differ between images (here both load 0x10350).
   - the result: catchup's post pins a0 to slots_spec (lib/Prog/qdisc_spec.v:8-11, the C source's
     slots_of); check_slots returns void, and its contract's content is that it RETURNS -- its abort
     (the abort call at image A 0x7e8dc, reached only from `bne a0,a3` at 0x7e8cc) is
     unreachable when a0 is slots_spec of the same (lead, fps). That is the harness's property.
   - the harness contract is ACfn's text with knock's names changed and its read-only premise written over
     lib/A/QPgBase.v's image-independent in_roP / arodata_okP, so that image B instantiates the same text.

   IMAGE-INDEPENDENT: this file Requires no image module. `segs`, the symbol record `B`, the meter `MT`,
   the sink `K`, the entry addresses and the harness constants are all Section variables or parameters. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCSpec.v, with its module paths and module names changed; 6 of its 69 lines of code are new or changed and 64 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths and module names changed; 220 of its 247 lines of code are new or changed and 42 lines of the source are left out. *)
(* The A-level contracts of the checking and text functions of fuzz_codec: the harness's check_refusal,
   check_range, check_bytes, check_text_masks, check_text_seg7, check_personality, check_text_scribble,
   check_text_counter, owed_seg7, owed_counter_text and text_arg, and the library's
   diginet_personality_from_name, diginet_scribble_text and diginet_counter_text.

   The content of a check_* contract is that it RETURNS: the call of abort each one guards is not reached
   when the plain agreement its premise names holds (lib/Prog/codec_agree.v, codec_owe.v, codec_text.v).
   The other six state the plain result of lib/Spec/DgnLib.v / lib/Prog/codec_owe.v unchanged.

   IMAGE-INDEPENDENT: the entry addresses, the addresses of the tables and of the string literals these
   functions read, and the image's read-only window are Section variables, so image B takes the same
   texts with its own constants.

   Side-stack frames: check_text_scribble takes one of class 0, diginet_counter_text and
   owed_counter_text one of class 1, check_text_counter one of class 0 and then calls two functions that
   each take one of class 1. Each of those contracts carries the room its chain needs
   (lib/A/Prog/sb_dec.v's form in the released fuzz_identity tree). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
(* The image's read-only window, the tables these functions read, and the ranges of the .rodata string
   literals they reach: the glyph strings of owed_seg7 and the announce names and name literals of
   diginet_personality_from_name and check_personality. *)
Variables RLO RHI : Z.
Variables SEG7TBL GLYPHA PERSA : Z.
Variable ROSTRS : list (Z * Z).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T :=
  (cdc_entry segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T).
Local Notation POST STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R :=
  (cdc_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R).
(* A call whose whole content is that it returns. *)
Local Notation RETURNS := (fun (_ : world segs) (_ : word -> option byte) (_ : bvmap 5 word) => True).

(* ================================ the three record checks ================================
   Each is called with a0 = &k, the 184-byte call record of fuzz_codec.c:74-90. *)

(* check_refusal (fuzz_codec.c:283-291; image A 0x844dc, 45 instructions, frame 16, no call): it reads
   kind, b and rc with lw and returns without calling abort when the record is not a refused SYSEX. *)
Definition cdc_check_refusal_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (kc : kcallZ),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_refusal ->
getr regs 10 = w64 q ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) T_check_refusal q 184 ->
~ (kz_kind kc = 11 /\ kz_b kc = 0x70 /\ kz_rc kc = 0) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_refusal cno_wr lyc Sc W memc mdc RETURNS).

(* check_range (fuzz_codec.c:293-314; image A 0x84590, 44 instructions, frame 32, bcmp wrapper at
   0x845dc): it returns without calling abort when a failed call left the 32 bytes of out as they were
   and the return code is the owed one. *)
Definition cdc_check_range_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (kc : kcallZ),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_range ->
getr regs 10 = w64 q ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) T_check_range q 184 ->
(kz_rc kc <> 0 -> kz_out kc = kz_before kc) ->
kz_rc kc = kz_want_rc kc ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_range cno_wr lyc Sc W memc mdc RETURNS).

(* check_bytes (fuzz_codec.c:316-344; image A 0x84640, 77 instructions, frame 32, bcmp wrapper at
   0x8469c): it compares out.len with want_len, out.bytes with want over out.len bytes, out.key with
   want_key and out.display with want_display, and returns when all four agree. *)
Definition cdc_check_bytes_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (kc : kcallZ),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_bytes ->
getr regs 10 = w64 q ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) T_check_bytes q 184 ->
kz_want_len kc = cmd_lenZ (kz_out kc) ->
kz_want_len kc <= 24 ->
firstn (Z.to_nat (kz_want_len kc)) (kz_out kc) = firstn (Z.to_nat (kz_want_len kc)) (kz_want kc) ->
cmd_keyZ (kz_out kc) = kz_want_key kc ->
cmd_displayZ (kz_out kc) = kz_want_display kc ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_bytes cno_wr lyc Sc W memc mdc RETURNS).

(* ================================ the agreement checks ================================ *)

(* check_text_masks (fuzz_codec.c:492-519; image A 0x842b0, 55 instructions, frame 48; calls the four
   frameless leaves diginet_meter_mask, diginet_meter_segments, diginet_ring_dot, diginet_ring_fill):
   a0 = n (an unsigned composed with slliw, so sign-extended), a1 = the mask (uint16_t). It returns
   without calling abort when the four library values are the owed ones. *)
Definition cdc_check_masks_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n mask : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_masks ->
arg_u32A (getr regs 10) n -> arg_zxA 16 (getr regs 11) mask ->
meter_mask_spec n = owed_meter_mask n ->
meter_segments_spec mask = spec_segments_spec mask ->
ring_dot_spec n = owed_ring_dot n ->
ring_fill_spec n = owed_ring_fill n ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_masks cno_wr lyc Sc W memc mdc RETURNS).

(* check_text_seg7 (fuzz_codec.c:454-466; image A 0x83ae4, 30 instructions, frame 48; calls diginet_seg7
   and owed_seg7 for every character): no arguments. It reads the table diginet_seg7 switches on, the
   glyph table owed_seg7 walks and the glyph strings; it returns without calling abort when the two
   agree on every character. *)
Definition cdc_check_seg7_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_seg7 ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_check_seg7
  ((SEG7TBL, 364) :: (GLYPHA, 464) :: ROSTRS) ->
(forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_seg7 cno_wr lyc Sc W memc mdc RETURNS).

(* check_personality (fuzz_codec.c:256-281; image A 0x83364, 156 instructions, frame 32; calls
   diginet_personality_of three times, the strcmp wrapper twice and diginet_personality_from_name five
   times): no arguments. Everything it compares is image data -- the two personalities, the five string
   literals it passes and the two announce names they point at -- so its only premises are that those
   bytes are the image's and are marked usable. *)
Definition cdc_check_pers_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_pers ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_check_pers ((PERSA, 48) :: ROSTRS) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_pers cno_wr lyc Sc W memc mdc RETURNS).

(* ============================== the library's name and text code ============================== *)

(* diginet_personality_from_name (diginet_codec.c:17-25; image A 0x847dc, 43 instructions, frame 48,
   strcmp wrapper at 0x84844): a0 is a C string; it compares that string with the announce names the two
   personalities point at and returns the address of the personality that matches, or 0. *)
Definition cdc_from_name_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (tb : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_from_name ->
getr regs 10 = w64 q ->
cstr_rd segs W memc (spZ regs) T_from_name q tb ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_from_name ((PERSA, 48) :: ROSTRS) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_from_name cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (from_name_resA PERSA tb))).

(* owed_seg7 (fuzz_codec.c:372-395; image A 0x8438c, 84 instructions, frame 16, no call): a0 is an
   unsigned char; it walks the glyph table and its strings and returns the owed segments. Its
   case-folding test is exact only for a byte, which is the plain premise 0 <= c < 256. *)
Definition cdc_owed_seg7_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_owed_seg7 ->
getr regs 10 = w64 c -> 0 <= c < 256 ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_owed_seg7 ((GLYPHA, 464) :: ROSTRS) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_owed_seg7 cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (owed_seg7_spec c))).

(* diginet_scribble_text (diginet_codec.c:267-285; image A 0x85cc4, 88 instructions, frame 16,
   __asan_memset at 0x85df0): a0 = the text, a1 = the output characters, a2 = their number n. It writes
   exactly out[0..n) and returns the number of text bytes it used. *)
Definition cdc_scribble_text_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q o n : Z) (tb oj : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_scribble_text ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) T_scribble_text q tb ->
getr regs 11 = w64 o -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 /\ n = Z.of_nat (length oj) ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_scribble_text o n ->
garr8 segs (rd W memc) o oj ->
(q + Z.of_nat (length tb) <= o \/ o + n <= q) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_scribble_text (fun x => o <= x < o + n) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     getr regs2 10 = w64 (snd (scribble_text_spec tb n)) /\
     garr8 segs (rd W2 mem2) o (fst (scribble_text_spec tb n)))).

(* diginet_counter_text (diginet_codec.c:337-369; image A 0x86120, 314 instructions, real frame 160 and a
   side-stack frame of class 1 taken at 0x86194, __asan_memset at 0x86254, diginet_seg7 at 0x862e0):
   a0 = the text, a1 = the eight segment bytes, a2 = the dots byte. On success the segments and the dots
   are the spec's; on failure it has written at most those nine bytes. It takes its frame and writes the
   frame's header and shadow before it reads the text, so the text may not be a byte of the runtime's own
   (a free frame is one). *)
Definition cdc_counter_text_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q sg dt : Z) (tb sj : list Z) (dj : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter_text ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) T_counter_text q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc sg 8 -> cobj_ok B lyc Sc dt 1 ->
getr regs 11 = w64 sg ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_counter_text sg 8 ->
garr8 segs (rd W memc) sg sj -> length sj = 8%nat ->
getr regs 12 = w64 dt ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_counter_text dt 1 ->
val_mem segs (rd W memc) dt 1 dj ->
(sg + 8 <= dt \/ dt + 1 <= sg) ->
(q + Z.of_nat (length tb) <= sg \/ sg + 8 <= q) ->
(q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_counter_text [(SEG7TBL, 364)] ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_counter_text
  (fun x => sg <= x < sg + 8 \/ dt <= x < dt + 1) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     let '(r, s, d) := counter_text_spec tb in
     getr regs2 10 = w64 r /\
     (r = 0 -> garr8 segs (rd W2 mem2) sg s /\ val_mem segs (rd W2 mem2) dt 1 d) /\
     (r <> 0 -> exists s' d', garr8 segs (rd W2 mem2) sg s' /\ length s' = 8%nat /\
                              val_mem segs (rd W2 mem2) dt 1 d'))).

(* owed_counter_text (fuzz_codec.c:402-429; image A 0x83df8, 302 instructions, real frame 160 and a
   side-stack frame of class 1 taken at 0x83e6c, __asan_memset at 0x83f38, owed_seg7 at 0x83f9c): the
   same shape with the owed result. a2 = the dots byte, in the caller's side-stack frame (the entry
   function's F + 432) or on the caller's machine stack (check_text_counter's own byte at its realigned
   sp + 55). *)
Definition cdc_owed_counter_text_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q sg dt : Z) (tb sj : list Z) (dj : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_owed_counter_text ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) T_owed_counter_text q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc sg 8 ->
getr regs 11 = w64 sg ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_owed_counter_text sg 8 ->
garr8 segs (rd W memc) sg sj -> length sj = 8%nat ->
getr regs 12 = w64 dt ->
((cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_owed_counter_text dt 1 /\
  cobj_ok B lyc Sc dt 1) \/
 cdstk_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_owed_counter_text dt 1) ->
val_mem segs (rd W memc) dt 1 dj ->
(sg + 8 <= dt \/ dt + 1 <= sg) ->
(q + Z.of_nat (length tb) <= sg \/ sg + 8 <= q) ->
(q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_owed_counter_text ((GLYPHA, 464) :: ROSTRS) ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_owed_counter_text
  (fun x => sg <= x < sg + 8 \/ dt <= x < dt + 1) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     let '(r, s, d) := owed_counter_text_spec tb in
     getr regs2 10 = w64 r /\
     (r = 0 -> garr8 segs (rd W2 mem2) sg s /\ val_mem segs (rd W2 mem2) dt 1 d) /\
     (r <> 0 -> exists s' d', garr8 segs (rd W2 mem2) sg s' /\ length s' = 8%nat /\
                              val_mem segs (rd W2 mem2) dt 1 d'))).

(* ============================ the two text agreement checks ============================ *)

(* check_text_scribble (fuzz_codec.c:431-452; image A 0x83798, 211 instructions, real frame 128 and a
   side-stack frame of class 0 taken at 0x83808, __asan_memset twice, diginet_scribble_text at 0x839b4,
   bcmp wrapper at 0x839c8): a0 = the text, a1 = the 24 character bytes of the record, a2 = n, the
   personality's scribble_chars. It returns without calling abort when the library text and the owed text
   agree, and leaves the 24 bytes as scribble_bytes says. *)
Definition cdc_check_text_scribble_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q ch n : Z) (tb cj : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_scribble ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) T_check_text_scribble q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc ch 24 ->
getr regs 11 = w64 ch ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_scribble ch 24 ->
garr8 segs (rd W memc) ch cj -> length cj = 24%nat ->
getr regs 12 = w64 n -> 0 <= n <= 8 ->
(q + Z.of_nat (length tb) <= ch \/ ch + 24 <= q) ->
owed_scribble_text_spec tb n = scribble_text_spec tb n ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_text_scribble
  (fun x => ch <= x < ch + 24) lyc Sc W memc mdc
  (fun W2 mem2 regs2 => garr8 segs (rd W2 mem2) ch (scribble_bytes tb n))).

(* check_text_counter (fuzz_codec.c:468-490; image A 0x83b5c, 167 instructions, real frame 160 and a
   side-stack frame of class 0 taken at 0x83bd0; calls owed_counter_text at 0x83c70, __asan_memset at
   0x83c88, diginet_counter_text at 0x83cac and the bcmp wrapper at 0x83cc4): a0 = the text, a1 = the 24
   byte array of the record, a2 = the dots byte. It returns without calling abort when the library text
   and the owed text agree, and leaves the sixteen bytes after the digits as the memset wrote them.
   Its two text callees each take a frame of class 1, so the room it asks for leaves two free. *)
Definition cdc_check_text_counter_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q sg dt : Z) (tb sj : list Z) (dj : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_check_text_counter ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) T_check_text_counter q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc sg 24 -> cobj_ok B lyc Sc dt 1 ->
getr regs 11 = w64 sg ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_counter sg 24 ->
garr8 segs (rd W memc) sg sj -> length sj = 24%nat ->
getr regs 12 = w64 dt ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_check_text_counter dt 1 ->
val_mem segs (rd W memc) dt 1 dj ->
(sg + 24 <= dt \/ dt + 1 <= sg) ->
(q + Z.of_nat (length tb) <= sg \/ sg + 24 <= q) ->
(q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) ->
cimg_rd segs B RLO RHI W memc (spZ regs) T_check_text_counter
  ((SEG7TBL, 364) :: (GLYPHA, 464) :: ROSTRS) ->
(let '(r1, s1, d1) := counter_text_spec tb in
 let '(r2, s2, d2) := owed_counter_text_spec tb in
 r1 = r2 /\ (r1 = 0 -> s1 = s2 /\ d1 = d2)) ->
Z.of_nat (length (frames Sc)) <= 6 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_check_text_counter
  (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     exists s' d', garr8 segs (rd W2 mem2) sg (s' ++ repeat 0xa5 16) /\ length s' = 8%nat /\
                   val_mem segs (rd W2 mem2) dt 1 d')).

(* ====================================== text_arg ======================================
   text_arg (fuzz_codec.c:523-529; image A 0x835d4, 113 instructions, frame 32, __asan_memcpy at
   0x8370c): a0 = &in, the cursor struct on the harness's own machine stack (p at in, n at in + 8),
   a1 = the 65-byte text buffer. It takes a uint16 length from the cursor bytes, copies that many bytes
   to the buffer, puts the 0 after them and advances the cursor. *)
Definition cdc_text_arg_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(ip tx p : Z) (data tj : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_text_arg ->
getr regs 10 = w64 ip ->
cdstk_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_text_arg ip 16 ->
val_mem segs (rd W memc) ip 8 p -> val_mem segs (rd W memc) (ip + 8) 8 (Z.of_nat (length data)) ->
0 <= p -> p + Z.of_nat (length data) <= 2 ^ 63 ->
garr8 segs (rd W memc) p data ->
crd_ok segs W memc (spZ regs) T_text_arg p (Z.of_nat (length data)) ->
getr regs 11 = w64 tx ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_text_arg tx 65 ->
garr8 segs (rd W memc) tx tj -> length tj = 65%nat ->
(ip + 16 <= tx \/ tx + 65 <= ip) ->
(p + Z.of_nat (length data) <= tx \/ tx + 65 <= p) ->
(p + Z.of_nat (length data) <= ip \/ ip + 16 <= p) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_text_arg
  (fun x => ip <= x < ip + 16 \/ tx <= x < tx + 65) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     val_mem segs (rd W2 mem2) ip 8 (p + Z.of_nat (text_usedZ data)) /\
     val_mem segs (rd W2 mem2) (ip + 8) 8 (Z.of_nat (length data - text_usedZ data)) /\
     garr8 segs (rd W2 mem2) tx
       (text_takenZ data ++ [0] ++ skipn (1 + text_lenZ data)%nat tj))).
End d.
End c.
End b.
