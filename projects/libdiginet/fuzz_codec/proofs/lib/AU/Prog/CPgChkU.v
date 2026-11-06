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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths and module names changed; 241 of its 268 lines of code are new or changed and 42 lines of the source are left out. *)
(* The image-B contracts of the checking and text functions of fuzz_codec: the harness's check_refusal,
   check_range, check_bytes, check_text_masks, check_text_seg7, check_personality, check_text_scribble,
   check_text_counter, owed_seg7, owed_counter_text, owe_sysex and text_arg, and the library's
   diginet_personality_from_name, diginet_scribble_text and diginet_counter_text.

   The texts are the image-A ones of lib/A/Prog/CPgChkC.v with image B's stack constants
   (lib/AU/Prog/CPgBaseU.v) and what image B adds:
   - owe_sysex is a function of its own at image B (at image A it is inlined into the entry function);
   - the UBSan check of the call record pointer k traps on a record that is not 8-aligned, so
     owe_sysex and the three record checks carry `q mod 8 = 0`, and text_arg carries the same of its
     cursor and `0 < p` (lib/U/Prog/*_c.v ask for the same);
   - diginet_scribble_text makes no call at image B, so its window is its own frame only;
   - the functions that take a side-stack frame carry the one-object premise `cobj_ok` for the caller
     objects they read or write, as at image A.
   The content of a check_* contract is still that it RETURNS, and the other contracts state the plain
   result of lib/Spec/DgnLib.v / lib/Prog/codec_owe.v unchanged. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU.
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
Variables RLO RHI : Z.
Variables SEG7TBL GLYPHA PERSA : Z.
Variable ROSTRS : list (Z * Z).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T :=
  (cdc_entry segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T).
Local Notation POST STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R :=
  (cdc_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R).
Local Notation RETURNS := (fun (_ : world segs) (_ : word -> option byte) (_ : bvmap 5 word) => True).

(* ================================ the three record checks ================================ *)

(* check_refusal (image B 0x84bc4, 48 instructions, frame 16, no call). *)
Definition cdcU_check_refusal_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (kc : kcallZ),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_refusal ->
getr regs 10 = w64 q -> q mod 8 = 0 ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) TB_check_refusal q 184 ->
~ (kz_kind kc = 11 /\ kz_b kc = 0x70 /\ kz_rc kc = 0) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_refusal cno_wr lyc Sc W memc mdc RETURNS).

(* check_range (image B 0x84c84, 47 instructions, frame 32, compare wrapper at 0x84cd8). *)
Definition cdcU_check_range_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (kc : kcallZ),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_range ->
getr regs 10 = w64 q -> q mod 8 = 0 ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) TB_check_range q 184 ->
(kz_rc kc <> 0 -> kz_out kc = kz_before kc) ->
kz_rc kc = kz_want_rc kc ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_range cno_wr lyc Sc W memc mdc RETURNS).

(* check_bytes (image B 0x84d40, 83 instructions, frame 32, compare wrapper at 0x84da4). *)
Definition cdcU_check_bytes_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (kc : kcallZ),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_bytes ->
getr regs 10 = w64 q -> q mod 8 = 0 ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) TB_check_bytes q 184 ->
kz_want_len kc = cmd_lenZ (kz_out kc) ->
kz_want_len kc <= 24 ->
firstn (Z.to_nat (kz_want_len kc)) (kz_out kc) = firstn (Z.to_nat (kz_want_len kc)) (kz_want kc) ->
cmd_keyZ (kz_out kc) = kz_want_key kc ->
cmd_displayZ (kz_out kc) = kz_want_display kc ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_bytes cno_wr lyc Sc W memc mdc RETURNS).

(* ================================ the agreement checks ================================ *)

(* check_text_masks (image B 0x84974, 56 instructions, frame 48; the four frameless leaves). *)
Definition cdcU_check_masks_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n mask : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_masks ->
arg_u32A (getr regs 10) n -> arg_zxA 16 (getr regs 11) mask ->
meter_mask_spec n = owed_meter_mask n ->
meter_segments_spec mask = spec_segments_spec mask ->
ring_dot_spec n = owed_ring_dot n ->
ring_fill_spec n = owed_ring_fill n ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_masks cno_wr lyc Sc W memc mdc RETURNS).

(* check_text_seg7 (image B 0x84148, 31 instructions, frame 48; diginet_seg7 and owed_seg7). *)
Definition cdcU_check_seg7_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_seg7 ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_check_seg7
  ((SEG7TBL, 364) :: (GLYPHA, 464) :: ROSTRS) ->
(forall c, 0 <= c < 256 -> seg7_spec c = owed_seg7_spec c) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_seg7 cno_wr lyc Sc W memc mdc RETURNS).

(* check_personality (image B 0x8391c, 161 instructions, frame 32; diginet_personality_of three times,
   the string-compare wrapper twice, diginet_personality_from_name five times). *)
Definition cdcU_check_pers_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_pers ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_check_pers ((PERSA, 48) :: ROSTRS) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_pers cno_wr lyc Sc W memc mdc RETURNS).

(* ============================== the library's name and text code ============================== *)

(* diginet_personality_from_name (image B 0x85090, 43 instructions, frame 48, string-compare wrapper at
   0x850f8). *)
Definition cdcU_from_name_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (tb : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_from_name ->
getr regs 10 = w64 q ->
cstr_rd segs W memc (spZ regs) TB_from_name q tb ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_from_name ((PERSA, 48) :: ROSTRS) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_from_name cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (from_name_resA PERSA tb))).

(* owed_seg7 (image B 0x84a54, 92 instructions, frame 16, no call). *)
Definition cdcU_owed_seg7_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_owed_seg7 ->
getr regs 10 = w64 c -> 0 <= c < 256 ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_owed_seg7 ((GLYPHA, 464) :: ROSTRS) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_owed_seg7 cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (owed_seg7_spec c))).

(* owe_sysex (fuzz_codec.c:101-111; image B 0x84e8c, 103 instructions, frame 48, __asan_memcpy at
   0x84f3c): a0 = the call record, a1 = device, a2 = fn (both uint8_t), a3 = the payload, a4 = its
   length. It writes the record's want, want_len and want_display and nothing else; the write set names
   the 40 bytes from want to the end of the record, want_key among them, which it leaves as it was. It
   calls __asan_memcpy also for an empty payload, so the payload's read premise holds at every length.
   The UBSan check of k at its first access traps on a record that is not 8-aligned. *)
Definition cdcU_owe_sysex_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q dev fn pl n : Z) (kc : kcallZ) (bs : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_owe_sysex ->
getr regs 10 = w64 q -> q mod 8 = 0 ->
kcall_atA segs W memc q kc -> kcall_wfZ kc ->
crd_ok segs W memc (spZ regs) TB_owe_sysex q 184 ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_owe_sysex (q + 144) 40 ->
arg_zxA 8 (getr regs 11) dev -> arg_zxA 8 (getr regs 12) fn ->
getr regs 13 = w64 pl -> getr regs 14 = w64 n ->
n = Z.of_nat (length bs) -> (length bs <= 19)%nat ->
crd_ok segs W memc (spZ regs) TB_owe_sysex pl n ->
(0 < n -> 0 < pl /\ garr8 segs (rd W memc) pl bs /\ (pl + n <= q + 144 \/ q + 184 <= pl)) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_owe_sysex
  (fun x => q + 144 <= x < q + 184) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     let '(w, dp) := owe_sx dev fn bs in
     kcall_atA segs W2 mem2 q
       (set_wantZ kc (w ++ skipn (length w) (kz_want kc)) (Z.of_nat (length w)) dp))).

(* diginet_scribble_text (image B 0x86500, 113 instructions, frame 16, no call: the padding is stored in
   line at image B). *)
Definition cdcU_scribble_text_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q o n : Z) (tb oj : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_scribble_text ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) TB_scribble_text q tb ->
getr regs 11 = w64 o -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 /\ n = Z.of_nat (length oj) ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_scribble_text o n ->
garr8 segs (rd W memc) o oj ->
(q + Z.of_nat (length tb) <= o \/ o + n <= q) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_scribble_text (fun x => o <= x < o + n) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     getr regs2 10 = w64 (snd (scribble_text_spec tb n)) /\
     garr8 segs (rd W2 mem2) o (fst (scribble_text_spec tb n)))).

(* diginet_counter_text (image B 0x869e4, 320 instructions, real frame 192, frame request of class 1 at
   0x86a58, __asan_memset at 0x86b18, diginet_seg7 at 0x86bbc). *)
Definition cdcU_counter_text_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q sg dt : Z) (tb sj : list Z) (dj : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_counter_text ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) TB_counter_text q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc sg 8 -> cobj_ok B lyc Sc dt 1 ->
getr regs 11 = w64 sg ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_counter_text sg 8 ->
garr8 segs (rd W memc) sg sj -> length sj = 8%nat ->
getr regs 12 = w64 dt ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_counter_text dt 1 ->
val_mem segs (rd W memc) dt 1 dj ->
(sg + 8 <= dt \/ dt + 1 <= sg) ->
(q + Z.of_nat (length tb) <= sg \/ sg + 8 <= q) ->
(q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_counter_text [(SEG7TBL, 364)] ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_counter_text
  (fun x => sg <= x < sg + 8 \/ dt <= x < dt + 1) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     let '(r, s, d) := counter_text_spec tb in
     getr regs2 10 = w64 r /\
     (r = 0 -> garr8 segs (rd W2 mem2) sg s /\ val_mem segs (rd W2 mem2) dt 1 d) /\
     (r <> 0 -> exists s' d', garr8 segs (rd W2 mem2) sg s' /\ length s' = 8%nat /\
                              val_mem segs (rd W2 mem2) dt 1 d'))).

(* owed_counter_text (image B 0x84474, 320 instructions, real frame 192, frame request of class 1 at
   0x844e8, __asan_memset at 0x845b4, owed_seg7 at 0x84630). Its dots byte comes from the entry
   function's own frame, or from check_text_counter's machine stack. *)
Definition cdcU_owed_counter_text_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q sg dt : Z) (tb sj : list Z) (dj : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_owed_counter_text ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) TB_owed_counter_text q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc sg 8 ->
getr regs 11 = w64 sg ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_owed_counter_text sg 8 ->
garr8 segs (rd W memc) sg sj -> length sj = 8%nat ->
getr regs 12 = w64 dt ->
((cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_owed_counter_text dt 1 /\
  cobj_ok B lyc Sc dt 1) \/
 cdstk_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_owed_counter_text dt 1) ->
val_mem segs (rd W memc) dt 1 dj ->
(sg + 8 <= dt \/ dt + 1 <= sg) ->
(q + Z.of_nat (length tb) <= sg \/ sg + 8 <= q) ->
(q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_owed_counter_text ((GLYPHA, 464) :: ROSTRS) ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_owed_counter_text
  (fun x => sg <= x < sg + 8 \/ dt <= x < dt + 1) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     let '(r, s, d) := owed_counter_text_spec tb in
     getr regs2 10 = w64 r /\
     (r = 0 -> garr8 segs (rd W2 mem2) sg s /\ val_mem segs (rd W2 mem2) dt 1 d) /\
     (r <> 0 -> exists s' d', garr8 segs (rd W2 mem2) sg s' /\ length s' = 8%nat /\
                              val_mem segs (rd W2 mem2) dt 1 d'))).

(* ============================ the two text agreement checks ============================ *)

(* check_text_scribble (image B 0x83dbc, 227 instructions, real frame 128, frame request of class 0 at
   0x83e2c, __asan_memset at 0x84000, diginet_scribble_text at 0x84010, compare wrapper at 0x84024). *)
Definition cdcU_check_text_scribble_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q ch n : Z) (tb cj : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_text_scribble ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) TB_check_text_scribble q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc ch 24 ->
getr regs 11 = w64 ch ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_check_text_scribble ch 24 ->
garr8 segs (rd W memc) ch cj -> length cj = 24%nat ->
getr regs 12 = w64 n -> 0 <= n <= 8 ->
(q + Z.of_nat (length tb) <= ch \/ ch + 24 <= q) ->
owed_scribble_text_spec tb n = scribble_text_spec tb n ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_text_scribble
  (fun x => ch <= x < ch + 24) lyc Sc W memc mdc
  (fun W2 mem2 regs2 => garr8 segs (rd W2 mem2) ch (scribble_bytes tb n))).

(* check_text_counter (image B 0x841c4, 172 instructions, real frame 160, frame request of class 0 at
   0x84238; owed_counter_text at 0x842d8, __asan_memset at 0x842f0, diginet_counter_text at 0x84314, the
   compare wrapper at 0x8432c). Its two text callees each take a frame of class 1. *)
Definition cdcU_check_text_counter_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(q sg dt : Z) (tb sj : list Z) (dj : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_text_counter ->
getr regs 10 = w64 q -> cstr_rd segs W memc (spZ regs) TB_check_text_counter q tb ->
cobj_ok B lyc Sc q (Z.of_nat (length tb)) -> cobj_ok B lyc Sc sg 24 -> cobj_ok B lyc Sc dt 1 ->
getr regs 11 = w64 sg ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_check_text_counter sg 24 ->
garr8 segs (rd W memc) sg sj -> length sj = 24%nat ->
getr regs 12 = w64 dt ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_check_text_counter dt 1 ->
val_mem segs (rd W memc) dt 1 dj ->
(sg + 24 <= dt \/ dt + 1 <= sg) ->
(q + Z.of_nat (length tb) <= sg \/ sg + 24 <= q) ->
(q + Z.of_nat (length tb) <= dt \/ dt + 1 <= q) ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_check_text_counter
  ((SEG7TBL, 364) :: (GLYPHA, 464) :: ROSTRS) ->
(let '(r1, s1, d1) := counter_text_spec tb in
 let '(r2, s2, d2) := owed_counter_text_spec tb in
 r1 = r2 /\ (r1 = 0 -> s1 = s2 /\ d1 = d2)) ->
Z.of_nat (length (frames Sc)) <= 6 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_check_text_counter
  (fun x => sg <= x < sg + 24 \/ dt <= x < dt + 1) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     exists s' d', garr8 segs (rd W2 mem2) sg (s' ++ repeat 0xa5 16) /\ length s' = 8%nat /\
                   val_mem segs (rd W2 mem2) dt 1 d')).

(* ====================================== text_arg ======================================
   text_arg (image B 0x83ba0, 135 instructions, frame 32, __asan_memcpy at 0x83d14). The UBSan checks of
   its cursor trap on a cursor that is not 8-aligned and on a NULL input pointer with bytes left (image B
   0x83c14), so it carries `ip mod 8 = 0` and `0 < p` (lib/U/Prog/text_arg_c.v asks for the same). *)
Definition cdcU_text_arg_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(ip tx p : Z) (data tj : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_text_arg ->
getr regs 10 = w64 ip -> ip mod 8 = 0 ->
cdstk_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_text_arg ip 16 ->
val_mem segs (rd W memc) ip 8 p -> val_mem segs (rd W memc) (ip + 8) 8 (Z.of_nat (length data)) ->
0 < p -> p + Z.of_nat (length data) <= 2 ^ 63 ->
garr8 segs (rd W memc) p data ->
crd_ok segs W memc (spZ regs) TB_text_arg p (Z.of_nat (length data)) ->
getr regs 11 = w64 tx ->
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_text_arg tx 65 ->
garr8 segs (rd W memc) tx tj -> length tj = 65%nat ->
(ip + 16 <= tx \/ tx + 65 <= ip) ->
(p + Z.of_nat (length data) <= tx \/ tx + 65 <= p) ->
(p + Z.of_nat (length data) <= ip \/ ip + 16 <= p) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_text_arg
  (fun x => ip <= x < ip + 16 \/ tx <= x < tx + 65) lyc Sc W memc mdc
  (fun W2 mem2 regs2 =>
     val_mem segs (rd W2 mem2) ip 8 (p + Z.of_nat (text_usedZ data)) /\
     val_mem segs (rd W2 mem2) (ip + 8) 8 (Z.of_nat (length data - text_usedZ data)) /\
     garr8 segs (rd W2 mem2) tx
       (text_takenZ data ++ [0] ++ skipn (1 + text_lenZ data)%nat tj))).
End d.
End c.
End b.
