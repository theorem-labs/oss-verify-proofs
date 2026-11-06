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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v, with its module paths and module names changed; 231 of its 258 lines of code are new or changed and 42 lines of the source are left out. *)
(* The image-B contracts of the encoders of fuzz_codec's library code and of the leaves they share:
   diginet_personality_of, diginet_ring_dot, diginet_ring_fill, diginet_meter_mask,
   diginet_meter_segments, diginet_seg7, the twelve encoders, and leds_encode, which is a function of its
   own at image B (at image A it is inlined into the two leds encoders).

   The texts are the image-A ones of lib/A/Prog/CPgEncC.v with image B's stack constants
   (lib/AU/Prog/CPgBaseU.v) and the three things image B adds:
   - the UBSan check of the 4-byte store of out->key traps on a destination that is not 4-aligned, so
     every encoder carries `out mod 4 = 0` (the plain UBSan contracts lib/U/Prog/*_c.v ask for the same);
   - diginet_ring_encode, diginet_meter_encode, leds_encode and diginet_counter_encode call
     diginet_sysex_encode and take a side-stack frame of class 0 for the payload, so they carry frame
     room and the one-object premise `cobj_ok` for the caller objects they read or write, exactly as
     diginet_scribble_encode does at image A;
   - diginet_strip_leds_encode and diginet_counter_leds_encode tail-call leds_encode, so a frame is
     requested inside their call too, and they carry the same two;
   - the UBSan check of the personality pointer traps on one that is not 8-aligned (image B 0x85428,
     0x8575c, 0x85930, 0x85d2c, 0x860b0, 0x86370, 0x861e8, 0x864a8, 0x86818, 0x8700c), so every encoder
     that takes a personality carries `p mod 8 = 0` (lib/U/Prog/codec_cells.v pers_arg asks for the
     same; NULL is 0 and meets it).
   The Gallina result each contract states is the plain one, unchanged (lib/Spec/DgnSpec.v, DgnLib.v).

   IMAGE-INDEPENDENT in the same way as the image-A file: the entry addresses and the table addresses are
   Section variables, instantiated at image B's constants by the closing. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
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
(* image B's read-only window and the address of the table diginet_seg7 switches on *)
Variables RLO RHI : Z.
Variable SEG7TBL : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T :=
  (cdc_entry segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T).
Local Notation POST STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R :=
  (cdc_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R).
Local Notation OUT STK sp0 FP ly S lyc Sc own W memc sp T out before :=
  (cenc_out segs B STK sp0 FP ly S lyc Sc own W memc sp T out before).

(* =============================== the register-only leaves ===============================
   Image B's are image A's with its own addresses; diginet_personality_of grew three instructions for
   the UBSan check of its comparison, and reads no memory either. *)

Definition cdcU_pers_of_specX (a PERSA : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (d : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_pers_of ->
getr regs 10 = w64 d -> 0 <= d < 2 ^ 64 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_pers_of cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (pers_ofA PERSA d))).

Definition cdcU_ring_dot_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_ring_dot ->
arg_u32A (getr regs 10) n ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_ring_dot cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (ring_dot_spec n))).

Definition cdcU_ring_fill_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_ring_fill ->
arg_u32A (getr regs 10) n ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_ring_fill cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (ring_fill_spec n))).

Definition cdcU_meter_mask_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_meter_mask ->
arg_u32A (getr regs 10) s ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_meter_mask cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (meter_mask_spec s))).

Definition cdcU_meter_segs_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (mask : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_meter_segs ->
arg_zxA 16 (getr regs 10) mask ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_meter_segs cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (meter_segments_spec mask))).

(* diginet_seg7 (image B 0x86978, 27 instructions, frame 16): one word of the 364-byte table the
   compiler made for its switch (image B 0x21400), and no store. *)
Definition cdcU_seg7_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_seg7 ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
cimg_rd segs B RLO RHI W memc (spZ regs) TB_seg7 [(SEG7TBL, 364)] ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_seg7 cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (seg7_spec (c mod 256)))).

(* ============================ the encoders that take no frame ============================ *)

(* diginet_fader_encode (image B 0x8540c, 116 instructions, frame 16, no call). *)
Definition cdcU_fader_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip value out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_fader ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_fader p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) strip -> arg_u32A (getr regs 12) value ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_fader out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_fader (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (fader_spec pd strip value))).

(* diginet_button_encode (image B 0x855dc, 90 instructions, frame 16, no call). *)
Definition cdcU_button_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(button id on out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_button ->
arg_u32A (getr regs 10) button -> arg_u32A (getr regs 11) id -> arg_s32A (getr regs 12) on ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_button out before ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_button (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (button_spec button id on))).

(* diginet_touch_encode (image B 0x85744, 116 instructions, frame 16, no call). The store of out->key
   after a failed button_encode is excluded by the same premise as at image A. *)
Definition cdcU_touch_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip on out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_touch ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_touch p pd -> p mod 8 = 0 ->
(forall d, pd = Some d -> d_strips d <= 64) ->
arg_u32A (getr regs 11) strip -> arg_s32A (getr regs 12) on ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_touch out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_touch (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (touch_spec pd strip on))).

(* diginet_vpot_encode (image B 0x85914, 94 instructions, frame 16, no call). *)
Definition cdcU_vpot_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip delta out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_vpot ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_vpot p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) strip -> arg_s32A (getr regs 12) delta ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_vpot out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_vpot (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (vpot_spec pd strip delta))).

(* diginet_jog_encode (image B 0x85a8c, 83 instructions, frame 16, no call). *)
Definition cdcU_jog_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(delta out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_jog ->
arg_s32A (getr regs 10) delta -> getr regs 11 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_jog out before ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_jog (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (jog_spec delta))).

(* diginet_sysex_encode (image B 0x85174, 166 instructions, frame 48, __asan_memcpy at 0x852e0). It takes
   no side-stack frame; its four callers at image B pass it the payload they built in theirs. *)
Definition cdcU_sysex_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(dev fn pl n out : Z) (bs before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_sysex ->
arg_zxA 8 (getr regs 10) dev -> arg_zxA 8 (getr regs 11) fn ->
getr regs 12 = w64 pl -> getr regs 13 = w64 n -> n = Z.of_nat (length bs) -> 0 <= n <= 24 ->
getr regs 14 = w64 out -> out mod 4 = 0 ->
(0 < n -> 0 < pl /\ garr8 segs (rd W memc) pl bs /\
          crd_ok segs W memc (spZ regs) TB_sysex pl n /\ (pl + n <= out \/ out + 32 <= pl)) ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_sysex out before ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_sysex (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (sysex_spec dev fn bs))).

(* ===================== the encoders that take a side-stack frame at image B =====================
   Each requests a frame of class 0 and then reads its arguments and writes out, so each carries frame
   room and the one-object premise for the caller objects, as diginet_scribble_encode does at image A. *)

(* diginet_ring_encode (image B 0x85c1c, 183 instructions, real frame 96, frame request at 0x85c8c,
   diginet_sysex_encode at 0x85df0). *)
Definition cdcU_ring_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip mask out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_ring ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_ring p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) strip -> arg_zxA 16 (getr regs 12) mask ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_ring out before ->
cobj_ok B lyc Sc out 32 ->
cpers_disj pd p out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_ring (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (ring_spec pd strip mask))).

(* diginet_meter_encode (image B 0x85f4c, 161 instructions, real frame 128, frame request at 0x85fc4,
   diginet_sysex_encode at 0x860d8). *)
Definition cdcU_meter_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p channel right segments out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_meter ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_meter p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) channel -> arg_s32A (getr regs 12) right -> arg_u32A (getr regs 13) segments ->
getr regs 14 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_meter out before ->
cobj_ok B lyc Sc out 32 ->
cpers_disj pd p out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_meter (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (meter_spec pd channel right segments))).

(* leds_encode (diginet_codec.c:235-245; image B 0x86248, 145 instructions, real frame 96, frame request
   at 0x862b8, diginet_sysex_encode at 0x86398). A function of its own at image B only. It is reached by
   the tail calls of the two leds encoders, which have tested the personality and the strip, so it makes
   no null test of its own and stores the key as addr | 0x50000 without a mask: its address argument is
   below 2 ^ 16 (lib/U/Prog/leds_encode_c.v states the same). *)
Definition cdcU_leds_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(d : desk) (p addr bits out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_leds ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_leds p (Some d) -> p mod 8 = 0 ->
getr regs 11 = w64 addr -> 0 <= addr < 2 ^ 16 ->
arg_u32A (getr regs 12) bits ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_leds out before ->
cobj_ok B lyc Sc out 32 ->
cpers_disj (Some d) p out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_leds (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (leds_spec d addr bits))).

(* diginet_strip_leds_encode (image B 0x861d0, 30 instructions, frame 16): it reads p->strips, tests the
   strip and TAIL-calls leds_encode, which takes the frame. *)
Definition cdcU_sleds_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip bits out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_sleds ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_sleds p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) strip -> arg_u32A (getr regs 12) bits ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_sleds out before ->
cobj_ok B lyc Sc out 32 ->
cpers_disj pd p out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_sleds (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (strip_leds_spec pd strip bits))).

(* diginet_counter_leds_encode (image B 0x8648c, 29 instructions, frame 16): it reads p->counter_addr and
   tail-calls leds_encode. *)
Definition cdcU_cleds_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p bits out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_cleds ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_cleds p pd -> p mod 8 = 0 ->
arg_u32A (getr regs 11) bits ->
getr regs 12 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_cleds out before ->
cobj_ok B lyc Sc out 32 ->
cpers_disj pd p out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_cleds (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (counter_leds_spec pd bits))).

(* diginet_scribble_encode (image B 0x866c4, 173 instructions, real frame 128, frame request at 0x8673c,
   __asan_memcpy at 0x86840, diginet_sysex_encode at 0x8686c). *)
Definition cdcU_scribble_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p addr cs out : Z) (chars before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_scribble ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_scribble p pd -> p mod 8 = 0 ->
(forall d, pd = Some d -> d_chars d <= 8 /\ d_chars d <= Z.of_nat (length chars)) ->
arg_u32A (getr regs 11) addr ->
getr regs 12 = w64 cs -> 0 < cs -> garr8 segs (rd W memc) cs chars ->
crd_ok segs W memc (spZ regs) TB_scribble cs (Z.of_nat (length chars)) ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_scribble out before ->
cpers_disj pd p out 32 ->
(cs + Z.of_nat (length chars) <= out \/ out + 32 <= cs) ->
cobj_ok B lyc Sc cs (Z.of_nat (length chars)) ->
cobj_ok B lyc Sc out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_scribble (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (scribble_spec pd addr chars))).

(* diginet_counter_encode (image B 0x86ee4, 191 instructions, real frame 128, frame request at 0x86f5c,
   diginet_sysex_encode at 0x870b4). It reads seg[0..8) and p->counter_addr / p->device. *)
Definition cdcU_counter_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p sg dots out : Z) (seg before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_counter ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) TB_counter p pd -> p mod 8 = 0 ->
getr regs 11 = w64 sg -> 0 < sg -> garr8 segs (rd W memc) sg seg -> (8 <= length seg)%nat ->
crd_ok segs W memc (spZ regs) TB_counter sg (Z.of_nat (length seg)) ->
arg_zxA 8 (getr regs 12) dots ->
getr regs 13 = w64 out -> out mod 4 = 0 ->
OUT STK sp0 FP ly S lyc Sc own W memc (spZ regs) TB_counter out before ->
cpers_disj pd p out 32 ->
(sg + Z.of_nat (length seg) <= out \/ out + 32 <= sg) ->
cobj_ok B lyc Sc sg (Z.of_nat (length seg)) ->
cobj_ok B lyc Sc out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs TB_counter (cenc_wr out) lyc Sc W memc mdc
  (cenc_res segs out before (counter_spec pd seg dots))).
End d.
End c.
End b.
