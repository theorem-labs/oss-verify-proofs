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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgMainC.v; 215 of its 241 lines of code are new or changed and 43 lines of the source are left out. *)
(* The A-level contracts of the encoders of fuzz_codec's library code and of the leaves they share:
   diginet_personality_of, diginet_ring_dot, diginet_ring_fill, diginet_meter_mask,
   diginet_meter_segments, diginet_seg7, and the twelve encoders diginet_{fader, button, touch, vpot, jog,
   sysex, ring, meter, strip_leds, counter_leds, scribble, counter}_encode.

   Each contract is `SRr segs W (cfg_at segs a regs memc mdc) Post` with the caller's journal as the
   premise and lib/A/Prog/CPgBase.v's cdc_entry / cdc_post as its two halves. The Gallina result each one
   states is the plain one, unchanged: lib/Spec/DgnSpec.v, lib/Spec/DgnLib.v.

   IMAGE-INDEPENDENT: the entry address of each function and the addresses of the tables the functions
   read are Section variables, so image B instantiates the same texts.

   What each encoder does to memory: it writes the 32 bytes of the caller's struct diginet_cmd at out and
   nothing else outside its own stack window; on every failing return it has written nothing (the plain
   contracts' `cmd_out before None = before`). diginet_scribble_encode takes a side-stack frame of
   class 0, so its contract carries frame room; the others use the real stack only. *)
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
(* The image's read-only window, and the address of the 91-word table diginet_seg7 switches on. *)
Variables RLO RHI : Z.
Variable SEG7TBL : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T :=
  (cdc_entry segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T).
Local Notation POST STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R :=
  (cdc_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs T E lyc Sc W memc mdc R).

(* The caller's struct diginet_cmd at out: 32 bytes the call may write, holding `before` now. *)
Definition cenc_out (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world segs) (memc : word -> option byte)
(sp T out : Z) (before : list Z) : Prop :=
cdst_ok segs B STK sp0 FP ly S lyc Sc own W memc sp T out 32 /\
garr8 segs (rd W memc) out before /\ length before = 32%nat.
(* The result of an encoder: the return code in a0 and the 32 bytes of the command. *)
Definition cenc_res (out : Z) (before : list Z) (r : Z * option cmd)
: world segs -> (word -> option byte) -> bvmap 5 word -> Prop :=
fun W2 mem2 regs2 =>
getr regs2 10 = w64 (fst r) /\ garr8 segs (rd W2 mem2) out (cmd_outZ before (snd r)).
(* The bytes an encoder writes. *)
Definition cenc_wr (out : Z) : Z -> Prop := fun x => out <= x < out + 32.

(* =============================== the register-only leaves =============================== *)

(* diginet_personality_of (diginet_codec.c:27-33; image A 0x84888, 11 instructions, no frame, no memory
   access, branchless): for any a0 it returns pers_ofA PERSA a0, with PERSA the address of
   personalities[0]. *)
Definition cdc_pers_of_specX (a PERSA : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (d : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_pers_of ->
getr regs 10 = w64 d -> 0 <= d < 2 ^ 64 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_pers_of cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (pers_ofA PERSA d))).

(* diginet_ring_dot (diginet_codec.c:169-172; image A 0x852d0, 8 instructions, no frame, no memory
   access): the uint16_t ring_dot_spec of its unsigned argument. *)
Definition cdc_ring_dot_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_ring_dot ->
arg_u32A (getr regs 10) n ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_ring_dot cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (ring_dot_spec n))).

(* diginet_ring_fill (diginet_codec.c:174-177; image A 0x852f0, 9 instructions, no frame). *)
Definition cdc_ring_fill_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (n : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_ring_fill ->
arg_u32A (getr regs 10) n ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_ring_fill cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (ring_fill_spec n))).

(* diginet_meter_mask (diginet_codec.c:202-207; image A 0x855ac, 7 instructions, no frame). *)
Definition cdc_meter_mask_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter_mask ->
arg_u32A (getr regs 10) s ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_meter_mask cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (meter_mask_spec s))).

(* diginet_meter_segments (diginet_codec.c:209-215; image A 0x855c8, 14 instructions, no frame); its
   argument is a uint16_t, loaded zero-extended. *)
Definition cdc_meter_segs_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (mask : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter_segs ->
arg_zxA 16 (getr regs 10) mask ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_meter_segs cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (meter_segments_spec mask))).

(* diginet_seg7 (diginet_codec.c:308-335; image A 0x860b4, 27 instructions, frame 16 for the error path's
   return address): it uses the low byte of a0 and reads one word of the 364-byte table the compiler made
   for its switch (image A 0x213a0), which the memory-checking runtime registers at start-up. It writes
   nothing. *)
Definition cdc_seg7_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c : Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_seg7 ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) ->
(forall i, 0 <= i < 364 -> in_roP segs RLO RHI (SEG7TBL + i)) ->
crd_ok segs W memc (spZ regs) T_seg7 SEG7TBL 364 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_seg7 cno_wr lyc Sc W memc mdc
  (fun W2 mem2 regs2 => getr regs2 10 = w64 (seg7_spec (c mod 256)))).

(* ==================================== the twelve encoders ==================================== *)

(* diginet_fader_encode (diginet_codec.c:95-111; image A 0x84ba8, 109 instructions, frame 16, no call).
   a0 = the personality, a1 = strip, a2 = value (both lw), a3 = &out. It reads p->strips (p + 17) and
   writes out[0..5), out[24], out[25] and out[28..32). *)
Definition cdc_fader_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip value out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_fader ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_fader p pd ->
arg_u32A (getr regs 11) strip -> arg_u32A (getr regs 12) value ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_fader out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_fader (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (fader_spec pd strip value))).

(* diginet_button_encode (diginet_codec.c:113-122; image A 0x84d5c, 87 instructions, frame 16, no call).
   a0 = button, a1 = id (lw), a2 = on (int), a3 = &out; it reads no memory but out's shadow. *)
Definition cdc_button_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(button id on out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_button ->
arg_u32A (getr regs 10) button -> arg_u32A (getr regs 11) id -> arg_s32A (getr regs 12) on ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_button out before ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_button (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (button_spec button id on))).

(* diginet_touch_encode (diginet_codec.c:124-134; image A 0x84eb8, 93 instructions, frame 16, no call).
   a0 = the personality, a1 = strip (lw), a2 = on (int), a3 = &out. The C stores out->key after a failed
   button_encode when 0x3f < strip < p->strips (image A 0x84fa0-0x84fb8), so the contract keeps the plain
   premise d_strips <= 64, which excludes that path: out is unchanged on every failure. *)
Definition cdc_touch_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip on out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_touch ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_touch p pd ->
(forall d, pd = Some d -> d_strips d <= 64) ->
arg_u32A (getr regs 11) strip -> arg_s32A (getr regs 12) on ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_touch out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_touch (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (touch_spec pd strip on))).

(* diginet_vpot_encode (diginet_codec.c:136-154; image A 0x8502c, 89 instructions, frame 16, no call).
   a0 = the personality, a1 = strip, a2 = delta (int), a3 = &out. *)
Definition cdc_vpot_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip delta out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_vpot ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_vpot p pd ->
arg_u32A (getr regs 11) strip -> arg_s32A (getr regs 12) delta ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_vpot out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_vpot (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (vpot_spec pd strip delta))).

(* diginet_jog_encode (diginet_codec.c:156-165; image A 0x85190, 80 instructions, frame 16, no call).
   a0 = delta (int), a1 = &out; it reads no memory but out's shadow. *)
Definition cdc_jog_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(delta out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_jog ->
arg_s32A (getr regs 10) delta -> getr regs 11 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_jog out before ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_jog (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (jog_spec delta))).

(* diginet_sysex_encode (diginet_codec.c:66-91; image A 0x848b4, 189 instructions, frame 48, calls
   __asan_memcpy at 0x84a5c). a0 = device, a1 = fn (both uint8_t, zero-extended), a2 = the payload,
   a3 = its length, a4 = &out. It reads the payload bytes one at a time (the seven-bit test) and copies
   them to out + 4; every failing return precedes the first store to out. The payload read premise is
   asked for when the payload is not empty. *)
Definition cdc_sysex_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(dev fn pl n out : Z) (bs before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_sysex ->
arg_zxA 8 (getr regs 10) dev -> arg_zxA 8 (getr regs 11) fn ->
getr regs 12 = w64 pl -> getr regs 13 = w64 n -> n = Z.of_nat (length bs) -> 0 <= n <= 24 ->
getr regs 14 = w64 out ->
(0 < n -> 0 < pl /\ garr8 segs (rd W memc) pl bs /\
          crd_ok segs W memc (spZ regs) T_sysex pl n /\ (pl + n <= out \/ out + 32 <= pl)) ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_sysex out before ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_sysex (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (sysex_spec dev fn bs))).

(* diginet_ring_encode (diginet_codec.c:179-198; image A 0x85314, 166 instructions, frame 48; sysex_encode
   is inlined, and the three payload bytes it builds lie in its own real-stack frame, from which
   __asan_memcpy (0x8547c) copies them to out + 4). a0 = the personality, a1 = strip (lw), a2 = the mask
   (uint16_t, lhu), a3 = &out. *)
Definition cdc_ring_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip mask out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_ring ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_ring p pd ->
arg_u32A (getr regs 11) strip -> arg_zxA 16 (getr regs 12) mask ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_ring out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_ring (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (ring_spec pd strip mask))).

(* diginet_meter_encode (diginet_codec.c:217-231; image A 0x85600, 141 instructions, frame 48; meter_mask
   and sysex_encode are inlined, __asan_memcpy at 0x85720). a0 = the personality, a1 = channel,
   a2 = right (int), a3 = segments, a4 = &out (all lw). *)
Definition cdc_meter_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p channel right segments out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_meter ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_meter p pd ->
arg_u32A (getr regs 11) channel -> arg_s32A (getr regs 12) right -> arg_u32A (getr regs 13) segments ->
getr regs 14 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_meter out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_meter (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (meter_spec pd channel right segments))).

(* diginet_strip_leds_encode (diginet_codec.c:247-255; image A 0x85834, 146 instructions, frame 16, leaf:
   leds_encode and sysex_encode are inlined and the two payload bytes are stored into out directly).
   a0 = the personality, a1 = strip, a2 = bits (lw), a3 = &out. *)
Definition cdc_sleds_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p strip bits out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_sleds ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_sleds p pd ->
arg_u32A (getr regs 11) strip -> arg_u32A (getr regs 12) bits ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_sleds out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_sleds (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (strip_leds_spec pd strip bits))).

(* diginet_counter_leds_encode (diginet_codec.c:257-263; image A 0x85a7c, 146 instructions, frame 16,
   leaf). a0 = the personality, a1 = bits (lw), a2 = &out. *)
Definition cdc_cleds_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p bits out : Z) (before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_cleds ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_cleds p pd ->
arg_u32A (getr regs 11) bits ->
getr regs 12 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_cleds out before ->
cpers_disj pd p out 32 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_cleds (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (counter_leds_spec pd bits))).

(* diginet_scribble_encode (diginet_codec.c:287-303; image A 0x85e24, 164 instructions, real frame 128 and
   a side-stack frame of class 0 taken at 0x85e9c, __asan_memcpy at 0x85f88, diginet_sysex_encode at
   0x85fb4). a0 = the personality, a1 = the address, a2 = the characters, a3 = &out. It copies
   p->scribble_chars characters into the ten payload bytes of its own frame (so the plain premise
   scribble_chars <= 8 stays) and writes out only through sysex_encode and the key store after it.
   It takes its frame and writes the frame's header and shadow before it reads the characters and the
   personality bytes, so neither range may be a byte of the runtime's own (a free frame is one). *)
Definition cdc_scribble_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p addr cs out : Z) (chars before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_scribble ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_scribble p pd ->
(forall d, pd = Some d -> d_chars d <= 8 /\ d_chars d <= Z.of_nat (length chars)) ->
arg_u32A (getr regs 11) addr ->
getr regs 12 = w64 cs -> 0 < cs -> garr8 segs (rd W memc) cs chars ->
crd_ok segs W memc (spZ regs) T_scribble cs (Z.of_nat (length chars)) ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_scribble out before ->
cpers_disj pd p out 32 ->
(cs + Z.of_nat (length chars) <= out \/ out + 32 <= cs) ->
cobj_ok B lyc Sc cs (Z.of_nat (length chars)) ->
cobj_ok B lyc Sc out 32 ->
Z.of_nat (length (frames Sc)) <= 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_scribble (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (scribble_spec pd addr chars))).

(* diginet_counter_encode (diginet_codec.c:371-386; image A 0x86608, 168 instructions, frame 64,
   sysex_encode inlined, __asan_memcpy at 0x8675c). a0 = the personality, a1 = the eight segment bytes,
   a2 = the dots (uint8_t), a3 = &out. It reads seg[0..8) and p->counter_addr / p->device. *)
Definition cdc_counter_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(pd : option desk) (p sg dots out : Z) (seg before : list Z),
ENTRY STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter ->
getr regs 10 = w64 p -> pers_argA segs B W memc (spZ regs) T_counter p pd ->
getr regs 11 = w64 sg -> 0 < sg -> garr8 segs (rd W memc) sg seg -> (8 <= length seg)%nat ->
crd_ok segs W memc (spZ regs) T_counter sg (Z.of_nat (length seg)) ->
arg_zxA 8 (getr regs 12) dots ->
getr regs 13 = w64 out ->
cenc_out STK sp0 FP ly S lyc Sc own W memc (spZ regs) T_counter out before ->
cpers_disj pd p out 32 ->
(sg + Z.of_nat (length seg) <= out \/ out + 32 <= sg) ->
SRr segs W (cfg_at segs a regs memc mdc)
(POST STK sp0 FP ly S W0 mem0 md0 own k regs T_counter (cenc_wr out) lyc Sc W memc mdc
  (cenc_res out before (counter_spec pd seg dots))).
End d.
End c.
End b.
