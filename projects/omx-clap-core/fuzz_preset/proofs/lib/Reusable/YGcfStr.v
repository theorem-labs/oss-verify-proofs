(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-28 (PresetStr, c-libc-stdio lane): the strcmp and strlen interceptor contracts of the
   SECOND allocator instance, the text of record for AsanAPI_cf's strcmp and strlen fields. rule 24: no function
   is proved in this file; nothing is proved here at all.

   WHAT EACH CONTRACT IS FOR
   - `astrcmp_realizes_cf pc`: a call of the ASan strcmp interceptor at pc by instrumented code. In each image
     `__wrap_strcmp` has 19 call sites, all `jal ra`: 12 in fuzz_preset's program code (check_round_trip 4,
     same 3, ex_value 3, round_trip_text 1, pj_get 1) and 7 in musl (__mo_lookup 1, __vdsosym 2, do_tzset 4),
     because the link wraps libc.a's calls too. Every one of the 19 tests only a0 = 0 / a0 <> 0 (beq / bne /
     sltiu against zero). The post returns to ra with ARcf kept, the callee-saved registers kept, a0 = the sign of
     the first differing byte, memory outside [sp - 2 * ESTACK, sp) unchanged.
   - `astrlen_realizes_cf pc`: a call of the ASan strlen interceptor at pc. `__wrap_strlen` has 14 call sites in
     each image: 8 in program code (check_round_trip, ex_word, round_trip_text, tx_value, fuzz_strdup,
     write_value, literal, put_string) and 6 in musl (__strchrnul, strncat, do_tzset 3, __strftime_fmt_1). Same
     post with a0 = the length.
   (Counts: riscv64-alpine-linux-musl-objdump in the toolchain image, sha256:6a6b4816..0a7b, on the two old-pin rebuilt
   unstripped twins, asan f0d2e8d4..0b15 and asan-ubsan 3b5e1a09..3c58.)

   THE TEXTS. These are the shared texts with the instance swapped, and one premise strengthened:
   - strcmp: the AR-form text of record is h-rw-cmd-7's AStrcmpDef (origin/cold/h-rw-cmd-7-rt 97c611eec86, the
     PROVED head, with the walk lib/A/Rt/Strcmp.v grant_strcmp_icpt on fuzz_grant image A;
     proofs/libreac/fuzz_grant/lib/Reusable/AStrcmpDef.v; c-asan named it the shared strcmp text). Its
     strcmp_res / str_meet are copied below verbatim, and astrcmp_realizes_cf is its astrcmp_realizes over the
     second instance. The sign in the post (a0 = CharCmpX) is AStrcmpDef's own, so it is kept, not weakened to
     equality. This file does not add a second AR-form text: it is the ARcf form.
   - strlen: YG0dcf.v's astrnlen_realizes_cf (cgif's YG0d.v astrnlen_realizes over the instance) with the bound
     removed.
   - Instance: ecall_pre -> ecall_pre_cf (YG0dcf.v), AR -> ARcf (YG0ncf.v), the ghost list Hp threaded unchanged;
     src_ok_cf (YG0d2cf.v) IS cgif's src_ok.
   - The one strengthened premise: amem_range -> amem_range8, which is the walks' own region_in_mem. Both kits'
     shadow check needs 8 bytes of application memory past the bytes read, and no ARcf field excludes a string
     that ends in the last 8 bytes of a range. Callers stated over plain amem_range (the stand-ins in
     c-omx-alloc's YGcallMx.v) do not supply it.
   - strcmp only, one premise ADDED (2026-10-29, the parent's decision): the per-call `rom_view segs W mem`, in the
     place astrlen_realizes_cf has it. This DEPARTS from AStrcmpDef's text in this one premise. Why: AStrcmpDef's
     own proof (fuzz_grant's symbolic walk) tracks each read, so it never needs rom_view. Our proof is a PORT of
     fuzz_state's kit composition (FSstrcmp.v), whose normalisation MemNorm.evt_normalize_cj needs ro_agree of the
     whole store (lib/MemNorm.v:861-862): the kit's mem_inv forbids stored bytes at read-only addresses
     (lib/K5/Lib/Mem.v:106, :127-130) while data loads read the store first (Mem.v:57). ARcf has no read-only value
     clause, so it cannot supply that. The per-call rom_view is what the donor's astrcmp_realizesU, our
     astrlen_realizes_cf and c-omx-alloc's astrcmp_realizes_x all take, so the two contracts here are uniform with
     each other and with their consumer.
   - the MEMNORM TWINS (2026-10-29, c-libc-stdio's decision 12:2xZ on c-omx-alloc's MemnormKeeps measurement):
     `astrcmp_realizes_cfm` / `astrlen_realizes_cfm` are the two texts above with ONE conjunct added LAST to the
     post, the keep `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'`. It cannot be derived from the
     posts above, which state mem' through views only, so the rows prove it from their runs (post_of_walk's raw
     KEEP, lib/A/PSstrlen.v and lib/AU/PSstrlen.v). The texts above are unchanged; the rows give them back by
     dropping the conjunct. Consumers: YGcallMxmn.v's astrcmp_realizes_xrom / astrlen_realizes_xrom (c-omx-alloc's
     family 1b), through lib/Reusable/YGcfStrRo.v.

   IMAGE FACTS. This file holds NONE, so the same blob is taken by path on every pin line: the entry pc is a
   PARAMETER of each text, and each image's own file supplies it BY FIELD NAME, `cf_pc_strcmp` / `cf_pc_strlen` of
   lib/A/CfImgA.v (image A) and lib/AU/CfImgB.v (image B), generated from that pin's ELF by the internal file gen_cfimg.py
   (h-mani-a8's API fields). The rows (lib/A/PSstrlen.v pc_strlen_A, ...) check that field against the kit's entry
   walk. Each pc is a trampoline of one instruction, `jal zero, <interceptor>`. The walks use 2192 B (strcmp,
   ISTRCMP_DEPTH) and 2224 B (strlen, ISTRLEN_DEPTH) below sp, inside the 2 * ESTACK window of the texts.

   TAKEN FROM, one entry per callee (rule 24):
   - strcmp interceptor: machine walk = leptonica/fhmtgen_fuzzer lib/K5/{A10,B10}/I_strcmp.v (origin/ossv/recipes
     c8557374ad2e), ported as lib/K5; contract text = AStrcmpDef (origin/cold/h-rw-cmd-7-rt 97c611eec86), copied
     verbatim and moved to ARcf; composition to the contract = fuzz_state's FSstrcmp.v (origin/cold/port-state-rt-str
     17818dd9abc), in port.
   - strlen interceptor: machine walk = bzip2/bzip2_compress_target lib/K/A/I_strlen.v (origin/ossv/recipes
     c8557374ad2e), ported as lib/K, musl strlen walked inside it; contract text = YG0dcf.v astrnlen_realizes_cf
     less its bound; composition = fuzz_state's FSstrlen.v (port-state-rt-str 17818dd9abc), in port.
   - the pieces those compositions compose: the evt -> SRr bridge = port-fm's FMbz_bridge.v (origin/cold/port-fm-rtscan
     10d0c5cd0be), ported as lib/Reusable/YEvtSRr.v; the shadow half = FMbz_str.v's chk_ok_of_view (via fuzz_state's
     FSbz_str.v, from port-fm-rtscan cedf3d02589); the transports = c-asan-rt's MemNorm / RegisterBridge (already in
     this unit as lib/MemNorm.v, lib/Lib/RegisterBridge.v).
   - ruled out: r-identity's strcmp (origin/cold/h-rw-ide-6-id-wrap lib/A/Rt/Strcmp.v): not built, and its post is
     equality only. disco's proved strlen (libreac/fuzz_disco lib/A/Rt/Strlen.v, strlen_icpt_contract): a different
     framework (a symbolic walk of disco's image under cgif's AR), so relocating it and its A/ files costs more than
     the route taken.

   PROOF STATUS (none of it in this file). PROVED and built in this unit, at the trampoline pcs, with no hypothesis
   left: `istrcmp_wrap_closed` (lib/K5/A10 and lib/K5/B10/I_strcmp_entry.v) and `istrlen_wrap_closed`
   (lib/K/A/I_strlen_entry.v, both images), in the kits' vocabulary (`evt` over a machine_state). Carrying them to
   these two contracts over ARcf: the compositions above, in progress. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YG0d2cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section CfStr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.

(* origin/cold/h-rw-cmd-7-rt 97c611eec86 proofs/libreac/fuzz_grant/lib/Reusable/AStrcmpDef.v, verbatim: the result
   (the interceptor's CharCmpX) and where the compare stops (the bytes before k equal and nonzero; at k they differ
   or s1's byte is 0). *)
Definition strcmp_res (c1 c2 : Z) : Z := if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1.

Definition str_meet (W : world segs) (mem : word -> option byte) (x y k c1 c2 : Z) : Prop :=
  0 <= k /\
  (forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\
                                     aview segs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
  aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\
  (c1 <> c2 \/ c1 = 0).

(* The ONE premise stronger than the texts above. It is exactly the walks' own `region_in_mem p n`
   (lib/K/A/I_consts.v:52 and :148, lib/K5/{A10,B10}/I_consts.v:46, the same text in both kits:
   (0 <= p /\ p + n + 8 <= 0x7fff7fff) \/ (0x10007fff7fff + 16 <= p /\ p + n + 8 <= 0x7fffffffffff)), which their
   shadow check `chk_ok` asks through `rng_ok`, written in YG0f.v's names. It implies YG0d.v's amem_range p n.
   Nothing in ARcf excludes a string ending in the last 8 bytes of a range, so the walks cannot be used without it.
   WHY THE MARGIN, MEASURED 2026-10-29 (the internal file strlen-range-need.md in a Theorem Labs lane's workers dir, both preset
   rebuilt images): the CODE needs only `(0 <= p /\ p + n <= kLowMemEnd - 1) \/ (kHighMemBeg <= p /\
   p + n <= kHighMemEnd - 1)`. The +8 (low upper), +15 (high lower) and +8 (high upper) serve no instruction:
   the shadow check reads no application byte, musl's aligned word over-read never leaves the NUL's own aligned
   word, and the layout tests run only for n >= 65. The margin is the ported kits' PROOF shape, spent at
   lib/K/A/R_isPoisoned.v:243 and :249 (the addr_in_mem obligations of the two MemToShadow calls). Witnesses the
   code accepts and this text rejects: p = 0x7fff7f00, n = 0xff; p = 0x10007fff8000, n = 8. It is kept because it
   is true at every caller (c-omx-alloc's decision, 07:16Z). (An earlier version of this comment gave a wrong
   reason, "application memory with 8 bytes to spare past the bytes read".) *)
Definition amem_range8 (p n : Z) : Prop :=
  p + n + 8 <= kLowMemEnd - 1 \/ (kHighMemBeg + 15 <= p /\ p + n + 8 <= kHighMemEnd - 1).

(* AStrcmpDef.v's astrcmp_realizes with ecall_pre -> ecall_pre_cf, src_ok -> src_ok_cf (the same constant),
   AR -> ARcf (the ghost list Hp threaded unchanged), amem_range -> amem_range8, and ONE ADDED premise, the
   per-call rom_view (as astrlen_realizes_cf below; the header says why). No other change. *)
Definition astrcmp_realizes_cf (pc : Z) : Prop :=
  forall ly S Hp W regs mem md x y k c1 c2,
  ecall_pre_cf segs B ly S Hp W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  str_meet W mem x y k c1 c2 ->
  src_ok_cf segs W regs mem x (k + 1) -> src_ok_cf segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range8 x (k + 1) -> amem_range8 y (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
  rom_view segs W mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* YG0dcf.v's astrnlen_realizes_cf with the bound n removed (no a1 premise, no `k + 8 <= n`; first_byte at
   n := k + 1: the string ends at its first NUL) and amem_range -> amem_range8. No other change. *)
Definition astrlen_realizes_cf (pc : Z) : Prop :=
  forall ly S Hp W regs mem md x k,
  ecall_pre_cf segs B ly S Hp W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> 0 < x ->
  0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
  first_byte segs W mem x (k + 1) 0 k ->
  src_ok_cf segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range8 x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
  rom_view segs W mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 k /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).


(* astrcmp_realizes_cf with the memnorm keep as the LAST post conjunct (the header says why). No other change. *)
Definition astrcmp_realizes_cfm (pc : Z) : Prop :=
  forall ly S Hp W regs mem md x y k c1 c2,
  ecall_pre_cf segs B ly S Hp W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  str_meet W mem x y k c1 c2 ->
  src_ok_cf segs W regs mem x (k + 1) -> src_ok_cf segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range8 x (k + 1) -> amem_range8 y (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (k + 1) ->
  rom_view segs W mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* astrlen_realizes_cf with the memnorm keep as the LAST post conjunct. No other change. *)
Definition astrlen_realizes_cfm (pc : Z) : Prop :=
  forall ly S Hp W regs mem md x k,
  ecall_pre_cf segs B ly S Hp W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> 0 < x ->
  0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
  first_byte segs W mem x (k + 1) 0 k ->
  src_ok_cf segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range8 x (k + 1) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
  rom_view segs W mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       ARcf segs B ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 k /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).
End CfStr.
