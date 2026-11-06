(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31 (the world relation R): aj_snprintf_at_xromR is the call-site rule over a
   journal at a reflexive and transitive world relation R (binders first; the call keeps the world, so no law of R is
   read); aj_snprintf_at_xrom keeps its statement and is the instance at wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSnp.v, with its module paths and module names changed; 366 of its 437 lines of code are new or changed and 191 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMsnprintfShared.v, with its module paths and numbers changed; 73 of its 107 lines of code are new or changed and 403 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): ONE contract of snprintf(d, n, f, ...) at link's wrapper
   LA_W_SNPRINTF 0x43088, for its three call sites (link-a/libc/printf.md (internal record, sha256 7bbba2c3aa7f) section 1):
     0x89ea8 remember, tail `j`: d = mark's block + 4 + 16k (a heap block), n = 16, f = .str.37 0x21680 "%s";
     0x839c4 LLVMFuzzerTestOneInput: d = blk + 0x2094 + 16k (a heap block), n = 16, f = .str.21 0x21240 "%s";
     0x82b14 LLVMFuzzerTestOneInput: d = g_names + 8i (.bss, g_names 0x62fac0, 640 bytes), n = 8, f = .str 0x20fa0
             "nl%d", i = 0..63.
   The donor's shared form (libreac/fuzz_disco lib/Rt/SnShared.v sh_asnprintf_realizes, origin/ossv/recipes
   501c0d516c69, on link as lib/Rt/SnShared.v, with link's two added premises in lib/A/Rt/LinkSnDefs.v
   lk_asnprintf_realizes), in disco's guarded form (lib/Rt/SnprintfDefR.v: arodata_okP instead of a caller-side
   consts_view, so the read-only constants the chain reads are fixed by the walk invariant every caller carries),
   with the destination premises replaced by plugin-hostd/fuzz_command lib/A/Rt/RtDefs.v awrite_ok's (ruling of
   2026-10-30): every byte of the written part [d, d + sn_len (n - 1) T) writable, not the runtime's
   and outside the window; the part in application memory, addressable in the shadow map, its shadow hull readable.
   There is NO donor dest_off_globals (the destination off the whole image; on link's chain SnShared.v's
   dest_off_globals has two arms, the second for this case): instead the destination is kept apart from every image
   byte the chain reads by address (link_snp_place and link_snp_rt_cells below), so it may lie in .bss.

   What the code does (neutral listings link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST)):
   - 0x43088 j 0x46f20; ___interceptor_snprintf 0x46f20 (frame 0x60): saves a3..a7 at sp + 0x38 (the va_list),
     jal TryAsanInitFromRtl 0x5b214 (reads asan_inited 0xab118, +0x14 lb); when it returns 0 it loads REAL(vsnprintf)
     from 0xa3740 (+0x74) and calls it, else it calls ___interceptor_vsnprintf 0x46b30 (+0x54);
   - ___interceptor_vsnprintf 0x46b30 (frame 0x870): TryAsanInitFromRtl again (+0x44); common_flags() from the .got
     cell 0xa19c0 (+0x50) and its check_printf byte 0x13bfbc (+0x58); when set, printf_common 0x45fb4 (+0x74; checks
     the format and each %s string through the shadow, the shadow base read through the .got cell 0xa19d0 = 0xaa438);
     REAL(vsnprintf) from 0xa3740 (+0x7c) and jalr (+0x90); then the WRITE_RANGE check of [d, d + min (n, res + 1))
     (+0x98..+0xf8: the shadow base through 0xa19d0 again, +0xc4 / +0xcc, then the shadow words of the range,
     +0xec / +0xf0; when a word is not zero, the byte-wise test +0x200..+0x22c; for a range of 65 bytes or more,
     +0xbc -> +0x1f8 -> +0x234, range_check 0x55b30 (+0x240), which reads the memory-layout words 0xab120..0xab138
     through the .got words 0xa19d8 / 0xa19e0 / 0xa19e8, as its helper 0x556a4 does); the report path (+0x250..)
     is not reached;
   - musl vsnprintf 0x9a50c (frame 0x130): the stack guard through the .got cell LA_GOT_GUARD 0xa2658 (+0x24, +0x28),
     the cookie {d, n - 1} on its stack (+0x3c..+0x50), the 232-byte FILE zeroed by the memset wrapper (+0x60),
     `*d = 0` (+0x8c, the first store to the destination), vfprintf through its wrapper 0x4307c (+0x9c), the guard
     again (+0xa0);
   - ___interceptor_vfprintf 0x46a7c (frame 0x30): TryAsanInitFromRtl (+0x24), common_flags()->check_printf (+0x30,
     +0x38), printf_common (+0x54), REAL(vfprintf) from 0xa3738 (+0x5c), musl vfprintf 0x973e0 -> printf_core 0x97590
     (its tables .rodata 0x22858 / 0x22938 / 0x22958 / 0x229a0 / 0x22b70, "-+   0X0x" 0x10b7d, "(null)" 0x207b2, the
     guard through 0xa2658; for %s the strnlen wrapper 0x43048 at +0x614 -> its interceptor 0x43374 (REAL(strnlen)
     0xa37f8 at +0x3c, common_flags()->intercept_strlen 0x13c063 at +0x5c) -> musl strnlen 0x9b490 -> the memchr
     wrapper 0x43060 (+0x20) -> its interceptor 0x44e08 (asan_inited through 0x5a304 at +0x34, REAL(memchr) 0xa3700
     at +0x44, the shadow base at +0x84 / +0x8c) -> musl memchr) -> sn_write 0x9a5d8 (copies through the memcpy
     wrapper into d), all ported by a Theorem Labs lane (GXA + FM layers, origin/ossv/recipes libreac/fuzz_disco; the strnlen
     interceptor through the donor's GXA StrnlenCall.v contract, STRN_DEPTH 4384).
   All of these reads happen after `*d = 0` except the first TryAsanInitFromRtl, check_printf, printf_common and the
   REAL(vsnprintf) loads of the two interceptor bodies; the guard and the shadow base are read again after the last
   store to d.

   Premises, with the instruction that needs each:
   - ecall_pre (YG0d.v:286): AR (every runtime cell the chain reads is a const cell of AR, AF0m.v Tfib_const_abs,
     REAL(vsnprintf) 0xa3740 and REAL(vfprintf) 0xa3738 included); ret_ok ra (the
     final `ret` / `jr` of ___interceptor_snprintf +0x6c / +0xa0, reached through the tail jump of remember 0x89ea8
     too); sp mod 16 = 0, gp, tp (the frames of every callee);
   - arodata_okP (YC20.v:46): the read-only constants printf_core reads (its tables, the prefix string, "(null)";
     FMsnprintfCr.fm_cr), and the format and %s literals in .rodata;
   - (no world premise: the world record carries w_H8 (Reusable/YA0n.v:25, proved
     for link's entry world by lib/A/AWH8.v H1_H8), so the GXA seam's readiness reads the 8-byte uniformity of the
     hidden map on the shadow bands from the world W of the call itself: `w_H8 W`);
   - (no REAL-cell premise: AF0m.v's const table holds every interceptor's REAL cell,
     so AR's const law gives rdword 0xa3740 = 0x9a50c, which
     ___interceptor_snprintf +0x74 and ___interceptor_vsnprintf +0x7c / +0x130 read);
   - the window: ly_stk_lo ly + K <= sp and [sp - K, sp) present: the deepest frame chain, measured on the donor
     (FMsnprintfFm.v fm_glue_img 0xa30 + GXA_VF_DEPTH 5552 = 8160 <= LINK_SNP_STK = 2 * ESTACK; the same bytes on
     link, link-a/libc/matrix.tsv (internal record, sha256 076ee7c640e5)). On link's listings: ___interceptor_snprintf
     0x60 + ___interceptor_vsnprintf 0x870 + vsnprintf 0x130 + ___interceptor_vfprintf 0x30 + vfprintf
     0x170 + printf_core 0x220 = 3520 down to printf_core's callees; the strnlen interceptor's contract window 4384
     (STRN_DEPTH) gives 7904, the memcpy wrapper's ESTACK window under __fwritex / sn_write gives 7744, printf_common
     2608 + 2320 = 4928, the WRITE_RANGE range_check arm 2256 + 0x40 + 0x10 = 2336 (range_check, then its leaf 0x65bd4);
   - a0 = d, a1 = n, a2 = f, the words ws (va_words: a3..a7, then xs at sp): ___interceptor_snprintf +0x1c..+0x38;
   - rdword LA_GOT_GUARD = LA_GUARD, rdword LA_GUARD = cval: musl vsnprintf +0x24 / +0x28 / +0xa0, vfprintf +0x2c,
     printf_core +0x64, pad +0x20 (the canary checks);
   - FF (the format family over the reader, with the regions written snp_out = window and destination): printf_common
     and printf_core read the format and the %s strings and nothing the call writes;
   - 1 <= n < 2 ^ 31: musl vsnprintf +0x3c..+0x48 (n - 1 as the cookie's count), the WRITE_RANGE length; |T| < 2^31 - 1
     (printf_core's int count); 0 < d, d + w <= 2 ^ 63;
   - the destination (awrite_ok, RtDefs.v:43-50, with the window K): every byte of [d, d + w), w = sn_len (n - 1) T =
     min (|T|, n - 1) + 1, writable (vsnprintf +0x8c, sn_write's copy), not runtime-owned (the store keeps AR) and
     outside [sp - K, sp) (the callees' frames); amem_range d (w + 8), range_addressable, shadow_hull_vis over
     [d, d + w): the WRITE_RANGE check of ___interceptor_vsnprintf (+0xc4..+0xf8) reads the shadow of the range;
   - link_snp_place d w: GXA's printf_core walk (G_printf_core_common.v SEP_E, the snprintf port's fourth arm, as on
     link's plain GX) separates the destination from what it reads BY ADDRESS. Every image byte the walked code reads
     at a fixed address (the memset / memcpy wrappers are applied through their AsanAPI contracts, which ask AR only)
     lies below LA_GOT_GUARD + 8 (.rodata: the format, printf_core's tables; the .got words 0xa19c0, 0xa19d0,
     0xa19d8, 0xa19e0, 0xa19e8, 0xa2658), at the guard [LA_GUARD, LA_GUARD + 8), or in the runtime cells
     link_snp_rt_cells. The %s argument bytes may lie anywhere the family allows (link's names are g_names slots or
     .rodata strings); the family's own disjointness from the written regions (pf_arg_asan, SnShared.v) keeps them
     apart from the destination. So the destination lies off the image, above it (IMG_TOP <= d: the stack, a heap
     block above the image) or below it (d + w <= IMG_LO: a heap block the model places below the image; a block's
     placement fact is the frame's two-sided `off_img p (req_size n)`, YCbq.v:792), or in the writable span between
     the stack-guard .got word and the guard (.bss below the guard, where g_names lies);
   - Forall (zdisjoint (d, w)) link_snp_rt_cells: the runtime cells inside that span the chain reads after `*d = 0`
     (each one is also runtime-owned, Tfib_owned_static, so the ownership premise excludes it as well);
   - frm0 at entry: the FP form ruled on 2026-10-30 (provisional; GXA VfprintfCall.v:36 frm0).
   Post (the donor's, as lk_asnprintf_realizes): it returns to ra at some FP state fx' that keeps every f
   register but f10 and has frm 0; AR at the same ly S W, the callee-saved registers, same_but_materialized; a0 =
   |T| (the untruncated length); the bytes sn_bytes (n - 1) T = firstn (n - 1) T ++ [0] at d; every byte outside the
   window and [d, d + w) kept; presence kept everywhere but at the destination's bytes inside the image (see the
   clause itself for why those go).

   `asnprintf_link_realizes`, the contract the callers cite, is this form at K = LINK_SNP_STK and at FF_link below:
   the shape of disco's SnFF.FF_disco (lib/Rt/SnFF.v, a copy) at link's pieces pf_link_piece (literal bytes,
   %d, %s) and link's format range. FF_link is inside FMsnprintfFmI.FF_fmP pf_link_piece, which the ported
   chain proves; the weakening is one lemma in LinkSnp.v, as disco's FMsnprintfDiscoR1.FF_disco_fmP.

   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Link's cells and the window
   ========================================================================== *)

(* the window: 2 * ESTACK >= the chain's measured 8160 (FMsnprintfFm.v fm_glue_img + GXA_VF_DEPTH) *)
Definition LINK_SNP_STK : Z := 2 * ESTACK.

(* The entries and the cells. Every address AND every size here is read from LINK's own binary (the unstripped twin
   66cd0f159895 of the pin 059dae63e07c, its .symtab and program headers), not from a donor and not from a tool's
   output: the sizes 8 / 8 / 8 / 8 / 1 / 8 / 288 are the st_size of real_vfprintf, real_vsnprintf, real_strnlen,
   real_memchr, asan_inited, __asan_shadow_memory_dynamic_address and common_flags_dont_use; (LA_MEM_LAYOUT, 24)
   is the three 8-byte objects kHighMemEnd 0xab120, kMidMemBeg 0xab128 and kMidMemEnd 0xab130; g_names is 640 bytes
   at 0x62fac0 in .bss; YImgTop.IMG_TOP 0x654000 is link's own PT_LOAD hull end 0x6534f0 rounded up to a page
   (checked 2026-10-30: 12 numerals recomputed, 0 differed). LA_W_SNPRINTF 0x43088, LA_GOT_GUARD 0xa2658 and
   LA_GUARD 0x651c50 are LinkMfDefs.v's (the printf contracts' shared text); the values the cells hold are AF0m.v's
   Tfib_const_abs rows. *)
Definition LA_I_SNPRINTF : Z := 0x46f20.       (* ___interceptor_snprintf, 164 B *)
Definition LA_I_VSNPRINTF : Z := 0x46b30.      (* ___interceptor_vsnprintf, 792 B *)
Definition LA_VSNPRINTF : Z := 0x9a50c.        (* musl vsnprintf, 204 B *)
Definition LA_REAL_VSNPRINTF : Z := 0xa3740.   (* _ZN14__interception14real_vsnprintfE: holds LA_VSNPRINTF *)
Definition LA_REAL_VFPRINTF : Z := 0xa3738.    (* _ZN14__interception13real_vfprintfE: holds musl vfprintf 0x973e0 *)
Definition LA_ASAN_INITED : Z := 0xab118.      (* _ZN6__asanL11asan_initedE (TryAsanInitFromRtl +0x10 / +0x14) *)
Definition LA_SHADOW_BASE : Z := 0xaa438.      (* __asan_shadow_memory_dynamic_address, named by the .got cell 0xa19d0 *)
Definition LA_COMMON_FLAGS : Z := 0x13bf68.    (* _ZN11__sanitizer21common_flags_dont_useE, named by 0xa19c0 *)
Definition LA_CHECK_PRINTF : Z := LA_COMMON_FLAGS + 0x54.
Definition LA_INTERCEPT_STRLEN : Z := LA_COMMON_FLAGS + 0xfb.
Definition LA_REAL_STRNLEN : Z := 0xa37f8.     (* _ZN14__interception12real_strnlenE: holds musl strnlen 0x9b490 *)
Definition LA_REAL_MEMCHR : Z := 0xa3700.      (* _ZN14__interception11real_memchrE: holds musl memchr 0x9aaa8 *)
Definition LA_MEM_LAYOUT : Z := 0xab120.       (* kHighMemEnd, kMidMemBeg, kMidMemEnd: three 8-byte objects *)

(* The runtime cells inside (LA_GOT_GUARD + 8, LA_GUARD) that the chain reads after musl vsnprintf's `*d = 0`
   (vsnprintf +0x8c), with the instructions that read them on the covered path:
   - REAL(vfprintf): ___interceptor_vfprintf +0x5c `ld a3, 0xa3738`;
   - REAL(vsnprintf): ___interceptor_snprintf +0x74, ___interceptor_vsnprintf +0x7c / +0x130 (before the store; listed
     so that the premise the caller gives at entry stays true of the memory the walk sees);
   - asan_inited: TryAsanInitFromRtl +0x14 `lb a1, 0(s0)` (s0 = 0xab118), from ___interceptor_vfprintf +0x24 (the
     word lr.w of +0x44 is on the not-yet-initialised arm, not taken when asan_inited = 1); the memchr interceptor's
     helper 0x5a304 +0x4 `lb a0` (from 0x44e08 +0x34);
   - the shadow base: printf_common +0x78 / +0x45c / +0x550 and ___interceptor_vsnprintf +0xcc `ld _, 0(_)` after
     the .got loads of 0xa19d0 (+0x74 / +0x454 / +0x548, +0xc4); the memchr interceptor +0x8c;
   - check_printf: ___interceptor_vsnprintf +0x58 `lbu a1, 0x54(s4)` and ___interceptor_vfprintf +0x38
     `lbu a0, 0x54(a0)` (the flags object from the .got cell 0xa19c0);
   - REAL(strnlen): the strnlen interceptor 0x43374 +0x3c `ld a2, 0xa37f8` (printf_core +0x614, for %s);
   - intercept_strlen: the strnlen interceptor +0x5c `lbu a1, 0xfb(s5)` (s5 = the flags object, +0x58);
   - REAL(memchr): the memchr interceptor 0x44e08 +0x44 `ld a3, 0xa3700` (from musl strnlen +0x20);
   - the memory-layout words 0xab120..0xab138: range_check 0x55b30 +0x5c / +0x60 / +0x78 / +0xa4 / +0xa8 / +0xc0
     and its helper 0x556a4 (through the .got words 0xa19d8 / 0xa19e0 / 0xa19e8), on the WRITE_RANGE arm for a
     range of 65 bytes or more (___interceptor_vsnprintf +0x240); the donor's strnlen readiness asks for them too
     (FMgxaSeamReady.v strn_ready_intro_loc, Bz/A/R_m2s.v m2s_cells).
   printf_common's other reads of the flags object (+0x614 .. +0xa34 `lbu 0x21`) and of ReportedOnce 0xa7d30
   (+0x8b8) are on its report arms, which the family's formats do not reach. *)
Definition link_snp_rt_cells : list (Z * Z) :=
  [(LA_REAL_VFPRINTF, 8); (LA_REAL_VSNPRINTF, 8); (LA_ASAN_INITED, 1); (LA_SHADOW_BASE, 8); (LA_CHECK_PRINTF, 1);
   (LA_REAL_STRNLEN, 8); (LA_INTERCEPT_STRLEN, 1); (LA_REAL_MEMCHR, 8); (LA_MEM_LAYOUT, 24)].

(* where the destination may lie (see the header): above the image, in the writable span between the stack-guard
   .got word and the guard, or below the image. The two off-image arms are the chain's first dest_off_globals arm
   (zdisjoint from [IMG_LO, IMG_TOP)); the below-the-image arm comes last so that a caller's `left` (above) and
   `right` (the span, by lia) keep their meaning. *)
Definition link_snp_place (d w : Z) : Prop :=
  YImgTop.IMG_TOP <= d \/ (LA_GOT_GUARD + 8 <= d /\ d + w <= LA_GUARD) \/ d + w <= YImgTop.IMG_LO.

(* Link's format family, the shape of disco's SnFF.FF_disco at link's pieces (literal bytes, %d, %s) and link's
   format range: the .rodata strings the three call sites pass, below the stack-guard .got word. It is inside
   FMsnprintfFmI.FF_fmP pf_link_piece (same conjuncts, same bounds), which the ported chain proves; the
   one-line weakening lemma is in LinkSnp.v, as disco's FMsnprintfDiscoR1.FF_disco_fmP. *)
Definition LINK_FMT_LO : Z := 0x10000.
Definition LINK_FMT_HI : Z := LA_GOT_GUARD.
Definition FF_link : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall pf_link_piece ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    LINK_FMT_LO <= f /\ f + Z.of_nat (length fmt) + 1 <= LINK_FMT_HI /\ SnFF.pf_args_slack ws args /\
    fmt <> [] /\ SnFF.pf_args_amem ws args.

(* ==========================================================================
   2. The contract
   ========================================================================== *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variables rlo rhi : Z.

(* The function's own premises at a call, over the registers and the memory the walk sees (H = w_H W): the
   argument registers, the canary cells, the argument words, the format family, the
   bounds, the destination's bytes (writable and outside the window: awrite_ok, RtDefs.v:46-47, without the
   ownership part, which the caller states against its allocator state), its shadow, its placement and its
   separation from the runtime cells. The satisfiability witnesses (LinkSnpWit.v) are of this bundle. *)
Definition asnprintf_link_fpre (FF : fmt_fam) (K : Z) (W : world segs) (mem : word -> option byte)
    (regs : bvmap 5 word) (d n f : Z) (xs ws T : list Z) (cval : Z) : Prop :=
  getr regs 10 = w64 d /\ getr regs 11 = w64 n /\ getr regs 12 = w64 f /\
  rdword (aview segs (w_H W) mem) LA_GOT_GUARD = Some LA_GUARD /\
  rdword (aview segs (w_H W) mem) LA_GUARD = Some cval /\
  (* no REAL(vsnprintf) cell premise: AF0m.v's const table has the row *)
  va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws /\
  spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 /\
  Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) /\
  FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T /\
  1 <= n < 2 ^ 31 /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\ 0 < d /\ d + sn_len (n - 1) T <= 2 ^ 63 /\
  (forall a, d <= a < d + sn_len (n - 1) T ->
     writable_at segs (mrestrict (w_H W) mem) a /\ ~ (spZ regs - K <= a < spZ regs)) /\
  amem_range d (sn_len (n - 1) T + 8) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) /\
  shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) /\
  link_snp_place d (sn_len (n - 1) T) /\
  Forall (zdisjoint (d, sn_len (n - 1) T)) link_snp_rt_cells.

Definition sh_asnprintf_link_realizes (FF : fmt_fam) (K pc : Z) : Prop :=
forall ly S W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
asnprintf_link_fpre FF K W mem regs d n f xs ws T cval ->
(* the destination is not the runtime's (awrite_ok's ~ aowned, RtDefs.v:47): its stores keep AR *)
(forall a, d <= a < d + sn_len (n - 1) T -> ~ aowned B ly S a) ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v:36) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(* presence kept, except at the destination's bytes inside the image [IMG_LO, IMG_TOP). A destination in .bss is an image
   byte, and link's image models .bss with ROM zero bytes (`seg_rom tfibsegs (Z_to_bv 64 0x62fac0) = Some 0`, measured in
   link-a/logs/build-20261030T154405Z.log (internal record, sha256 0b27a147d519)), so GXA's post pins the written bytes'
   VALUES (the bytes clause above) but not the store's domain there: the NUL equals the ROM byte. For a destination off
   the image the exception is empty. The journal's own presence clause is over `alloc_ceiling <= a` (link_amem.v akept),
   above the image, and the lift aj_gx_call_atFo takes that plus each written byte's visibility. *)
(forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a ->
   ~ (d <= a < d + sn_len (n - 1) T /\ YImgTop.IMG_LO <= a < YImgTop.IMG_TOP) -> apresent (w_H W) mem' a)).

(* the contract the callers of link's three snprintf sites cite *)
Definition asnprintf_link_realizes (pc : Z) : Prop := sh_asnprintf_link_realizes FF_link LINK_SNP_STK pc.

End s.

(* ==========================================================================
   3. Facts about the placement the walk and the callers use
   ========================================================================== *)

(* the written part is never empty: sn_bytes ends with the NUL *)
Lemma sn_len_pos : forall N T, 1 <= sn_len N T.
Proof.
intros N T. unfold sn_len, sn_bytes. rewrite length_app. cbn [length]. lia.
Qed.

(* every range of link_snp_rt_cells lies in the span the placement's second arm allows, so a destination that
   takes an off-image arm is apart from all of them by its address alone *)
Lemma link_snp_rt_cells_in_img :
  Forall (fun r => LA_GOT_GUARD + 8 <= fst r /\ fst r + snd r <= LA_GUARD) link_snp_rt_cells.
Proof.
unfold link_snp_rt_cells, LA_REAL_VFPRINTF, LA_REAL_VSNPRINTF, LA_ASAN_INITED, LA_SHADOW_BASE, LA_CHECK_PRINTF,
LA_REAL_STRNLEN, LA_INTERCEPT_STRLEN, LA_REAL_MEMCHR, LA_MEM_LAYOUT, LA_COMMON_FLAGS, LA_GOT_GUARD, LA_GUARD.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.

(* a destination off the image, on either side (the frame's off_img d w, YCbq.v:792), misses every runtime cell *)
Lemma link_snp_rt_cells_of_off : forall d w,
  d + w <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= d -> Forall (zdisjoint (d, w)) link_snp_rt_cells.
Proof.
intros d w Hd. assert (E : YImgTop.IMG_TOP = 0x654000) by reflexivity.
assert (E0 : YImgTop.IMG_LO = 0x10000) by reflexivity.
eapply Forall_impl; [|exact link_snp_rt_cells_in_img].
intros r [H1 H2]. unfold zdisjoint, LA_GOT_GUARD, LA_GUARD in *. cbn [fst snd] in *. lia.
Qed.

(* the case above the image, the form the callers already cite *)
Lemma link_snp_rt_cells_of_place : forall d w,
  YImgTop.IMG_TOP <= d -> Forall (zdisjoint (d, w)) link_snp_rt_cells.
Proof. intros d w Hd. apply link_snp_rt_cells_of_off. right. exact Hd. Qed.
