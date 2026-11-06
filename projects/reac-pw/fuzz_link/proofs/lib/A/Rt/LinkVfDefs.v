(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31 (the world relation R): aj_snprintf_at_xromR is the call-site rule over a
   journal at a reflexive and transitive world relation R (binders first; the call keeps the world, so no law of R is
   read); aj_snprintf_at_xrom keeps its statement and is the instance at wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallSnp.v, with its module paths and module names changed; 366 of its 437 lines of code are new or changed and 191 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMsnprintfShared.v, with its module paths and module names changed; 65 of its 106 lines of code are new or changed and 396 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): vfprintf and fprintf on link's memory FILE, at the
   wrappers link's own code calls, in the shared form of the image-A printf family (lib/Rt/SnShared.v
   sh_asnprintf_realizes / sh_avfprintf_icpt_realizes: ecall_pre, a window K of present stack, the read-only bytes
   as the walk invariant arodata_okP fixes them (disco's guarded form, lib/Rt/SnprintfDefR.v; the proof derives
   consts_view over the constants the chain reads), the stack-protector cells gc -> gv -> cval, the format family FF over the reader and the regions the
   call writes, the argument words, rounding mode 0 at entry; post: the FP state f10 aside and frm 0 kept, AR at the same
   ly S W, aregs_preserved, same_but_materialized, a0 = |T|, every byte outside the window and the FILE block kept,
   presence kept), with the FILE in LinkMfDefs.v's vocabulary. The A twin of lib/Prog/vfprintf_c.v and fprintf_c.v
   (plain): the same cases, the same FILE words, the same post (pf_file_post here
   apf_file_post), THE SAME FIT PREMISE k + |T| <= 1024.

   The call sites (link-a/libc/printf.md (internal record, sha256 7bbba2c3aa7f) section 1): V1 reac_code_emit 0x89d1c (wrapper_vfprintf
   (f, fmt, ap), ap at reac_code_emit's spill of a4..a7, 0x89c3c..0x89c48); F1 reac_code_emit 0x89d00, F2 reac_served_mark
   0x89aec, F3 reac_served_mark 0x89b5c (wrapper_fprintf (f, fmt, s ...)). Every one prints on g_say = mark_quietly's memory FILE.

   The path of one call (neutral listings link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST)):
   - 0x4307c j 0x46a7c. ___interceptor_vfprintf 0x46a7c (frame 0x30): +0x1c..+0x20 keeps f, fmt, ap; +0x24 jal
     TryAsanInitFromRtl (0x5b214); when it returns 0, +0x88..+0xb0 a tail jump to REAL(vfprintf) (the cell 0xa3738 =
     0x973e0); else +0x2c..+0x38 lbu common_flags()->check_printf (the .got cell 0xa19c0 -> 0x13bf68, +0x54) and, when
     it is set, +0x54 jal printf_common (ctx 0x1ebfc, fmt, aq) (0x45fb4); then +0x58..+0x6c REAL(vfprintf) (f, fmt, ap)
     by jalr, +0x70.. the epilogue.
   - 0x43084 j 0x46e48. ___interceptor_fprintf 0x46e48 (frame 0x70): +0x1c..+0x30 stores a2..a7 at sp+0x40..+0x68,
     +0x34..+0x38 the va_list sp+0x40; +0x3c jal TryAsanInitFromRtl; when 0, +0x90.. REAL(vfprintf) (f, fmt, va) by
     jalr; else +0x44..+0x48 aq, +0x4c jal TryAsanInitFromRtl again (0: +0xa8.., REAL(vfprintf)); else the same
     check_printf / printf_common / REAL(vfprintf) steps as the vfprintf body (+0x54..+0xbc), +0xc0.. the epilogue.
   - musl vfprintf 0x973e0 (frame 0x170): +0x28..+0x34 reads the guard (.got 0xa2658 -> 0x651c50) into the frame;
     +0x64 printf_core (0, fmt, &ap2, nl_arg, nl_type), the format check; +0x6c lw lock: -1 (amemfile_static +140), so
     +0x70 bltz skips __lockfile; +0x90..+0x9c F_ERR cleared, the old bit kept in s5; +0x94 ld buf_size = 1024, so
     +0xa0 takes the buffered arm (no internal-buffer swap, saved_buf s4 = 0); +0xa4 ld wend: when 0, +0xd8 jal
     __towrite 0x97140 (mode |= mode - 1 (+0x0..+0x14); F_NOWR clear (+0x10, +0x18); wbase = wpos = buf, wend = buf +
     1024, rpos = rend = 0); +0x104 printf_core (f, fmt, &ap2, ...), each piece through __fwritex 0x96f50; +0x110 beqz
     s4: no flush; +0x14c..+0x164 the old F_ERR put back (the return value |T| is taken before: F_ERR is clear after
     printf_core); +0x168 bnez s3 skips __unlockfile; +0x17c..+0x184 the guard compare; +0x188.. the epilogue.
   - __fwritex 0x96f50 (frame 0x40): +0x28 ld wend (non-0 after __towrite); +0x34..+0x3c room = wend - wpos >= l, so
     +0x3c bgeu skips f->write (+0x70 jr t1, mwrite); +0x74 lw lbf = -1 (amemfile_static +144), so +0x7c bltz skips
     the line flush; +0x100 jal the memcpy wrapper 0x52d74 (wpos, s, l), +0x104..+0x10c wpos += l.
   So with k + |T| <= 1024 mwrite is not called: the text goes into the buffer after the k pending bytes, and the next
   rewind moves the buffer to g_said (LinkMfDefs.v arewind_mf_realizes).

   The windows: musl vfprintf on the GXA route takes VFA_DEPTH = 368 + PC_DEPTH 5184 = 5552 (lib/CJ/RL/GXA
   G_vfprintf_snf.v, G_printf_core_common.v: printf_core's 0x220, __fwritex's 0x40, the memcpy wrapper's ESTACK, the
   strnlen wrapper's STRN_DEPTH), printf_common 2320 below it (FMsnprintfFmI.v); so the vfprintf body needs LVF_STK =
   0x30 + 5552 and the fprintf body LFP_STK = 0x70 + 5552.

   Premise by premise (the instruction that needs it):
   - ecall_pre: the runtime calls (TryAsanInitFromRtl, printf_common, the memcpy / strnlen wrappers) and the returns
     (ret_ok ra; gp, tp);
   - ly_stk_lo ly + K <= spZ regs, [sp - K, sp) present: the frames above and the runtime windows;
   - a0 = f (+0x1c mv s1,a0; vfprintf +0x24 mv s0,a0), a1 = fmt (+0x18 mv s0,a1; vfprintf +0x20 mv s1,a1), a2 = ap
     (vfprintf body +0x14, +0x20; fprintf body: a2..a7 are the first six argument words);
   - In (f, AMF_BLOCK) (ablocks B ly S): every store into the FILE (vfprintf +0x9c, +0x164; __towrite +0x14..+0x38;
     __fwritex +0x10c) and the memcpy wrapper's destination [wpos, wpos + l) (its WRITE_RANGE: present, writable, not
     the runtime's, shadow addressable, hull readable; AR_blocks_law / AR_shadow_law of the block);
   - the FILE block apart from the window: the frames' stores do not touch the FILE, and the memcpy destination is
     outside the wrapper's window;
   - amf_k: amemfile_at (the fields read above: lock, buf, buf_size, lbf, write, flags) and the window with k pending;
   - amf_dyn: the seven words' values (flags +0, orientation +136, wend +32, wpos +40, wbase +56, the cookie's pos and
     len); amf_pend and |pb| = k: the k bytes the buffer already holds;
   - k + |T| <= AMF_BUFSIZ: __fwritex +0x3c for every piece (no f->write);
   - arodata_okP segs rlo rhi B (the callers' read-only invariant at their relro bounds, PCAP_RLO / PCAP_RHI of
     lib/A/Prog/PcapRelro.v): printf_core's tables and the formats in .rodata read as the image (with AR's pins of
     the owned .rodata redzones; the proof gets consts_view over the non-writable segments from it and AR, disco
     FMsnprintfRomO.v); the runtime cells the bodies read come from AR's const law;
   - gc -> gv -> cval (bounds, apart from the written regions): vfprintf +0x28..+0x34 and +0x17c..+0x184;
   - the argument words (vfprintf: words_at ap ws; fprintf: a2..a7 then the caller's slots at sp), apart from the
     written regions: printf_core's pop_arg, printf_common's argument walk; for vfprintf, ap at or above sp and below
     2^47: musl vfprintf keeps its va copy at 0(sp) of its frame (+0x50, +0x54), below ap (GXA printf_core: sp <= a2,
     a2 + 8 <= VA), and the GXA seam and printf_common bound the slots by 2^47 (the shadow of their bytes);
   - FF rd (vmf_out K sp f) fmt ws T: the format and the %s strings as printf_core and printf_common read them (with
     their shadow), rendering T;
   - |T| < 2^31 - 1: printf_core's count stays below INT_MAX (no EOVERFLOW, a0 = |T|);
   - frm 0 at entry: GXA's printf_core (VfprintfCall.v frm0). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. Windows and regions
   ========================================================================== *)

(* musl vfprintf's window on the GXA route (G_vfprintf_snf.v VFA_DEPTH = 368 + PC_DEPTH 5184) *)
Definition LVF_MUSL_STK : Z := 5552.
(* the vfprintf body's frame (+0x0 addi sp,sp,-0x30) above musl vfprintf's window *)
Definition LVF_STK : Z := 0x30 + LVF_MUSL_STK.
(* the fprintf body's frame (+0x0 addi sp,sp,-0x70) above musl vfprintf's window *)
Definition LFP_STK : Z := 0x70 + LVF_MUSL_STK.

(* the regions one call writes: its window and the FILE block (the FILE's first 272 bytes and the buffer) *)
Definition vmf_out (K sp f : Z) : list (Z * Z) := [(sp - K, K); (f, AMF_BLOCK)].

(* fprintf's argument words: a2..a7 (the body stores them at sp+0x40..+0x68 and points the va_list there), then the
   caller's stack slots at sp (va_words of SnShared.v with a2 first) *)
Definition fva_words (regs : bvmap 5 word) (rd : reader) (sp : Z) (xs ws : list Z) : Prop :=
  ws = map (argZ regs) [2; 3; 4; 5; 6; 7] ++ xs /\ words_at rd sp xs.

(* ==========================================================================
   2. What the call leaves on the FILE (vfprintf_c.v pf_file_post)
   ========================================================================== *)

Section c.
Variable segs : list Segment.
Variable MS : amemfile_syms.

(* the text after the k pending bytes, the window active with k + |T| pending, the flags as they were, the
   orientation -1 when __towrite ran (wend = 0 at entry), the cookie as it was *)
Definition apf_file_post (m' : word -> option byte) (f k : Z) (pb T : list Z) (fl om wend pos len : Z) : Prop :=
  amf_k segs MS m' f (k + Z.of_nat (length T)) /\
  amf_dyn segs MS m' f fl (if wend =? 0 then AU32M1 else om)
    (f + AMF_BUF + AMF_BUFSIZ) (f + AMF_BUF + k + Z.of_nat (length T)) (f + AMF_BUF) pos len /\
  amf_pend segs m' f (pb ++ T).

End c.

(* ==========================================================================
   3. The contracts
   ========================================================================== *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable MS : amemfile_syms.
Variables rlo rhi : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* vfprintf (f, fmt, ap) at pc (the wrapper 0x4307c or the runtime body 0x46a7c), entered with a stack window of K
   bytes, on link's memory FILE at f with k bytes pending *)
Definition avfprintf_mf_realizes (FF : fmt_fam) (K gc gv : Z) (pc : Z) : Prop :=
forall ly S W regs mem md (f fmt ap k fl om wend wpos wbase pos len : Z) (pb ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 f -> getr regs 11 = w64 fmt -> getr regs 12 = w64 ap ->
In (f, AMF_BLOCK) (ablocks B ly S) ->
pairwise zdisjoint (vmf_out K (spZ regs) f) ->
amf_k segs MS (rd W mem) f k ->
amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
k + Z.of_nat (length T) <= AMF_BUFSIZ ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (vmf_out K (spZ regs) f) ->
Forall (zdisjoint (gv, 8)) (vmf_out K (spZ regs) f) ->
words_at (aview segs (w_H W) mem) ap ws ->
spZ regs <= ap -> ap + 8 * Z.of_nat (length ws) <= 2 ^ 47 ->
Forall (zdisjoint (ap, 8 * Z.of_nat (length ws))) (vmf_out K (spZ regs) f) ->
FF (aview segs (w_H W) mem) (vmf_out K (spZ regs) f) fmt ws T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
apf_file_post segs MS (rd W mem') f k pb T fl om wend pos len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* fprintf (f, fmt, ...) at pc (the wrapper 0x43084 or the runtime body 0x46e48): the same, with the argument words
   a2..a7 and then the caller's stack slots xs at sp *)
Definition afprintf_mf_realizes (FF : fmt_fam) (K gc gv : Z) (pc : Z) : Prop :=
forall ly S W regs mem md (f fmt k fl om wend wpos wbase pos len : Z) (pb xs ws T : list Z) cval,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 f -> getr regs 11 = w64 fmt ->
In (f, AMF_BLOCK) (ablocks B ly S) ->
pairwise zdisjoint (vmf_out K (spZ regs) f) ->
amf_k segs MS (rd W mem) f k ->
amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
k + Z.of_nat (length T) <= AMF_BUFSIZ ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (vmf_out K (spZ regs) f) ->
Forall (zdisjoint (gv, 8)) (vmf_out K (spZ regs) f) ->
fva_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (vmf_out K (spZ regs) f) ->
FF (aview segs (w_H W) mem) (vmf_out K (spZ regs) f) fmt ws T ->
Z.of_nat (length T) < 2 ^ 31 - 1 ->
(* frm0_entry: rounding mode 0 at entry (GXA VfprintfCall.v) *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
apf_file_post segs MS (rd W mem') f k pb T fl om wend pos len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + AMF_BLOCK) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

End s.
