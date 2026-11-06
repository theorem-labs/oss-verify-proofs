(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contracts of the format entries that plugin-hostd/fuzz_command calls and cgif_file_fuzzer does not (snprintf, sprintf), in the form cgif_file_fuzzer's lib/YG0d.v states its interceptor contracts; the text they write is the one fuzz_command's own plain proof states for musl's printf core (lib/Prog/printf_facts_c.v), with its argument premise restated over the asan view of memory. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtFormat.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

Module PF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.printf_facts_c.

(* The entries, on the pinned image: snprintf 0x45184 -> ___interceptor_snprintf 0x49fb8 -> the vsnprintf
   interceptor 0x49858, which calls musl's vsnprintf through the slot at 0xa8198 (value 0x9e490);
   sprintf 0x45180 -> ___interceptor_sprintf 0x49f28 -> the vsprintf interceptor 0x49b70, slot 0xa81a0
   (value 0x9e638). musl's vsprintf is five instructions and tail-jumps to the vsnprintf trampoline 0x45178
   (0x9e648), so a sprintf call runs the vsnprintf interceptor a second time; musl's vsnprintf then reaches
   the printf core through the vfprintf trampoline 0x45174 -> 0x497a4 -> slot 0xa8190 -> musl vfprintf
   0x9b364 -> printf_core 0x9b514. The pieces of the format, the text they produce and the shape of an
   argument are fuzz_command's own plain definitions (lib/Prog/printf_facts_c.v:10-91); only the premise
   that each pointer argument is readable is restated here over the asan view.

   The scratch window is 3 * ESTACK = 12288 bytes: the measured worst case below the trampoline's entry sp
   is 6,672 bytes for snprintf and 8,816 for sprintf, against 5936 for the same chain without ASan
   (lib/Prog/snprintf_c.v:17 SNPRINTF_K). Every musl body of the chain (vsnprintf 0x9e490, vfprintf 0x9b364,
   printf_core 0x9b514, pad 0x9c478) is built with the stack protector, so both entries carry aguard_ok over
   the cells 0xa7098 -> 0x6045d8. A wider window would not fit the budget the program interface gives the
   fuzz-target entry (LLVMF_STK). *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation WR stk := (awrite_ok segs B stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

Definition apf_arg_ok (stk : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
(D n : Z) (r : word) (a : PF.pf_arg) : Prop :=
match a with
| PF.AInt v => -2^31 <= v < 2^31 /\ bv_unsigned r mod 2^32 = v mod 2^32
| PF.AU64 u => bv_unsigned r = u
| PF.APtr s =>
Forall (fun c => 0 < c < 256) s /\
0 < bv_unsigned r /\
STR W mem (bv_unsigned r) (PF.pf_bytes s) /\
RD stk W regs mem (bv_unsigned r) (Z.of_nat (length s) + 1) /\
atail_vis segs W mem (bv_unsigned r + Z.of_nat (length s)) /\
(bv_unsigned r + Z.of_nat (length s) + 1 <= D \/ D + n <= bv_unsigned r)
end.

Fixpoint apf_args_ok (stk : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
(D n : Z) (rs : list word) (args : list PF.pf_arg) : Prop :=
match args, rs with
| [], _ => True
| a :: args', r :: rs' => apf_arg_ok stk W regs mem D n r a /\ apf_args_ok stk W regs mem D n rs' args'
| _ :: _, [] => False
end.

(* snprintf(d, n, fmt, ...) and sprintf(d, fmt, ...). Since 2026-10-29 these are the stream's shared contracts
   (omx-clap-core/fuzz_manifest's lib/A/FMsnprintfShared.v) instantiated at this
   image's format family FR_cmd, so there is one text per function across the units: see lib/A/Rt/RtPFCmd.v, which
   states asnprintf_sh and asprintf_sh over the copies RtPFShared.v, RtPFPf.v, RtPFSx.v, RtPFupoison.v. For the GXA
   route FR_cmd has fuzz_manifest's FF_fm shape, the read-only lists are the image's two read-only
   segments, and the one premise our texts change in the shared one is consts_view over those lists, replaced by
   RtDefs.rt_rom_view (the unowned read-only bytes; the proof gets the owned ones from AR, RtPFCv.v).
   The earlier local forms were dropped: the shared post is FP-existential by design (GXA's
   pop_arg loses fa0), which a `forall fx` form cannot give, and the shared text carries six premises the local one
   lacked (rounding mode 0 at entry, every %.*s precision >= 1, the format kept off the destination, |s| + 8 < 2^31,
   the word tail after each string kept off the destination, and dest_off_globals). Windows, measured on this image:
   CMD_SNP_K = 2 * ESTACK (glue 2,608 + GXA's VF_DEPTH 5,552 = 8,160) and CMD_SP_K = 3 * ESTACK (glue 4,752 + 5,552 =
   10,304, sprintf running the vsnprintf interceptor twice); a caller may lift either with RtPFSx.sh_asnprintf_mono.
   The apf_arg_ok / apf_args_ok definitions above are kept for the callers that still name them. *)
Definition asnprintf_realizes (pc gotw guard : Z) : Prop := RtPFCmd.asnprintf_sh segs B pc gotw guard.

Definition asprintf_realizes (pc gotw guard : Z) : Prop := RtPFCmd.asprintf_sh segs B pc gotw guard.
End c.
End b.

