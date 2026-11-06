(* The closed forms of the general memchr, strnlen, strncmp and strlen wrapper contracts of reac-pw/fuzz_link's image A
   (fuzz_link.asan): each proved contract restated with its `AR_laws tfibsegs B` premise discharged by the kit's own
   law proof (Reusable/YG0q.v:805, `YG0q.AR_laws_ok tfibsegs B`), so that only the per-binary record `PcapSyms B`
   (A/AF0m.v) remains. The walks are the plugin-hostd/fuzz_command ports in this directory:
   - memchr(x, c, n) at the trampoline 0x43060: A/Rt/Memchr.v (statement lib/Rt/MemchrDef.v);
   - strnlen(x, n) at the trampoline 0x43048: A/Rt/Strnlen.v (statement lib/Rt/StrnlenDef.v);
   - strncmp(x, y, n) at the trampoline 0x43050: A/Rt/RtLStrncmpR.v (statement A/Rt/RtString.v);
   - strlen(x) at the trampoline 0x43044: A/Rt/RtSStrlen.v (statement A/Rt/RtString.v).
   Each theorem stays generic in the floating-point state and the run ceiling. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK15 YK0s YP09 YI04 YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG0v YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import ConstsViewDef MemchrDef StrnlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Memchr Strnlen RtLStrncmpR RtSStrlen.
Import ListNotations.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the per-binary record of fuzz_link.asan (A/AF0m.v) *)
Hypothesis HB : PcapSyms B.

(* memchr through __interceptor_trampoline_memchr (0x43060): any byte c, n < 2^32, found or not found *)
Theorem link_memchr_closed : amemchr_realizes tfibsegs B 0x43060.
Proof. exact (Memchr.memchr_icpt_realizes B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem link_memchrM_closed : amemchr_realizesM tfibsegs B 0x10360 0x10380 0x43060.
Proof. exact (Memchr.memchr_icpt_realizesM B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* strnlen through __interceptor_trampoline_strnlen (0x43048): n < 2^32, the result is the first NUL index or n *)
Theorem link_strnlen_closed : astrnlen_whole_realizes tfibsegs B 0x43048.
Proof. exact (Strnlen.strnlen_icpt_realizes B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem link_strnlenM_closed : astrnlen_whole_realizesM tfibsegs B 0x10360 0x10380 0x43048.
Proof. exact (Strnlen.strnlen_icpt_realizesM B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* strncmp through __interceptor_trampoline_strncmp (0x43050) *)
Theorem cmd_strncmp_closed : RtString.astrncmp_realizes tfibsegs B 0x43050.
Proof. exact (RtLStrncmpR.cmd_strncmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* strlen through __interceptor_trampoline_strlen (0x43044), window ESTACK *)
Theorem cmd_strlen_closed : RtString.astrlen_realizes tfibsegs B 0x43044.
Proof. exact (RtSStrlen.cmd_strlen B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
End closed.

About link_memchr_closed.
About link_strnlen_closed.
About cmd_strncmp_closed.
About cmd_strlen_closed.
Print Assumptions link_memchr_closed.
Print Assumptions link_memchrM_closed.
Print Assumptions link_strnlen_closed.
Print Assumptions link_strnlenM_closed.
Print Assumptions cmd_strncmp_closed.
Print Assumptions cmd_strlen_closed.
