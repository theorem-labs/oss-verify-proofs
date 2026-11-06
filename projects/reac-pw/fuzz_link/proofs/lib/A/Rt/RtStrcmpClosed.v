(* The closed forms of the strcmp wrapper contracts of reac-pw/fuzz_link's image A (fuzz_link.asan), at the trampoline
   0x4304c (`j 0x4360c`, the entry of the runtime's strcmp, 1328 bytes, which on the path the walk covers compares the
   two strings by itself and does not reach musl's strcmp 0x9b1bc): each proved contract with its `AR_laws tfibsegs B`
   premise discharged by the kit's own law proof (Reusable/YG0q.v, `YG0q.AR_laws_ok tfibsegs B`), so that only the
   per-binary record `PcapSyms B` (A/AF0m.v) remains. The walks are the plugin-hostd/fuzz_command ports in this
   directory:
   - Reusable/AStrcmpDef.v astrcmp_realizes (the compare stops at an index k; the checks read [x, x + k + 1) and
     [y, y + k + 1), each outside the stack window [sp - 2 * ESTACK, sp)): A/Rt/RtStrcmp.v cmd_strcmp_tramp;
   - A/Rt/RtString.v astrcmp_realizes (two C strings, each readable outside the same window over its whole length
     and NUL; the answer word is 0 exactly when the strings are equal): A/Rt/RtStrcmpC.v cmd_strcmp, which reads the
     first form's premises off the second's.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtStrcmp RtStrcmpC.
Import ListNotations.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* the per-binary record of fuzz_link.asan (A/AF0m.v) *)
Hypothesis HB : PcapSyms B.

(* strcmp through __interceptor_trampoline_strcmp (0x4304c), the stop-index form *)
Theorem link_astrcmp_closed : AStrcmpDef.astrcmp_realizes tfibsegs B 0x4304c.
Proof. exact (RtStrcmp.cmd_strcmp_tramp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* strcmp through __interceptor_trampoline_strcmp (0x4304c), the C-string form *)
Theorem link_strcmp_closed : RtString.astrcmp_realizes tfibsegs B 0x4304c.
Proof. exact (RtStrcmpC.cmd_strcmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
End closed.

About link_astrcmp_closed.
About link_strcmp_closed.
Print Assumptions link_astrcmp_closed.
Print Assumptions link_strcmp_closed.
