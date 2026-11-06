(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 Qc3B Q9A7 Q5Rg QZAi QfYR Qx2n QTp6 QJVP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 Qc3B Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR Qx2n.
Import QTp6.
Import QJVP.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Definition rstrtod_total_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
bytes_at rsegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> zlength pre < 2^31 -> zlength txt <= 2^40 ->
rw_cells rsegs m PE [C8 ejunk] ->
scan_strtod_h txt = Some (bits, used) ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
0 < T ->
(((T + zlength txt <= RIMG_LO \/ RGLOBALS_TOP <= T) /\ T + zlength txt <= lo) \/ bv_unsigned sp <= T) ->
T + 2^41 <= 2^63 -> ((RGLOBALS_TOP <= PE /\ PE + 8 <= lo) \/ bv_unsigned sp <= PE) -> PE + 8 <= 2^63 ->
(PE + 8 <= T \/ T + zlength txt <= PE) ->
ssp_cells m canary -> rw_cells rsegs m RERRNO [C4 ev] ->
mem_inv rsegs m -> frm0 fc ->
tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
evt rsegs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom rsegs)).

Definition scan_strtod_h_total_stmt : Prop :=
forall l, Forall (fun c => 0 <= c < 256) l -> exists bits used, scan_strtod_h (l ++ [0]) = Some (bits, used) /\ 0 <= used.

End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJVP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJVP.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Definition rstrtod_total_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
bytes_at usegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
txt = pre ++ 0 :: post -> zlength pre < 2^31 -> zlength txt <= 2^40 ->
rw_cells usegs m PE [C8 ejunk] ->
scan_strtod_h txt = Some (bits, used) ->
stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
0 < T ->
(((T + zlength txt <= RIMG_LO \/ RGLOBALS_TOP <= T) /\ T + zlength txt <= lo) \/ bv_unsigned sp <= T) ->
T + 2^41 <= 2^63 -> ((RGLOBALS_TOP <= PE /\ PE + 8 <= lo) \/ bv_unsigned sp <= PE) -> PE + 8 <= 2^63 ->
(PE + 8 <= T \/ T + zlength txt <= PE) ->
ssp_cells m canary -> rw_cells usegs m RERRNO [C4 ev] ->
mem_inv usegs m -> frm0 fc ->
tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
evt usegs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom usegs)).

Definition scan_strtod_h_total_stmt : Prop :=
forall l, Forall (fun c => 0 <= c < 256) l -> exists bits used, scan_strtod_h (l ++ [0]) = Some (bits, used) /\ 0 <= used.

