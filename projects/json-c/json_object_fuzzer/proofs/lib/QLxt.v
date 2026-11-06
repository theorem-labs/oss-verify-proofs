(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QZzg QTVW QbcP_c1 Qu4g QN4c QMSY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QZzg QTVW QbcP_c1 Qu4g QN4c QMSY.Mq0.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma classid_block2 : forall (n : Z) ra sp gp tp t0 t1 t2 s0 s1 (a0v : Z) a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (Q : machine_state -> Prop),
1 <= n <= 65536 -> 0 <= a0v -> a0v + 112 < 2^64 ->
(forall a2' a3' a4' a5' a6',
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a0v + 112)) (wz (class_id n)) a2' a3' a4' a5' a6' a7 s2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f924) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz a0v) a1 a2 a3 a4 a5 a6 a7 s2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f830) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hn A0 A1 CONT.
step.
step.
step.
destruct (Z.leb_spec n 512) as [SM|BG].
- ifz.
step. step.
rewrite (unsigned_lit (n + 31)), Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite <- class_id_small by lia.
step.
apply CONT.
- ifz.
set (cv0 := wz n) in |- *.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 13%Z.
stp. sname 14%Z.
stp. sname 15%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 13%Z.
stp. sname 14%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 12%Z.
stp. sname 16%Z.
stp. sname 13%Z.
stp. sname 16%Z.
stp. sname 14%Z.
stp. sname 16%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 13%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 11%Z.
assert (E36 : cv36 = wz (class_id n)).
{ revert cv36. revert cv35. revert cv34. revert cv33. revert cv32. revert cv31. revert cv30. revert cv29. revert cv28. revert cv27.
revert cv26. revert cv25. revert cv24. revert cv23. revert cv22. revert cv21. revert cv20. revert cv19. revert cv18. revert cv17.
revert cv16. revert cv15. revert cv14. revert cv13. revert cv12. revert cv11. revert cv10. revert cv9. revert cv8. revert cv7.
revert cv6. revert cv5. revert cv4. revert cv3. revert cv2. revert cv1. revert cv. revert cv0.
exact (cid_goal n ltac:(lia)). }
rewrite E36. apply CONT.
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMSY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMSY.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Lemma classid_block2 : forall (n : Z) ra sp gp tp t0 t1 t2 s0 s1 (a0v : Z) a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (Q : machine_state -> Prop),
1 <= n <= 65536 -> 0 <= a0v -> a0v + 112 < 2^64 ->
(forall a2' a3' a4' a5' a6',
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a0v + 112)) (wz (class_id n)) a2' a3' a4' a5' a6' a7 s2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f6f8) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz a0v) a1 a2 a3 a4 a5 a6 a7 s2 (wz n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f604) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hn A0 A1 CONT.
step.
step.
step.
destruct (Z.leb_spec n 512) as [SM|BG].
- ifz.
step. step.
rewrite (unsigned_lit (n + 31)), Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. rewrite <- class_id_small by lia.
step.
apply CONT.
- ifz.
set (cv0 := wz n) in |- *.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 13%Z.
stp. sname 14%Z.
stp. sname 15%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 13%Z.
stp. sname 14%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 12%Z.
stp. sname 16%Z.
stp. sname 13%Z.
stp. sname 16%Z.
stp. sname 14%Z.
stp. sname 16%Z.
stp. sname 15%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 16%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 13%Z.
stp. sname 11%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 14%Z.
stp. sname 12%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 12%Z.
stp. sname 11%Z.
stp. sname 11%Z.
assert (E36 : cv36 = wz (class_id n)).
{ revert cv36. revert cv35. revert cv34. revert cv33. revert cv32. revert cv31. revert cv30. revert cv29. revert cv28. revert cv27.
revert cv26. revert cv25. revert cv24. revert cv23. revert cv22. revert cv21. revert cv20. revert cv19. revert cv18. revert cv17.
revert cv16. revert cv15. revert cv14. revert cv13. revert cv12. revert cv11. revert cv10. revert cv9. revert cv8. revert cv7.
revert cv6. revert cv5. revert cv4. revert cv3. revert cv2. revert cv1. revert cv. revert cv0.
exact (cid_goal n ltac:(lia)). }
rewrite E36. apply CONT.
Qed.
