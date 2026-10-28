(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Qc3B QZDE QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import UEQM.
Import Qc3B QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import Qsw7 QJjn QRUw QRUw.Mq2.
Import QSL3.
Import TopUbTac.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac genregs SPV :=
repeat (match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Some ?v] =>
tryif is_var v then fail else
lazymatch v with
| Z_to_bv _ ?z =>
match z with context [bv_unsigned ?x] => is_var x; tryif constr_eq x SPV then fail else (generalize v; intros ?w) end
| _ => generalize v; intros ?w
end end end).
Ltac hstep SPV := step; genregs SPV.
Ltac tstep SPV := ub_skip; step; genregs SPV.

Section HashCore.
Variables (kp : Z) (ks slack : list byte) (m : word -> option byte).
Let full := ks ++ Z_to_bv 8 0 :: slack.
Let len := Z.of_nat (length ks).
Hypothesis STR : bytes_at rsegs m kp full.
Hypothesis MI : mem_inv rsegs m.
Hypothesis AL : kp mod 4 = 0.
Hypothesis KP0 : 0 < kp.

#[using="slack full STR AL KP0"] Lemma hash_loop :
forall (k : nat) (j : Z) (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
(k = Z.to_nat (len - j))%nat -> 0 <= j -> 12 < len - j -> j mod 4 = 0 ->
evt rsegs (fun ms' => exists (j' : Z) (t0' t1' t2' a1' a2' a3' t3' : word),
0 <= j' /\ 0 <= len - j' <= 12 /\ j' mod 4 = 0 /\
ms' = MS (mkR x1 sp gp tp t0' t1' t2' (Z_to_bv 64 (kp + j')) x9 (Z_to_bv 64 (len - j')) a1' a2' a3' (Z_to_bv 64 (-4)) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-13)) (Z_to_bv 64 12) x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F (Z_to_bv 64 0x27c8c) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) x9 (Z_to_bv 64 (len - j)) a1 a2 a3 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-13)) (Z_to_bv 64 12) x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x27a20) fc None m (seg_rom rsegs)).
Proof.
induction k as [k IH] using lt_wf_ind; intros until fc; intros Hk Hj Hr Hal.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bytes_at_read rsegs m kp full j 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD0.
pose proof (bytes_at_read rsegs m kp full (j + 4) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD1.
pose proof (bytes_at_read rsegs m kp full (j + 8) 4 STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as RD2.
assert (KB : kp + j + 13 <= 2^64 - 1) by lia.
step. if_falsex. step. if_falsex. step. if_falsex. step. if_falsex.
do 46 (hstep sp).
replace (kp + j + 12) with (kp + (j + 12)) by lia. replace (len - j + -12) with (len - (j + 12)) by lia.
destruct (Z.lt_ge_cases 12 (len - (j + 12))) as [LT | GE].
- if_truex. eapply (IH (Z.to_nat (len - (j + 12)))); try lia; rewrite <- Zplus_mod_idemp_l, Hal; reflexivity.
- if_falsex. step. step. apply evt_done. exists (j + 12). do 7 eexists.
split; [lia|]. split; [lia|]. split; [rewrite <- Zplus_mod_idemp_l, Hal; reflexivity|]. reflexivity.
Qed.
Ltac tstep_to PC SPV :=
repeat (lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 PC) _ _ _ _) => fail
| |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => tstep SPV
end);
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 PC) _ _ _ _) => idtac
| |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "tstep_to: stuck at" pc; fail
end.
Ltac rd j off n H :=
pose proof (bytes_at_read rsegs m kp full (j + off) n STR ltac:(lia) ltac:(unfold full; rewrite length_app; cbn; lia)) as H.

#[using="slack full STR MI AL KP0"] Lemma hash_tail :
forall (j : Z) (x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32),
0 <= j -> 0 <= len - j <= 12 -> j mod 4 = 0 ->
evt rsegs (fun ms' => exists (u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word),
ms' = MS (mkR x1 sp gp tp u0 u1 u2 (Z_to_bv 64 (kp + j)) x9 v0 v1 v2 v3 v4 v5 v6 v7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 0x282dc) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (kp + j)) x9 (Z_to_bv 64 (len - j)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x27c8c) fc None m (seg_rom rsegs)).
Proof.
intros until fc; intros Hj Hr Hal.
pose proof (bytes_at_bound _ _ _ _ STR) as AB. unfold full in AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
assert (CASES : len - j = 0 \/ len - j = 1 \/ len - j = 2 \/ len - j = 3 \/ len - j = 4 \/ len - j = 5 \/ len - j = 6 \/
len - j = 7 \/ len - j = 8 \/ len - j = 9 \/ len - j = 10 \/ len - j = 11 \/ len - j = 12) by lia.
destruct CASES as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]; rewrite E.
- tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 1%nat RDa. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 2%nat RDa. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 1%nat RDb. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 2%nat RDb. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 1%nat RDc. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 2%nat RDc. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 4%nat RDc. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
- rd j 0 4%nat RDa. rd j 4 4%nat RDb. rd j 8 4%nat RDc. tstep_to 0x282dc sp. apply evt_done; do 15 eexists; reflexivity.
Qed.
End HashCore.

End Mq0.
