(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 QlKV QsKa QJZd Q3Gm QGm2 QhtD QbKA QjDJ QrJ1 Qlna Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq8.
Import Q3Gm.Mq0.
Import QGm2.Mq0 QhtD.Mq0 QbKA.Mq2 QjDJ.Mq0 QrJ1.Mq0 Qlna.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition ATEXIT_A : Z := 0x642eb0.
Definition COVFLAG_A : Z := 0x1819a0.
Definition NEEDLOCKS_A : Z := 0x6430f3.

Definition ADFLAG_A : Z := 0x622150.
Definition AEF_FLAG_A : Z := 0x622154.
Definition AEF_GUARD_A : Z := 0x91a20.
Definition ATX_CALL_A : Z := 0xcc65c.
Definition ATX_COV_A : Z := 0x81058.
Definition ax_phase (m : word -> option byte) : Z := match m (Z_to_bv 64 ADFLAG_A) with None => 1 | Some _ => 2 end.
Lemma ax_phase_cases : forall m, ax_phase m = 1 \/ ax_phase m = 2.
Proof. intros m. unfold ax_phase. destruct (m (Z_to_bv 64 ADFLAG_A)); [right | left]; reflexivity. Qed.
Lemma ax_phase_agree : forall m m' : word -> option byte, m' (Z_to_bv 64 ADFLAG_A) = m (Z_to_bv 64 ADFLAG_A) -> ax_phase m' = ax_phase m.
Proof. intros m m' E. unfold ax_phase. rewrite E. reflexivity. Qed.

Ltac fold_lits :=
try unfold zxb; try unfold sxb;
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with
| context [sx32 (Z_to_bv 64 ?z)] =>
lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
let v := eval vm_compute in (Z.modulo (bv_unsigned (sx32 (Z_to_bv 64 z))) (2^64)) in
replace (sx32 (Z_to_bv 64 z) : bv 64) with (Z_to_bv 64 v : bv 64) by (apply bv_eq; vm_compute; reflexivity)
| context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac
| Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac | Z.opp _ => idtac | bv_swrap _ _ => idtac | bv_wrap _ _ => idtac | bv_signed _ => idtac
end;
closed_term e;
let v0 := eval vm_compute in e in
lazymatch v0 with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
let v := eval vm_compute in (Z.modulo v0 (2^64)) in
first [ change (Z_to_bv 64 e) with (Z_to_bv 64 v)
| replace (Z_to_bv 64 e : bv 64) with (Z_to_bv 64 v : bv 64) by (apply bv_eq; vm_compute; reflexivity) ]
end
end.

Section P4.
Context {RC__ : Q6q3.RunConsts}.

Definition atexit_cellsK (k : Z) (mid : list byte) : list cell :=
[C1 (Z_to_bv 8 0); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (ATEXIT_A + 24)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ATX_CALL_A); C8 (Z_to_bv 64 (if k =? 2 then ATX_CALL_A else 0)); CB 240 mid;
C8 (Z_to_bv 64 ATX_COV_A); C8 (Z_to_bv 64 (if k =? 2 then AEF_GUARD_A else 0))].
Definition atexit_cells_afterK (k : Z) (mid : list byte) : list cell :=
[C1 (Z_to_bv 8 1); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 32); C4 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ATX_CALL_A); C8 (Z_to_bv 64 (if k =? 2 then ATX_CALL_A else 0)); CB 240 mid;
C8 (Z_to_bv 64 ATX_COV_A); C8 (Z_to_bv 64 (if k =? 2 then AEF_GUARD_A else 0))].

Definition atexit_cells (m : word -> option byte) (mid : list byte) : list cell := atexit_cellsK (ax_phase m) mid.
Lemma atexit_cellsK_size : forall k mid, length mid = 240%nat -> cells_size (atexit_cellsK k mid) = 304%nat.
Proof. intros k mid L. cbn [atexit_cellsK cells_size csize Nat.add]. first [rewrite L; reflexivity | reflexivity]. Qed.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) (mid : list byte) (k : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (ATEXIT_A, ATEXIT_A + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' ATEXIT_A (atexit_cells_afterK k mid).

Lemma funcs_on_exit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (mid : list byte) (k : Z),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
length mid = 240%nat ->
(k = 1 \/ k = 2) ->
rw_cells asegs m ATEXIT_A (atexit_cellsK k mid) ->
ro_cells asegs m NEEDLOCKS_A [C1 (Z_to_bv 8 0)] ->
ro_cells asegs m COVFLAG_A [C1 (Z_to_bv 8 0)] ->
(k = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]) ->
evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo mid k)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcc4cc) fc None m (seg_rom asegs)).
Proof.
intros until k. intros MI ST CEIL LO LEN K12 AT NL CF AEF.
unfold funcs_on_exit_post.
destruct K12 as [PH|PH]; rewrite PH in AT |- *; [clear AEF | specialize (AEF PH)];
unfold atexit_cellsK in AT; cbn [Z.eqb Pos.eqb] in AT; unfold ATEXIT_A, NEEDLOCKS_A, COVFLAG_A, AEF_FLAG_A, AEF_GUARD_A, ATX_CALL_A, ATX_COV_A in *.
-
replace (6565552 + 24) with 6565576 in AT by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x642eb0, 0x642eb0 + 24)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step.
step.
step. step. step. if_truex. step.
step. step. if_falsex.
step. step.
step. fold_lits. stepz.
step. if_falsex.
step. (step; fold_lits). (step; fold_lits).
step. step.
step. step.
step. fold_lits. step. if_falsex. step.
step. step.
step.
step. step. step. step. if_truex. step.
step. step.
step. step. step. if_truex. step.
step. fold_lits.
step. fold_lits.
stepz.
step. if_falsex.
step. step.
step.
step. stepz. stepz.
step. if_truex.
step. stepz. step.
do 6 step.
release_frame FR ST (bv_unsigned sp).
step.
step. fold_lits. step. if_falsex. step.
apply evt_done.
do 16 eexists. split; [reflexivity|].
unfold atexit_cells_afterK. cbn [Z.eqb Pos.eqb].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact AT].
-
replace (6565552 + 24) with 6565576 in AT by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x642eb0, 0x642eb0 + 24)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step.
step.
step. step. step. if_truex. step.
step. step. if_falsex.
step. step.
step. fold_lits. stepz.
step. if_falsex.
step. (step; fold_lits). (step; fold_lits).
step. step.
step. step.
step. fold_lits. step. if_falsex. step.
step. step.
step.
step. step. step. if_falsex. step.
step. step.
step. step. step. if_truex. step.
step. fold_lits.
step. fold_lits.
stepz.
step. if_truex.
(step; fold_lits). (step; fold_lits). (step; fold_lits).
step. step.
step. step.
step. fold_lits. step. if_falsex. step.
step. step.
step.
step. step. step. step. if_truex. step.
step. step.
step. step. step. if_truex. step.
step. fold_lits.
step. fold_lits.
stepz.
step. if_falsex.
step. step.
step.
step. stepz. stepz.
step. if_truex.
step. stepz. step.
do 6 step.
release_frame FR ST (bv_unsigned sp).
step.
step. fold_lits. step. if_falsex. step.
apply evt_done.
do 16 eexists. split; [reflexivity|].
unfold atexit_cells_afterK. cbn [Z.eqb Pos.eqb].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact AT].
Qed.

Definition COMPLETED_A : Z := 0xec490.
Definition FINI_A : Z := 0xe23f0.

Definition W_FINI (usp : Z) : list (Z * Z) :=
[(usp - 304, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0a00); (FLAG_A, FLAG_A + 8); (COMPLETED_A, COMPLETED_A + 1)]%Z.

Definition exit_fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_FINI (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).

Lemma exit_fini_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 304 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
ro_cells asegs m 0xe6bb0 [C8 (Z_to_bv 64 (FINI_A + 16)); C8 (Z_to_bv 64 FINI_A)] ->
ro_cells asegs m FINI_A [C8 (Z_to_bv 64 0x99f88); C8 (Z_to_bv 64 0x3dee0)] ->
rw_cells asegs m COMPLETED_A [C1 (Z_to_bv 8 0)] ->
ro_cells asegs m 0xe5d88 [C8 (Z_to_bv 64 0xcc594); C8 (Z_to_bv 64 0)] ->
ro_cells asegs m 0xe7c00 [C8 dso] ->
ro_cells asegs m 0xe5d98 (got9 g0 g1 g5 g6 g7) ->
ro_cells asegs m 0xe6ab0 [C8 (Z_to_bv 64 AGLOB_START); C8 (Z_to_bv 64 AGLOB_STOP)] ->
ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xed310 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xef35c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
rw_cells asegs m MUTEX_A [C8 (Z_to_bv 64 0)] ->
rw_cells asegs m FLAG_A [C8 (Z_to_bv 64 1)] ->
recs_ro m AGLOB_START tokA_globals8 -> shadows_rw m tokA_globals8 -> rw_cells asegs m ODR_A [C1 ob] ->
rw_cells asegs m META_SH [CB 856 junkM] ->
evt asegs (exit_fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcc664) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL GOTF FINI COMP GOTW DSO GOT GOT2 INITED RG SB CP THR RM MUT FLAG RR SW ODRB MSH.
unfold FINI_A, COMPLETED_A, AGLOB_START, AGLOB_STOP, FLAG_A, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
replace (926712 + 16) with 926728 in GOTF by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xec490, 0xec490 + 1)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
do 4 step.
do 4 step.
step. if_falsex.
step. (step; fold_lits).
step.

carve_frame 16%nat ST.
step. stepz. stepz. step.
step. step. step. fold_lits. step. fold_lits.
step. if_truex.
step. step. step. stepz.
step. step. step. if_falsex.
step.
step. step. step.
step. step.
step.
step. step. step. if_truex.
step. step. step.
release_frame FR0 ST (bv_unsigned sp - 32).
step.
step. step. if_truex.
step. (step; fold_lits). step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (module_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| unfold got9; exact GOT | exact GOT2 | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM | exact MUT | exact FLAG
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | exact MSH ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MUT3 & FLAG3 & [ob3 ODRB3] & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH in MUc, MUT3, FLAG3, ODRB3, MSH3.
clear MSH ST ODRB MUT FLAG MI RR SW.
assert (MU' : munch (W_FINI (bv_unsigned sp)) m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 0xcc694)) with (Z_to_bv 64 0xcc694 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A in MU.
step. step. if_falsex.
step. step. step. step.
release_frame FR ST3 (bv_unsigned sp).
step. step.
apply evt_done. unfold exit_fini_post.
do 16 eexists. split; [reflexivity|].
unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A.
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST3].
Qed.
End P4.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3Gm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3Gm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrJ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrJ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlna.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlna.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition ATEXIT_A : Z := 0x645570.
Definition COVFLAG_A : Z := 0x184060.
Definition NEEDLOCKS_A : Z := 0x6457b3.

Definition ADFLAG_A : Z := 0x624810.
Definition AEF_FLAG_A : Z := 0x624814.
Definition AEF_GUARD_A : Z := 0x91df8.
Definition ATX_CALL_A : Z := 0xced20.
Definition ATX_COV_A : Z := 0x81430.
Definition ax_phase (m : word -> option byte) : Z := match m (Z_to_bv 64 ADFLAG_A) with None => 1 | Some _ => 2 end.
Lemma ax_phase_cases : forall m, ax_phase m = 1 \/ ax_phase m = 2.
Proof. intros m. unfold ax_phase. destruct (m (Z_to_bv 64 ADFLAG_A)); [right | left]; reflexivity. Qed.
Lemma ax_phase_agree : forall m m' : word -> option byte, m' (Z_to_bv 64 ADFLAG_A) = m (Z_to_bv 64 ADFLAG_A) -> ax_phase m' = ax_phase m.
Proof. intros m m' E. unfold ax_phase. rewrite E. reflexivity. Qed.

Ltac fold_lits :=
try unfold zxb; try unfold sxb;
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with
| context [sx32 (Z_to_bv 64 ?z)] =>
lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
let v := eval vm_compute in (Z.modulo (bv_unsigned (sx32 (Z_to_bv 64 z))) (2^64)) in
replace (sx32 (Z_to_bv 64 z) : bv 64) with (Z_to_bv 64 v : bv 64) by (apply bv_eq; vm_compute; reflexivity)
| context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac
| Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac | Z.opp _ => idtac | bv_swrap _ _ => idtac | bv_wrap _ _ => idtac | bv_signed _ => idtac
end;
closed_term e;
let v0 := eval vm_compute in e in
lazymatch v0 with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
let v := eval vm_compute in (Z.modulo v0 (2^64)) in
first [ change (Z_to_bv 64 e) with (Z_to_bv 64 v)
| replace (Z_to_bv 64 e : bv 64) with (Z_to_bv 64 v : bv 64) by (apply bv_eq; vm_compute; reflexivity) ]
end
end.

Section P4.
Context {RC__ : Q6q3.RunConsts}.

Definition atexit_cellsK (k : Z) (mid : list byte) : list cell :=
[C1 (Z_to_bv 8 0); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (ATEXIT_A + 24)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ATX_CALL_A); C8 (Z_to_bv 64 (if k =? 2 then ATX_CALL_A else 0)); CB 240 mid;
C8 (Z_to_bv 64 ATX_COV_A); C8 (Z_to_bv 64 (if k =? 2 then AEF_GUARD_A else 0))].
Definition atexit_cells_afterK (k : Z) (mid : list byte) : list cell :=
[C1 (Z_to_bv 8 1); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 32); C4 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ATX_CALL_A); C8 (Z_to_bv 64 (if k =? 2 then ATX_CALL_A else 0)); CB 240 mid;
C8 (Z_to_bv 64 ATX_COV_A); C8 (Z_to_bv 64 (if k =? 2 then AEF_GUARD_A else 0))].

Definition atexit_cells (m : word -> option byte) (mid : list byte) : list cell := atexit_cellsK (ax_phase m) mid.
Lemma atexit_cellsK_size : forall k mid, length mid = 240%nat -> cells_size (atexit_cellsK k mid) = 304%nat.
Proof. intros k mid L. cbn [atexit_cellsK cells_size csize Nat.add]. first [rewrite L; reflexivity | reflexivity]. Qed.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) (mid : list byte) (k : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (ATEXIT_A, ATEXIT_A + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' ATEXIT_A (atexit_cells_afterK k mid).

Lemma funcs_on_exit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (mid : list byte) (k : Z),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
length mid = 240%nat ->
(k = 1 \/ k = 2) ->
rw_cells asegs m ATEXIT_A (atexit_cellsK k mid) ->
ro_cells asegs m NEEDLOCKS_A [C1 (Z_to_bv 8 0)] ->
ro_cells asegs m COVFLAG_A [C1 (Z_to_bv 8 0)] ->
(k = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]) ->
evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo mid k)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb90) fc None m (seg_rom asegs)).
Proof.
intros until k. intros MI ST CEIL LO LEN K12 AT NL CF AEF.
unfold funcs_on_exit_post.
destruct K12 as [PH|PH]; rewrite PH in AT |- *; [clear AEF | specialize (AEF PH)];
unfold atexit_cellsK in AT; cbn [Z.eqb Pos.eqb] in AT; unfold ATEXIT_A, NEEDLOCKS_A, COVFLAG_A, AEF_FLAG_A, AEF_GUARD_A, ATX_CALL_A, ATX_COV_A in *.
-
replace (6575472 + 24) with 6575496 in AT by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x645570, 0x645570 + 24)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step.
step.
step. step. step. if_truex. step.
step. step. if_falsex.
step. step.
step. fold_lits. stepz.
step. if_falsex.
step. (step; fold_lits). (step; fold_lits).
step. step.
step. step.
step. fold_lits. step. if_falsex. step.
step. step.
step.
step. step. step. step. if_truex. step.
step. step.
step. step. step. if_truex. step.
step. fold_lits.
step. fold_lits.
stepz.
step. if_falsex.
step. step.
step.
step. stepz. stepz.
step. if_truex.
step. stepz. step.
do 6 step.
release_frame FR ST (bv_unsigned sp).
step.
step. fold_lits. step. if_falsex. step.
apply evt_done.
do 16 eexists. split; [reflexivity|].
unfold atexit_cells_afterK. cbn [Z.eqb Pos.eqb].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact AT].
-
replace (6575472 + 24) with 6575496 in AT by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x645570, 0x645570 + 24)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step.
step.
step. step. step. if_truex. step.
step. step. if_falsex.
step. step.
step. fold_lits. stepz.
step. if_falsex.
step. (step; fold_lits). (step; fold_lits).
step. step.
step. step.
step. fold_lits. step. if_falsex. step.
step. step.
step.
step. step. step. if_falsex. step.
step. step.
step. step. step. if_truex. step.
step. fold_lits.
step. fold_lits.
stepz.
step. if_truex.
(step; fold_lits). (step; fold_lits). (step; fold_lits).
step. step.
step. step.
step. fold_lits. step. if_falsex. step.
step. step.
step.
step. step. step. step. if_truex. step.
step. step.
step. step. step. if_truex. step.
step. fold_lits.
step. fold_lits.
stepz.
step. if_falsex.
step. step.
step.
step. stepz. stepz.
step. if_truex.
step. stepz. step.
do 6 step.
release_frame FR ST (bv_unsigned sp).
step.
step. fold_lits. step. if_falsex. step.
apply evt_done.
do 16 eexists. split; [reflexivity|].
unfold atexit_cells_afterK. cbn [Z.eqb Pos.eqb].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact AT].
Qed.

Definition COMPLETED_A : Z := 0xeeb50.
Definition FINI_A : Z := 0xe4ab8.

Definition W_FINI (usp : Z) : list (Z * Z) :=
[(usp - 304, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0e00); (FLAG_A, FLAG_A + 8); (COMPLETED_A, COMPLETED_A + 1)]%Z.

Definition exit_fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_FINI (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp).

Lemma exit_fini_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 304 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
ro_cells asegs m 0xe8fc0 [C8 (Z_to_bv 64 (FINI_A + 16)); C8 (Z_to_bv 64 FINI_A)] ->
ro_cells asegs m FINI_A [C8 (Z_to_bv 64 0x9b3cc); C8 (Z_to_bv 64 0x3e10c)] ->
rw_cells asegs m COMPLETED_A [C1 (Z_to_bv 8 0)] ->
ro_cells asegs m 0xe8188 [C8 (Z_to_bv 64 0xcec58); C8 (Z_to_bv 64 0)] ->
ro_cells asegs m 0xea020 [C8 dso] ->
ro_cells asegs m 0xe8198 (got9 g0 g1 g5 g6 g7) ->
ro_cells asegs m 0xe8ec0 [C8 (Z_to_bv 64 AGLOB_START); C8 (Z_to_bv 64 AGLOB_STOP)] ->
ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xef9d0 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xf1a1c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
rw_cells asegs m MUTEX_A [C8 (Z_to_bv 64 0)] ->
rw_cells asegs m FLAG_A [C8 (Z_to_bv 64 1)] ->
recs_ro m AGLOB_START tokA_globals8 -> shadows_rw m tokA_globals8 -> rw_cells asegs m ODR_A [C1 ob] ->
rw_cells asegs m META_SH [CB 856 junkM] ->
evt asegs (exit_fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced28) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL GOTF FINI COMP GOTW DSO GOT GOT2 INITED RG SB CP THR RM MUT FLAG RR SW ODRB MSH.
unfold FINI_A, COMPLETED_A, AGLOB_START, AGLOB_STOP, FLAG_A, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
replace (936640 + 16) with 936656 in GOTF by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xeeb50, 0xeeb50 + 1)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
do 4 step.
do 4 step.
step. if_falsex.
step. (step; fold_lits).
step.

carve_frame 16%nat ST.
step. stepz. stepz. step.
step. step. step. fold_lits. step. fold_lits.
step. if_truex.
step. step. step. stepz.
step. step. step. if_falsex.
step.
step. step. step.
step. step.
step.
step. step. step. if_truex.
step. step. step.
release_frame FR0 ST (bv_unsigned sp - 32).
step.
step. step. if_truex.
step. (step; fold_lits). step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (module_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| unfold got9; exact GOT | exact GOT2 | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM | exact MUT | exact FLAG
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | exact MSH ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MUT3 & FLAG3 & [ob3 ODRB3] & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH in MUc, MUT3, FLAG3, ODRB3, MSH3.
clear MSH ST ODRB MUT FLAG MI RR SW.
assert (MU' : munch (W_FINI (bv_unsigned sp)) m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 0xced58)) with (Z_to_bv 64 0xced58 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A in MU.
step. step. if_falsex.
step. step. step. step.
release_frame FR ST3 (bv_unsigned sp).
step. step.
apply evt_done. unfold exit_fini_post.
do 16 eexists. split; [reflexivity|].
unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A.
split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST3].
Qed.
End P4.
