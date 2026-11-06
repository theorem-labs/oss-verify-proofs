(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 QlKV QsKa QJZd Q3Gm QGm2 QhtD QbKA QjDJ QrJ1 Q6q3.
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
Import QGm2.Mq0 QhtD.Mq0 QbKA.Mq2 QjDJ.Mq0 QrJ1.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition FLAG_A : Z := 0xec440.

Definition W_DTOR (usp : Z) : list (Z * Z) :=
[(usp - 272, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0a00); (FLAG_A, FLAG_A + 8)]%Z.

Definition W_ELF (usp : Z) : list (Z * Z) :=
[(usp - 256, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0a00); (FLAG_A, FLAG_A + 8)]%Z.

Section P3.
Context {RC__ : Q6q3.RunConsts}.

Definition unreg_elf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_ELF (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' MUTEX_A [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' FLAG_A [C8 (Z_to_bv 64 0)]
/\ (exists ob', rw_cells asegs m' ODR_A [C1 ob']) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma unreg_elf_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 256 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp + 16 <= 2^64 ->
a0 = Z_to_bv 64 FLAG_A -> a1 = Z_to_bv 64 AGLOB_START -> a2 = Z_to_bv 64 AGLOB_STOP ->
ro_cells asegs m 0xe5d98 (got9 g0 g1 g5 g6 g7) ->
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
evt asegs (unreg_elf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4d8f8) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL SPH A0 A1 A2 GOT INITED RG SB CP THR RM MUT FLAG RR SW ODRB MSH. subst a0 a1 a2.
unfold AGLOB_START, AGLOB_STOP, FLAG_A, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. if_falsex.
step. step. step. if_falsex.
do 3 (step; fold_closed_bv2). if_falsex.
step.
match goal with |- context [Z_to_bv 64 (Z.shiftr ?a ?b)] => let v := eval vm_compute in (Z.shiftr a b) in change (Z_to_bv 64 (Z.shiftr a b)) with (Z_to_bv 64 v : bv 64) end || idtac.
fold_closed_bv2.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (unreg_globals_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| reflexivity | reflexivity | unfold got9; exact GOT | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM | exact MUT
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | exact MSH ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MUT3 & [ob3 ODRB3] & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold W_UNREG, MUTEX_A, W_ODR, ODR_A, META_SH in MUc, MUT3, ODRB3, MSH3.
clear MSH ST ODRB MUT MI RR SW.
assert (MU' : munch (W_ELF (bv_unsigned sp)) m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs m1 m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 317744)) with (Z_to_bv 64 317744 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A in MU.
stepz.
step. step. step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_done. unfold unreg_elf_post.
do 16 eexists.
split; [reflexivity|].
unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH.
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
split; [exact MUT3|]. split; [exact FLAG|]. split; [exists ob3; exact ODRB3 | exact MSH3].
Qed.

Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_DTOR (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' MUTEX_A [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' FLAG_A [C8 (Z_to_bv 64 0)]
/\ (exists ob', rw_cells asegs m' ODR_A [C1 ob']) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma module_dtor_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
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
evt asegs (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x99f88) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL GOT GOT2 INITED RG SB CP THR RM MUT FLAG RR SW ODRB MSH.
unfold AGLOB_START, AGLOB_STOP, FLAG_A, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step.
do 6 step. fold_closed_bv2.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (unreg_elf_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity | reflexivity | unfold got9; exact GOT | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM | exact MUT | exact FLAG
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | exact MSH ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MUT3 & FLAG3 & [ob3 ODRB3] & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH in MUc, MUT3, FLAG3, ODRB3, MSH3.
clear MSH ST ODRB MUT FLAG MI RR SW.
assert (MU' : munch (W_DTOR (bv_unsigned sp)) m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 0x99fac)) with (Z_to_bv 64 0x99fac : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A in MU.
step. step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_done. unfold module_dtor_post.
do 16 eexists.
split; [reflexivity|].
unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH.
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
split; [exact MUT3|]. split; [exact FLAG3|]. split; [exists ob3; exact ODRB3 | exact MSH3].
Qed.
End P3.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrJ1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition FLAG_A : Z := 0xeeb00.

Definition W_DTOR (usp : Z) : list (Z * Z) :=
[(usp - 272, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0e00); (FLAG_A, FLAG_A + 8)]%Z.

Definition W_ELF (usp : Z) : list (Z * Z) :=
[(usp - 256, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0e00); (FLAG_A, FLAG_A + 8)]%Z.

Section P3.
Context {RC__ : Q6q3.RunConsts}.

Definition unreg_elf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_ELF (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' MUTEX_A [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' FLAG_A [C8 (Z_to_bv 64 0)]
/\ (exists ob', rw_cells asegs m' ODR_A [C1 ob']) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma unreg_elf_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 256 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
bv_unsigned sp + 16 <= 2^64 ->
a0 = Z_to_bv 64 FLAG_A -> a1 = Z_to_bv 64 AGLOB_START -> a2 = Z_to_bv 64 AGLOB_STOP ->
ro_cells asegs m 0xe8198 (got9 g0 g1 g5 g6 g7) ->
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
evt asegs (unreg_elf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4dcd0) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL SPH A0 A1 A2 GOT INITED RG SB CP THR RM MUT FLAG RR SW ODRB MSH. subst a0 a1 a2.
unfold AGLOB_START, AGLOB_STOP, FLAG_A, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. if_falsex.
step. step. step. if_falsex.
do 3 (step; fold_closed_bv2). if_falsex.
step.
match goal with |- context [Z_to_bv 64 (Z.shiftr ?a ?b)] => let v := eval vm_compute in (Z.shiftr a b) in change (Z_to_bv 64 (Z.shiftr a b)) with (Z_to_bv 64 v : bv 64) end || idtac.
fold_closed_bv2.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (unreg_globals_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| reflexivity | reflexivity | unfold got9; exact GOT | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM | exact MUT
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | exact MSH ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MUT3 & [ob3 ODRB3] & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold W_UNREG, MUTEX_A, W_ODR, ODR_A, META_SH in MUc, MUT3, ODRB3, MSH3.
clear MSH ST ODRB MUT MI RR SW.
assert (MU' : munch (W_ELF (bv_unsigned sp)) m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs m1 m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 318728)) with (Z_to_bv 64 318728 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A in MU.
stepz.
step. step. step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_done. unfold unreg_elf_post.
do 16 eexists.
split; [reflexivity|].
unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH.
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
split; [exact MUT3|]. split; [exact FLAG|]. split; [exists ob3; exact ODRB3 | exact MSH3].
Qed.

Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_DTOR (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' MUTEX_A [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' FLAG_A [C8 (Z_to_bv 64 0)]
/\ (exists ob', rw_cells asegs m' ODR_A [C1 ob']) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma module_dtor_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 272 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
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
evt asegs (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b3cc) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL GOT GOT2 INITED RG SB CP THR RM MUT FLAG RR SW ODRB MSH.
unfold AGLOB_START, AGLOB_STOP, FLAG_A, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step.
do 6 step. fold_closed_bv2.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (unreg_elf_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| rewrite unsigned_lit by lia; lia
| reflexivity | reflexivity | reflexivity | unfold got9; exact GOT | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM | exact MUT | exact FLAG
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | exact MSH ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MUT3 & FLAG3 & [ob3 ODRB3] & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold W_ELF, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH in MUc, MUT3, FLAG3, ODRB3, MSH3.
clear MSH ST ODRB MUT FLAG MI RR SW.
assert (MU' : munch (W_DTOR (bv_unsigned sp)) m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 0x9b3f0)) with (Z_to_bv 64 0x9b3f0 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A in MU.
step. step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_done. unfold module_dtor_post.
do 16 eexists.
split; [reflexivity|].
unfold W_DTOR, MUTEX_A, W_ODR, ODR_A, FLAG_A, META_SH.
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
split; [exact MUT3|]. split; [exact FLAG3|]. split; [exists ob3; exact ODRB3 | exact MSH3].
Qed.
End P3.
