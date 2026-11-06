(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 QlKV QsKa QJZd Q3Gm QGm2 QhtD QbKA QjDJ QrJ1 Qlna Qirj Q6q3.
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
Import QGm2.Mq0 QhtD.Mq0 QbKA.Mq2 QjDJ.Mq0 QrJ1.Mq0 Qlna.Mq0 Qirj.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition EXITLOCK_A : Z := 0x6430d0.

Definition W_EXIT (usp : Z) : list (Z * Z) :=
[(usp - 320, usp); (EXITLOCK_A, EXITLOCK_A + 4); (ATEXIT_A, ATEXIT_A + 24);
(MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0a00); (FLAG_A, FLAG_A + 8); (COMPLETED_A, COMPLETED_A + 1)]%Z.

Section P5.
Context {RC__ : Q6q3.RunConsts}.

Record exit_cells_A (m : word -> option byte) (tid : Z) (g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte) : Prop := {
xc_tid   : ro_cells asegs m (A_TP - 168) [C4 (Z_to_bv 64 tid)];
xc_tidr  : 0 < tid < 2^31;
xc_lock  : rw_cells asegs m EXITLOCK_A [C4 (Z_to_bv 64 0)];
xc_nl    : ro_cells asegs m NEEDLOCKS_A [C1 (Z_to_bv 8 0)];
xc_cov   : ro_cells asegs m COVFLAG_A [C1 (Z_to_bv 8 0)];
xc_at    : rw_cells asegs m ATEXIT_A (atexit_cells m mid);
xc_midl  : length mid = 240%nat;
xc_aef   : ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)];
xc_gotf  : ro_cells asegs m 0xe6bb0 [C8 (Z_to_bv 64 (FINI_A + 16)); C8 (Z_to_bv 64 FINI_A)];
xc_fini  : ro_cells asegs m FINI_A [C8 (Z_to_bv 64 0x99f88); C8 (Z_to_bv 64 0x3dee0)];
xc_comp  : rw_cells asegs m COMPLETED_A [C1 (Z_to_bv 8 0)];
xc_gotw  : ro_cells asegs m 0xe5d88 [C8 (Z_to_bv 64 0xcc594); C8 (Z_to_bv 64 0)];
xc_dso   : ro_cells asegs m 0xe7c00 [C8 dso];
xc_got9  : ro_cells asegs m 0xe5d98 (got9 g0 g1 g5 g6 g7);
xc_got2  : ro_cells asegs m 0xe6ab0 [C8 (Z_to_bv 64 AGLOB_START); C8 (Z_to_bv 64 AGLOB_STOP)];
xc_inited: ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)];
xc_rg    : ro_cells asegs m 0xed310 [C4 (Z_to_bv 64 1)];
xc_sb    : ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)];
xc_cp    : ro_cells asegs m 0xef35c [C1 (Z_to_bv 8 1)];
xc_thr   : ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)];
xc_rm    : ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)];
xc_mut   : rw_cells asegs m MUTEX_A [C8 (Z_to_bv 64 0)];
xc_flag  : rw_cells asegs m FLAG_A [C8 (Z_to_bv 64 1)];
xc_recs  : recs_ro m AGLOB_START tokA_globals8;
xc_shad  : shadows_rw m tokA_globals8;
xc_odr   : rw_cells asegs m ODR_A [C1 ob];
xc_msh   : rw_cells asegs m META_SH [CB 856 junkM]
}.

Lemma exit_entry_spec : forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo tid : Z)
(g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 320 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
munch (W_EXIT (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp - 16) ->
rw_cells asegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcc71c) (Z_to_bv 64 (bv_unsigned sp - 16)) gp (Z_to_bv 64 A_TP) t0' t1' t2' a0 s1
a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0xd2fb0) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcc6b0) fc None m (seg_rom asegs)).
Proof.
intros until mid. intros MI ST CEIL LO AL XC K. destruct XC.
unfold A_TP, EXITLOCK_A, NEEDLOCKS_A, COVFLAG_A, ATEXIT_A, FINI_A, COMPLETED_A, AGLOB_START, AGLOB_STOP, MUTEX_A, FLAG_A, ODR_A, META_SH in *.
replace (6434400 - 168) with 6434232 in xc_tid0 by reflexivity. unfold atexit_cells, atexit_cellsK in xc_at0. unfold got9 in xc_got10.
replace (926712 + 16) with 926728 in xc_gotf0 by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x6430d0, 0x6430d0 + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. step.
step. rewrite (sx32_small tid) by lia.
step. step.
step. fold_lits.
step. if_falsex.
stepz.
step. if_falsex.
step. fold_lits.
step. if_falsex.
step. if_truex.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (funcs_on_exit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo mid (ax_phase m));
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia | exact xc_midl0
| apply ax_phase_cases | exact xc_at0 | exact xc_nl0 | exact xc_cov0
| intros E; eapply ro_cells_transport; [exact (xc_aef0 E) | exact MU | unfold AEF_FLAG_A; cbn [disjoint_from cells_size csize Nat.add]; lia] ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & AT3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold ATEXIT_A in MUc, AT3.
clear ST xc_at0 MI.
assert (MU' : munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x6430d0, 0x6430d0 + 4); (0x642eb0, 0x642eb0 + 24)]%Z m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 0xcc714)) with (Z_to_bv 64 0xcc714 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (exit_fini_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 dso ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST3 | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| exact xc_gotf0 | exact xc_fini0 | exact xc_comp0 | exact xc_gotw0 | exact xc_dso0 | unfold got9; exact xc_got10 | exact xc_got3
| exact xc_inited0 | exact xc_rg0 | exact xc_sb0 | exact xc_cp0 | exact xc_thr0 | exact xc_rm0 | exact xc_mut0 | exact xc_flag0
| eapply recs_ro_transport; [exact xc_recs0 | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact xc_shad0 | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact xc_odr0 | exact xc_msh0 ] | ]
end.
intros ms' PO. destruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MI4 & ST4). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST4 by lia.
unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A in MUc.
clear ST3 MI xc_recs0 xc_shad0 xc_odr0 xc_msh0 xc_mut0 xc_flag0 xc_comp0.
assert (MU' : munch (W_EXIT (bv_unsigned sp)) m m4).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_EXIT, EXITLOCK_A, ATEXIT_A, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A;
intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m4 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI4 into MI.
replace (ret_pc (Z_to_bv 64 0xcc718)) with (Z_to_bv 64 0xcc718 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
eapply K; [exact MU | exact WM | exact MI | replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact ST4 | exact FR].
Qed.
End P5.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlna. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition EXITLOCK_A : Z := 0x645790.

Definition W_EXIT (usp : Z) : list (Z * Z) :=
[(usp - 320, usp); (EXITLOCK_A, EXITLOCK_A + 4); (ATEXIT_A, ATEXIT_A + 24);
(MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0e00); (FLAG_A, FLAG_A + 8); (COMPLETED_A, COMPLETED_A + 1)]%Z.

Section P5.
Context {RC__ : Q6q3.RunConsts}.

Record exit_cells_A (m : word -> option byte) (tid : Z) (g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte) : Prop := {
xc_tid   : ro_cells asegs m (A_TP - 168) [C4 (Z_to_bv 64 tid)];
xc_tidr  : 0 < tid < 2^31;
xc_lock  : rw_cells asegs m EXITLOCK_A [C4 (Z_to_bv 64 0)];
xc_nl    : ro_cells asegs m NEEDLOCKS_A [C1 (Z_to_bv 8 0)];
xc_cov   : ro_cells asegs m COVFLAG_A [C1 (Z_to_bv 8 0)];
xc_at    : rw_cells asegs m ATEXIT_A (atexit_cells m mid);
xc_midl  : length mid = 240%nat;
xc_aef   : ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)];
xc_gotf  : ro_cells asegs m 0xe8fc0 [C8 (Z_to_bv 64 (FINI_A + 16)); C8 (Z_to_bv 64 FINI_A)];
xc_fini  : ro_cells asegs m FINI_A [C8 (Z_to_bv 64 0x9b3cc); C8 (Z_to_bv 64 0x3e10c)];
xc_comp  : rw_cells asegs m COMPLETED_A [C1 (Z_to_bv 8 0)];
xc_gotw  : ro_cells asegs m 0xe8188 [C8 (Z_to_bv 64 0xcec58); C8 (Z_to_bv 64 0)];
xc_dso   : ro_cells asegs m 0xea020 [C8 dso];
xc_got9  : ro_cells asegs m 0xe8198 (got9 g0 g1 g5 g6 g7);
xc_got2  : ro_cells asegs m 0xe8ec0 [C8 (Z_to_bv 64 AGLOB_START); C8 (Z_to_bv 64 AGLOB_STOP)];
xc_inited: ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)];
xc_rg    : ro_cells asegs m 0xef9d0 [C4 (Z_to_bv 64 1)];
xc_sb    : ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)];
xc_cp    : ro_cells asegs m 0xf1a1c [C1 (Z_to_bv 8 1)];
xc_thr   : ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)];
xc_rm    : ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)];
xc_mut   : rw_cells asegs m MUTEX_A [C8 (Z_to_bv 64 0)];
xc_flag  : rw_cells asegs m FLAG_A [C8 (Z_to_bv 64 1)];
xc_recs  : recs_ro m AGLOB_START tokA_globals8;
xc_shad  : shadows_rw m tokA_globals8;
xc_odr   : rw_cells asegs m ODR_A [C1 ob];
xc_msh   : rw_cells asegs m META_SH [CB 856 junkM]
}.

Lemma exit_entry_spec : forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (lo tid : Z)
(g0 g1 g5 g6 g7 dso : word) (ob : byte) (junkM mid : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 320 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
munch (W_EXIT (bv_unsigned sp)) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp - 16) ->
rw_cells asegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
evt asegs Q (MS (mkR (Z_to_bv 64 0xcede0) (Z_to_bv 64 (bv_unsigned sp - 16)) gp (Z_to_bv 64 A_TP) t0' t1' t2' a0 s1
a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0xd5674) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xced74) fc None m (seg_rom asegs)).
Proof.
intros until mid. intros MI ST CEIL LO AL XC K. destruct XC.
unfold A_TP, EXITLOCK_A, NEEDLOCKS_A, COVFLAG_A, ATEXIT_A, FINI_A, COMPLETED_A, AGLOB_START, AGLOB_STOP, MUTEX_A, FLAG_A, ODR_A, META_SH in *.
replace (6444320 - 168) with 6444152 in xc_tid0 by reflexivity. unfold atexit_cells, atexit_cellsK in xc_at0. unfold got9 in xc_got10.
replace (936640 + 16) with 936656 in xc_gotf0 by reflexivity.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (0x645790, 0x645790 + 4)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
step. step. step.
step. step.
step. rewrite (sx32_small tid) by lia.
step. step.
step. fold_lits.
step. if_falsex.
stepz.
step. if_falsex.
step. fold_lits.
step. if_falsex.
step. if_truex.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (funcs_on_exit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo mid (ax_phase m));
[ exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia | exact xc_midl0
| apply ax_phase_cases | exact xc_at0 | exact xc_nl0 | exact xc_cov0
| intros E; eapply ro_cells_transport; [exact (xc_aef0 E) | exact MU | unfold AEF_FLAG_A; cbn [disjoint_from cells_size csize Nat.add]; lia] ] | ]
end.
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & AT3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold ATEXIT_A in MUc, AT3.
clear ST xc_at0 MI.
assert (MU' : munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x645790, 0x645790 + 4); (0x645570, 0x645570 + 24)]%Z m m3).
{ eapply munch_join; [exact MU | exact MUc | |]; intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m3 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI3 into MI.
replace (ret_pc (Z_to_bv 64 0xcedd8)) with (Z_to_bv 64 0xcedd8 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply evt_cut; [eapply (exit_fini_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc lo g0 g1 g5 g6 g7 dso ob junkM);
[ exact MI | rewrite unsigned_lit by lia; exact ST3 | exact CEIL | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) by lia; rewrite <- Zminus_mod_idemp_l, AL; reflexivity
| exact xc_gotf0 | exact xc_fini0 | exact xc_comp0 | exact xc_gotw0 | exact xc_dso0 | unfold got9; exact xc_got10 | exact xc_got3
| exact xc_inited0 | exact xc_rg0 | exact xc_sb0 | exact xc_cp0 | exact xc_thr0 | exact xc_rm0 | exact xc_mut0 | exact xc_flag0
| eapply recs_ro_transport; [exact xc_recs0 | exact MU | intros q Hq1 Hq2; rewrite tok_len in Hq2; unfold AGLOB_START in *; cbn [disjoint_from]; lia]
| eapply shadows_rw_transport_gen; [exact xc_shad0 | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact xc_odr0 | exact xc_msh0 ] | ]
end.
intros ms' PO. destruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m4 & E & MUc & WMc & MI4 & ST4). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST4 by lia.
unfold W_FINI, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A in MUc.
clear ST3 MI xc_recs0 xc_shad0 xc_odr0 xc_msh0 xc_mut0 xc_flag0 xc_comp0.
assert (MU' : munch (W_EXIT (bv_unsigned sp)) m m4).
{ eapply munch_join; [exact MU | exact MUc | |]; unfold W_EXIT, EXITLOCK_A, ATEXIT_A, MUTEX_A, W_ODR, ODR_A, FLAG_A, COMPLETED_A;
intros x Hx; cbn [outside] in Hx |- *; lia. }
clear MU. transport_after_call rsegs ltac:(lazymatch type of WMc with wmono _ ?ma _ => ma end) m4 MUc WMc. clear MUc WMc. rename MU' into MU. rename MI4 into MI.
replace (ret_pc (Z_to_bv 64 0xceddc)) with (Z_to_bv 64 0xceddc : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
eapply K; [exact MU | exact WM | exact MI | replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact ST4 | exact FR].
Qed.
End P5.
