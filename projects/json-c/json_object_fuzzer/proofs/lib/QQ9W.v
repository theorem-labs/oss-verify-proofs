(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUvT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUvT.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsJM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEDI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEDI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Lift3.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.
Hypothesis HRF : forall FS RE X m, ac_RFake C FS RE X m <-> RFake FS RE X m.

Ltac open_run AR X G LB0 FS0 PB PF AX GC RT RF :=
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX);
pose proof (proj1 AX) as GC;
pose proof (proj1 (HRT _ _ _) (proj1 (proj2 AX))) as RT;
pose proof (proj1 (HRF _ _ _ _) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 AX))))))))) as RF.

Lemma stack_malloc_3_A : astack_mallocA_stmt asegs a_alayout (ARUN C) 3 fsmalloc3_entry.
Proof.
unfold astack_mallocA_stmt. intros until lo. intros AR ROOM ST CEIL LO MI Htp Hgp Ha0 SZ SAL.
open_run AR X G LB0 FS0 PB PF AX GC RT RF. pose proof (proj1 GC) as RL.
pose proof (rl_objs_lia _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CEo & _). cbn [fst snd] in AL, K, CEo.
subst tp gp. cbn [ala_tp ala_gp ala_stack_malloc_stack a_alayout] in *.
rewrite (filter_perm_length 3 FS FS0 PF) in ROOM. change (fframe_cap 3) with (fs_N 3) in ROOM.
eapply evt_mono.
{ eapply (fsmalloc3_spec RE X); [exact RT| exact RL| exact RF| exact MI| exact ST| exact CEIL| lia| exact ROOM| exact Ha0]. }
cbv beta. intros ms' POST. unfold rpost in POST.
destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & STK'
& f & pos & junk & Ea0 & Ef & PR & FRESH & FR & RT' & RF' & BODY & SHC & MU2).
subst ms'. unfold std_postA. do 16 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
split.
{ eapply (fs_op_pres _ LB0 FS0 G RE X LB FS (bv_unsigned sp) (bv_unsigned sp - 224) (ae_fs_base RE + 24) (ff_size 3 / 8) m m' 3 pos f GC PB
(RFake_shape _ _ _ _ RF)); try eassumption.
- intros g Hg. assert (Hg0 : In g FS0) by (eapply Permutation_in; [exact PF| exact Hg]). split; [exact Hg0|].
intros Eg. apply FRESH. rewrite <- Eg. apply in_map. exact Hg0.
- unfold kFsClasses. lia.
- change (ff_size 3 / 8) with 64. lia.
- lia. - lia. - lia. - lia. }
split; [reflexivity|]. split; [reflexivity|].
split.
{
eapply depot_keep_of_munch; [exact MU| exact WM|]. unfold DP_N.
constructor; [cbn [fst snd]; unfold A_FS_MAP_SIZE in *; lia|]. constructor; [cbn [fst snd]; rewrite !SH_eq; unfold A_FS_MAP_SIZE in *; Z.div_mod_to_equations; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
exists f, junk.
split; [exact Ea0|]. split; [exact FR|].
split.
{ apply (ARUN_close C s LB ((3, f) :: FS) RE m' X G LB0 ((3, f) :: FS0)); [exact PB| apply perm_skip; exact PF|].
eapply (ARUNX_fs C HRT HRF _ LB0 FS0 _ G RE X m m'); [exact AX| exact MU| exact WM| | exact RT'| exact RF'|].
- intros lo' hi' x Hin Hx. eapply (fs_W_czone LB0 RE (bv_unsigned sp - 224) (bv_unsigned sp)); [lia| Z.div_mod_to_equations; lia| exact Hin| exact Hx].
- eapply (gcons_ff_add _ LB0 FS0 G RE X GC 3 pos f (RFake_shape _ _ _ _ RF)); [unfold kFsClasses; lia| exact PR| exact Ef| exact FRESH| exact FR]. }
split; [exact BODY|].
eapply rw_cells_recast'; [exact SHC| |].
- cbn. rewrite !repeat_length. easy.
- reflexivity.
Qed.

End Lift3.
