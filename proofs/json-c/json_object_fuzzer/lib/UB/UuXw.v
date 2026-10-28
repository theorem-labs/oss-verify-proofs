(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTKj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTKj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoArrShrink.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

#[using="Type"] Lemma json_object_array_shrink_cps : jo_array_shrink_P HIx.
Proof.
unfold jo_array_shrink_P, jo_array_shrink_stmt. intros until errv. intros PRE J A0 A1 K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR.
destruct (sarr_open rsegs S4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
pose proof HAL as (arr & size & ajunk & EAL & Hlen & Hsz & _). subst ABS AL.
assert (HPa : HEAPx A ((a, 32) :: (arr, 8 * size) :: ((p, 48) :: concat KBS ++ PBS ++ LB)) m md).
{ eapply (heap_perm S4L HIx); [exact HP | perm]. }
set (LBR := (p, 48) :: concat KBS ++ PBS ++ LB) in HPa.
assert (INp : In (p, 48) LBR) by (left; reflexivity).
assert (HiK : incl (concat KBS) LBR) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBR) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HPa ltac:(right; right; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p 48 HPa ltac:(right; right; exact INp)) as Himg_p. cbn [hl_img_lo hl_img_hi S4L] in Himg_p.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
unfold jhdr_cells in HDR. cbn [app] in HDR.
stash OPB. stash KIDS. stash HAL. clear HP J.
apply rz_evt; [exact MOK|]. subst a0 a1 tp.
step. if_false. step. if_falsex. step. step. ubsan_align Hpal. step. step.
unstash OPB. unstash KIDS. unstash HAL.

apply evt_RZ_done.
eapply (array_list_shrink_cps HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LBR lo a arr size ps T);
[ exact HPa | exact HAL | exact ST | clia | lia | exact SPA | exact HT | exact ERR | exact RA | reflexivity | reflexivity | ].
intros ms' md' (m' & A' & r & errv' & arr' & size' & RS & VM & ST' & HPR' & ERR' & HP' & AL' & _).
cbn [hl_segs S4L] in *.
assert (AG : agree_on rsegs LBR m m') by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR' | reflexivity | apply incl_refl]).
apply (K ms' md' m' r).
- unfold jo_post_frame. cbn [hl_segs hl_tp S4L]. split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [| exists errv'; exact ERR'].
eapply heap_pres_weaken; [exact HPR' | lia | exact HiL].
- exists A', (((p, 48) :: [(a, 32); (arr', 8 * size')] ++ concat KBS) ++ PBS). split.
+ eapply (sarr_close rsegs S4F); try reflexivity.
* eapply opt_pbuf_agree; [exact OPB | exact AG | exact HiP].
* unfold jhdr_cells. cbn [app]. eapply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR'). { exact HDR. } eapply client_range_block; [exact INp | lia | cbn; lia].
* exact AL'.
* exact L1.
* exact L2.
* eapply akids_agree; [exact KIDS | exact AG | exact HiK].
+ eapply (heap_perm S4L HIx); [exact HP' | unfold LBR; perm].
Qed.
End JoArrShrink.

End RC__1.
