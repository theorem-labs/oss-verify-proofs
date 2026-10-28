(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UunB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UunB.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.


Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoNewArray.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma json_object_new_array_cps : jo_new_array_P HIx.
Proof.
unfold jo_new_array_P, jo_new_container_stmt. intros until errv. intros PRE _ K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 16%nat ST.
do 5 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 mA md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mA) as MU.
pose proof (wmono_refl rsegs mA) as WM.
reenter MOK2.
step. if_truex. do 4 step.
apply evt_RZ_done. apply (K _ md2 mA 0).
+ unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [apply ret_statew_same|]. split; [exact VM2|]. split; [|split; [exact HPR | exists e2; exact ERR2]].
release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ left. split; [reflexivity|]. exists A2. exact HP2.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mA) as MU.
pose proof (wmono_refl rsegs mA) as WM.
reenter MOK2.
step. if_falsex.
step. step. ubsan_align Hal.
do 5 step. stepz. stepz. stepz. stepz. stepz.
do 5 step. step.

apply evt_RZ_done.
eapply (array_list_new2_cps HIx) with (LB := (r, 48) :: LB) (isz := 32) (lo := lo);
[ heap_now S4L HIx HP2 MU WM MI | .. ]; try alloc_side.
intros ms3 md3 (mB & A3 & r2 & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR3 by lia.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI.
destruct OUT3 as [(-> & HP3) | (Hr2 & BS2 & AL3 & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl rsegs mB) as WM.
reenter MOK3.
step. step. stepz. step. if_false. step.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms4 mC md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR4, HP4.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR4 by lia.
extend_pres S4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
reenter MOK4.
step. do 4 step.
apply evt_RZ_done. apply (K _ md4 mC 0).
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [exact HPR | exists e3; exact ERR4]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM4].
-- release_frame FR ST4 (bv_unsigned sp). exact ST4.
* left. split; [reflexivity|]. exists A4. exact HP4.
+
pose proof AL3 as (arr & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR). subst BS2. cbn [app] in HP3.
pose proof (rw_cells_bound rsegs mB r2 _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ r2 32 HP3 ltac:(left; reflexivity)) as Himg_r2. cbn [hl_img_lo hl_img_hi S4L] in Himg_r2.
pose proof (heap_blk_img S4L HIx _ _ _ _ arr (8 * size) HP3 ltac:(right; left; reflexivity)) as Himg_arr. cbn [hl_img_lo hl_img_hi S4L] in Himg_arr.
pose proof (heap_blk S4L HIx _ _ _ _ r2 32 HP3 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
pose proof (heap_blk S4L HIx _ _ _ _ arr (8 * size) HP3 ltac:(right; left; reflexivity)) as (_ & Haal & Halo & Hahi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi, Hahi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Harr : arr <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 32 r 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ arr (8 * size) r 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harr) as Hdj2.
clear AHDR AARR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl rsegs mB) as WM.
reenter MOK3.
step. step. step. step. if_truex. do 4 step.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => apply (K _ md3 mf r) end.
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [ | exists e3; exact ERR3]]]].
-- apply ret_statew_intro; [exact FS3 | exact FRM3].
-- eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- release_frame FR ST3 (bv_unsigned sp). exact ST3.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; right; right; exact Hb | clia |]. solve_clientW S4L HIx HP3.
* right. split; [exact Hr|]. exists A3, [(r, 48); (r2, 32); (arr, 8 * size)]. split.
-- jhdr_split BLK.
cbn [jval]. exists 0, [], [(r, 48); (r2, 32); (arr, 8 * size)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists r2, [(r2, 32); (arr, 8 * size)], [], []. split; [reflexivity|]. split; [| split; [| split; [reflexivity | split; [reflexivity | exact I]]]].
++ unfold jhdr_cells. cbn [fn_arr_to_json_string S4F app]. exact BLK.
++ eapply (alist_agree rsegs S4F); [exact AL3 | | apply incl_refl].
eapply (agree_of_munch rsegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- cbn [app]. eapply (heap_perm S4L HIx).
++ eapply (heap_frame S4L HIx); [ exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW_with HP3.
++ perm.
Qed.
End JoNewArray.

End RC__1.
