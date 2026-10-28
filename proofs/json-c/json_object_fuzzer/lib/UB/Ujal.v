(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uihm.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.


Local Ltac if_lit0 := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota end.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoNewObject.
Variable HIx : heap_iface S4L.
Notation lh_glob4 := (lh_glob rsegs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

#[using="Type"] Lemma jc_glob_P_lh : forall m, jc_glob_P m -> lh_glob4 m.
Proof. intros m G. exact G. Qed.

#[using="Type"] Lemma json_object_new_object_cps : jo_new_object_P HIx.
Proof.
unfold jo_new_object_P, jo_new_container_stmt. intros until errv. intros PRE G K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
assert (Gk : True -> jc_glob_P m) by (intros _; exact G). clear G.
apply rz_evt; [exact MOK|]. subst tp.
carve_frame 16%nat ST.
do 5 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 mA md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
pose proof (jc_glob_P_pres _ _ _ _ HPR (Gk I)) as G2. clear Gk.
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
stash G2.
reenter MOK2.
step. if_falsex.
step. step. ubsan_align Hal.
do 5 step. stepz. stepz. stepz. stepz. stepz.
do 4 step. step.
unstash G2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (G3 : jc_glob_P mx) by
(eapply jc_glob_P_munch; [exact G2 | exact MU | exact WM |];
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia) end.
apply evt_RZ_done.
eapply (lh_kchar_table_new_cps HIx) with (LB := (r, 48) :: LB) (lo := lo);
[ heap_now S4L HIx HP2 MU WM MI | exact G3 | .. ]; try alloc_side.
intros ms3 md3 (mB & A3 & r2 & e3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & G4 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR3 by lia.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
clear MU WM MI G2 G3.
destruct OUT3 as [(-> & HP3) | (Hr2 & BS2 & TAB & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl rsegs mB) as WM.
reenter MOK3.
step. step. stepz. step. if_false. step. step. step. step.

apply evt_RZ_done.
eapply (printbuf_free_cps HIx) with (LB := (r, 48) :: LB) (BS := []) (p := 0) (lo := lo);
[ cbn [app]; heap_now S4L HIx HP3 MU WM MI | left; split; reflexivity | .. ]; try alloc_side.
intros ms5 md5 (mC & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP5).
destruct RS5 as (x0 & x1' & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR5 by lia.
extend_pres S4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
reenter MOK5.
step. step.

alloc_call (hi_free S4L HIx) S4L HIx HP5 MU WM MI.
{ right. exists 48. left. reflexivity. }
intros ms6 mD md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR6, HP6.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST6 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR6 by lia.
extend_pres S4L HIx HPR MU WM HP5 HPR6.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
pose proof (heap_model_ok _ _ _ _ _ _ HP6) as MOK6.
pose proof (heap_mem_inv _ _ _ _ _ _ HP6) as MI. cbn [hl_segs S4L] in MI.
lazymatch type of ERR6 with rw_cells _ _ _ [C4 ?e] => assert (ERR6x : rw_cells rsegs mD 490332 [C4 e]) by exact ERR6 end. clear ERR6. rename ERR6x into ERR6.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (490332, 490336)] mD) as MU. pose proof (wmono_refl rsegs mD) as WM.
reenter MOK6.
do 4 step. step. if_lit0. step. step. step. if_lit0. step. stepz.
do 4 step.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ => apply (K _ md6 mf 0) end.
* unfold jo_post_frame. cbn [hl_segs hl_tp S4L].
split; [| split; [| split; [| split; [ | eexists; eassumption]]]].
-- apply ret_statew_intro; [eapply fsaved_trans; [exact FS3 | exact FS5] | intros Hf; apply FRM5; apply FRM3; exact Hf].
-- eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM5 | exact VM6].
-- release_frame FR ST6 (bv_unsigned sp). exact ST6.
-- eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |]. solve_clientW S4L HIx HP6.
* left. split; [reflexivity|]. exists A6.
eapply (heap_frame S4L HIx); [exact HP6 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP6 MU). solve_frameW_with HP6.
+
pose proof TAB as (tbl & size & es & svs & Hkvs & EBS2 & OPEN).
destruct es as [|e0 es']; [| cbn in Hkvs; discriminate]. subst BS2. unfold lh_blocks in HP3. cbn [map app] in HP3.
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR.
pose proof (rw_cells_bound rsegs mB r2 _ THDR) as R2B. cbn [cells_size csize Nat.add] in R2B. clear THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk_img S4L HIx _ _ _ _ r2 56 HP3 ltac:(left; reflexivity)) as Himg_r2. cbn [hl_img_lo hl_img_hi S4L] in Himg_r2.
pose proof (heap_blk_img S4L HIx _ _ _ _ tbl (40 * size) HP3 ltac:(right; left; reflexivity)) as Himg_tbl. cbn [hl_img_lo hl_img_hi S4L] in Himg_tbl.
pose proof (heap_blk S4L HIx _ _ _ _ r2 56 HP3 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
pose proof (heap_blk S4L HIx _ _ _ _ tbl (40 * size) HP3 ltac:(right; left; reflexivity)) as (_ & Htal & Htlo & Hthi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi, Hthi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Htbr : tbl <> r).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ r2 56 r 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tbl (40 * size) r 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Htbr) as Hdj2.
stash TAB. clear OPEN.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] mB) as MU. pose proof (wmono_refl rsegs mB) as WM.
reenter MOK3.
step. step. step. step. if_truex. do 4 step.
unstash TAB.
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
* right. split; [exact Hr|]. exists A3, [(r, 48); (r2, 56); (tbl, 40 * size)]. split.
-- jhdr_split BLK.
eapply (sobj_close rsegs S4F) with (TBS := [(r2, 56); (tbl, 40 * size)]) (KBS := []) (PBS := []) (pb := 0) (kvs := []) (t := r2); try reflexivity.
++ left. split; reflexivity.
++ unfold jhdr_cells. cbn [fn_obj_to_json_string S4F app]. exact BLK.
++ eapply (lhtab2_agree rsegs S4F); [exact TAB | | apply incl_refl].
eapply (agree_of_munch rsegs); [exact MU | exact WM |].
intros b k Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
-- cbn [app]. eapply (heap_perm S4L HIx).
++ eapply (heap_frame S4L HIx); [ exact HP3 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW_with HP3.
++ perm.
Qed.
End JoNewObject.

End RC__1.
