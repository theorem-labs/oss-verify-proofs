(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoNewDouble.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition json_object_new_double_entry : Z := 0x25ff4.

Definition new_obj_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, jval rsegs S4F s m' BS r 1 /\ HEAPx A' (BS ++ LB) m' md') ).

Lemma json_object_new_double_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 ->
bv_unsigned ra mod 2 = 0 ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
(forall ms' md', new_obj_post (Sdouble false) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA DBL K.
unfold_consts. word_range sp SPR. word_range a0 A0R.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
subst tp.
apply rz_evt; [exact MOK|]. unfold json_object_new_double_entry.
carve_frame 16%nat ST.
do 6 step.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_truex. do 4 step.
apply evt_RZ_done. apply K. unfold new_obj_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | left; auto]]]]].
+ apply ret_statew_intro; [apply fsaved_set_self'; reflexivity | intros Hf; exact Hf].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 48 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
step. if_falsex.
step. step. ubsan_align Hal.
do 5 step.
stepz.
stepz.
stepz. stepz. stepz.
stepz.
do 4 step.
apply evt_RZ_done. apply K. unfold new_obj_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A2, r, e2 end.
split; [| split; [exact VM2 | split; [| split; [ | split; [exact ERR2 | right]]]]].
+ apply ret_statew_intro; [apply fsaved_set_self'; reflexivity | intros Hf; exact Hf].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; right; exact Hb | clia |].
solve_clientW S4L HIx HP2.
+ split; [exact Hr|]. exists [(r, 48)]. split.
*
jhdr_split BLK.
cbn [jval]. exists 0, [], [(r, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
eexists. split; [reflexivity|]. split; [exact DBL|].
unfold jhdr_cells. cbn [fn_dbl_to_json_string S4F app]. exact BLK.
* eapply (heap_frame S4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP2 MU). solve_frameW.
Qed.
End JoNewDouble.

End RC__1.
