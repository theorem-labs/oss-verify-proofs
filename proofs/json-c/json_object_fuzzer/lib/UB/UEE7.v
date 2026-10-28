(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup UEQM Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ UC8c Qsw7 QJjn QKQo Q6WR QrPc Qvbw QYIF Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import UC8c.Mq0.
Import Qsw7 QJjn QKQo.
Import Q6WR.Mq0 QrPc.
Import Qvbw QYIF.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Ltac bstep := TopUbTac.ub_skip; step. Ltac bstepz := TopUbTac.ub_skip; stepz.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoSetDoubleP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation jroot_repP := (jroot_rep S4L S4F).

Definition SD_ENTRY_P : Z := 0x26458.

Definition SD_TBL_P : Z := 0x626a0.
Definition SD_STK : Z := 16 + 8256.

Definition jo_set_double_stmt2 (entry tbl stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB BS : list blk) (lo p : Z) (r : jroot) (errv : word),
jf_pre S4L HIx A (BS ++ LB) m md sp tp ra lo stkb errv -> jroot_repP r m BS p ->
a0 = Z_to_bv 64 p ->
bytes_at rsegs m tbl (le8 (Z_to_bv 64 (fn_dbl_to_json_string S4F))) ->
(forall ms' md' m' rv, jf_post S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo rv m' ms' md' ->
rw_cells rsegs m' (hl_tp S4L - 164) [C4 errv] ->
(exists A' BS', jroot_repP (set_double_root (fn_dbl_to_json_string S4F) r) m' BS' p /\ HEAPx A' (BS' ++ LB) m' md') ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)) md) T.

#[using="Type"] Theorem jo_set_double_P : jo_set_double_stmt2 SD_ENTRY_P SD_TBL_P SD_STK.
Proof.
unfold jo_set_double_stmt2, SD_ENTRY_P, SD_TBL_P, SD_STK.
intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 TBL K.
cbn [hl_segs hl_tp S4L] in *.
unfold_consts. word_range sp SPR. subst a0 tp.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl rsegs m) as WM.

assert (K0 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
set_double_root (fn_dbl_to_json_string S4F) r = r ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 (hl_tp S4L)) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m (seg_rom rsegs)) md) T).
{ intros. eapply (K _ md m (bv_unsigned a0')).
- split; [| split; [apply model_vm_only_refl | split; [exact ST | split; [exact HPR | exists errv; exact ERR]]]].
rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
- exact ERR.
- exists A, BS. rewrite H. split; [exact RR | exact HP]. }
destruct r as [ | s | tojs | ].
-  destruct RR as [-> ->].
pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_truex. bstep.
apply evt_RZ_done. apply K0. intros; reflexivity.
-  destruct RR as [Hp J].
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jval_hdr rsegs S4F s m BS p 1 J (nodup_app_l' _ _ ND)) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
destruct (Z.eq_dec (jtype s) JT_DOUBLE) as [TD | NTD].
+  destruct s as [|u| | | |]; try discriminate TD. clear TD CLOSE HDR SZ N48.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
destruct u.
*
destruct J as (bits & ud_ & udn & uds & -> & Hudn & CELLS & CSTR). cbn [app] in EBS. subst BS. cbn [app] in HP, ND.
destruct INp as [INp|INp]; [injection INp as <- | exfalso; cbn in ND; inversion ND as [|x_ l_ Hni Hnd]; subst; apply Hni; change (In p (map blk_addr (((ud_, udn) :: PBS) ++ LB))); rewrite map_app; apply in_app_iff; left; exact (in_map blk_addr _ _ INp)].
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app fn_ud_to_json_string fn_free_userdata S4F hl_segs S4L] in CELLS. cbn [hl_segs S4L] in OPB. clear CSTR.
pose proof (heap_blk S4L HIx _ _ _ _ ud_ udn HP ltac:(right; left; reflexivity)) as (Hudn0 & Hual & Hulo & Huhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Huhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hpud.
pose proof (heap_blk_img S4L HIx _ _ _ _ p 48 HP ltac:(left; reflexivity)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
carve_frame 16%nat ST.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bstep. rewrite sx32_small by lia. bstep. bstep. if_falsex.
bstep. bstep. bstep. bstep. bstep. if_falsex.
bstep. bstep. if_falsex. bstep. bstep. bstep. bstep. bstep. bstep.

bstep. bstep.
alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists udn. right; left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in CELLS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in CELLS.
apply (heap_pres_bytes_at S4L _ _ _ _ _ _ HPR3) in TBL; [| right; left; rewrite length_le8; intros a Ha; cbn; unfold s4_client_static; lia ]. cbn [hl_segs S4L] in TBL.
assert (OPB3 : opt_pbuf rsegs m3 PBS pb_).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_on_trans.
- eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin. cbn. split; [|split; [|exact I]].
+ pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(right; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hk & _). clia.
+ assert (NE : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni. right.
change (In p (map blk_addr (PBS ++ LB))). rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 a k HP ltac:(left; reflexivity) ltac:(right; right; apply in_or_app; left; exact Hin) NE). lia.
- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m m3).
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia|].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 48.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,48)::(ud_,udn)::PBS) LB p 48 48); [exact ND | left; reflexivity].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; apply in_or_app; right; exact Hb]. }
clear MU WM MI ST.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m3) as MU.
pose proof (wmono_refl rsegs m3) as WM.
reenter MOK3.
bstep. bstep. bstep. bstep. bstep. rewrite sx32_small by lia. bstep. bstepz. bstepz. bstep. try if_falsex. bstep. bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (bytes_at_read rsegs mc 403104 _ 0 8 TBL ltac:(lia) ltac:(cbn; lia)) as RD8 end. cbn [fn_dbl_to_json_string S4F] in RD8. change (Z.to_nat 0) with 0%nat in RD8. rewrite skipn_O in RD8.
rewrite firstn_all2 in RD8 by (rewrite length_le8; lia). replace (403104 + 0) with 403104 in RD8 by lia.
bstep. bstepz. bstep. bstep.
apply evt_RZ_done.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md3 mf 1) end.
-- split; [| split; [exact VM3 | split; [ | split; [ | exists errv; exact ERR3 ]]]].
++ apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
++ release_frame FR ST3 (bv_unsigned sp). exact ST3.
++ eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP3 | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia|].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 48.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,48)::(ud_,udn)::PBS) LB p 48 48); [exact ND | left; reflexivity].
-- exact ERR3.
-- exists A3, ((p, 48) :: PBS). split.
++ cbn [set_double_root jroot_rep]. split; [exact Hp|]. split; [left; reflexivity|].
exists pb_, PBS, (Sem.reg_get F (Z_to_bv 5 10)). split; [reflexivity|]. split.
** eapply opt_pbuf_agree; [exact OPB3 | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. cbn. split; [|split; [|exact I]].
+++ pose proof (heap_blk S4L HIx _ _ _ _ a k HP3 ltac:(right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hk & _). clia.
+++ assert (NE : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni. right.
change (In p (map blk_addr (PBS ++ LB))). rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 a k HP3 ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NE). lia.
** unfold jhdr_cells, JT_DOUBLE. cbn [app fn_dbl_to_json_string S4F]. assumption.
++ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU). solve_frameW.
*
destruct J as (bits & -> & DS & CELLS). cbn [app] in EBS. subst BS.
destruct INp as [INp|INp]; [injection INp as <- | exfalso; cbn in ND; inversion ND as [|x_ l_ Hni Hnd]; subst; apply Hni; rewrite map_app; apply in_app_iff; left; exact (in_map blk_addr _ _ INp)].
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app fn_dbl_to_json_string S4F hl_segs S4L] in CELLS. cbn [hl_segs S4L] in OPB.
pose proof (munch_refl [(p, p + 48)] m) as MU.
pose proof (heap_blk_img S4L HIx _ _ _ _ p 48 HP ltac:(left; reflexivity)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bstep. rewrite sx32_small by lia. bstep. bstep. if_falsex.
bstep. bstep. bstep. bstep. bstep. if_truex. bstep. bstep.
apply evt_RZ_done.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (K _ md mf 1) end.
-- split; [| split; [apply model_vm_only_refl | split; [ | split; [ | exists errv ]]]].
++ apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
++ exact ST.
++ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 48.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,48)::PBS) LB p 48 48); [exact ND | left; reflexivity].
++ exact ERR.
-- exact ERR.
-- exists A, ((p, 48) :: PBS). split.
++ cbn [set_double_root jroot_rep]. split; [exact Hp|]. split; [left; reflexivity|].
exists pb_, PBS, (Sem.reg_get F (Z_to_bv 5 10)). split; [reflexivity|]. split.
** eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. cbn. split; [|exact I].
assert (NE : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NE). lia.
** unfold jhdr_cells. cbn [app fn_dbl_to_json_string S4F]. assumption.
++ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW.
+
pose proof (munch_refl [] m) as MU.
pose proof (jtype_range s) as JR. unfold JT_DOUBLE in NTD.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bstep. rewrite sx32_small by (cbn; lia). bstep. bstep. if_truex. bstep. bstep.
apply evt_RZ_done. apply K0. destruct s; first [reflexivity | exfalso; apply NTD; reflexivity | idtac "K0FAIL"].
-
destruct RR as (Hp & Htojs & pb_ & PBS & bits & -> & OPB & CELLS). cbn [app] in HP.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn in ND.
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(left; reflexivity)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (heap_blk_img S4L HIx _ _ _ _ p 48 HP ltac:(left; reflexivity)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app hl_segs S4L] in CELLS. cbn [hl_segs S4L] in OPB.
assert (PBSdisj : forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m m1 -> wmono rsegs m m1 -> opt_pbuf rsegs m1 PBS pb_).
{ intros m1 MU1 WM1. eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_of_munch; [exact MU1 | exact WM1 |]. intros a k Hin. cbn. split; [|split; [|exact I]].
+ pose proof (heap_blk S4L HIx _ _ _ _ a k HP ltac:(right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hk & _). clia.
+ assert (NE : p <> a).
{ intros <-. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni.
change (In p (map blk_addr (PBS ++ LB))). rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NE). lia. }
assert (HPRW : forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m m1 -> wmono rsegs m m1 -> heap_pres S4L LB (bv_unsigned sp) m m1).
{ intros m1 MU1 WM1. eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia|].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 48.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,48)::PBS) LB p 48 48); [exact ND | left; reflexivity]. }
assert (KX : forall m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' bits',
munch [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp) -> rw_cells rsegs m1 (490496 - 164) [C4 errv] ->
rw_cells rsegs m1 p [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (fn_dbl_to_json_string S4F)); C8 (Z_to_bv 64 pb_); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 bits'] ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 (hl_tp S4L)) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m1 (seg_rom rsegs)) md) T).
{ intros until bits'. intros MU1 WM1 MI1 ST1 ERR1 CELLS1. eapply (K _ md m1 1).
- split; [| split; [apply model_vm_only_refl | split; [exact ST1 | split; [ apply HPRW; assumption | exists errv; exact ERR1 ]]]].
apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
- exact ERR1.
- exists A, ((p, 48) :: PBS). split.
+ cbn [set_double_root jroot_rep]. split; [exact Hp|]. split; [left; reflexivity|].
exists pb_, PBS, bits'. split; [reflexivity|]. split; [apply PBSdisj; assumption|].
unfold jhdr_cells, JT_DOUBLE. cbn [app hl_segs S4L]. exact CELLS1.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU1). solve_frameW. }
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m) as MU.
destruct Htojs as [-> | ->].
+
apply rz_evt; [exact MOK|]. bstep. if_falsex. bstep. rewrite sx32_small by lia. bstep. bstep. if_falsex.
bstep. bstep. bstep. bstep. bstep. if_truex. bstep. bstep.
apply evt_RZ_done. eapply KX; [exact MU | exact WM | exact MI | exact ST | exact ERR | cbn [fn_dbl_to_json_string S4F]; exact CELLS].
+
apply rz_evt; [exact MOK|]. bstep. if_falsex. bstep. rewrite sx32_small by lia. bstep. bstep. if_falsex.
bstep. bstep. bstep. bstep. bstep. if_falsex.
bstep. bstep. if_truex.
bstep. rewrite sx32_small by lia. bstep. bstepz. bstepz. bstep. try if_falsex. bstep. bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (bytes_at_read rsegs mc 403104 _ 0 8 TBL ltac:(lia) ltac:(cbn; lia)) as RD8 end. cbn [fn_dbl_to_json_string S4F] in RD8. change (Z.to_nat 0) with 0%nat in RD8. rewrite skipn_O in RD8.
rewrite firstn_all2 in RD8 by (rewrite length_le8; lia). replace (403104 + 0) with 403104 in RD8 by lia.
bstep. bstepz. bstep. bstep.
apply evt_RZ_done. eapply KX; [exact MU | exact WM | exact MI | exact ST | exact ERR | cbn [fn_dbl_to_json_string S4F]; exact CELLS].
-
destruct RR as (Hp & pb_ & PBS & DBS & cap & len & str & -> & OPB & Hcap & Hlen & Hstr & ALT). cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ p (48 + cap) HP ltac:(left; reflexivity)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (munch_refl [] m) as MU.
assert (CELLS : exists rest, rw_cells rsegs m p (C4 (Z_to_bv 64 6) :: rest)).
{ destruct ALT as [(_ & _ & _ & junk & C) | (_ & pd & pdn & junk & junk2 & _ & _ & C & _)];
unfold jhdr_cells, JT_STRING in C; cbn [app hl_segs S4L] in C; eexists; exact C. }
destruct CELLS as [rest CELLS].
apply rz_evt; [exact MOK|]. bstep. if_falsex. bstep. rewrite sx32_small by lia. bstep. bstep. if_truex. bstep. bstep.
apply evt_RZ_done. apply K0. reflexivity.
Qed.
End JoSetDoubleP.

End RC__1.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Import Q6q3.
Ltac bstep := TopUbTac.ub_skip; step. Ltac bstepz := TopUbTac.ub_skip; stepz.
Ltac bw := repeat (TopUbTac.ub_skip; stepz; try norm_w32).
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SetScalP.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma jroot_hdr : forall r m BS p,
jroot_rep S4L S4F r m BS p -> r <> JRnull -> List.NoDup (map blk_addr BS) ->
exists n ty tojs pb udel ud rest,
In (p, n) BS /\ Z.of_nat (cells_size (jhdr_cells ty 1 tojs pb udel ud ++ rest)) = n /\ 48 <= n /\ 0 <= ty <= 6 /\
rw_cells rsegs m p (jhdr_cells ty 1 tojs pb udel ud ++ rest) /\
(ty = JT_BOOLEAN -> r = JRtree Sbool) /\ (ty = JT_INT -> r = JRtree Sint).
Proof.
intros r m BS p RR NN ND. destruct r as [|s|tojs|]; [exfalso; exact (NN eq_refl)| | |].
- destruct RR as [Hp J].
destruct (jval_hdr rsegs S4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & _).
exists n, (jtype s), tojs, pb, udel, ud, rest. split; [exact INp|]. split; [exact SZ|]. split; [exact N48|].
split; [apply jtype_range|]. split; [exact HDR|].
split; intros E; destruct s as [|u| |h|kids|kids]; cbn [jtype] in E; try discriminate E; reflexivity.
- destruct RR as (Hp & Htojs & pb & PBS & bits & EBS & OPB & HDR).
exists 48, JT_DOUBLE, tojs, pb, 0, 0, [C8 bits]. split; [rewrite EBS; left; reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold JT_DOUBLE; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
- destruct RR as (Hp & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)].
+ exists (48 + cap), JT_STRING, (fn_str_to_json_string S4F), pb, 0, 0, [C8 (Z_to_bv 64 len); CB (Z.to_nat cap) (str ++ [Z_to_bv 8 0] ++ junk)].
split; [rewrite EBS; left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia|]. split; [lia|].
split; [unfold JT_STRING; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
+ exists (48 + cap), JT_STRING, (fn_str_to_json_string S4F), pb, 0, 0, [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd); CB (Z.to_nat (cap - 8)) junk].
split; [rewrite EBS; left; reflexivity|]. split; [rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia|]. split; [lia|].
split; [unfold JT_STRING; lia|]. split; [exact HDR|]. split; intros E; discriminate E.
Qed.

Ltac ss_open HP RR ST ERR K :=
cbn [hl_segs hl_tp S4L] in *; unfold_consts; subst;
lazymatch goal with |- realizes _ (mkCfg (MS (mkR ?ra ?sp ?gp ?tp _ _ _ ?s0 ?s1 _ _ _ _ _ _ _ _ ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 _ _ _ _) ?F _ ?fc _ ?m _) ?md) ?T =>
let SPR := fresh "SPR" in word_range sp SPR;
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK;
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI;
pose proof (wmono_refl rsegs m) as WM;

assert (K0 : forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m (seg_rom rsegs)) md) T);
[ intros; lazymatch goal with |- realizes _ (mkCfg (MS (mkR _ _ _ _ _ _ _ _ _ ?a0v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _) _ => eapply (K _ md m (bv_unsigned a0v)) end;
[ split; [| split; [apply model_vm_only_refl | split; [exact ST | split; [apply heap_pres_refl | eexists; exact ERR]]]];
rewrite Z_to_bv_bv_unsigned; apply ret_statew_intro; [apply fsaved_refl | let Hf := fresh in intros Hf; exact Hf]
| exact ERR | exact RR | exact HP ]
| ] end.

#[using="Type"] Lemma jroot_null_dec : forall r : jroot, r = JRnull \/ r <> JRnull.
Proof. destruct r; [left; reflexivity | right; discriminate ..]. Qed.

#[using="Type"] Lemma set_boolean_P : jo_set_scalar_stmt S4L HIx S4F 0x25754.
Proof.
unfold jo_set_scalar_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
ss_open HP RR ST ERR K.
destruct (jroot_null_dec r) as [-> | NN].
{ destruct RR as [-> ->]. pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_truex. bw. apply evt_RZ_done. apply K0. }
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jroot_hdr r m BS p RR NN (nodup_app_l' _ _ ND)) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app hl_segs S4L] in HDR.
destruct (Z.eq_dec ty JT_BOOLEAN) as [E | NE].
-
specialize (TB E). subst r ty. clear TI. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs S4L] in CELLS, OPB. unfold jhdr_cells, JT_BOOLEAN in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR.
pose proof (munch_refl [(p, p + 48)] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_lit.
bw.
apply evt_RZ_done.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ split; [| split; [apply model_vm_only_refl | split; [ exact ST | split; [ | exists errv; exact ERR ]]]].
* apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
* eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b' Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 48.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,48)::PBS) LB p 48 48); [exact ND | left; reflexivity].
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 48)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. cbn. split; [|exact I].
assert (NEa : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NEa). lia.
* exists (bv_unsigned a1), junk_. split; [reflexivity|]. unfold jhdr_cells, JT_BOOLEAN. cbn [app]. rewrite Z_to_bv_bv_unsigned. assumption.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW.
-
pose proof (munch_refl [] m) as MU. unfold JT_BOOLEAN in NE.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_truex.
bw. apply evt_RZ_done. apply K0.
Qed.

#[using="Type"] Lemma set_int_P : jo_set_scalar_stmt S4L HIx S4F 0x2598c.
Proof.
unfold jo_set_scalar_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
ss_open HP RR ST ERR K.
destruct (jroot_null_dec r) as [-> | NN].
{ destruct RR as [-> ->]. pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_truex. bw. apply evt_RZ_done. apply K0. }
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jroot_hdr r m BS p RR NN (nodup_app_l' _ _ ND)) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app hl_segs S4L] in HDR.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR.
pose proof (munch_refl [(p, p + 56)] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_lit.
bw.
apply evt_RZ_done.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ split; [| split; [apply model_vm_only_refl | split; [ exact ST | split; [ | exists errv; exact ERR ]]]].
* apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
* eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b' Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 56.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,56)::PBS) LB p 56 56); [exact ND | left; reflexivity].
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. cbn. split; [|exact I].
assert (NEa : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 56 a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NEa). lia.
* exists 0, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW.
-
pose proof (munch_refl [] m) as MU. unfold JT_INT in NE.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_truex.
bw. apply evt_RZ_done. apply K0.
Qed.

#[using="Type"] Lemma set_int64_P : jo_set_scalar_stmt S4L HIx S4F 0x259c0.
Proof.
unfold jo_set_scalar_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
ss_open HP RR ST ERR K.
destruct (jroot_null_dec r) as [-> | NN].
{ destruct RR as [-> ->]. pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_truex. bw. apply evt_RZ_done. apply K0. }
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jroot_hdr r m BS p RR NN (nodup_app_l' _ _ ND)) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app hl_segs S4L] in HDR.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR.
pose proof (munch_refl [(p, p + 56)] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_lit.
bw.
apply evt_RZ_done.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ split; [| split; [apply model_vm_only_refl | split; [ exact ST | split; [ | exists errv; exact ERR ]]]].
* apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
* eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b' Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 56.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,56)::PBS) LB p 56 56); [exact ND | left; reflexivity].
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. cbn. split; [|exact I].
assert (NEa : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 56 a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NEa). lia.
* exists 0, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW.
-
pose proof (munch_refl [] m) as MU. unfold JT_INT in NE.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_truex.
bw. apply evt_RZ_done. apply K0.
Qed.

#[using="Type"] Lemma set_uint64_P : jo_set_scalar_stmt S4L HIx S4F 0x25d28.
Proof.
unfold jo_set_scalar_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
ss_open HP RR ST ERR K.
destruct (jroot_null_dec r) as [-> | NN].
{ destruct RR as [-> ->]. pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_truex. bw. apply evt_RZ_done. apply K0. }
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (jroot_hdr r m BS p RR NN (nodup_app_l' _ _ ND)) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app hl_segs S4L] in HDR.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR.
pose proof (munch_refl [(p, p + 56)] m) as MU.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_lit.
bw.
apply evt_RZ_done.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ split; [| split; [apply model_vm_only_refl | split; [ exact ST | split; [ | exists errv; exact ERR ]]]].
* apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf].
* eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b' Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists p, 56.
split; [left; reflexivity | split; [ | lia]].
eapply (nodup_prefix_suffix ((p,56)::PBS) LB p 56 56); [exact ND | left; reflexivity].
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. cbn. split; [|exact I].
assert (NEa : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_app_iff. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 56 a k HP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NEa). lia.
* exists 1, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW.
-
pose proof (munch_refl [] m) as MU. unfold JT_INT in NE.
apply rz_evt; [exact MOK|]. bstep. if_falsex. bw. if_truex.
bw. apply evt_RZ_done. apply K0.
Qed.

End SetScalP.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac bstep := TopUbTac.ub_skip; step. Ltac bstepz := TopUbTac.ub_skip; stepz.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section GetPureP.
Variable HIx : heap_iface S4L.

Ltac gp_open HP JO m s BS p :=
let MOK := fresh "MOK" in
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK;
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI;
pose proof (wmono_refl rsegs m) as WM; pose proof (munch_refl (@nil (Z * Z)) m) as MU;
apply rz_evt; [exact MOK|];
destruct s as [sh|];
[ destruct JO as [Hp J];
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND;
destruct (jval_hdr rsegs S4F sh m BS p 1 J (nodup_app_l' _ _ ND)) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE);
pose proof (heap_blk S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as (_ & Hpal & Hplo & Hphi & _);
pose proof (heap_blk_img S4L HIx _ _ _ _ p n HP ltac:(in_sub INp)) as Hpimg; cbn [hl_img_lo hl_img_hi S4L] in Hpimg;
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi;
unfold jhdr_cells in HDR, SZ; cbn [app hl_segs S4L] in HDR, SZ;
pose proof (jtype_range sh) as JR;
bstep; if_falsex
| destruct JO as [Hp _]; rewrite Hp in *; bstep; if_truex ].

Ltac gp_ret K := apply evt_RZ_done; eapply K; apply ret_statew_intro; [ try apply fsaved_refl | intros Hf; exact Hf ].

#[using="Type"] Lemma get_type_P : jo_get_pure_stmt S4L HIx S4F 0x2496c.
Proof.
unfold jo_get_pure_stmt. intros until s. intros HP JO RA FRM A0 K. cbn [hl_segs S4L] in *. subst a0.
gp_open HP JO m s BS p.
- bstep. bstep. gp_ret K.
- bstep. gp_ret K.
Qed.

#[using="Type"] Lemma get_object_P : jo_get_pure_stmt S4L HIx S4F 0x254cc.
Proof.
unfold jo_get_pure_stmt. intros until s. intros HP JO RA FRM A0 K. cbn [hl_segs S4L] in *. subst a0.
gp_open HP JO m s BS p.
- bstep. rewrite sx32_small by lia. bstep. bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit;
try (bstep; bstep; gp_ret K).

destruct (jval_obj_open rsegs S4F kids m BS p 1 J) as (pb1 & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR1 & LT & OK).
unfold jhdr_cells in HDR1. cbn [app hl_segs S4L] in HDR1.
bstep. bstep. gp_ret K.
- bstep. gp_ret K.
Qed.

#[using="Type"] Lemma get_array_P : jo_get_pure_stmt S4L HIx S4F 0x268c4.
Proof.
unfold jo_get_pure_stmt. intros until s. intros HP JO RA FRM A0 K. cbn [hl_segs S4L] in *. subst a0.
gp_open HP JO m s BS p.
- bstep. rewrite sx32_small by lia. bstep. bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit;
try (bstep; bstep; gp_ret K).
destruct (jval_arr_open rsegs S4F kids m BS p 1 J) as (pb1 & PBS & a & ABS & ps & KBS & EBS & OPB & HDR1 & AL & OK).
unfold jhdr_cells in HDR1. cbn [app hl_segs S4L] in HDR1.
bstep. bstep. gp_ret K.
- bstep. gp_ret K.
Qed.

#[using="Type"] Lemma get_string_len_P : jo_get_pure_stmt S4L HIx S4F 0x26658.
Proof.
unfold jo_get_pure_stmt. intros until s. intros HP JO RA FRM A0 K. cbn [hl_segs S4L] in *. subst a0.
gp_open HP JO m s BS p.
- bstep. rewrite sx32_small by lia. bstep. bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit;
try (bstep; bstep; gp_ret K).

destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists len tl, - 2^31 < len < 2^31 /\ rw_cells rsegs m p (jhdr_cells 6 1 (fn_str_to_json_string S4F) pb_ 0 0 ++ C8 (Z_to_bv 64 len) :: tl)).
{ destruct h; [destruct J as (len & pd & pdn & str & junk2 & _ & HL & _ & _ & C & _) | destruct J as (len & str & junk & _ & HL & _ & C)];
exists len; eexists; (split; [lia | exact C]). }
clear J. destruct CELLS as (len & tl & Hlen & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. bstep.
destruct (Z_lt_le_dec len 0) as [Hn | Hn].
+ if_falsex. TopUbTac.ub_skip.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; rewrite QRBl.wz_neg_unsigned; QRBl.ub_cmp_norm; vm_compute; reflexivity] end.
bstep. bstep. gp_ret K.
+ if_truex. bstep. bstep. gp_ret K.
- bstep. bstep. gp_ret K.
Qed.

#[using="Type"] Lemma get_boolean_P : jo_get_pure_stmt S4L HIx S4F 0x25680.
Proof.
unfold jo_get_pure_stmt. intros until s. intros HP JO RA FRM A0 K. cbn [hl_segs S4L] in *. subst a0.
gp_open HP JO m s BS p.
- bstep. rewrite sx32_small by lia. bstep. bstep.
destruct sh as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
+  bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. bstep. gp_ret K.
+  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists tojs' udel' ud' bits, rw_cells rsegs m p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])).
{ destruct u; [destruct J as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct J as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear J. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
apply evt_RZ_done. eapply K. apply ret_statew_intro; [| intros _; assumption].
intros k Hk. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite !freg_get_other by (vm_compute; reflexivity); reflexivity.
+  bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs S4L] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
* bstep. if_lit. bstep. bstep. bstep. gp_ret K.
* bstep. bstep. bstep. gp_ret K.
+  bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct J as (pb_ & PBS & REST & EBS & OPB & J). cbn [hl_segs S4L] in J.
assert (CELLS : exists len tl, rw_cells rsegs m p (jhdr_cells 6 1 (fn_str_to_json_string S4F) pb_ 0 0 ++ C8 (Z_to_bv 64 len) :: tl)).
{ destruct h; [destruct J as (len & pd & pdn & str & junk2 & _ & HL & _ & _ & C & _) | destruct J as (len & str & junk & _ & HL & _ & C)];
exists len; eexists; exact C. }
clear J. destruct CELLS as (len & tl & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. bstep. bstep. gp_ret K.
+  bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. bstep. gp_ret K.
+  bstep. bstep. if_lit. bstep. bstep. if_lit. bstep. bstep. gp_ret K.
- bstep. bstep. gp_ret K.
Qed.
End GetPureP.

End RC__1.
