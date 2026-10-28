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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ3T.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ3T. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiRK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiRK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require USK8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import USK8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeuE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeuE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIX4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIX4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uxk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uxk8. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiEN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiEN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNPb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKci.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKci. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UP7U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UP7U. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPNZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPNZ.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section BodyA.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - 8432.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis MEMMOVE : memmove_stmt.

Notation head_stmt' := (head_stmt HIx sp gp s10 s11 lo errv).

#[using="LO LOS SPA HT MEMMOVE"] Lemma body_arr_ok : forall kids k,
desc_opt HIx sp gp s10 s11 lo errv k ->
cont_stmt HIx sp gp s10 s11 lo errv false kids ->
head_stmt' false kids ->
body_stmt HIx sp gp s10 s11 lo errv false kids k.
Proof.
intros kids k KD CONT HEADK.
unfold body_stmt. intros until cur. intros HP ZB ST ERR K.
unfold_consts. word_range sp SPW. cbn [tyof].
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct ZB as (a & arr & size & Z0).
destruct (zarr_last rsegs S4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & ps1 & v & EX & OPB & HDR & AL & L1 & OK1 & Hk). clear Z0.
assert (HPal : HEAPx A ((a, 32) :: (arr, 8 * size) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB) m md).
{ eapply (heap_perm S4L HIx); [exact HP | rewrite EX; hperm]. }
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HPal) as ((Haal & Halo & Hahi & Haimg) & (Hral & Hrlo & Hrhi & Hrimg) & Har).
cbn [hl_img_lo hl_img_hi S4L] in Haimg, Hrimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi, Hrhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INr : In (arr, 8 * size) (XBS ++ LB)) by (rewrite EX; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (Hxr : x <> arr).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. inversion ND3 as [|y' l' Hn2 ND4]; subst. apply Hn2. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 arr (8 * size) HP INx INr Hxr) as Dxr.
pose proof AL as (arr_ & size_ & junk_ & Eal & Hlen & Hsz & _ & _). injection Eal as E1 E2.
assert (size_ = size) by lia. subst arr_ size_. clear E2 junk_.
rewrite length_app, length_app, repeat_length in Hlen. cbn [length] in Hlen.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [] m) as MU.
pose proof HDR as HDR0. stash HDR0. stash OPB. stash OK1. stash Hk.
pose proof (array_list_set_idx_spec) as SETX.
specialize SETX with (a := a) (arr := arr) (size := size) (ps := (ps1 ++ [v]) ++ repeat 0 nz) (idx := Z.of_nat (length kids)) (d := 0).
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. if_true. step. step. step.
call array_list_get_idx_spec; [exact MI | exact AL | intros b n Hb; destruct Hb as [E | [E | []]]; inversion E; subst; clear E; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | reflexivity | reflexivity | lia |].
replace (al_nth ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids))) with v by (rewrite <- L1; symmetry; apply al_nth_app_len).
replace (Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz))) with true by (symmetry; apply Z.ltb_lt; rewrite !length_app, repeat_length; cbn [length]; lia).
cbn match.
step. step. step. step. step. step.

match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (AL3 : alist rsegs S4F m3 [(a, 32); (arr, 8 * size)] a ((ps1 ++ [v]) ++ repeat 0 nz)).
{ eapply alist_agree; [exact AL | eapply agree_of_munch; [exact MU | exact WM | intros; exact I] | apply incl_refl]. }
assert (MU' : munch [(arr, arr + 8 * size)] m m3) by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; slia).
clear MU. rename MU' into MU.
stash Haimg. stash Hximg.
call SETX; [exact MI3 | exact AL3 | intros b n Hb; destruct Hb as [E | [E | []]]; inversion E; subst; clear E; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | exact Har | reflexivity | reflexivity | reflexivity | lia |].
unstash Haimg. unstash Hximg.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv rsegs m4 |- _ => rename H into MI4 end.
match goal with H : alist _ _ m4 _ _ _ |- _ => rename H into AL4 end.
replace (Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz))) with true in AL4 |- *
by (symmetry; apply Z.ltb_lt; rewrite !length_app, repeat_length; cbn [length]; lia).
rewrite Nat2Z.id, <- L1, <- app_assoc in AL4. cbn [app] in AL4. rewrite upd_app_len' in AL4.
change (ps1 ++ 0 :: repeat 0 nz) with (ps1 ++ [0] ++ repeat 0 nz) in AL4. rewrite app_assoc in AL4.
clear AL AL3.
destruct (blk_write_in S4L HIx _ _ _ _ _ _ _ _ HP INr MU WM MI4 ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as [HP4 AGR].
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
set (XBS1 := ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS1) ++ PBS).
assert (HPR4 : heap_pres S4L LB (bv_unsigned sp + -96) m m4).
{ eapply (blk_write_in_pres S4L HIx); [exact HP | exact INr | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]
| intros b Hb; in_sub Hb | intros kk Hkk; exact (nodup_prefix_suffix XBS LB arr (8 * size) kk ND ltac:(rewrite EX; in_elem) Hkk) | clia]. }
unstash HDR0. unstash OPB. unstash OK1. unstash Hk.
assert (Z4 : zarr rsegs S4F m4 x q kids (S nz) a arr size XBS1).
{ subst XBS1. eapply (zarr_last_close rsegs S4F m m4); [exact OPB | exact HDR0 | exact OK1 | exact AL4 |].
eapply agree_on_incl; [exact AGR|]. intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
apply not_eq_sym. eapply (nodup_in_ne (XBS ++ LB) [(arr, 8 * size)] ((a, 32) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact ND | left; reflexivity | in_sub Hb]. }
unstash Hk. step. destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J4 : jval rsegs S4F c m4 bs v 1).
{ eapply jval_agree; [exact J | eapply agree_on_incl; [exact AGR|] | apply incl_refl].
intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
apply not_eq_sym. eapply (nodup_in_ne (XBS ++ LB) [(arr, 8 * size)] ((a, 32) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact ND | left; reflexivity | in_sub Hb]. }
clear J.
assert (HPc : HEAPx A (bs ++ XBS1 ++ LB) m4 md) by (eapply (heap_perm S4L HIx); [exact HP4 | subst XBS1; rewrite EX; hperm]).
pose proof (nodup_app_l _ _ (heap_blk_nodup S4L HIx _ _ _ _ HPc)) as NDbs.
destruct (jval_hdr rsegs S4F c m4 bs v 1 J4 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heap_blk S4L HIx _ _ _ _ v cn HPc ltac:(in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_falsex. step. step. step.
apply evt_RZ_done.
eapply (maybe_free_cps HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := v) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J4 | .. ]; try alloc_side.
intros ms5 md5 (m5 & A5 & r & RS5 & VM5 & ST5 & HPR5 & ERR5 & OUT5).
destruct RS5 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR5 by lia.
match goal with H : rw_cells _ m4 x _ |- _ => rename H into HDR4 end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in HDR4; [| eapply client_range_block; [subst XBS1; in_elem | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR4.
assert (Z5 : zarr rsegs S4F m5 x q kids (S nz) a arr size XBS1).
{ eapply (zarr_agree rsegs S4F (XBS1 ++ LB)); [exact Z4 | eapply (agree_of_heap_pres rsegs S4L); [exact HPR5 | reflexivity | intros b Hb; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR45 : heap_pres S4L LB (bv_unsigned sp + -96) m m5).
{ eapply heap_pres_trans; [exact HPR4 | eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; in_sub Hb]]. }
clear MU WM MI4 HP4 HPal HP AGR Z4 ST J4 HPc.
destruct OUT5 as [(_ & Habs & _) | [(-> & _ & HP5) | (-> & _ & ZC & HP5)]]; [lia | |].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl rsegs m5) as WM.
reenter MOK5.
step. if_falsex. step. norm_w32. step. if_true.
apply evt_RZ_done.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [exact HP5 | exists a, arr, size; exact Z5 | exact ST5 | exact ERR5 |].
intros ms' md' NP. apply K. eapply next_post_w; [exact FS5 | exact FRM5 | exact VM5 | exact HPR45 | exact NP].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl rsegs m5) as WM.
reenter MOK5.
step. if_true.
apply evt_RZ_done.
eapply (descend_arr HIx sp gp s10 s11 lo errv LO LOS SPA HT MEMMOVE c kids KD HEADK); [exact HP5 | exact ZC | exact Z5 | exact ST5 | exact ERR5 |].
intros ms' md' NP. apply K. eapply next_post_w; [exact FS5 | exact FRM5 | exact VM5 | exact HPR45 | exact NP].
-
destruct Hk as [Hv Ebs]. rewrite Hv. if_true. step. norm_w32. step. if_true.
apply evt_RZ_done.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
assert (HPn : HEAPx A (XBS1 ++ LB) m4 md) by (eapply (heap_perm S4L HIx); [exact HP4 | subst XBS1 bs; rewrite EX; hperm]).
eapply CONT; [exact HPn | exists a, arr, size; exact Z4 | exact ST | | ].
+ assumption.
+ intros ms' md' NP. apply K. eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | exact HPR4 | exact NP].
Qed.
End BodyA.

End RC__1.
