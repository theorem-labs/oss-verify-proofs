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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UAIk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UAIk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXZq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXZq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ3T.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ3T.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPNZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUoP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFsM.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Loop3.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - 8432.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis DEL : lh_delete_tail_stmt2 HIx.
Hypothesis MEMMOVE : memmove_stmt.

Notation head_stmt' := (head_stmt HIx sp gp s10 s11 lo errv).
Notation cont_stmt' := (cont_stmt HIx sp gp s10 s11 lo errv).
Notation body_stmt' := (body_stmt HIx sp gp s10 s11 lo errv).

#[using="RC__ sp"] Lemma zcont_len : forall isobj m x q kids nz cur XBS,
zcont isobj m x q kids nz cur XBS -> Z.of_nat (length kids) < 2^62.
Proof.
intros isobj m x q kids nz cur XBS ZC. destruct isobj.
- destruct ZC as (t & tbl & size & es & svs & Z0 & _).
destruct Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & _). pose proof (lf_thr_lt size Hsz). pose proof (lf_size_range size Hsz).
assert (length esk <= length es)%nat by (rewrite Ees, length_app; lia). lia.
- destruct ZC as (a & arr & size & pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _].
destruct AL as (arr' & size' & junk & E & Hlen & Hsz & _). rewrite length_app in Hlen. lia.
Qed.

#[using="LO LOS SPA HT"] Lemma cont_ok : forall isobj kids,
(forall kids1 kl, kids = kids1 ++ [kl] -> body_stmt' isobj kids1 kl) -> cont_stmt' isobj kids.
Proof.
intros isobj kids BODY. unfold cont_stmt. intros until cur. intros HP ZC ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (zcont_len _ _ _ _ _ _ _ _ ZC) as LK.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [] m) as MU.
apply rz_evt; [exact MOK|].
step. step. step.
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
- cbn [length Z.of_nat Z.add]. if_true.
apply evt_RZ_done.
eapply (pop_ok HIx sp gp s10 s11 lo errv LO LOS SPA HT isobj); [exact HP | | exact ST | exact ERR | exact K].
destruct isobj; [destruct ZC as (t & tbl & size & es & svs & Z0 & _); exists t, tbl, size, es, svs; exact Z0 | exact ZC].
- rewrite length_app in LK |- *. cbn [length] in LK |- *.
if_falsex.
replace (Z.of_nat (length kids1 + 1) + -1) with (Z.of_nat (length kids1)) by lia.
apply evt_RZ_done.
eapply (BODY kids1 kl eq_refl); [exact HP | | exact ST | exact ERR | exact K].
destruct isobj.
+ destruct ZC as (t & tbl & size & es & svs & Z0 & CUR). destruct (CUR kids1 kl eq_refl) as (e & He & Ec).
exists t, tbl, size, es, svs, e. split; [exact Z0 | split; [exact He | exact Ec]].
+ exact ZC.
Qed.

#[using="LO LOS SPA HT"] Lemma head_ok : forall isobj kids,
(forall kids1 kl, kids = kids1 ++ [kl] -> body_stmt' isobj kids1 kl) -> head_stmt' isobj kids.
Proof.
intros isobj kids BODY. unfold head_stmt. intros until T. intros HP ZH ST ERR K.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [] m) as MU.
destruct isobj.
- destruct ZH as (t & tbl & size & es & svs & Z0).
pose proof Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1.
destruct esz; [| cbn in Lz; discriminate]. rewrite app_nil_r in Ees. subst esk.
pose proof OPEN as (HDRT & _ & _ & _ & Hsz & Hcnt & Hlen). unfold lh_hdrf in HDRT.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
assert (HPl : HEAPx A (lh_blocks t tbl size es ++ ((x, 48) :: concat KBS ++ PBS ++ LB)) m md).
{ eapply (heap_perm S4L HIx); [exact HP | rewrite EX; hperm]. }
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HPl) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & Httb & _).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi. clear HPl.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (LT : lhtab2 rsegs S4F m (lh_blocks t tbl size es) t (map (fun e => (le_k e, le_v e)) es)).
{ exists tbl, size, es, svs. split; [reflexivity|]. split; [reflexivity | exact OPEN]. }
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. step. ubsan_align Hxal.
step. norm_w32. step. step. if_false. step.
call lh_table_length_spec; [exact MI | exact LT | exact Htlo | exact Htal | reflexivity |].
rewrite length_map. step. step. if_falsex. step. step. ubsan_align Htal. step.
step.
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
+ destruct es; [| cbn in L1; discriminate]. cbn [length Z.of_nat]. if_false. step.
apply evt_RZ_done.
eapply (pop_ok HIx sp gp s10 s11 lo errv LO LOS SPA HT true); [ | exists t, tbl, size, (@nil lent), svs | | | intros ms' md' NP; apply K; eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | eapply (heap_pres_of_munch S4L); [exact MU | exact WM | intros; exact I] | exact NP]].
* eapply (heap_frame S4L HIx); [exact HP | eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_nil | exact WM | assumption].
* eapply (zobj_agree rsegs S4F (XBS ++ LB)); [exact Z0 | eapply agree_of_munch; [exact MU | exact WM | intros; exact I] | intros b Hb; in_sub Hb].
* assumption.
* assumption.
+ rewrite length_app in L1. cbn [length] in L1.
if_truex. step. norm_w32. step. step. step.
replace (Z.of_nat (length es) + -1) with (Z.of_nat (length kids1)) by lia.
destruct (snoc_inv_gen es) as [-> | (es1 & el & ->)]; [cbn in L1; lia|].
rewrite length_app in L1. cbn [length] in L1.
rewrite (tl_of_last tbl (es1 ++ [el]) (length kids1) el) by (first [rewrite nth_error_app2 by lia; replace (length kids1 - length es1)%nat with 0%nat by lia; reflexivity | rewrite length_app; cbn; lia]).
apply evt_RZ_done. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 0 + 1)).
eapply (BODY kids1 kl eq_refl); [ | | | | intros ms' md' NP; apply K; eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | eapply (heap_pres_of_munch S4L); [exact MU | exact WM | intros; exact I] | exact NP]].
* eapply (heap_frame S4L HIx); [exact HP | eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_nil | exact WM | assumption].
* exists t, tbl, size, (es1 ++ [el]), svs, el. split; [| split; [rewrite nth_error_app2 by lia; replace (length kids1 - length es1)%nat with 0%nat by lia; reflexivity | reflexivity]].
eapply (zobj_agree rsegs S4F (XBS ++ LB)); [exact Z0 | eapply agree_of_munch; [exact MU | exact WM | intros; exact I] | intros b Hb; in_sub Hb].
* assumption.
* assumption.
- destruct ZH as (a & arr & size & Z0).
pose proof Z0 as (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. cbn [repeat] in AL. rewrite app_nil_r in AL.
pose proof AL as (arr' & size' & junk & Eal & Hlen & Hsz & _ & _). injection Eal as E1 E2. assert (size' = size) by lia. subst arr' size'. clear E2.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
apply rz_evt; [exact MOK|].
step. step. ubsan_align Hxal.
step. norm_w32. step. step. if_true. step.
call array_list_length_spec; [exact MI | exact AL | intros b n Hb; assert (Hb' : In (b, n) (XBS ++ LB)) by (rewrite EX; in_sub Hb); destruct (heap_blk S4L HIx _ _ _ _ b n HP Hb') as (_ & Hb16 & Hb0 & Hbhi & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | reflexivity |].
step. step.
destruct (snoc_inv_gen kids) as [-> | (kids1 & kl & ->)].
+ destruct ps; [| cbn in L1; discriminate]. cbn [length Z.of_nat]. if_true.
apply evt_RZ_done.
eapply (pop_ok HIx sp gp s10 s11 lo errv LO LOS SPA HT false); [ | exists a, arr, size | | | intros ms' md' NP; apply K; eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | eapply (heap_pres_of_munch S4L); [exact MU | exact WM | intros; exact I] | exact NP]].
* eapply (heap_frame S4L HIx); [exact HP | eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_nil | exact WM | assumption].
* eapply (zarr_agree rsegs S4F (XBS ++ LB)); [exact Z0 | eapply agree_of_munch; [exact MU | exact WM | intros; exact I] | intros b Hb; in_sub Hb].
* assumption.
* assumption.
+ rewrite length_app in L1. cbn [length] in L1.
if_falsex. step. norm_w32. step. step. step.
replace (Z.of_nat (length ps) + -1) with (Z.of_nat (length kids1)) by lia.
apply evt_RZ_done. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 0 + 1)).
eapply (BODY kids1 kl eq_refl); [ | | | | intros ms' md' NP; apply K; eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | eapply (heap_pres_of_munch S4L); [exact MU | exact WM | intros; exact I] | exact NP]].
* eapply (heap_frame S4L HIx); [exact HP | eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU); apply Forall_nil | exact WM | assumption].
* exists a, arr, size.
eapply (zarr_agree rsegs S4F (XBS ++ LB)); [exact Z0 | eapply agree_of_munch; [exact MU | exact WM | intros; exact I] | intros b Hb; in_sub Hb].
* assumption.
* assumption.
Qed.

#[using="LO LOS SPA HT DEL MEMMOVE"] Lemma loop_all : forall isobj kids, kids_desc HIx sp gp s10 s11 lo errv kids -> cont_stmt' isobj kids /\ head_stmt' isobj kids.
Proof.
intros isobj kids. induction kids as [|k kids IH] using rev_ind; intros KD.
- split; [apply cont_ok | apply head_ok]; intros kids1 kl E; destruct kids1; discriminate.
- assert (KD1 : kids_desc HIx sp gp s10 s11 lo errv kids) by (intros k' Hk'; apply KD; apply in_or_app; left; exact Hk').
destruct (IH KD1) as [CONT HEAD].
assert (B : body_stmt' isobj kids k).
{ destruct isobj; [apply body_obj_ok | apply body_arr_ok]; try assumption; apply KD; apply in_or_app; right; left; reflexivity. }
split; [apply cont_ok | apply head_ok]; intros kids1 kl E; apply app_inj_last in E as [<- <-]; exact B.
Qed.

#[using="LO LOS SPA HT DEL MEMMOVE"] Theorem desc_all : forall c, desc_stmt HIx sp gp s10 s11 lo errv c.
Proof.
apply jshape_ind2; try (intros; exact I).
- intros kids IH. cbn. apply (proj2 (loop_all true kids ltac:(intros [c|] Hin; [exact (IH c Hin) | exact I]))).
- intros kids IH. cbn. apply (proj2 (loop_all false kids ltac:(intros [c|] Hin; [exact (IH c Hin) | exact I]))).
Qed.
End Loop3.

End RC__1.
