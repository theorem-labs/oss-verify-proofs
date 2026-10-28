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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UP7U.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DescA.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -96 - 8432.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis MEMMOVE : memmove_stmt.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -96)).
Notation TP := (Z_to_bv 64 0x77c00).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation NEXT := (next_post HIx sp gp s10 s11 lo errv).
Notation head_stmt' := (head_stmt HIx sp gp s10 s11 lo errv).

#[using="LO LOS SPA HT MEMMOVE"] Lemma descend_arr : forall c kids,
desc_stmt HIx sp gp s10 s11 lo errv c -> head_stmt' false kids ->
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS1 bs : list blk) (x q v : Z) (T : TSet)
(nz : nat) (a arr size : Z),
HEAPx A (bs ++ XBS1 ++ LB) m md ->
zomb rsegs S4F c m v bs ->
zarr rsegs S4F m x q kids (S nz) a arr size XBS1 ->
stk rsegs m lo (bv_unsigned sp + -96) -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x247ec) fc1 None m (seg_rom rsegs)) md) T.
Proof.
intros c kids KD HK. intros until size. intros HP ZC Z ST ERR K.
unfold_consts. word_range sp SPW.
assert (USP : bv_unsigned SPR = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
destruct Z as (pb & PBS & KBS & ps & EX1 & OPB & HDR & AL & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L _].
destruct (zomb_zhead HIx sp gp s10 s11 lo errv c m v bs ZC KD) as (isobjc & ck & ZCH & HC). clear ZC KD.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct (zhead_hdr isobjc m v 0 ck bs ZCH (nodup_app_l _ _ ND)) as (pbc & cfc & INv & HDRC & CLOSEC).
assert (INv' : In (v, 48) (bs ++ XBS1 ++ LB)) by in_sub INv.
assert (INx : In (x, 48) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
pose proof (heap_blk S4L HIx _ _ _ _ v 48 HP INv') as (_ & Hval & Hvlo & Hvhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ v 48 HP INv') as Hvimg. cbn [hl_img_lo hl_img_hi S4L] in Hvimg.
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi, Hxhi.
assert (NVX : forall k, ~ In (v, k) (XBS1 ++ LB)) by (intros k; exact (nodup_prefix_suffix bs (XBS1 ++ LB) v 48 k ND INv)).
assert (Hxv : x <> v) by (intros ->; apply (NVX 48); rewrite EX1; in_elem).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 v 48 HP INx INv' Hxv) as Dxv.
assert (HPal : HEAPx A ((a, 32) :: (arr, 8 * size) :: (x, 48) :: concat KBS ++ PBS ++ bs ++ LB) m md).
{ eapply (heap_perm S4L HIx); [exact HP | rewrite EX1; hperm]. }
destruct (al_blocks S4L HIx _ _ _ _ _ _ _ HPal) as ((Haal & Halo & Hahi & Haimg) & (Hral & Hrlo & Hrhi & Hrimg) & Har).
cbn [hl_img_lo hl_img_hi S4L] in Haimg, Hrimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi, Hrhi.
assert (INa : In (a, 32) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (INr : In (arr, 8 * size) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_elem).
assert (Hva : v <> a) by (intros E; apply (NVX 32); rewrite E, EX1; in_elem).
assert (Hvr : v <> arr) by (intros E; apply (NVX (8 * size)); rewrite E; rewrite EX1; in_elem).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ v 48 a 32 HP INv' INa Hva) as Dva.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ v 48 arr (8 * size) HP INv' INr Hvr) as Dvr.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HPal) as Har'.
assert (Hxa : x <> a).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. apply Hn1. right. left. reflexivity. }
assert (Hxr : x <> arr).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. inversion ND3 as [|y' l' Hn2 ND4]; subst. apply Hn2. left. reflexivity. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 a 32 HP INx INa Hxa) as Dxa.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x 48 arr (8 * size) HP INx INr Hxr) as Dxr.
clear HPal.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(v + 24, v + 40)] m) as MU.
unfold jhdr_cells in HDRC. cbn [app] in HDRC. unfold jhdr_cells in HDR. cbn [app] in HDR.
stash Dxa. stash Dxr. stash Dva. stash Dvr.
apply rz_evt; [exact MOK|].
step. step. ubsan_align Hval.
stepz. step. step. norm_w32. step. step. if_true. step. step. step.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
destruct (blk_write_in S4L HIx _ _ _ _ _ _ _ _ HP INv' MU WM MI ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as [HP1 AGV].
assert (AGX : agree_on rsegs (XBS1 ++ LB) m m1).
{ eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others; [in_sub Hb | intros ->; exact (NVX bk Hb)]. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp + -96) m m1).
{ eapply (blk_write_in_pres S4L HIx); [exact HP | exact INv' | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]
| intros b Hb; in_sub Hb | intros k Hk; apply (NVX k); in_sub Hk | clia]. }
assert (ZCH1 : zhead isobjc m1 v x ck bs).
{ apply (CLOSEC m1 x); [unfold jhdr_cells; cbn [app]; exact HDRC |].
eapply agree_on_incl; [exact AGV|]. intros [ba bk] Hb. apply in_others_iff in Hb as [Hb Hne]. apply in_others; [in_sub Hb | exact Hne]. }
assert (AL1 : alist rsegs S4F m1 [(a, 32); (arr, 8 * size)] a (ps ++ repeat 0 (S nz))).
{ eapply alist_agree; [exact AL | exact AGX | intros b Hb; rewrite EX1; in_sub Hb]. }
clear CLOSEC MU WM.
match goal with H : rw_cells _ m1 v _ |- _ => stash H end.
unstash Dxa. unstash Dxr.
pose proof (wmono_refl rsegs m1) as WM. pose proof (munch_refl [(bv_unsigned sp + -96 - 80, bv_unsigned sp + -96); (a, a + 32); (arr, arr + 8 * size)] m1) as MU.
pose proof (array_list_del_idx_spec MEMMOVE) as DELX.
specialize DELX with (a := a) (arr := arr) (size := size) (ps := ps) (zs := repeat 0 (S nz)) (lo := lo).
stash Hvimg. stash Hximg. stash Dxv. stash Har. stash NVX. stash AGV. stash AGX.
call DELX; [exact MI | exact AL1 | intros b n Hb; destruct Hb as [E | [E | []]]; inversion E; subst; clear E; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | apply Forall_repeat0 | exact Har | rewrite USP; exact ST | rewrite USP; lia | lia | lia
| reflexivity | rewrite L; reflexivity | rewrite repeat_length; apply f_equal; lia |].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv rsegs m4 |- _ => rename H into MI4 end.
match goal with H : stk rsegs m4 _ _ |- _ => rename H into ST4 end.
match goal with H : alist _ _ m4 _ _ _ |- _ => rename H into AL4 end.
rewrite USP in ST4.
unstash Hvimg. unstash Hximg. unstash Dxv. unstash Har. unstash NVX. unstash AGV. unstash AGX.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP1) as ND1.
assert (NEa : forall bb kk, In (bb, kk) (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB) -> a <> bb /\ arr <> bb).
{ intros bb kk Hb. split.
- eapply (nodup_in_ne (bs ++ XBS1 ++ LB) [(a, 32); (arr, 8 * size)] (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB)); [rewrite EX1; hperm | exact ND1 | in_elem | exact Hb].
- eapply (nodup_in_ne (bs ++ XBS1 ++ LB) [(a, 32); (arr, 8 * size)] (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB)); [rewrite EX1; hperm | exact ND1 | in_elem | exact Hb]. }
assert (AG4 : agree_on rsegs (bs ++ (x, 48) :: concat KBS ++ PBS ++ LB) m1 m4).
{ eapply agree_of_munch; [exact MU | exact WM |]. intros bb kk Hb.
assert (Hb' : In (bb, kk) (bs ++ XBS1 ++ LB)) by (rewrite EX1; in_sub Hb).
destruct (NEa bb kk Hb) as [N1 N2].
pose proof (heap_blk S4L HIx _ _ _ _ bb kk HP1 Hb') as (Hk0 & _ & _ & Hbhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a 32 bb kk HP1 INa Hb' N1) as D1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ arr (8 * size) bb kk HP1 INr Hb' N2) as D2.
cbn. clear - D1 D2 Hbhi Hk0 LO LOS SPW. lia. }
assert (HP4 : HEAPx A (bs ++ XBS1 ++ LB) m4 md).
{ eapply (heap_frame S4L HIx); [exact HP1 | | exact WM | exact MI4].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [cbn [fst snd]; left; split; [clia | pose proof (hi_top_hi S4L HIx); lia] |].
apply Forall_cons; [cbn [fst snd]; right; left; exists a, 32; split; [exact INa | lia] |].
apply Forall_cons; [cbn [fst snd]; right; left; exists arr, (8 * size); split; [exact INr | lia] | apply Forall_nil]. }
assert (HPR4 : heap_pres S4L LB (bv_unsigned sp + -96) m1 m4).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp + -96)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP1 | intros b Hb; in_sub Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists a, 32; split; [exact INa|]; split; [| lia] |].
{ intros Hin. exact (proj1 (NEa a 32 ltac:(in_sub Hin)) eq_refl). }
apply Forall_cons; [cbn [fst snd]; right; left; exists arr, (8 * size); split; [exact INr|]; split; [| lia] | apply Forall_nil].
{ intros Hin. exact (proj2 (NEa arr (8 * size) ltac:(in_sub Hin)) eq_refl). } }
step.
apply evt_RZ_done.
eapply (descend_tail HIx sp gp s10 s11 lo errv isobjc false ck kids)
with (XBS2 := ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS) ++ PBS) (bs := bs) (LB := LB) (q := q);
[exact HC | exact HK | eapply (heap_perm S4L HIx); [exact HP4 | rewrite EX1; hperm] | | | exact ST4 | exact ERR |].
- eapply (zhead_agree isobjc); [exact ZCH1 | exact AG4 | intros b Hb; in_sub Hb].
- exists a, arr, size. exists pb, PBS, KBS, ps. split; [reflexivity|].
split; [| split; [unfold jhdr_cells; cbn [app]; assumption | split; [cbn [repeat]; rewrite app_nil_r; exact AL4|]]].
+ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply agree_on_incl; [exact AG4 | intros b Hb; in_sub Hb].
+ eapply okids_agree; [exact OK | | apply incl_refl]. eapply agree_on_trans.
* eapply agree_on_incl; [exact AGX | intros b Hb; rewrite EX1; in_sub Hb].
* eapply agree_on_incl; [exact AG4 | intros b Hb; in_sub Hb].
- intros ms' md' NP. apply K. eapply next_post_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | | exact NP].
eapply heap_pres_trans; [exact HPR1 | exact HPR4].
Qed.
End DescA.

End RC__1.
