(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKdB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKdB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U22i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Umd7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtfO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtfO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULAQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULAQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ug1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ug1M.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoObjAdd.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis HASH : lh_char_hash_stmt HIx model_vm_only 8320.

Definition RESIZE : lh_resize_stmt HIx model_vm_only (64 + 8320) :=
lh_resize_cps HIx lf_test_spec_proof model_vm_only model_vm_only_refl model_vm_only_trans (fun a b H => H) 8320 ltac:(lia) HASH.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB VBS PBS : list blk) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (96 + 64 + 64 + 8256 + 2048).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis INK : In (k, kn) LB.
Hypothesis KN : kn <= 2^31.
Hypothesis FRM : frm0 fc.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.

Definition OBS : list blk := ((p, 48) :: lh_blocks t tbl size es ++ concat KBS) ++ PBS.

Definition OHDR : list cell :=
[C4 (Z_to_bv 64 JT_OBJECT); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 (fn_obj_to_json_string S4F)); C8 (Z_to_bv 64 pb); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 t)].
Definition oadd_frame (m : word -> option byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Hypothesis Kont : forall ms' md' m' r,
jo_post_framex S4L ra sp gp (Z_to_bv 64 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo r m' ms' md' -> jc_glob_P m' ->
((r = 0 /\ exists A' OBS' kids', jval rsegs S4F (Sobj kids') m' OBS' p 1 /\ HEAPx A' (OBS' ++ LB) m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)) \/
(r = 2^64 - 1 /\ exists A' REM, jval rsegs S4F (Sobj kids) m' OBS p 1 /\ jopt rsegs S4F vs m' VBS v /\ HEAPx A' (OBS ++ VBS ++ REM ++ LB) m' md')) ->
realizes rsegs (mkCfg ms' md') T.

#[using="Type"] Lemma oadd_facts : forall A m md LIST REST,
HEAPx A LIST m md -> Permutation LIST (lh_blocks t tbl size es ++ (p, 48) :: REST) ->
(p mod 16 = 0 /\ 0 < p /\ p + 48 <= alloc_ceiling /\ (p + 48 <= 0x10000 \/ 0x99000 <= p)) /\
(t mod 16 = 0 /\ 0 < t /\ t + 56 <= alloc_ceiling /\ (t + 56 <= 0x10000 \/ 0x99000 <= t)) /\
(tbl mod 16 = 0 /\ 0 < tbl /\ tbl + 40 * size <= alloc_ceiling /\ (tbl + 40 * size <= 0x10000 \/ 0x99000 <= tbl)) /\
(t + 56 <= tbl \/ tbl + 40 * size <= t) /\ (p + 48 <= t \/ t + 56 <= p) /\ (p + 48 <= tbl \/ tbl + 40 * size <= p) /\
(forall e, In e es -> 0 <= le_kn e /\ 0 < le_k e /\ le_k e + le_kn e <= alloc_ceiling /\
(t + 56 <= le_k e \/ le_k e + le_kn e <= t) /\ (tbl + 40 * size <= le_k e \/ le_k e + le_kn e <= tbl)).
Proof.
clear Kont LO LOS SPA HT RA INK KN FRM LK1 LK2. intros A m md LIST REST HP0 PERM.
pose proof (heap_perm S4L HIx _ _ _ _ _ HP0 PERM) as HP. clear HP0 PERM.
destruct (lh_heap_facts S4L HIx _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi S4L] in Htimg, Hbimg.
unfold lh_blocks in HP. cbn [app] in HP.
assert (INp : In (p, 48) ((t, 56) :: (tbl, 40 * size) :: map (fun e => (le_k e, le_kn e)) es ++ (p, 48) :: REST)) by (right; right; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p 48 HP INp) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn in ND. rewrite map_app in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst.
assert (Hpt : p <> t) by (intros E; apply Hni; right; apply in_or_app; right; left; exact E).
assert (Hpb : p <> tbl) by (intros E; apply Hni'; apply in_or_app; right; left; exact E).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 t 56 HP INp ltac:(left; reflexivity) Hpt) as D1.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ p 48 tbl (40 * size) HP INp ltac:(right; left; reflexivity) Hpb) as D2.
split; [repeat split; assumption|]. split; [repeat split; assumption|]. split; [repeat split; assumption|].
split; [exact SEP|]. split; [exact D1|]. split; [exact D2|].
intros e He. destruct (KF e He) as (K0 & K1 & K2 & _ & K4 & K5). repeat (split; [assumption|]). exact K5.
Qed.

#[using="Type"] Lemma oadd_pv : forall A m md LIST REST,
HEAPx A LIST m md -> Permutation LIST ((p, 48) :: VBS ++ REST) -> jopt rsegs S4F vs m VBS v ->
p <> v /\ 0 <= v /\ v + 1 <= alloc_ceiling.
Proof.
clear Kont LO LOS SPA HT RA INK KN FRM LK1 LK2. intros A m md LIST REST HP0 PERM JOB.
pose proof (heap_perm S4L HIx _ _ _ _ _ HP0 PERM) as HP. clear HP0 PERM.
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(left; reflexivity)) as (_ & _ & Hplo & Hphi & _).
pose proof (jopt_val rsegs S4F S4L HIx _ _ _ _ vs VBS v HP ltac:(intros b Hb; right; apply in_or_app; left; exact Hb) JOB) as [V0 V1].
split; [| split; [exact V0 | exact V1]].
destruct vs as [s'|]; cbn in JOB.
- destruct JOB as [Hv J]. destruct (jval_root_in rsegs S4F _ _ _ _ _ J) as (n & Hin & Hn).
intros E. subst v.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. apply Hni.
rewrite map_app. apply in_or_app; left. exact (in_map blk_addr _ _ Hin).
- destruct JOB as [-> _]. lia.
Qed.

#[using="HASH fc LO LOS SPA HT RA INK KN LK1 LK2 Kont"] Lemma oadd_ins :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : Model) (A2 : AS S4L HIx) (h : Z) (errc : word) (svs : list slotv),
HEAPx A2 (OBS ++ VBS ++ LB) mc mdc ->
rw_cells rsegs mc p OHDR ->
lh_open rsegs S4F mc t tbl size es svs ->
okids rsegs S4F mc kids (map kv es) KBS -> opt_pbuf rsegs mc PBS pb -> jopt rsegs S4F vs mc VBS v ->
cstr rsegs mc k kn ks -> jc_glob_P mc ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
stk rsegs mc lo (bv_unsigned sp + -48) ->
oadd_frame mc ->
model_vm_only md0 mdc -> heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 mc ->
fsaved F F2 -> frm0 fc2 -> 0 <= h < 2^64 ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 v) (Z_to_bv 64 0) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) (Z_to_bv 64 k) (Z_to_bv 64 h) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x255a0) fc2 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until svs. intros HP HDR OPEN KIDS OPB JOB CS G ERR ST FR VMa HPRa FSa FRMa Hh.
unfold oadd_frame in FR. unfold OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
unfold_consts. word_range sp SPR.
destruct (oadd_facts _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold OBS; perm)) as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold OBS; perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.
assert (INK' : In (k, kn) (OBS ++ VBS ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact INK).
destruct (key_string HIx _ _ _ _ _ _ _ HP INK' CS) as (slack & STR & PAD & NN & KAL & KL & KPOS & KHI & KSL).
unfold alloc_ceiling, sp_window_lo, stack_max_size in KHI.
pose proof (heap_blk_img S4L HIx _ _ _ _ k kn HP INK') as Hkimg. cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] mc) as MU.
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash G. stash KF. stash SEP. stash D1. stash D2.
apply rz_evt; [exact MOK|].
step. step. try ub_if_lit. step. step.

apply evt_RZ_done.
eapply (strdup_cps HIx) with (LB := OBS ++ VBS ++ LB) (lo := lo) (str := ks) (slack := slack);
[ heap_now S4L HIx HP MU WM MI
| rewrite unsigned_lit by lia; exact STR | exact NN | rewrite unsigned_lit by lia; exact PAD
| rewrite !unsigned_lit by lia; eapply client_range_block; [exact INK' | lia | lia]
| rewrite !unsigned_lit by lia; left; lia | lia | .. ]; try alloc_side.
intros ms4 md4 (mE & A4 & r2 & e4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & STR4 & OUT4). open_ret RS4. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit k) in STR4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR4 by lia.
unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash CS. unstash G.
assert (AG4 : agree_on rsegs (OBS ++ VBS ++ LB) mc mE) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | apply incl_refl]).
assert (HPRb : heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 mE).
{ eapply heap_presx_trans; [exact HPRa|]. apply heap_pres_presx.
eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (INp : In (p, 48) (OBS ++ VBS ++ LB)) by (unfold OBS; cbn; left; reflexivity).
apply (rw_cells_agree rsegs _ _ _ _ _ HDR) in AG4 as HDR4; [| exists p, 48; split; [exact INp | cbn; lia]].
pose proof (lh_open_agree rsegs S4F _ _ _ _ _ _ _ _ OPEN AG4 ltac:(unfold OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN4.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS AG4 ltac:(unfold OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS4.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG4 ltac:(unfold OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB4.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG4 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB4.
pose proof (jc_glob_P_pres _ _ _ _ HPR4 G) as G4.
clear MU WM MI HDR OPEN KIDS OPB JOB G ST STR.
destruct OUT4 as [(-> & HP4) | (Hr2 & NEWK & HP4)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mE) as WM. pose proof (munch_refl [] mE) as MU.
stash OPEN4. stash KIDS4. stash OPB4. stash JOB4.
reenter MOK4.
step. step. if_true. step. do 8 step.
apply evt_RZ_done.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
unstash OPEN4. unstash KIDS4. unstash OPB4. unstash JOB4.
apply (Kont _ md4 mE (2^64 - 1)).
+ unfold jo_post_framex. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [exact FSa | intros _; exact FRMa] |].
split; [eapply model_vm_only_trans; [exact VMa | exact VM4] |].
split; [release_frame FR ST4 (bv_unsigned sp); exact ST4 |].
split; [exact HPRb | exists e4; exact ERR4].
+ exact G4.
+ right. split; [reflexivity|]. exists A4, []. split; [| split; [exact JOB4 | cbn [app]; exact HP4]].
eapply (sobj_close rsegs S4F) with (TBS := lh_blocks t tbl size es) (kvs := map kv es);
[ reflexivity | exact OPB4 | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR4
| exists tbl, size, es, svs; split; [reflexivity | split; [reflexivity | exact OPEN4]]
| rewrite length_map; exact LK1 | exact LK2 | exact KIDS4 ].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
pose proof (wmono_refl rsegs mE) as WM. pose proof (munch_refl [] mE) as MU.
stash OPEN4. stash KIDS4. stash OPB4. stash JOB4. stash NEWK.
reenter MOK4.
step. step. if_falsex. step. step. step. step. step. step. do 5 step. step. step.
unstash OPEN4. unstash KIDS4. unstash OPB4. unstash JOB4. unstash NEWK. unstash CS.
release_frame FR ST4 (bv_unsigned sp).
assert (CS4 : cstr rsegs mE r2 (Z.of_nat (length ks) + 1) ks).
{ split; [lia|]. split; [exact (proj1 (proj2 CS))|]. exists []. rewrite app_nil_r.
replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (Z.to_nat (Z.of_nat (length ks) + 1)) by reflexivity. exact NEWK. }
apply evt_RZ_done.
eapply (lh_insert_cps HIx lf_test_spec_proof model_vm_only model_vm_only_refl (64 + 8320) RESIZE ltac:(lia))
with (LB := (p, 48) :: concat KBS ++ PBS ++ VBS ++ LB) (t := t) (tbl := tbl) (size := size) (es := es) (svs := svs)
(k := r2) (kn := Z.of_nat (length ks) + 1) (ks := ks) (v := v) (h := h) (lo := lo) (errv := e4);
[ eapply (heap_perm S4L HIx); [exact HP4 | unfold OBS; perm]
| exact OPEN4 | exact G4 | exact CS4 | lia | lia | exact Hh | exact ST4 | clia | lia | exact SPA | exact HT | exact ERR4
| reflexivity | exact RA | exact FRMa | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
intros ms5 md5 (mF & A5 & r5 & e5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & G5 & OUT5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs S4L] in *.
set (LBI := (p, 48) :: concat KBS ++ PBS ++ VBS ++ LB) in *.
assert (AG5 : agree_on rsegs LBI mE mF) by (eapply (agree_of_heap_presx rsegs S4L); [exact HPR5 | reflexivity | apply incl_refl]).
assert (HiK : incl (concat KBS) LBI) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBS LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LB LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
apply (rw_cells_agree rsegs _ _ _ _ _ HDR4) in AG5 as HDR5; [| exists p, 48; split; [left; reflexivity | cbn; lia]].
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS4 AG5 HiK) as KIDS5.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB4 AG5 HiP) as OPB5.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB4 AG5 HiV) as JOB5.
apply (Kont _ md5 mF r5).
+ unfold jo_post_framex. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FSa | exact FS5] | intros _; apply FRM5; exact FRMa] |].
split; [eapply model_vm_only_trans; [exact VMa | eapply model_vm_only_trans; [exact VM4 | exact VM5]] |].
split; [exact ST5|].
split; [| exists e5; exact ERR5].
eapply heap_presx_trans; [exact HPRb|]. eapply heap_presx_weaken; [exact HPR5 | lia | exact HiL | intros a Xa; exact Xa].
+ exact G5.
+ destruct OUT5 as [(-> & OPEN5 & CS5 & HP5) | (-> & tbl' & size' & es' & svs' & g & STRIP & OPEN5 & HP5)].
*
right. split; [reflexivity|]. exists A5, [(r2, Z.of_nat (length ks) + 1)]. split; [| split; [exact JOB5 |]].
-- eapply (sobj_close rsegs S4F) with (TBS := lh_blocks t tbl size es) (kvs := map kv es);
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR5
| exists tbl, size, es, svs; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map; exact LK1 | exact LK2 | exact KIDS5 ].
-- eapply (heap_perm S4L HIx); [exact HP5 | unfold LBI, OBS; perm].
*
left. split; [reflexivity|].
exists A5, (((p, 48) :: lh_blocks t tbl' size' (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks v]) ++ concat (KBS ++ [VBS])) ++ PBS), (kids ++ [vs]).
split; [| split; [| split]].
-- eapply (sobj_close rsegs S4F) with (kvs := map kv (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks v]));
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR5
| exists tbl', size', (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks v]), svs'; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map, !length_app, (strip_length _ _ STRIP); cbn [length]; lia
| rewrite !length_app; cbn [length]; lia
| rewrite map_app, (strip_kv _ _ STRIP); cbn [map]; apply okids_app; [exact KIDS5 | apply okids_one; unfold kv; cbn [le_v]; exact JOB5] ].
-- rewrite concat_app. cbn [concat]. rewrite app_nil_r. eapply (heap_perm S4L HIx); [exact HP5 | unfold LBI; perm].
-- rewrite length_app. cbn [length]. lia.
-- rewrite okmax_app, okmax_single. pose proof (okmax_nonneg kids). pose proof (odep_nonneg vs). lia.
Qed.
End JoObjAdd.

End RC__1.
