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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U22i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Umd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Umd7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtfO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtfO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ug1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ug1M. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDc2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDc2.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoObjAdd2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB VBS PBS : list blk) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (96 + 64 + 64 + 8256 + 2048).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.
Notation OBS := (OBS PBS KBS p t tbl size es).
Notation OHDR := (OHDR pb t).
Notation oadd_frame := (oadd_frame ra sp s0 s1 s2 s3 s4).
Hypothesis Kont : forall ms' md' m' r,
jo_post_framex S4L ra sp gp (Z_to_bv 64 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo r m' ms' md' -> jc_glob_P m' ->
((r = 0 /\ exists A' OBS' kids', jval rsegs S4F (Sobj kids') m' OBS' p 1 /\ HEAPx A' (OBS' ++ LB) m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)) \/
(r = 2^64 - 1 /\ exists A' REM, jval rsegs S4F (Sobj kids) m' OBS p 1 /\ jopt rsegs S4F vs m' VBS v /\ HEAPx A' (OBS ++ VBS ++ REM ++ LB) m' md')) ->
realizes rsegs (mkCfg ms' md') T.

#[using="LO LOS LK1 LK2 Kont"] Lemma oadd_setv :
forall (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F3 : bvmap 5 word) (fc3 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errc : word) (svs : list slotv)
(j : nat) (e : lent) (CK : list blk) (kids1 kids2 : list (option jshape)) (kj : option jshape) (KBS1 KBS2 : list (list blk)) (bsj : list blk)
(pre post : list lent),
HEAPx A ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e => (le_k e, le_kn e)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)) m md ->
rw_cells rsegs m p OHDR ->
lh_open rsegs S4F m t tbl size es svs -> nth_error es j = Some e -> es = pre ++ e :: post -> length pre = j ->
kids = kids1 ++ kj :: kids2 -> KBS = KBS1 ++ bsj :: KBS2 -> length kids1 = j -> length KBS1 = j ->
okids rsegs S4F m kids1 (map kv pre) KBS1 -> okids rsegs S4F m kids2 (map kv post) KBS2 ->
opt_pbuf rsegs m PBS pb -> jopt rsegs S4F vs m VBS v -> jc_glob_P m ->
rw_cells rsegs m (0x77c00 - 164) [C4 errc] ->
stk rsegs m lo (bv_unsigned sp + -48) ->
oadd_frame m ->
model_vm_only md0 md -> heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 m ->
fsaved F F3 -> (frm0 fc -> frm0 fc3) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 v) x9 (Z_to_bv 64 (ent_addr tbl (le_ix e))) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F3 (Z_to_bv 64 0x25590) fc3 None m (seg_rom rsegs)) md) T.
Proof.
intros until post. intros HP HDR OPEN Hj Ees Lpre Ek EK Lk1 Lb1 K1 K2 OPB JOB G ERR ST FR VMa HPRa FSa FRMa.
unfold UDc2.oadd_frame in FR. unfold UDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
unfold_consts. word_range sp SPR.
destruct (oadd_facts HIx p t tbl size es _ _ _ _ (concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB) HP ltac:(unfold lh_blocks; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS p v vs _ _ _ _ ((t, 56) :: (tbl, 40 * size) :: (map (fun e => (le_k e, le_kn e)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ LB)) HP ltac:(perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.
destruct (lh_open_slot rsegs S4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & _ & _ & Hlen).
remember (ent_addr tbl (le_ix e)) as EA eqn:HEA.
assert (EAR : tbl <= EA /\ EA + 40 <= tbl + 40 * size) by (subst EA; unfold ent_addr; split; [lia | nia]).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(EA + 16, EA + 24)] m) as MU.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash Hpimg. stash Htimg.

pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn [map blk_addr fst] in ND.
assert (NTB : ~ In tbl (map blk_addr (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB))).
{ inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. inversion Hnd' as [|x'' l'' Hni'' Hnd'']; subst. exact Hni''. }
assert (NOTIN : ~ In (tbl, 40 * size) LB).
{ intros Hin. apply NTB. rewrite !map_app. repeat (apply in_or_app; right). exact (in_map blk_addr _ _ Hin). }
apply rz_evt; [exact MOK|].
step. step. step.
do 8 step.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G. unstash KF. unstash SEP. unstash Hpimg. unstash Htimg.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
assert (AGo : agree_on rsegs (others tbl ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB))) m mS).
{ eapply (agree_others_of_munch rsegs); [ right; right; left; reflexivity | | | exact MU | exact WM | ].
- intros a1' k1 a2' k2 H1 H2 NE. exact (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP H1 H2 NE).
- intros a1' k1 H1. exact (proj1 (heap_blk S4L HIx _ _ _ _ _ _ HP H1)).
- apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
assert (INC : forall X, incl X (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB) ->
incl X (others tbl ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)))).
{ intros X HX b Hb. apply in_others_iff. split; [right; right; right; exact (HX _ Hb)|]. cbn. intros E. apply NTB. rewrite <- E. exact (in_map blk_addr _ _ (HX _ Hb)). }
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AGo ltac:(apply INC; intros b Hb; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB'.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AGo ltac:(apply INC; intros b Hb; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB'.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K1 AGo ltac:(apply INC; intros b Hb; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K1'.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K2 AGo ltac:(apply INC; intros b Hb; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K2'.
assert (OPEN' : lh_open rsegs S4F mS t tbl size (upd es j (with_v e v)) (upd svs (le_ix e) (sv_with_v sl v))).
{ unfold lh_open. eapply (lh_open_set_val rsegs S4F); [exact OPEN | exact Hj | exact Hsl | lia | exact MU | exact WM | | exact SEP | | ].
- apply Forall_cons; [subst EA; cbn [fst snd]; lia | apply Forall_nil].
- intros x Hx. destruct (KF x Hx) as (_ & _ & _ & _ & K5). exact K5.
- subst EA. exact SLOT. }
apply evt_RZ_done. apply (Kont _ md mS 0).
- unfold jo_post_framex. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [exact FSa | exact FRMa] |].
split; [exact VMa|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| exists errc; exact ERR].
eapply heap_presx_trans; [exact HPRa|].
eapply (heap_presx_of_munch S4L); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; right; right; right; do 5 (apply in_or_app; right); exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists tbl, (40 * size). split; [in_prefix | split; [exact NOTIN | lia]].
- eapply jc_glob_P_munch; [exact G | exact MU | exact WM |]. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
- left. split; [reflexivity|].
exists A, (((p, 48) :: lh_blocks t tbl size (upd es j (with_v e v)) ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS), (kids1 ++ vs :: kids2).
split; [| split; [| split]].
+ eapply (sobj_close rsegs S4F) with (kvs := map kv (upd es j (with_v e v))) (KBS := KBS1 ++ VBS :: KBS2);
[ reflexivity | exact OPB' | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR
| exists tbl, size, (upd es j (with_v e v)), (upd svs (le_ix e) (sv_with_v sl v)); split; [reflexivity | split; [reflexivity | exact OPEN']]
| rewrite length_map, upd_length, !length_app; cbn [length]; subst kids; rewrite length_app in LK1; cbn [length] in LK1; lia
| rewrite !length_app; cbn [length]; subst kids KBS; rewrite !length_app in LK2; cbn [length] in LK2; lia
| ].
rewrite (kv_upd_v es j e v pre post Hj Ees Lpre).
apply okids_app; [exact K1'|]. apply (okids_app rsegs S4F mS [vs] [(le_k e, v)] [VBS] kids2); [apply okids_one; exact JOB' | exact K2'].
+ rewrite (lh_blocks_upd_v t tbl size es j e v Hj). rewrite concat_mid.
eapply (heap_perm S4L HIx).
* eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
* unfold lh_blocks. perm.
+ subst kids. rewrite !length_app. cbn [length]. lia.
+ subst kids. rewrite !okmax_app, !okmax_cons. pose proof (okmax_nonneg kids1). pose proof (okmax_nonneg kids2). pose proof (odep_nonneg vs). pose proof (odep_nonneg kj). lia.
Qed.

#[using="PUT LO LOS SPA HT LK1 LK2 Kont"] Lemma oadd_dup :
forall (x1 t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 x18 x20 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : Model) (A2 : AS S4L HIx) (errc : word) (svs : list slotv)
(j : nat) (e : lent),
HEAPx A2 (OBS ++ VBS ++ LB) mc mdc ->
rw_cells rsegs mc p OHDR ->
lh_open rsegs S4F mc t tbl size es svs -> nth_error es j = Some e ->
okids rsegs S4F mc kids (map kv es) KBS -> opt_pbuf rsegs mc PBS pb -> jopt rsegs S4F vs mc VBS v -> jc_glob_P mc ->
rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
stk rsegs mc lo (bv_unsigned sp + -48) ->
oadd_frame mc ->
model_vm_only md0 mdc -> heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 mc ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0x77c00) t0 t1 t2
(Z_to_bv 64 v) x9 (Z_to_bv 64 (ent_addr tbl (le_ix e))) a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 k) x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x25570) fc2 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until e. intros HP HDR OPEN Hj KIDS OPB JOB G ERR ST FR VMa HPRa FSa FRMa.
pose proof FR as FR0. unfold UDc2.oadd_frame in FR. pose proof HDR as HDR0. unfold UDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
unfold_consts. word_range sp SPR.
destruct (oadd_facts HIx p t tbl size es _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold UDc2.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS p v vs _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold UDc2.OBS; perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.

destruct (lh_open_slot rsegs S4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & LINK & _ & _ & _ & Hlen). destruct LINK as (_ & _ & _ & LK4).
destruct (LK4 e (nth_error_In _ _ Hj)) as (_ & _ & _ & Hve).
remember (ent_addr tbl (le_ix e)) as EA eqn:HEA.
assert (EAR : tbl <= EA /\ EA + 40 <= tbl + 40 * size) by (subst EA; unfold ent_addr; split; [lia | nia]).
assert (EA8 : EA mod 8 = 0) by (subst EA; unfold ent_addr; clear - Hbal; Z.div_mod_to_equations; lia).
assert (Hjkv : nth_error (map kv es) j = Some (le_k e, le_v e)) by (rewrite nth_error_map, Hj; reflexivity).
destruct (okids_nth rsegs S4F _ _ _ _ _ _ _ KIDS Hjkv) as (kj & bsj & Hkj & Hbsj & JO).
destruct (nth_error_split3 _ es j e Hj) as [Ees Lpre]. set (pre := firstn j es) in *. set (post := skipn (S j) es) in *.
destruct (nth_error_split3 _ kids j kj Hkj) as [Ek Lk1]. set (kids1 := firstn j kids) in *. set (kids2 := skipn (S j) kids) in *.
destruct (nth_error_split3 _ KBS j bsj Hbsj) as [EK Lb1]. set (KBS1 := firstn j KBS) in *. set (KBS2 := skipn (S j) KBS) in *.
clearbody pre post kids1 kids2 KBS1 KBS2.
assert (K12 : okids rsegs S4F mc kids1 (map kv pre) KBS1 /\ okids rsegs S4F mc kids2 (map kv post) KBS2).
{ rewrite Ek, Ees, EK, map_app in KIDS. cbn [map] in KIDS.
apply okids_app_inv in KIDS as [K1 K2]; [| rewrite length_map; lia | lia].
split; [exact K1 | exact (proj2 K2)]. }
destruct K12 as [K1 K2].
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash KIDS. stash JO.
apply rz_evt; [exact MOK|].
step. step.
repeat match goal with |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) _] => rewrite (unsigned_lit x) by lia end.
rewrite (ub_land7 EA EA8). if_false. step. step.
destruct kj as [sj|].
-
unstash JO. destruct JO as [Hvo J].
if_falsex. step. step. step.

unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G.
set (LBput := (p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)).
assert (HPp : HEAPx A2 (bsj ++ LBput) mc mdc).
{ eapply (heap_perm S4L HIx); [exact HP|]. unfold UDc2.OBS, LBput. rewrite EK, concat_mid. unfold lh_blocks. perm. }
pose proof PUT as PUT'. unfold put_stmt_P, put_stmt in PUT'. cbn [hl_segs hl_tp S4L] in PUT'.
apply evt_RZ_done.
eapply PUT' with (s := Some sj) (BS := bsj) (p := le_v e) (rc := 1) (LB := LBput) (lo := lo) (errv := errc);
[ exact HPp | cbn [put_pre]; split; [exact Hvo | split; [lia | exact J]] | reflexivity | rewrite unsigned_lit by lia; exact ST | clia
| unfold put_stk_P; rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| rewrite unsigned_lit by lia; lia | exact ERR | reflexivity | rewrite unsigned_lit by lia; reflexivity | ].
clear PUT'.
intros ms5 md5 (mP & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & OUT5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR5 by lia.
destruct OUT5 as [[_ HP5] | (s'' & _ & Hrc & _)]; [| lia].
assert (AG5 : agree_on rsegs LBput mc mP) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR5 | reflexivity | apply incl_refl]).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR0; [| left; cbn; lia].
apply (rw_cells_agree rsegs _ _ _ _ _ HDR0) in AG5 as HDR5; [| exists p, 48; split; [left; reflexivity | cbn; lia]].
pose proof (lh_open_agree rsegs S4F _ _ _ _ _ _ _ _ OPEN AG5 ltac:(unfold LBput, lh_blocks; intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|[Hb|Hb]]; [(clear - Hb; tauto)|(clear - Hb; tauto)|]; right; right; right; apply in_or_app; left; exact Hb)) as OPEN5.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K1 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K15.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K2 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K25.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB5.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB5.
pose proof (jc_glob_P_pres _ _ _ _ HPR5 G) as G5.
assert (HPRb : heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 mP).
{ eapply heap_presx_trans; [exact HPRa|]. apply heap_pres_presx.
eapply heap_pres_weaken; [exact HPR5 | lia | unfold LBput; intros b Hb; right; right; right; do 5 (apply in_or_app; right); exact Hb]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs S4L] in MI5.
clear MU WM MI SLOT HDR OPEN K1 K2 OPB JOB G ST HP HPp AG5 ERR.
pose proof (wmono_refl rsegs mP) as WM. pose proof (munch_refl [] mP) as MU.
reenter MOK5. step. subst EA.
apply evt_RZ_done.
eapply (oadd_setv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 mP md5 A5 errc svs j e [] kids1 kids2 (Some sj) KBS1 KBS2 bsj pre post);
first [exact HP5 | exact HDR5 | exact OPEN5 | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K15 | exact K25 | exact OPB5 | exact JOB5 | exact G5
| exact ERR5 | exact ST5 | exact FR0 | exact HPRb | lia
| eapply model_vm_only_trans; [exact VMa | exact VM5]
| eapply fsaved_trans; [exact FSa | exact FS5]
| intros Hf; apply FRM5; apply FRMa; exact Hf ].
-
unstash JO. destruct JO as [Hvo Ebsj]. rewrite Hvo. if_true.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G.
subst EA.
apply evt_RZ_done.
eapply (oadd_setv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mc mdc A2 errc svs j e [] kids1 kids2 None KBS1 KBS2 bsj pre post);
first [exact HDR0 | exact OPEN | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K1 | exact K2 | exact OPB | exact JOB | exact G
| exact ERR | exact ST | exact FR0 | exact HPRa | exact VMa | exact FSa | exact FRMa | lia | idtac ].
eapply (heap_perm S4L HIx); [exact HP|]. unfold UDc2.OBS. rewrite EK, Ebsj, concat_mid. unfold lh_blocks. perm.
Qed.
End JoObjAdd2.

End RC__1.
