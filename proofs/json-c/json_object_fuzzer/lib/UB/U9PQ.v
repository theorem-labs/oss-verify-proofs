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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ug1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ug1M. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDc2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDc2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFNy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFNy.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section JoObjAdd3.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis HASH : lh_char_hash_stmt HIx model_vm_only 8320.
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

#[using="PUT HASH LO LOS SPA HT RA INK KN FRM LK1 LK2 Kont"] Lemma oadd_main :
forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (errv : word) (svs : list slotv),
HEAPx A (OBS ++ VBS ++ LB) m0 md0 ->
rw_cells rsegs m0 p OHDR ->
lh_open rsegs S4F m0 t tbl size es svs ->
okids rsegs S4F m0 kids (map kv es) KBS -> opt_pbuf rsegs m0 PBS pb -> jopt rsegs S4F vs m0 VBS v ->
cstr rsegs m0 k kn ks -> jc_glob_P m0 ->
rw_cells rsegs m0 (0x77c00 - 164) [C4 errv] ->
stk rsegs m0 lo (bv_unsigned sp) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x254f8) fc None m0 (seg_rom rsegs)) md0) T.
Proof.
intros until svs. intros HP HDR OPEN KIDS OPB JOB CS G ERR ST.
pose proof HDR as HDR0. unfold UDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
unfold_consts. word_range sp SPR.
destruct (oadd_facts HIx p t tbl size es _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold UDc2.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS p v vs _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold UDc2.OBS; perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.
assert (INK' : In (k, kn) (OBS ++ VBS ++ LB)) by (apply in_or_app; right; apply in_or_app; right; exact INK).
destruct (key_string HIx _ _ _ _ _ _ _ HP INK' CS) as (slack & STR & PAD & NN & KAL & KL & KPOS & KHI & KSL).
unfold alloc_ceiling, sp_window_lo, stack_max_size in KHI.
pose proof (heap_blk_img S4L HIx _ _ _ _ k kn HP INK') as Hkimg. cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free S4F] in THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m0) as MU.
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash G. stash KF. stash STR. stash HDR0. stash PAD. stash KSL. stash KAL.
stash Hpimg. stash Htimg. stash Hbimg. stash Hkimg. stash SEP. stash D1. stash D2.
apply rz_evt; [exact MOK|].
carve_frame 48%nat ST.
do 7 step. step. if_falsex. step. step. step. ubsan_align Hpal. step. step. if_falsex.
step. step. step. ubsan_align Htal. do 5 step.

unstash CS. unstash G.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
assert (HP1 : HEAPx A (OBS ++ VBS ++ LB) mA md0) by heap_now S4L HIx HP MU WM MI.
assert (HPR1 : heap_pres S4L (OBS ++ VBS ++ LB) (bv_unsigned sp) m0 mA).
{ eapply (heap_pres_of_munch S4L); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; exact Hb | clia | solve_clientW S4L HIx HP]. }
assert (AG1 : agree_on rsegs (OBS ++ VBS ++ LB) m0 mA) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR1 | reflexivity | apply incl_refl]).
pose proof (cstr_agree rsegs _ _ _ _ _ _ CS AG1 INK' ltac:(lia)) as CS1.
pose proof (jc_glob_P_pres _ _ _ _ HPR1 G) as G1.
pose proof HASH as HASH'. unfold lh_char_hash_stmt in HASH'.
apply evt_RZ_done.
eapply HASH' with (LB := OBS ++ VBS ++ LB) (lo := lo) (kp := k) (kn := kn) (ks := ks);
[ exact HP1 | exact INK' | exact CS1 | exact G1 | rewrite unsigned_lit by lia; exact ST | clia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRM | reflexivity | ].
clear HASH'.
intros ms2 md2 (mB & A2 & h & e2 & RS2 & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash HDR0.
assert (AG2 : agree_on rsegs (OBS ++ VBS ++ LB) m0 mB).
{ eapply agree_on_trans; [exact AG1|]. eapply (agree_of_heap_presx rsegs S4L); [exact HPR2 | reflexivity | apply incl_refl]. }
assert (HPRa : heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 mB).
{ eapply heap_presx_trans; [apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR1 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb] |].
eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb | intros a Xa; exact Xa]. }
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (INp : In (p, 48) (OBS ++ VBS ++ LB)) by (unfold UDc2.OBS; cbn; left; reflexivity).
apply (rw_cells_agree rsegs _ _ _ _ _ HDR0) in AG2 as HDR2; [| exists p, 48; split; [exact INp | cbn; lia]].
pose proof HDR2 as HDR2'. unfold UDc2.OHDR in HDR2. cbn [fn_obj_to_json_string S4F] in HDR2.
pose proof (lh_open_agree rsegs S4F _ _ _ _ _ _ _ _ OPEN AG2 ltac:(unfold UDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN2.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS AG2 ltac:(unfold UDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS2.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG2 ltac:(unfold UDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB2.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB2.
pose proof (cstr_agree rsegs _ _ _ _ _ _ CS AG2 INK' ltac:(lia)) as CS2.
clear HP MU WM MI HDR THDR OPEN KIDS OPB JOB CS G ST HP1 HPR1 AG1 CS1 G1 AG2 STR.

pose proof (proj1 (cstr_bytes rsegs _ _ _ _ CS2)) as KB2.
pose proof (proj1 OPEN2) as THDR. unfold lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free S4F] in THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mB) as WM. pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp + -48)] mB) as MU.
stash OPEN2. stash KIDS2. stash OPB2. stash JOB2. stash CS2. stash G2. stash HDR2'.
reenter MOK2.
step. step. step. try ub_if_lit. step. step. step. step.

unstash OPEN2.
assert (BELOW : lh_below lo t tbl size es).
{ unstash KF. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He) as (_ & _ & K2 & _). unfold_consts. lia. }
eapply evt_cut.
{ eapply (lh_lookup_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 t tbl size k lo es svs ks) with (h := h);
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
first [exact MI | exact OPEN2 | exact BELOW | exact KB2 | exact NN | exact ST2 | reflexivity | exact Hh | exact Htal | exact Hbal | exact Htlo | exact Hblo | lia]. }
unfold lh_lookup_post. cbv beta. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia.
post_call rsegs mB.
match goal with H : lh_open rsegs S4F ?mx t tbl size es svs |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN3; rename mx into mC end.
match goal with H : stk rsegs mC lo _ |- _ => rename H into ST3 end.
match goal with H : lookup_res tbl es ks ?rr |- _ => rename H into RES; rename rr into r end.
match goal with H : mem_inv rsegs mC |- _ => rename H into MI3 end.
unstash KIDS2. unstash OPB2. unstash JOB2. unstash CS2. unstash G2. unstash HDR2'.
assert (HP3 : HEAPx A2 (OBS ++ VBS ++ LB) mC md2) by heap_now S4L HIx HP2 MU WM MI3.
assert (AG3 : agree_on rsegs (OBS ++ VBS ++ LB) mB mC).
{ eapply (agree_of_munch rsegs); [exact MU | exact WM |]. intros a n Ha. cbn.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP2 Ha) as (? & _ & _ & ? & _). unfold_consts. lia. }
assert (HPRb : heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 mC).
{ eapply heap_presx_trans; [exact HPRa|]. eapply (heap_presx_of_munch S4L); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP2 | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb | clia | solve_clientW S4L HIx HP2]. }
pose proof (rw_cells_agree rsegs _ _ _ _ _ HDR2' AG3 ltac:(exists p, 48; split; [exact INp | cbn; lia])) as HDR3.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS2 AG3 ltac:(unfold UDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS3.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB2 AG3 ltac:(unfold UDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB3.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB2 AG3 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB3.
pose proof (cstr_agree rsegs _ _ _ _ _ _ CS2 AG3 INK' ltac:(lia)) as CS3.
pose proof (jc_glob_P_munch _ _ _ G2 MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; unfold_consts; lia)) as G3.
match goal with H : oadd_frame mC |- _ => rename H into FR3 | H : rw_cells rsegs mC (bv_unsigned sp + -48) _ |- _ => rename H into FR3 end.
match goal with H : rw_cells rsegs mC (490496 - 164) _ |- _ => rename H into ERR3 | H : rw_cells rsegs mC 490332 _ |- _ => rename H into ERR3 end.
step. if_falsex. step.
destruct RES as [-> | (j & e & Hj & -> & Hks)].
-
if_true.
apply evt_RZ_done.
eapply (oadd_ins HIx HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB VBS PBS KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN LK1 LK2 Kont);
first [exact HP3 | exact HDR3 | exact OPEN3 | exact KIDS3 | exact OPB3 | exact JOB3 | exact CS3 | exact G3 | exact ERR3 | exact ST3 | exact FR3
| exact VM2 | exact HPRb | exact FS2 | exact (FRM2 FRM) | exact Hh].
-
destruct (lh_open_slot rsegs S4F _ _ _ _ _ _ _ _ _ OPEN3 Hj) as (sl & _ & Hix & _).
pose proof OPEN3 as (_ & _ & _ & _ & _ & _ & Hlen).
unfold ent_addr. if_falsex. fold (ent_addr tbl (le_ix e)).
apply evt_RZ_done.
eapply (oadd_dup HIx PUT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB VBS PBS KBS lo p v k pb t tbl size es kids vs T
LO LOS SPA HT LK1 LK2 Kont);
first [exact HP3 | exact HDR3 | exact OPEN3 | exact Hj | exact KIDS3 | exact OPB3 | exact JOB3 | exact G3 | exact ERR3 | exact ST3 | exact FR3
| exact VM2 | exact HPRb | exact FS2 | exact FRM2].
Qed.
End JoObjAdd3.

Section JoObjAddStmt.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.
Hypothesis HASH : lh_char_hash_stmt HIx model_vm_only 8320.

#[using="PUT HASH"] Lemma json_object_object_add_ex_cps : jo_object_add_ex_P HIx 0.
Proof.
unfold jo_object_add_ex_P, jo_object_add_ex_stmt. intros until errv. intros PRE G J JOB INK CS KN FRM A0 A1 A2 A3 K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA). cbn [hl_segs hl_tp hl_volatile S4L] in *.
destruct (sobj_open rsegs S4F _ _ _ _ _ J) as (pb & PBS & t & TBS & kvs & KBS & EBS & OPB & HDR & TAB & L1 & L2 & KIDS).
destruct TAB as (tbl & size & es & svs & Hkvs & ETBS & OPEN). subst OBS TBS kvs a0 a1 a2 a3 tp.
rewrite length_map in L1.
eapply (oadd_main HIx PUT HASH ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB VBS PBS KBS lo p v k kn pb t tbl size es ks kids vs T
LO LOS SPA HT RA INK KN FRM L1 L2).
- intros ms' md' m' r PO G' OUT. exact (K ms' md' m' r PO G' OUT).
- exact HP.
- exact HDR.
- exact OPEN.
- exact KIDS.
- exact OPB.
- exact JOB.
- exact CS.
- exact G.
- exact ERR.
- exact ST.
Qed.

#[using="PUT HASH"] Lemma json_object_object_add_cps : jo_object_add_P HIx.
Proof.
pose proof json_object_object_add_ex_cps as AX. unfold jo_object_add_ex_P, jo_object_add_ex_stmt in AX.
unfold jo_object_add_P, jo_object_add_stmt. intros until errv. intros PRE G J JOB INK CS KN FRM A0 A1 A2 K.
pose proof PRE as (HP & _). cbn [hl_segs S4L] in HP.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
cbn [hl_segs S4L].
apply rz_evt; [exact MOK|].
step. step.
apply evt_RZ_done.
eapply AX; [exact PRE | exact G | exact J | exact JOB | exact INK | exact CS | exact KN | exact FRM | exact A0 | exact A1 | exact A2
| first [reflexivity | apply bv_eq; vm_compute; reflexivity] | exact K].
Qed.
End JoObjAddStmt.

End RC__1.
