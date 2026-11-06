(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QZDE Qc3B QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QRUw QKQo Q8tj Qu4M QPZI QSL3 Q3jZ Qmd7 Qvbw Qg1M Q7UD Qhd4 Qwm6 QlKV QsKa Q30W Q1Y6 Qiiq Qoif Qkxa Q9O6 QnPO Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QRUw QKQo Q8tj. Import Qu4M.Mq0 QPZI.Mq4.
Import QSL3. Import Q3jZ Qmd7.
Import Qvbw. Import Qg1M.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QlKV.Mq7 QsKa.Mq5 Q30W.Mq3 Q1Y6.Mq0 Q30W.Mq1 QsKa.Mq4 Qiiq.Mq0 QlKV.Mq5 Qoif.Mq0 Qkxa.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import QlKV.Mq2 Q9O6.Mq1 QnPO.Mq1.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoObjAdd2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB VBS PBS LM : list blk) (FRS : list frame) (B0 : bud) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (64 + 96 + 4096 + 128 + HD).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.
Hypothesis BR0 : 512 * (3 + Z.of_nat (length es) + Z.of_nat (length (concat KBS)) + Z.of_nat (length PBS)) <= bB B0.
Hypothesis BD0 : 0 <= bD B0.
Notation OBS := (OBS PBS KBS p t tbl size es).
Notation OHDR := (OHDR pb t).
Notation oadd_frameA := (oadd_frameA ra sp s0 s1 s2 s3 s4 s5 s6).
Notation oadd_factsL := (oadd_factsX HIx LM FRS p t tbl size es).
Notation oadd_pvL := (oadd_pvX HIx VBS LM FRS p v vs).
Notation SB0 := 2147450880.
Hypothesis Kont : forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B0 <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( ( Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA size (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ ( Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B0 - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = size
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms'.

Lemma oadd_len_dup : forall es2 (KBS1 KBS2 : list (list blk)) (bsj : list blk),
KBS = KBS1 ++ bsj :: KBS2 -> length es2 = length es ->
Z.of_nat (length (((p, 48) :: lh_blocks t tbl size es2 ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS)) + Z.of_nat (length bsj)
= Z.of_nat (length OBS) + Z.of_nat (length VBS).
Proof.
clear. intros es2 KBS1 KBS2 bsj EK LEN. unfold Qkxa.OBS, lh_blocks. rewrite EK. cbn [app length].
rewrite !length_app. cbn [length]. rewrite !length_map, !concat_app. cbn [concat]. rewrite !length_app, LEN. lia.
Qed.
Lemma oadd_len_bsj : forall (KBS1 KBS2 : list (list blk)) (bsj : list blk),
KBS = KBS1 ++ bsj :: KBS2 -> (length bsj <= length (concat KBS))%nat.
Proof. clear. intros KBS1 KBS2 bsj ->. rewrite concat_app. cbn [concat]. rewrite !length_app. lia. Qed.

Lemma oadd_setvA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F3 : bvmap 5 word) (fc3 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (errc : word) (svs : list slotv)
(j : nat) (e : lent) (kids1 kids2 : list (option jshape)) (kj : option jshape) (KBS1 KBS2 : list (list blk)) (bsj : list blk)
(pre post : list lent),
HEAPAx A ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e => (le_k e, le_kn e)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)) LM FRS B m md ->
rw_cells asegs m p OHDR ->
lh_open asegs A4F m t tbl size es svs -> nth_error es j = Some e -> es = pre ++ e :: post -> length pre = j ->
kids = kids1 ++ kj :: kids2 -> KBS = KBS1 ++ bsj :: KBS2 -> length kids1 = j -> length KBS1 = j ->
okids asegs A4F m kids1 (map kv pre) KBS1 -> okids asegs A4F m kids2 (map kv post) KBS2 ->
opt_pbuf asegs m PBS pb -> jopt asegs A4F vs m VBS v -> lh_globA m ->
rw_cells asegs m A_ERRNO [C4 errc] ->
stk asegs m lo (bv_unsigned sp + -64) ->
oadd_frameA m ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
fsaved F F3 -> (frm0 fc -> frm0 fc3) ->
bB B0 - 512 * Z.of_nat (length bsj) <= bB B -> bD B0 <= bD B ->
(forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj (kids1 ++ vs :: kids2)) (((p, 48) :: lh_blocks t tbl size es ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS) = Some (w', []) /\ w' <= w + wv) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 v) (Z_to_bv 64 (ent_addr tbl (le_ix e) + 16)) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 (ent_addr tbl (le_ix e) / 8 + 2 + SB0)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F3 (Z_to_bv 64 0x9bf24) fc3 None m (seg_rom asegs)).
Proof.
intros until post. intros HP HDR OPEN Hj Ees Lpre Ek EK Lk1 Lb1 K1 K2 OPB JOB G ERR ST FR VMa HPRa FSa FRMa BBd BDd JX.
unfold Qkxa.oadd_frameA in FR. unfold Qkxa.OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG.
destruct (oadd_factsL _ _ _ _ _ (concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB) HP ltac:(unfold lh_blocks; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvL _ _ _ _ _ ((t, 56) :: (tbl, 40 * size) :: (map (fun e => (le_k e, le_kn e)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ LB)) HP ltac:(perm) JOB) as (Hpv & V0 & V1).
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & Hsz & _ & Hlen).
remember (ent_addr tbl (le_ix e)) as EA eqn:HEA.
assert (EAR : tbl <= EA /\ EA + 40 <= tbl + 40 * size) by (subst EA; unfold ent_addr; split; [lia | nia]).
assert (TB8 : tbl mod 8 = 0) by (clear - Hbal; Z.div_mod_to_equations; lia).
assert (EA8 : EA mod 8 = 0) by (subst EA; unfold ent_addr; clear - TB8; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(EA + 16, EA + 24)] m) as MU.
assert (INtbl : In (tbl, 40 * size) ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)) by (right; right; left; reflexivity).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP INtbl TB8 ltac:(lia)) as SHe. rewrite <- HEA in SHe. a4l.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash Hpimg. stash Htimg.

pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_r in ND. cbn [map blk_addr fst] in ND.
assert (NTB : ~ In tbl (map blk_addr (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB))).
{ inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. inversion Hnd' as [|x'' l'' Hni'' Hnd'']; subst. exact Hni''. }
assert (NOTIN : ~ In (tbl, 40 * size) LB).
{ intros Hin. apply NTB. rewrite !map_app. repeat (apply in_or_app; right). exact (in_map blk_addr _ _ Hin). }
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite ?zxb_zero. step. if_false.
stepz.
do 8 step. step.
release_frame FR ST (bv_unsigned sp). step.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G. unstash KF. unstash SEP. unstash Hpimg. unstash Htimg.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
assert (AGo : agree_on asegs (others tbl ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB))) m mS).
{ eapply (agree_others_of_munch asegs); [ right; right; left; reflexivity | | | exact MU | exact WM | ].
- intros a1' k1 a2' k2 H1 H2 NE. exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact H1) ltac:(apply in_or_app; left; exact H2) NE).
- intros a1' k1 H1. exact (proj1 (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact H1))).
- apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
assert (INC : forall X, incl X (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB) ->
incl X (others tbl ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)))).
{ intros X HX b Hb. apply in_others_iff. split; [right; right; right; exact (HX _ Hb)|]. cbn. intros E. apply NTB. rewrite <- E. exact (in_map blk_addr _ _ (HX _ Hb)). }
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AGo ltac:(apply INC; intros b Hb; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB'.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AGo ltac:(apply INC; intros b Hb; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB'.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K1 AGo ltac:(apply INC; intros b Hb; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K1'.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K2 AGo ltac:(apply INC; intros b Hb; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K2'.
assert (OPEN' : lh_open asegs A4F mS t tbl size (upd es j (with_v e v)) (upd svs (le_ix e) (sv_with_v sl v))).
{ unfold lh_open. eapply (lh_open_set_val asegs A4F); [exact OPEN | exact Hj | exact Hsl | lia | exact MU | exact WM | | exact SEP | | ].
- apply Forall_cons; [subst EA; cbn [fst snd]; lia | apply Forall_nil].
- intros x Hx. destruct (KF x Hx) as (_ & _ & _ & _ & K5). exact K5.
- subst EA. exact SLOT. }
evt_done5. apply (Kont _ md mS 0 A B).
- unfold jo_post_framexA. a4l_goal.
split; [apply ret_statew_intro; [exact FSa | exact FRMa] |].
split; [exact VMa|].
split; [exact ST|].
split; [| exists errc; exact ERR].
eapply heap_presx_trans; [exact HPRa|].
eapply (heap_presx_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
+ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; right; do 5 (apply in_or_app; right); exact Hb | right; exact Hb].
+ apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists tbl, (40 * size).
split; [apply in_or_app; left; in_prefix | split; [| lia]].
apply not_in_app3; [| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ tbl (40 * size) HP ltac:(apply in_or_app; left; exact INtbl))].
intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (NOTIN Hin)|].
clear - HP INtbl Hin. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND.
revert ND. generalize (in_map blk_addr _ _ INtbl). generalize (in_map blk_addr _ _ Hin). cbn [blk_addr fst].
generalize (map blk_addr LM). generalize (map blk_addr ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)).
intros l1 l2 H2 H1 ND. induction l1 as [|y l1 IH]; [exact H1|]. cbn in ND. inversion ND; subst.
destruct H1 as [-> | H1]; [apply H3; apply in_or_app; right; exact H2 | exact (IH H1 H4)].
- eapply lh_globA_frame; [exact G | exact MU | exact WM |]. unfold GHASHA, GSEEDA. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
- exact BDd.
- left. split; [reflexivity|].
exists (((p, 48) :: lh_blocks t tbl size (upd es j (with_v e v)) ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS), (kids1 ++ vs :: kids2).
assert (LU : length (upd es j (with_v e v)) = length es) by (apply upd_length).
pose proof LK1 as LK1'. rewrite Ek, length_app in LK1'. cbn [length] in LK1'.
pose proof LK2 as LK2'. rewrite Ek, EK, !length_app in LK2'. cbn [length] in LK2'.
split; [| split; [| split; [| split]]].
+ eapply (sobj_close asegs A4F) with (kvs := map kv (upd es j (with_v e v))) (KBS := KBS1 ++ VBS :: KBS2);
[ reflexivity | exact OPB' | unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR
| exists tbl, size, (upd es j (with_v e v)), (upd svs (le_ix e) (sv_with_v sl v)); split; [reflexivity | split; [reflexivity | exact OPEN']]
| rewrite length_map, upd_length, !length_app; cbn [length]; lia
| rewrite !length_app; cbn [length]; lia
| ].
rewrite (kv_upd_v es j e v pre post Hj Ees Lpre).
apply okids_app; [exact K1'|]. apply (okids_app asegs A4F mS [vs] [(le_k e, v)] [VBS] kids2); [apply okids_one; exact JOB' | exact K2'].
+ rewrite (lh_blocks_upd_v t tbl size es j e v Hj). rewrite concat_mid.
eapply (heapA_perm A4L HIx); [ | | apply Permutation_refl | apply Permutation_refl].
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU). solve_frameW_withA HP. }
unfold lh_blocks. perm.
+ rewrite Ek, !length_app. cbn [length]. lia.
+ rewrite Ek, !okmax_app, !okmax_cons. pose proof (okmax_nonneg kids1). pose proof (okmax_nonneg kids2). pose proof (odep_nonneg vs). pose proof (odep_nonneg kj). lia.
+ right. pose proof (oadd_len_dup (upd es j (with_v e v)) KBS1 KBS2 bsj EK LU) as LD.
split; [rewrite Ek, !length_app; cbn [length]; lia|].
split; [clear - LD BBd; unfold blk in *; lia|]. split; [clear - LD; unfold blk in *; lia|].
split; [apply obj_capA_lh; lia|].
rewrite (lh_blocks_upd_v t tbl size es j e v Hj). exact JX.
Qed.

Lemma oadd_dupA :
forall (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : config) (A2 : ASA A4L HIx) (errc : word) (svs : list slotv)
(j : nat) (e : lent),
HEAPAx A2 (OBS ++ VBS ++ LB) LM FRS B0 mc mdc ->
rw_cells asegs mc p OHDR ->
lh_open asegs A4F mc t tbl size es svs -> nth_error es j = Some e ->
okids asegs A4F mc kids (map kv es) KBS -> opt_pbuf asegs mc PBS pb -> jopt asegs A4F vs mc VBS v -> lh_globA mc ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
stk asegs mc lo (bv_unsigned sp + -64) ->
oadd_frameA mc ->
model_vm_only (cfg_model md0) (cfg_model mdc) -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T mdc
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 v) (Z_to_bv 64 (p + 40)) a0 (Z_to_bv 64 (ent_addr tbl (le_ix e))) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 k) x19 (Z_to_bv 64 p) (Z_to_bv 64 (p / 8 + 5 + SB0)) (Z_to_bv 64 SB0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x9bf04) fc2 None mc (seg_rom asegs)).
Proof.
intros until e. intros HP HDR OPEN Hj KIDS OPB JOB G ERR ST FR VMa HPRa FSa FRMa.
pose proof FR as FR0. unfold Qkxa.oadd_frameA in FR. pose proof HDR as HDR0. unfold Qkxa.OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG.
destruct (oadd_factsL _ _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold Qkxa.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvL _ _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold Qkxa.OBS; perm) JOB) as (Hpv & V0 & V1).

destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & LINK & _ & Hsz & _ & Hlen). destruct LINK as (_ & _ & _ & LK4).
destruct (LK4 e (nth_error_In _ _ Hj)) as (_ & _ & _ & Hve).
remember (ent_addr tbl (le_ix e)) as EA eqn:HEA.
assert (EAR : tbl <= EA /\ EA + 40 <= tbl + 40 * size) by (subst EA; unfold ent_addr; split; [lia | nia]).
assert (TB8 : tbl mod 8 = 0) by (clear - Hbal; Z.div_mod_to_equations; lia).
assert (EA8 : EA mod 8 = 0) by (subst EA; unfold ent_addr; clear - TB8; Z.div_mod_to_equations; lia).
assert (Hjkv : nth_error (map kv es) j = Some (le_k e, le_v e)) by (rewrite nth_error_map, Hj; reflexivity).
destruct (okids_nth asegs A4F _ _ _ _ _ _ _ KIDS Hjkv) as (kj & bsj & Hkj & Hbsj & JO).
destruct (nth_error_split3 _ es j e Hj) as [Ees Lpre]. set (pre := firstn j es) in *. set (post := skipn (S j) es) in *.
destruct (nth_error_split3 _ kids j kj Hkj) as [Ek Lk1]. set (kids1 := firstn j kids) in *. set (kids2 := skipn (S j) kids) in *.
destruct (nth_error_split3 _ KBS j bsj Hbsj) as [EK Lb1]. set (KBS1 := firstn j KBS) in *. set (KBS2 := skipn (S j) KBS) in *.
clearbody pre post kids1 kids2 KBS1 KBS2.
assert (K12 : okids asegs A4F mc kids1 (map kv pre) KBS1 /\ okids asegs A4F mc kids2 (map kv post) KBS2).
{ rewrite Ek, Ees, EK, map_app in KIDS. cbn [map] in KIDS.
apply okids_app_inv in KIDS as [K1 K2]; [| rewrite length_map; lia | lia].
split; [exact K1 | exact (proj2 K2)]. }
destruct K12 as [K1 K2].
assert (JX : forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj (kids1 ++ vs :: kids2)) (((p, 48) :: lh_blocks t tbl size es ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS) = Some (w', []) /\ w' <= w + wv).
{ intros w wv Hw Hwv. unfold Qkxa.OBS, lh_blocks in Hw |- *. pose proof KIDS as KIDS'. rewrite Ek, EK in Hw, KIDS'.
exact (obj_set_jtx asegs A4F mc kids1 kj kids2 (map kv es) KBS1 bsj KBS2 PBS (p, 48) (t, 56) (tbl, 40 * size) (tbl, 40 * size)
(map (fun e0 : lent => (le_k e0, le_kn e0)) es) vs VBS w wv KIDS' ltac:(lia) ltac:(rewrite length_map, <- Ek; exact LK1) Hw Hwv). }
pose proof (oadd_len_bsj KBS1 KBS2 bsj EK) as LBSJ.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [] mc) as MU.
assert (INtbl : In (tbl, 40 * size) (OBS ++ VBS ++ LB)) by (unfold Qkxa.OBS, lh_blocks; cbn; right; right; left; reflexivity).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP INtbl TB8 ltac:(lia)) as SHe. rewrite <- HEA in SHe. a4l.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash KIDS. stash JO.
reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. sh_norm. rewrite (div8_add EA 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false.
step.
step.
destruct kj as [sj|].
-
unstash JO. destruct JO as [Hvo J].
if_falsex. step.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G.
set (LBput := (p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)).
assert (HPp : HEAPAx A2 (bsj ++ LBput) LM FRS B0 mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP| | apply Permutation_refl | apply Permutation_refl]. unfold Qkxa.OBS, LBput. rewrite EK, concat_mid. unfold lh_blocks. perm. }
pose proof PUT as PUT'. unfold put_stmt_A, put_stmtA in PUT'.
evt_done5.
eapply PUT' with (s := Some sj) (BS := bsj) (p := le_v e) (rc := 1) (LB := LBput) (lo := lo) (errv := errc);
a4l_goal; rewrite ?unsigned_lit by lia;
first [ exact HPp | cbn [put_pre]; split; [exact Hvo | split; [lia | exact J]] | exact ST | exact ERR | reflexivity
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | unfold put_stk_A; lia
| unfold put_costA; rewrite Z.eqb_refl; lia | lia | idtac ].
clear PUT'.
intros ms5 md5 A5 (mP & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & OUT5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST5, HPR5 by lia.
destruct OUT5 as [[_ HP5] | (s'' & _ & Hrc & _)]; [| lia].
assert (AG5 : agree_on asegs LBput mc mP).
{ eapply (agree_of_heap_pres asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_pres_weaken; [exact HPR5 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb]. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR0; [| left; cbn; lia].
apply (rw_cells_agree asegs _ _ _ _ _ HDR0) in AG5 as HDR5; [| exists p, 48; split; [left; reflexivity | cbn; lia]].
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN AG5 ltac:(unfold LBput, lh_blocks; intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|[Hb|Hb]]; [tauto|tauto|]; right; right; right; apply in_or_app; left; exact Hb)) as OPEN5.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K1 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K15.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K2 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K25.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB5.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB5.
pose proof (lh_globA_client _ _ _ _ HPR5 G) as G5.
assert (HPRb : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mP).
{ eapply heap_presx_trans; [exact HPRa|]. apply heap_pres_presx.
eapply heap_pres_weaken; [exact HPR5 | lia |].
unfold LBput. intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; right; do 5 (apply in_or_app; right); exact Hb | right; exact Hb]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs hla_base A4L A4H] in MI5.
clear MU WM MI SLOT HDR OPEN K1 K2 OPB JOB G ST HP HPp AG5 ERR SHe.
pose proof (wmono_refl asegs mP) as WM. pose proof (munch_refl [] mP) as MU.
reenterA asegs A4L HIx asegs_wx HP5.
replace (Z_to_bv 64 (EA / 8 + 2147450882)) with (Z_to_bv 64 (EA / 8 + 2 + SB0)) by (f_equal; lia). subst EA.
evt_done5.
eapply (oadd_setvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 mP md5 A5 B5 errc svs j e kids1 kids2 (Some sj) KBS1 KBS2 bsj pre post);
first [exact HP5 | exact HDR5 | exact OPEN5 | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K15 | exact K25 | exact OPB5 | exact JOB5 | exact G5
| exact ERR5 | exact ST5 | exact FR0 | exact HPRb | lia
| eapply model_vm_only_trans; [exact VMa | exact VM5]
| eapply fsaved_trans; [exact FSa | exact FS5]
| intros Hf; apply FRM5; apply FRMa; exact Hf
| exact JX
| unfold put_costA in BB5; rewrite Z.eqb_refl in BB5; lia ].
-
unstash JO. destruct JO as [Hvo Ebsj]. rewrite Hvo. if_true.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G.
replace (Z_to_bv 64 (EA / 8 + 2147450882)) with (Z_to_bv 64 (EA / 8 + 2 + SB0)) by (f_equal; lia). subst EA.
evt_done5.
eapply (oadd_setvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mc mdc A2 B0 errc svs j e kids1 kids2 None KBS1 KBS2 bsj pre post);
first [exact HDR0 | exact OPEN | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K1 | exact K2 | exact OPB | exact JOB | exact G
| exact ERR | exact ST | exact FR0 | exact HPRa | exact VMa | exact FSa | exact FRMa | exact JX | rewrite Ebsj; cbn [length]; lia | lia | idtac ].
eapply (heapA_perm A4L HIx); [exact HP| | apply Permutation_refl | apply Permutation_refl]. unfold Qkxa.OBS. rewrite EK, Ebsj, concat_mid. unfold lh_blocks. perm.
Qed.
End AJoObjAdd2.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3jZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmd7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg1M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg1M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoif.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qm5W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qm5W.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnPO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnPO.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoObjAdd2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.
Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB VBS PBS LM : list blk) (FRS : list frame) (B0 : bud) (KBS : list (list blk)).
Variables (lo p v k kn pb t tbl size : Z) (es : list lent) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - (80 + 96 + 4096 + 144 + HD).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis LK1 : length es = length kids.
Hypothesis LK2 : length KBS = length kids.
Hypothesis BR0 : 512 * (3 + Z.of_nat (length es) + Z.of_nat (length (concat KBS)) + Z.of_nat (length PBS)) <= bB B0.
Hypothesis BD0 : 0 <= bD B0.
Notation OBS := (OBS PBS KBS p t tbl size es).
Notation OHDR := (OHDR pb t).
Notation oadd_frameA := (oadd_frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7).
Notation oadd_factsL := (oadd_factsX HIx LM FRS p t tbl size es).
Notation oadd_pvL := (oadd_pvX HIx VBS LM FRS p v vs).
Notation SB0 := 2147450880.
Hypothesis Kont : forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_framexA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
lh_globA m' -> bD B0 <= bD B' ->
((r = 0 /\ exists OBS' kids', jval asegs A4F (Sobj kids') m' OBS' p 1 /\ HEAPAx A' (OBS' ++ LB) LM FRS B' m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)
/\ ( ( Z.of_nat (length kids') = Z.of_nat (length kids) + 1
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B'
/\ Z.of_nat (length OBS') = Z.of_nat (length OBS) + Z.of_nat (length VBS) + 1
/\ obj_grownA size (Z.of_nat (length kids)) (obj_capA OBS')
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sobj kids') OBS' = Some (w + (key_w (Z.of_nat (length ks) + 1) + wv), [])))
\/ ( Z.of_nat (length kids') = Z.of_nat (length kids)
/\ bB B0 - 512 * (Z.of_nat (length OBS) + Z.of_nat (length VBS) - Z.of_nat (length OBS')) <= bB B'
/\ Z.of_nat (length OBS') <= Z.of_nat (length OBS) + Z.of_nat (length VBS)
/\ obj_capA OBS' = size
/\ (forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj kids') OBS' = Some (w', []) /\ w' <= w + wv)))) \/
(r = 2^64 - 1 /\ exists REM, jval asegs A4F (Sobj kids) m' OBS p 1 /\ jopt asegs A4F vs m' VBS v
/\ HEAPAx A' (OBS ++ VBS ++ REM ++ LB) LM FRS B' m' md'
/\ bB B0 - oadd_costB (Z.of_nat (length ks)) size (Z.of_nat (length kids)) <= bB B')) ->
AJ5 A4L HIx A' T md' ms'.

Lemma oadd_len_dup : forall es2 (KBS1 KBS2 : list (list blk)) (bsj : list blk),
KBS = KBS1 ++ bsj :: KBS2 -> length es2 = length es ->
Z.of_nat (length (((p, 48) :: lh_blocks t tbl size es2 ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS)) + Z.of_nat (length bsj)
= Z.of_nat (length OBS) + Z.of_nat (length VBS).
Proof.
clear. intros es2 KBS1 KBS2 bsj EK LEN. unfold Qm5W.OBS, lh_blocks. rewrite EK. cbn [app length].
rewrite !length_app. cbn [length]. rewrite !length_map, !concat_app. cbn [concat]. rewrite !length_app, LEN. lia.
Qed.
Lemma oadd_len_bsj : forall (KBS1 KBS2 : list (list blk)) (bsj : list blk),
KBS = KBS1 ++ bsj :: KBS2 -> (length bsj <= length (concat KBS))%nat.
Proof. clear. intros KBS1 KBS2 bsj ->. rewrite concat_app. cbn [concat]. rewrite !length_app. lia. Qed.

Lemma oadd_setvA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 t3 t4 t5 t6 : word) (F3 : bvmap 5 word) (fc3 : bv 32) (junk0 : list byte)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (errc : word) (svs : list slotv)
(j : nat) (e : lent) (kids1 kids2 : list (option jshape)) (kj : option jshape) (KBS1 KBS2 : list (list blk)) (bsj : list blk)
(pre post : list lent),
HEAPAx A ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e => (le_k e, le_kn e)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)) LM FRS B m md ->
rw_cells asegs m p OHDR ->
lh_open asegs A4F m t tbl size es svs -> nth_error es j = Some e -> es = pre ++ e :: post -> length pre = j ->
kids = kids1 ++ kj :: kids2 -> KBS = KBS1 ++ bsj :: KBS2 -> length kids1 = j -> length KBS1 = j ->
okids asegs A4F m kids1 (map kv pre) KBS1 -> okids asegs A4F m kids2 (map kv post) KBS2 ->
opt_pbuf asegs m PBS pb -> jopt asegs A4F vs m VBS v -> lh_globA m ->
rw_cells asegs m A_ERRNO [C4 errc] ->
stk asegs m lo (bv_unsigned sp + -80) ->
oadd_frameA junk0 m ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
fsaved F F3 -> (frm0 fc -> frm0 fc3) ->
bB B0 - 512 * Z.of_nat (length bsj) <= bB B -> bD B0 <= bD B ->
(forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj (kids1 ++ vs :: kids2)) (((p, 48) :: lh_blocks t tbl size es ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS) = Some (w', []) /\ w' <= w + wv) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 v) (Z_to_bv 64 (ent_addr tbl (le_ix e) + 16)) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 (Z_to_bv 64 (ent_addr tbl (le_ix e) / 8 + 2 + SB0)) s8 s9 s10 s11 t3 t4 t5 t6)
F3 (Z_to_bv 64 0x9d74c) fc3 None m (seg_rom asegs)).
Proof.
intros until post. intros HP HDR OPEN Hj Ees Lpre Ek EK Lk1 Lb1 K1 K2 OPB JOB G ERR ST FR VMa HPRa FSa FRMa BBd BDd JX.
unfold Qm5W.oadd_frameA in FR. unfold Qm5W.OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG.
destruct (oadd_factsL _ _ _ _ _ (concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB) HP ltac:(unfold lh_blocks; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvL _ _ _ _ _ ((t, 56) :: (tbl, 40 * size) :: (map (fun e => (le_k e, le_kn e)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ LB)) HP ltac:(perm) JOB) as (Hpv & V0 & V1).
destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & Hsz & _ & Hlen).
remember (ent_addr tbl (le_ix e)) as EA eqn:HEA.
assert (EAR : tbl <= EA /\ EA + 40 <= tbl + 40 * size) by (subst EA; unfold ent_addr; split; [lia | nia]).
assert (TB8 : tbl mod 8 = 0) by (clear - Hbal; Z.div_mod_to_equations; lia).
assert (EA8 : EA mod 8 = 0) by (subst EA; unfold ent_addr; clear - TB8; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(EA + 16, EA + 24)] m) as MU.
assert (INtbl : In (tbl, 40 * size) ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)) by (right; right; left; reflexivity).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP INtbl TB8 ltac:(lia)) as SHe. rewrite <- HEA in SHe. a4l.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash Hpimg. stash Htimg.

pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_r in ND. cbn [map blk_addr fst] in ND.
assert (NTB : ~ In tbl (map blk_addr (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB))).
{ inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. inversion Hnd' as [|x'' l'' Hni'' Hnd'']; subst. exact Hni''. }
assert (NOTIN : ~ In (tbl, 40 * size) LB).
{ intros Hin. apply NTB. rewrite !map_app. repeat (apply in_or_app; right). exact (in_map blk_addr _ _ Hin). }
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite ?zxb_zero. step. if_false.
stepz.
step. do 9 step. step.
release_frame FR ST (bv_unsigned sp). step.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G. unstash KF. unstash SEP. unstash Hpimg. unstash Htimg.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
assert (AGo : agree_on asegs (others tbl ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB))) m mS).
{ eapply (agree_others_of_munch asegs); [ right; right; left; reflexivity | | | exact MU | exact WM | ].
- intros a1' k1 a2' k2 H1 H2 NE. exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact H1) ltac:(apply in_or_app; left; exact H2) NE).
- intros a1' k1 H1. exact (proj1 (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact H1))).
- apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
assert (INC : forall X, incl X (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB) ->
incl X (others tbl ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)))).
{ intros X HX b Hb. apply in_others_iff. split; [right; right; right; exact (HX _ Hb)|]. cbn. intros E. apply NTB. rewrite <- E. exact (in_map blk_addr _ _ (HX _ Hb)). }
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AGo ltac:(apply INC; intros b Hb; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB'.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AGo ltac:(apply INC; intros b Hb; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB'.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K1 AGo ltac:(apply INC; intros b Hb; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K1'.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K2 AGo ltac:(apply INC; intros b Hb; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K2'.
assert (OPEN' : lh_open asegs A4F mS t tbl size (upd es j (with_v e v)) (upd svs (le_ix e) (sv_with_v sl v))).
{ unfold lh_open. eapply (lh_open_set_val asegs A4F); [exact OPEN | exact Hj | exact Hsl | lia | exact MU | exact WM | | exact SEP | | ].
- apply Forall_cons; [subst EA; cbn [fst snd]; lia | apply Forall_nil].
- intros x Hx. destruct (KF x Hx) as (_ & _ & _ & _ & K5). exact K5.
- subst EA. exact SLOT. }
evt_done5. apply (Kont _ md mS 0 A B).
- unfold jo_post_framexA. a4l_goal.
split; [apply ret_statew_intro; [exact FSa | exact FRMa] |].
split; [exact VMa|].
split; [exact ST|].
split; [| exists errc; exact ERR].
eapply heap_presx_trans; [exact HPRa|].
eapply (heap_presx_of_munch A4H); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
+ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; right; do 5 (apply in_or_app; right); exact Hb | right; exact Hb].
+ apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists tbl, (40 * size).
split; [apply in_or_app; left; in_prefix | split; [| lia]].
apply not_in_app3; [| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ tbl (40 * size) HP ltac:(apply in_or_app; left; exact INtbl))].
intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exact (NOTIN Hin)|].
clear - HP INtbl Hin. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND.
revert ND. generalize (in_map blk_addr _ _ INtbl). generalize (in_map blk_addr _ _ Hin). cbn [blk_addr fst].
generalize (map blk_addr LM). generalize (map blk_addr ((p, 48) :: (t, 56) :: (tbl, 40 * size) :: map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)).
intros l1 l2 H2 H1 ND. induction l1 as [|y l1 IH]; [exact H1|]. cbn in ND. inversion ND; subst.
destruct H1 as [-> | H1]; [apply H3; apply in_or_app; right; exact H2 | exact (IH H1 H4)].
- eapply lh_globA_frame; [exact G | exact MU | exact WM |]. unfold GHASHA, GSEEDA. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
- exact BDd.
- left. split; [reflexivity|].
exists (((p, 48) :: lh_blocks t tbl size (upd es j (with_v e v)) ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS), (kids1 ++ vs :: kids2).
assert (LU : length (upd es j (with_v e v)) = length es) by (apply upd_length).
pose proof LK1 as LK1'. rewrite Ek, length_app in LK1'. cbn [length] in LK1'.
pose proof LK2 as LK2'. rewrite Ek, EK, !length_app in LK2'. cbn [length] in LK2'.
split; [| split; [| split; [| split]]].
+ eapply (sobj_close asegs A4F) with (kvs := map kv (upd es j (with_v e v))) (KBS := KBS1 ++ VBS :: KBS2);
[ reflexivity | exact OPB' | unfold jhdr_cells; cbn [app fn_obj_to_json_string A4F]; exact HDR
| exists tbl, size, (upd es j (with_v e v)), (upd svs (le_ix e) (sv_with_v sl v)); split; [reflexivity | split; [reflexivity | exact OPEN']]
| rewrite length_map, upd_length, !length_app; cbn [length]; lia
| rewrite !length_app; cbn [length]; lia
| ].
rewrite (kv_upd_v es j e v pre post Hj Ees Lpre).
apply okids_app; [exact K1'|]. apply (okids_app asegs A4F mS [vs] [(le_k e, v)] [VBS] kids2); [apply okids_one; exact JOB' | exact K2'].
+ rewrite (lh_blocks_upd_v t tbl size es j e v Hj). rewrite concat_mid.
eapply (heapA_perm A4L HIx); [ | | apply Permutation_refl | apply Permutation_refl].
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU). solve_frameW_withA HP. }
unfold lh_blocks. perm.
+ rewrite Ek, !length_app. cbn [length]. lia.
+ rewrite Ek, !okmax_app, !okmax_cons. pose proof (okmax_nonneg kids1). pose proof (okmax_nonneg kids2). pose proof (odep_nonneg vs). pose proof (odep_nonneg kj). lia.
+ right. pose proof (oadd_len_dup (upd es j (with_v e v)) KBS1 KBS2 bsj EK LU) as LD.
split; [rewrite Ek, !length_app; cbn [length]; lia|].
split; [clear - LD BBd; unfold blk in *; lia|]. split; [clear - LD; unfold blk in *; lia|].
split; [apply obj_capA_lh; lia|].
rewrite (lh_blocks_upd_v t tbl size es j e v Hj). exact JX.
Qed.

Lemma oadd_dupA :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (junk0 : list byte)
(mc : word -> option byte) (mdc : config) (A2 : ASA A4L HIx) (errc : word) (svs : list slotv)
(j : nat) (e : lent),
HEAPAx A2 (OBS ++ VBS ++ LB) LM FRS B0 mc mdc ->
rw_cells asegs mc p OHDR ->
lh_open asegs A4F mc t tbl size es svs -> nth_error es j = Some e ->
okids asegs A4F mc kids (map kv es) KBS -> opt_pbuf asegs mc PBS pb -> jopt asegs A4F vs mc VBS v -> lh_globA mc ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
stk asegs mc lo (bv_unsigned sp + -80) ->
oadd_frameA junk0 mc ->
model_vm_only (cfg_model md0) (cfg_model mdc) -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc ->
fsaved F F2 -> (frm0 fc -> frm0 fc2) ->
AJ5 A4L HIx A2 T mdc
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 v) (Z_to_bv 64 0) (Z_to_bv 64 (ent_addr tbl (le_ix e))) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 k) (Z_to_bv 64 (p + 40)) (Z_to_bv 64 p) x21 (Z_to_bv 64 (p / 8 + 5 + SB0)) (Z_to_bv 64 SB0) s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x9d724) fc2 None mc (seg_rom asegs)).
Proof.
intros until e. intros HP HDR OPEN Hj KIDS OPB JOB G ERR ST FR VMa HPRa FSa FRMa.
pose proof FR as FR0. unfold Qm5W.oadd_frameA in FR. pose proof HDR as HDR0. unfold Qm5W.OHDR in HDR. cbn [fn_obj_to_json_string A4F] in HDR.
a4l. word_range sp SPR. pose proof (hiA_top_le A4L HIx) as HTL. pose proof alloc_ceiling_ge as ACG.
destruct (oadd_factsL _ _ _ _ _ (concat KBS ++ PBS ++ VBS ++ LB) HP ltac:(unfold Qm5W.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pvL _ _ _ _ _ (lh_blocks t tbl size es ++ concat KBS ++ PBS ++ LB) HP ltac:(unfold Qm5W.OBS; perm) JOB) as (Hpv & V0 & V1).

destruct (lh_open_slot asegs A4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & LINK & _ & Hsz & _ & Hlen). destruct LINK as (_ & _ & _ & LK4).
destruct (LK4 e (nth_error_In _ _ Hj)) as (_ & _ & _ & Hve).
remember (ent_addr tbl (le_ix e)) as EA eqn:HEA.
assert (EAR : tbl <= EA /\ EA + 40 <= tbl + 40 * size) by (subst EA; unfold ent_addr; split; [lia | nia]).
assert (TB8 : tbl mod 8 = 0) by (clear - Hbal; Z.div_mod_to_equations; lia).
assert (EA8 : EA mod 8 = 0) by (subst EA; unfold ent_addr; clear - TB8; Z.div_mod_to_equations; lia).
assert (Hjkv : nth_error (map kv es) j = Some (le_k e, le_v e)) by (rewrite nth_error_map, Hj; reflexivity).
destruct (okids_nth asegs A4F _ _ _ _ _ _ _ KIDS Hjkv) as (kj & bsj & Hkj & Hbsj & JO).
destruct (nth_error_split3 _ es j e Hj) as [Ees Lpre]. set (pre := firstn j es) in *. set (post := skipn (S j) es) in *.
destruct (nth_error_split3 _ kids j kj Hkj) as [Ek Lk1]. set (kids1 := firstn j kids) in *. set (kids2 := skipn (S j) kids) in *.
destruct (nth_error_split3 _ KBS j bsj Hbsj) as [EK Lb1]. set (KBS1 := firstn j KBS) in *. set (KBS2 := skipn (S j) KBS) in *.
clearbody pre post kids1 kids2 KBS1 KBS2.
assert (K12 : okids asegs A4F mc kids1 (map kv pre) KBS1 /\ okids asegs A4F mc kids2 (map kv post) KBS2).
{ rewrite Ek, Ees, EK, map_app in KIDS. cbn [map] in KIDS.
apply okids_app_inv in KIDS as [K1 K2]; [| rewrite length_map; lia | lia].
split; [exact K1 | exact (proj2 K2)]. }
destruct K12 as [K1 K2].
assert (JX : forall w wv, jtx (Sobj kids) OBS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
exists w', jtx (Sobj (kids1 ++ vs :: kids2)) (((p, 48) :: lh_blocks t tbl size es ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBS) = Some (w', []) /\ w' <= w + wv).
{ intros w wv Hw Hwv. unfold Qm5W.OBS, lh_blocks in Hw |- *. pose proof KIDS as KIDS'. rewrite Ek, EK in Hw, KIDS'.
exact (obj_set_jtx asegs A4F mc kids1 kj kids2 (map kv es) KBS1 bsj KBS2 PBS (p, 48) (t, 56) (tbl, 40 * size) (tbl, 40 * size)
(map (fun e0 : lent => (le_k e0, le_kn e0)) es) vs VBS w wv KIDS' ltac:(lia) ltac:(rewrite length_map, <- Ek; exact LK1) Hw Hwv). }
pose proof (oadd_len_bsj KBS1 KBS2 bsj EK) as LBSJ.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [] mc) as MU.
assert (INtbl : In (tbl, 40 * size) (OBS ++ VBS ++ LB)) by (unfold Qm5W.OBS, lh_blocks; cbn; right; right; left; reflexivity).
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (le_ix e) HP INtbl TB8 ltac:(lia)) as SHe. rewrite <- HEA in SHe. a4l.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash KIDS. stash JO.
reenterA asegs A4L HIx asegs_wx HP.
step. rewrite (unsigned_lit EA) by lia. rewrite (ub_land7 EA EA8). step. if_false.
step.
step. step. sh_norm. rewrite (div8_add EA 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false.
step.
step.
destruct kj as [sj|].
-
unstash JO. destruct JO as [Hvo J].
if_falsex. step.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G.
set (LBput := (p, 48) :: (t, 56) :: (tbl, 40 * size) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) es ++ concat KBS1 ++ concat KBS2 ++ PBS ++ VBS ++ LB)).
assert (HPp : HEAPAx A2 (bsj ++ LBput) LM FRS B0 mc mdc).
{ eapply (heapA_perm A4L HIx); [exact HP| | apply Permutation_refl | apply Permutation_refl]. unfold Qm5W.OBS, LBput. rewrite EK, concat_mid. unfold lh_blocks. perm. }
pose proof PUT as PUT'. unfold put_stmt_A, put_stmtA in PUT'.
evt_done5.
eapply PUT' with (s := Some sj) (BS := bsj) (p := le_v e) (rc := 1) (LB := LBput) (lo := lo) (errv := errc);
a4l_goal; rewrite ?unsigned_lit by lia;
first [ exact HPp | cbn [put_pre]; split; [exact Hvo | split; [lia | exact J]] | exact ST | exact ERR | reflexivity
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | unfold put_stk_A; lia
| unfold put_costA; rewrite Z.eqb_refl; lia | lia | idtac ].
clear PUT'.
intros ms5 md5 A5 (mP & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & OUT5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST5, HPR5 by lia.
destruct OUT5 as [[_ HP5] | (s'' & _ & Hrc & _)]; [| lia].
assert (AG5 : agree_on asegs LBput mc mP).
{ eapply (agree_of_heap_pres asegs A4H); [| reflexivity | apply incl_refl].
eapply heap_pres_weaken; [exact HPR5 | apply Z.le_refl | intros b Hb; apply in_or_app; left; exact Hb]. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR0; [| left; cbn; lia].
apply (rw_cells_agree asegs _ _ _ _ _ HDR0) in AG5 as HDR5; [| exists p, 48; split; [left; reflexivity | cbn; lia]].
pose proof (lh_open_agree asegs A4F _ _ _ _ _ _ _ _ OPEN AG5 ltac:(unfold LBput, lh_blocks; intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|[Hb|Hb]]; [tauto|tauto|]; right; right; right; apply in_or_app; left; exact Hb)) as OPEN5.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K1 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K15.
pose proof (okids_agree asegs A4F _ _ _ _ _ _ K2 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K25.
pose proof (opt_pbuf_agree asegs _ _ _ _ _ OPB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB5.
pose proof (jopt_agree asegs A4F _ _ _ _ _ _ JOB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB5.
pose proof (lh_globA_client _ _ _ _ HPR5 G) as G5.
assert (HPRb : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mP).
{ eapply heap_presx_trans; [exact HPRa|]. apply heap_pres_presx.
eapply heap_pres_weaken; [exact HPR5 | lia |].
unfold LBput. intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; right; right; do 5 (apply in_or_app; right); exact Hb | right; exact Hb]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs hla_base A4L A4H] in MI5.
clear MU WM MI SLOT HDR OPEN K1 K2 OPB JOB G ST HP HPp AG5 ERR SHe.
pose proof (wmono_refl asegs mP) as WM. pose proof (munch_refl [] mP) as MU.
reenterA asegs A4L HIx asegs_wx HP5.
replace (Z_to_bv 64 (EA / 8 + 2147450882)) with (Z_to_bv 64 (EA / 8 + 2 + SB0)) by (f_equal; lia). subst EA.
evt_done5.
eapply (oadd_setvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 junk0 mP md5 A5 B5 errc svs j e kids1 kids2 (Some sj) KBS1 KBS2 bsj pre post);
first [exact HP5 | exact HDR5 | exact OPEN5 | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K15 | exact K25 | exact OPB5 | exact JOB5 | exact G5
| exact ERR5 | exact ST5 | exact FR0 | exact HPRb | lia
| eapply model_vm_only_trans; [exact VMa | exact VM5]
| eapply fsaved_trans; [exact FSa | exact FS5]
| intros Hf; apply FRM5; apply FRMa; exact Hf
| exact JX
| unfold put_costA in BB5; rewrite Z.eqb_refl in BB5; lia ].
-
unstash JO. destruct JO as [Hvo Ebsj]. rewrite Hvo. if_true.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G.
replace (Z_to_bv 64 (EA / 8 + 2147450882)) with (Z_to_bv 64 (EA / 8 + 2 + SB0)) by (f_equal; lia). subst EA.
evt_done5.
eapply (oadd_setvA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 junk0 mc mdc A2 B0 errc svs j e kids1 kids2 None KBS1 KBS2 bsj pre post);
first [exact HDR0 | exact OPEN | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K1 | exact K2 | exact OPB | exact JOB | exact G
| exact ERR | exact ST | exact FR0 | exact HPRa | exact VMa | exact FSa | exact FRMa | exact JX | rewrite Ebsj; cbn [length]; lia | lia | idtac ].
eapply (heapA_perm A4L HIx); [exact HP| | apply Permutation_refl | apply Permutation_refl]. unfold Qm5W.OBS. rewrite EK, Ebsj, concat_mid. unfold lh_blocks. perm.
Qed.
End AJoObjAdd2.
End RC__1.
