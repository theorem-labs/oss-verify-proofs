(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QWxq_c1 QEQM QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ QC8c Qsw7 QJjn QKQo QPZI Qu4M Q8tj QKdB QRUw QSL3 QhI1 Q22i Q3jZ Qmd7 QtfO QLAQ QgoP QfOM Qvbw QYIF Qg1M QDc2 QrIB Qdgq_c1 Qzop Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg QWxq_c1.Mq0.
Import QEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import QC8c.Mq0.
Import Qsw7 QJjn QKQo.
Import QPZI.Mq0 Qu4M.Mq0 QPZI.Mq4.
Import Q8tj QKdB QRUw.Mq2.
Import QSL3.
Import QhI1 Q22i Q3jZ Qmd7 QtfO QLAQ.
Import QgoP.
Import QfOM.
Import Qvbw QYIF.
Import Qg1M QDc2.
Import QrIB.Mq0 Qdgq_c1.Mq0 Qzop.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section DcObjAdd.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis HASH : lh_char_hash_stmt HIx model_vm_only 8320.
Definition RESIZE3 : lh_resize_stmt HIx model_vm_only (64 + 8320) :=
lh_resize_cps HIx lf_test_spec_proof model_vm_only model_vm_only_refl model_vm_only_trans (fun a b H => H) 8320 ltac:(lia) HASH.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (T : TSet).
Variable kids : list (option jshape).
Let r : jroot := JRtree (Sobj kids).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stk (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Notation dc_inv := (dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 md0 LB BS lo D).
Notation dc_cell := (dc_cell sp).
Ltac dc_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact FRM0 | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact PUTX | exact PUT | clia ].

Variables (q pbq tq tblq sizeq : Z) (esq : list lent) (KBSq : list (list blk)) (PBSq : list blk) (kidsq : list (option jshape)).
Variables (jso : Z) (vs : option jshape) (VBS : list blk) (k kn : Z) (ks : list byte) (REM : list blk) (ea : Z) (jk : list byte).
Variable SV : (word -> option byte) -> Prop.
Hypothesis SVAG : forall m m', SV m -> agree_on rsegs BS m m' -> SV m'.
Hypothesis INK : In (k, kn) BS.
Hypothesis KN : kn <= 2^31.
Hypothesis LQ1 : length esq = length kidsq.
Hypothesis LQ2 : length KBSq = length kidsq.
Hypothesis Hq : q <> 0.
Hypothesis OKQ : okmax kidsq <= okmax kids.
Hypothesis ODEP : odep vs <= okmax kids.
Notation LR := (BS ++ REM ++ LB).
Notation OBSq := (OBS PBSq KBSq q tq tblq sizeq esq).
Notation OHDRq := (OHDR pbq tq).

Hypothesis ONEXT :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x26 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : Model) (A2 : AS S4L HIx) (kids2 : list (option jshape)) (CBS2 REM2 : list blk) (cj : list byte) (e2 : word),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs m2 (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell m2 cj -> rw_cells rsegs m2 (0x75e70 - 164) [C4 e2] ->
HEAPx A2 (BS ++ CBS2 ++ REM2 ++ LB) m2 md2 -> SV m2 ->
rw_cells rsegs m2 D [C8 (wz q)] -> jval rsegs S4F (Sobj kids2) m2 CBS2 q 1 -> okmax kids2 <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) x21 x22 x23 x24 (wz ea) x26 s11 t3 t4 t5 t6)
F2 (wz 0x259a0) fc2 None m2 (seg_rom rsegs)) md2) T.

#[using="PUT PUTX fc kids r LO LOS SPA HT SPD DAL NN JR0 Kont esq KBSq kidsq LQ1 LQ2 Hq ODEP"] Lemma dc_failc :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (CBS REMc : list blk) (sq : jshape) (errc : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
rw_cells rsegs mc (bv_unsigned sp + -104) [C8 (wz jso)] -> rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] ->
rw_cells rsegs mc (0x75e70 - 164) [C4 errc] ->
HEAPx A (VBS ++ BS ++ CBS ++ REMc ++ LB) mc mdc ->
rw_cells rsegs mc D [C8 (wz q)] -> jval rsegs S4F sq mc CBS q 1 -> jopt rsegs S4F vs mc VBS jso ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
F1 (wz 0x25a50) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV FS FRM1 CELL FRJ ERR HP DC JQ JOB. pose proof INV as (VM & PRES & ST & FR & G).
pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu. rewrite sdepth_Sobj in LOSu.
pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash JQ. stash JOB. stash G.
apply rz_evt; [exact MOK|].
step. step. step.
unstash JQ. unstash JOB. unstash G.
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := sq) (CBS := CBS) (CBSc := VBS) (REM := REMc); dc_hyps.
all: first [ exact FRJ | exact ERR | exact DC | exact Hq | exact FS | exact FRM1 | exact HP | exact INV | exact JQ | idtac ].
- unfold Qzop.dc_cell. apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL; [exact CELL | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
- destruct vs as [s''|]; cbn [jopt] in JOB.
+ right; left. destruct JOB as [Hj J]. split; [exact Hj | exists s''; exact J].
+ left. exact JOB.
Qed.

#[using="kids r LO LOS SPD DAL SVAG LQ1 LQ2 Hq OKQ ODEP ONEXT"] Lemma dc_osetv :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x26 t3 t4 t5 t6 : word) (F3 : bvmap 5 word) (fc3 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (errc : word) (cj : list byte) (svs : list slotv)
(j : nat) (e : lent) (kids1 kids2 : list (option jshape)) (kj : option jshape) (KBS1 KBS2 : list (list blk)) (bsj : list blk)
(pre post : list lent),
HEAPx A ((q, 48) :: (tq, 56) :: (tblq, 40 * sizeq) :: (map (fun e => (le_k e, le_kn e)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR)) m md ->
rw_cells rsegs m q OHDRq ->
lh_open rsegs S4F m tq tblq sizeq esq svs -> nth_error esq j = Some e -> esq = pre ++ e :: post -> length pre = j ->
kidsq = kids1 ++ kj :: kids2 -> KBSq = KBS1 ++ bsj :: KBS2 -> length kids1 = j -> length KBS1 = j ->
okids rsegs S4F m kids1 (map kv pre) KBS1 -> okids rsegs S4F m kids2 (map kv post) KBS2 ->
opt_pbuf rsegs m PBSq pbq -> jopt rsegs S4F vs m VBS jso -> SV m ->
rw_cells rsegs m (0x75e70 - 164) [C4 errc] -> rw_cells rsegs m D [C8 (wz q)] ->
dc_inv m md -> fsaved F F3 -> frm0 fc3 ->
rw_cells rsegs m (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell m cj ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) (wz jso) x22 x23 (wz (ent_addr tblq (le_ix e))) (wz ea) x26 s11 t3 t4 t5 t6)
F3 (wz 0x2599c) fc3 None m (seg_rom rsegs)) md) T.
Proof.
intros until post. intros HP HDR OPEN Hj Ees Lpre Ek EK Lk1 Lb1 K1 K2 OPB JOB SVm ERR DC INV FSa FRMa FRJ CELL.
pose proof INV as (VMa & PRES & ST & FR & G). unfold Qzop.dc_frame in FR. unfold Qzop.dc_cell in CELL.
unfold QDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu. rewrite sdepth_Sobj in LOSu.
pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
destruct (oadd_facts HIx q tq tblq sizeq esq _ _ _ _ (concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR) HP ltac:(unfold lh_blocks; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS q jso vs _ _ _ _ ((tq, 56) :: (tblq, 40 * sizeq) :: (map (fun e => (le_k e, le_kn e)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ LR)) HP ltac:(perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.
destruct (lh_open_slot rsegs S4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & _ & _ & _ & _ & Hlen).
remember (ent_addr tblq (le_ix e)) as EA eqn:HEA.
assert (EAR : tblq <= EA /\ EA + 40 <= tblq + 40 * sizeq) by (subst EA; unfold ent_addr; split; [(clear; lia) | (clear - Hix Hlen; nia)]).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(EA + 16, EA + 24)] m) as MU.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash Hpimg. stash Htimg. stash SVm.

pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. cbn [map blk_addr fst] in ND.
assert (NTB : ~ In tblq (map blk_addr (map (fun e0 : lent => (le_k e0, le_kn e0)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR))).
{ inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. inversion Hnd' as [|x'' l'' Hni'' Hnd'']; subst. exact Hni''. }
assert (NOTIN : ~ In (tblq, 40 * sizeq) (BS ++ LB)).
{ intros Hin. apply NTB. rewrite !map_app. apply in_app_or in Hin as [Hin|Hin].
- do 5 (apply in_or_app; right). apply in_or_app; left. exact (in_map blk_addr _ _ Hin).
- do 7 (apply in_or_app; right). exact (in_map blk_addr _ _ Hin). }
apply rz_evt; [exact MOK|].
step.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G. unstash KF. unstash SEP. unstash Hpimg. unstash Htimg. unstash SVm.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
assert (AGo : agree_on rsegs (others tblq ((q, 48) :: (tq, 56) :: (tblq, 40 * sizeq) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR))) m mS).
{ eapply (agree_others_of_munch rsegs); [ right; right; left; reflexivity | | | exact MU | exact WM | ].
- intros a1' k1 a2' k2 H1 H2 NE. exact (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP H1 H2 NE).
- intros a1' k1 H1. exact (proj1 (heap_blk S4L HIx _ _ _ _ _ _ HP H1)).
- apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
assert (INC : forall X, incl X (map (fun e0 : lent => (le_k e0, le_kn e0)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR) ->
incl X (others tblq ((q, 48) :: (tq, 56) :: (tblq, 40 * sizeq) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR)))).
{ intros X HX b Hb. apply in_others_iff. split; [right; right; right; exact (HX _ Hb)|]. cbn. intros E. apply NTB. rewrite <- E. exact (in_map blk_addr _ _ (HX _ Hb)). }
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AGo ltac:(apply INC; intros b Hb; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB'.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AGo ltac:(apply INC; intros b Hb; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB'.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K1 AGo ltac:(apply INC; intros b Hb; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K1'.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K2 AGo ltac:(apply INC; intros b Hb; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K2'.
pose proof (SVAG _ _ SVm (agree_on_incl rsegs _ _ _ _ AGo (INC BS ltac:(intros bb Hbb; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hbb)))) as SV'.
assert (OPEN' : lh_open rsegs S4F mS tq tblq sizeq (upd esq j (with_v e jso)) (upd svs (le_ix e) (sv_with_v sl jso))).
{ unfold lh_open. eapply (lh_open_set_val rsegs S4F); [exact OPEN | exact Hj | exact Hsl | lia | exact MU | exact WM | | exact SEP | | ].
- apply Forall_cons; [subst EA; cbn [fst snd]; lia | apply Forall_nil].
- intros x Hx. destruct (KF x Hx) as (_ & _ & _ & _ & K5). exact K5.
- subst EA. exact SLOT. }
assert (HPS : HEAPx A (BS ++ (((q, 48) :: lh_blocks tq tblq sizeq (upd esq j (with_v e jso)) ++ concat (KBS1 ++ VBS :: KBS2)) ++ PBSq) ++ REM ++ LB) mS md).
{ rewrite (lh_blocks_upd_v tq tblq sizeq esq j e jso Hj). rewrite concat_mid.
eapply (heap_perm S4L HIx).
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
- unfold lh_blocks. perm. }
apply evt_RZ_done.
eapply (ONEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mS md A (kids1 ++ vs :: kids2) _ REM cj errc);
[ | exact FSa | exact FRMa | exact FRJ | unfold Qzop.dc_cell; exact CELL | exact ERR | exact HPS | exact SV' | exact DC | | ].
- split; [exact VMa|]. split; [| split; [exact ST | split; [unfold Qzop.dc_frame; exact FR |]]].
+ eapply presxD_trans; [exact PRES|]. eapply presxD_of_munch; [exact MU | exact WM |]. intros b Hb Hc Hd.
eapply (client_outside S4L HIx) with (SP := bv_unsigned sp); [exact HP | | clia | | exact Hb | exact Hc].
* intros bb Hbb. right; right; right. apply in_app_or in Hbb as [Hbb|Hbb]; [do 5 (apply in_or_app; right); apply in_or_app; left; exact Hbb | do 7 (apply in_or_app; right); exact Hbb].
* apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists tblq, (40 * sizeq). split; [in_prefix | split; [exact NOTIN | lia]].
+ eapply jc_glob_P_munch; [exact G | exact MU | exact WM |]. apply Forall_cons; [cbn [fst snd]; (clear - Hbimg EAR; lia) | apply Forall_nil].
- eapply (sobj_close rsegs S4F) with (kvs := map kv (upd esq j (with_v e jso))) (KBS := KBS1 ++ VBS :: KBS2);
[ reflexivity | exact OPB' | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR
| exists tblq, sizeq, (upd esq j (with_v e jso)), (upd svs (le_ix e) (sv_with_v sl jso)); split; [reflexivity | split; [reflexivity | exact OPEN']]
| rewrite length_map, upd_length, !length_app; cbn [length]; subst kidsq; rewrite length_app in LQ1; cbn [length] in LQ1; lia
| rewrite !length_app; cbn [length]; subst kidsq KBSq; rewrite !length_app in LQ2; cbn [length] in LQ2; lia
| ].
rewrite (kv_upd_v esq j e jso pre post Hj Ees Lpre).
apply okids_app; [exact K1'|]. apply (okids_app rsegs S4F mS [vs] [(le_k e, jso)] [VBS] kids2); [apply okids_one; exact JOB' | exact K2'].
- subst kidsq. rewrite !okmax_app, !okmax_cons in OKQ |- *. pose proof (okmax_nonneg kids1). pose proof (okmax_nonneg kids2). pose proof (odep_nonneg vs). pose proof (odep_nonneg kj). lia.
Qed.

#[using="PUT kids r LO LOS SPA HT SPD DAL SVAG LQ1 LQ2 Hq OKQ ODEP ONEXT"] Lemma dc_odup :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : Model) (A2 : AS S4L HIx) (errc : word) (cj : list byte) (svs : list slotv)
(j : nat) (e : lent),
HEAPx A2 (OBSq ++ VBS ++ LR) mc mdc ->
rw_cells rsegs mc q OHDRq ->
lh_open rsegs S4F mc tq tblq sizeq esq svs -> nth_error esq j = Some e ->
okids rsegs S4F mc kidsq (map kv esq) KBSq -> opt_pbuf rsegs mc PBSq pbq -> jopt rsegs S4F vs mc VBS jso -> SV mc ->
rw_cells rsegs mc (0x75e70 - 164) [C4 errc] -> rw_cells rsegs mc D [C8 (wz q)] ->
dc_inv mc mdc -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell mc cj ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D)
(wz (ent_addr tblq (le_ix e))) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) (wz jso) (wz k) x23 (wz (ent_addr tblq (le_ix e))) (wz ea) (wz q) s11 t3 t4 t5 t6)
F2 (wz 0x25a18) fc2 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until e. intros HP HDR OPEN Hj KIDS OPB JOB SVm ERR DC INV FSa FRMa FRJ CELL.
pose proof INV as (VMa & PRES & ST & FR & G). unfold Qzop.dc_frame in FR. unfold Qzop.dc_cell in CELL.
pose proof HDR as HDR0. unfold QDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu. rewrite sdepth_Sobj in LOSu.
pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
destruct (oadd_facts HIx q tq tblq sizeq esq _ _ _ _ (concat KBSq ++ PBSq ++ VBS ++ LR) HP ltac:(unfold QDc2.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS q jso vs _ _ _ _ (lh_blocks tq tblq sizeq esq ++ concat KBSq ++ PBSq ++ LR) HP ltac:(unfold QDc2.OBS; perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.

destruct (lh_open_slot rsegs S4F _ _ _ _ _ _ _ _ _ OPEN Hj) as (sl & Hsl & Hix & SLOT).
pose proof OPEN as (_ & _ & LINK & _ & _ & _ & Hlen). destruct LINK as (_ & _ & _ & LK4).
destruct (LK4 e (nth_error_In _ _ Hj)) as (_ & _ & _ & Hve).
remember (ent_addr tblq (le_ix e)) as EA eqn:HEA.
assert (EAR : tblq <= EA /\ EA + 40 <= tblq + 40 * sizeq) by (subst EA; unfold ent_addr; split; [(clear; lia) | (clear - Hix Hlen; nia)]).
assert (Hjkv : nth_error (map kv esq) j = Some (le_k e, le_v e)) by (rewrite nth_error_map, Hj; reflexivity).
destruct (okids_nth rsegs S4F _ _ _ _ _ _ _ KIDS Hjkv) as (kj & bsj & Hkj & Hbsj & JO).
destruct (nth_error_split3 _ esq j e Hj) as [Ees Lpre]. set (pre := firstn j esq) in *. set (post := skipn (S j) esq) in *.
destruct (nth_error_split3 _ kidsq j kj Hkj) as [Ek Lk1]. set (kids1 := firstn j kidsq) in *. set (kids2 := skipn (S j) kidsq) in *.
destruct (nth_error_split3 _ KBSq j bsj Hbsj) as [EK Lb1]. set (KBS1 := firstn j KBSq) in *. set (KBS2 := skipn (S j) KBSq) in *.
clearbody pre post kids1 kids2 KBS1 KBS2.
assert (K12 : okids rsegs S4F mc kids1 (map kv pre) KBS1 /\ okids rsegs S4F mc kids2 (map kv post) KBS2).
{ rewrite Ek, Ees, EK, map_app in KIDS. cbn [map] in KIDS.
apply okids_app_inv in KIDS as [K1 K2]; [| rewrite length_map; lia | lia].
split; [exact K1 | exact (proj2 K2)]. }
destruct K12 as [K1 K2].
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash OPEN. stash K1. stash K2. stash OPB. stash JOB. stash G. stash KF. stash SEP. stash D1. stash KIDS. stash JO. stash SVm. stash PRES.
apply rz_evt; [exact MOK|].
step. step.
destruct kj as [sj|].
-
unstash JO. destruct JO as [Hvo J].
if_falsex. step.

unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G. unstash SVm. unstash PRES.
set (LBput := (q, 48) :: (tq, 56) :: (tblq, 40 * sizeq) :: (map (fun e0 : lent => (le_k e0, le_kn e0)) esq ++ concat KBS1 ++ concat KBS2 ++ PBSq ++ VBS ++ LR)).
assert (HPp : HEAPx A2 (bsj ++ LBput) mc mdc).
{ eapply (heap_perm S4L HIx); [exact HP|]. unfold QDc2.OBS, LBput. rewrite EK, concat_mid. unfold lh_blocks. perm. }
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
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR5 by lia.
destruct OUT5 as [[_ HP5] | (s'' & _ & Hrc & _)]; [| lia].
assert (AG5 : agree_on rsegs LBput mc mP) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR5 | reflexivity | apply incl_refl]).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in CELL; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FRJ; [| left; cbn; lia]. cbn [hl_segs S4L] in FRJ.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (rw_cells_agree rsegs _ _ _ _ _ HDR0) in AG5 as HDR5; [| exists q, 48; split; [left; reflexivity | cbn; lia]].
pose proof (lh_open_agree rsegs S4F _ _ _ _ _ _ _ _ OPEN AG5 ltac:(unfold LBput, lh_blocks; intros b Hb; cbn in Hb |- *; destruct Hb as [Hb|[Hb|Hb]]; [tauto|tauto|]; right; right; right; apply in_or_app; left; exact Hb)) as OPEN5.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K1 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 1 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K15.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ K2 AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as K25.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as OPB5.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 4 (apply in_or_app; right); apply in_or_app; left; exact Hb)) as JOB5.
pose proof (SVAG _ _ SVm (agree_on_incl rsegs _ _ _ _ AG5 ltac:(unfold LBput; intros b Hb; right; right; right; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb))) as SV5.
pose proof (jc_glob_P_pres _ _ _ _ HPR5 G) as G5.
assert (PRES5 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mP).
{ eapply presxD_trans; [exact PRES|]. apply pres_presxD.
eapply heap_pres_weaken; [exact HPR5 | lia | unfold LBput; intros b Hb; right; right; right; do 5 (apply in_or_app; right); apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | do 2 (apply in_or_app; right); exact Hb]]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI5. cbn [hl_segs S4L] in MI5.
clear MU WM MI SLOT HDR OPEN K1 K2 OPB JOB G ST HP HPp AG5 ERR SVm PRES.
pose proof (wmono_refl rsegs mP) as WM. pose proof (munch_refl [] mP) as MU.
stash OPEN5. stash K15. stash K25. stash OPB5. stash JOB5. stash G5. stash SV5. stash PRES5.
apply rz_evt; [exact MOK5|].
replace (ret_pc (wz 0x25a24)) with (wz 0x25a24) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. subst EA.
unstash OPEN5. unstash K15. unstash K25. unstash OPB5. unstash JOB5. unstash G5. unstash SV5. unstash PRES5.
apply evt_RZ_done.
eapply (dc_osetv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 mP md5 A5 _ cj svs j e kids1 kids2 (Some sj) KBS1 KBS2 bsj pre post);
first [exact HP5 | exact HDR5 | exact OPEN5 | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K15 | exact K25 | exact OPB5 | exact JOB5 | exact SV5
| exact ERR5 | exact DC | exact FRJ | exact CELL | lia
| eapply fsaved_trans; [exact FSa | exact FS5]
| apply FRM5; exact FRMa
| split; [eapply model_vm_only_trans; [exact VMa | exact VM5] | split; [exact PRES5 | split; [exact ST5 | split; [exact FR | exact G5]]]] ].
-
unstash JO. destruct JO as [Hvo Ebsj]. rewrite Hvo. if_true.
unstash OPEN. unstash K1. unstash K2. unstash OPB. unstash JOB. unstash G. unstash SVm. unstash PRES.
subst EA.
apply evt_RZ_done.
eapply (dc_osetv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 mc mdc A2 errc cj svs j e kids1 kids2 None KBS1 KBS2 bsj pre post);
first [exact HDR0 | exact OPEN | exact Hj | exact Ees | exact Lpre | exact Ek | exact EK | exact K1 | exact K2 | exact OPB | exact JOB | exact G | exact SVm
| exact ERR | exact DC | exact FRJ | exact CELL | exact FSa | exact FRMa | lia
| split; [exact VMa | split; [exact PRES | split; [exact ST | split; [exact FR | exact G]]]]
| idtac ].
eapply (heap_perm S4L HIx); [exact HP|]. unfold QDc2.OBS. rewrite EK, Ebsj, concat_mid. unfold lh_blocks. perm.
Qed.

#[using="PUT PUTX HASH fc kids r LO LOS SPA HT SPD DAL NN JR0 Kont SVAG INK KN LQ1 LQ2 Hq OKQ ODEP ONEXT"] Lemma dc_oins :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : Model) (A2 : AS S4L HIx) (h : Z) (errc : word) (svs : list slotv),
HEAPx A2 (OBSq ++ VBS ++ LR) mc mdc ->
rw_cells rsegs mc q OHDRq ->
lh_open rsegs S4F mc tq tblq sizeq esq svs ->
okids rsegs S4F mc kidsq (map kv esq) KBSq -> opt_pbuf rsegs mc PBSq pbq -> jopt rsegs S4F vs mc VBS jso -> SV mc ->
cstr rsegs mc k kn ks ->
rw_cells rsegs mc (0x75e70 - 164) [C4 errc] -> rw_cells rsegs mc D [C8 (wz q)] ->
dc_inv mc mdc -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> rw_cells rsegs mc (bv_unsigned sp + -104) [C8 (wz jso)] -> 0 <= h < 2^64 ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D)
(wz 0) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) (wz jso) (wz k) (wz h) x24 (wz ea) (wz q) s11 t3 t4 t5 t6)
F2 (wz 0x25a28) fc2 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until svs. intros HP HDR OPEN KIDS OPB JOB SVm CS ERR DC INV FSa FRMa FRJ CELL Hh.
pose proof INV as (VMa & PRES & ST & FR & G). unfold Qzop.dc_frame in FR.
pose proof HDR as HDR0. unfold QDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu. rewrite sdepth_Sobj in LOSu.
pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
destruct (oadd_facts HIx q tq tblq sizeq esq _ _ _ _ (concat KBSq ++ PBSq ++ VBS ++ LR) HP ltac:(unfold QDc2.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS q jso vs _ _ _ _ (lh_blocks tq tblq sizeq esq ++ concat KBSq ++ PBSq ++ LR) HP ltac:(unfold QDc2.OBS; perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.
assert (INK' : In (k, kn) (OBSq ++ VBS ++ LR)) by (apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact INK).
destruct (key_string HIx _ _ _ _ _ _ _ HP INK' CS) as (slack & STR & PAD & NNk & KAL & KL & KPOS & KHI & KSL).
unfold alloc_ceiling, sp_window_lo, stack_max_size in KHI.
pose proof (heap_blk_img S4L HIx _ _ _ _ k kn HP INK') as Hkimg. cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] mc) as MU.
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash G. stash KF. stash SEP. stash D1. stash D2. stash SVm. stash PRES.
apply rz_evt; [exact MOK|].
step. step.

apply evt_RZ_done.
pose proof (strdup_cps HIx) as SDP. unfold strdup_stmt in SDP.
eapply SDP with (LB := OBSq ++ VBS ++ LR) (lo := lo) (str := ks) (slack := slack); clear SDP;
[ heap_now S4L HIx HP MU WM MI
| rewrite unsigned_lit by lia; exact STR | exact NNk | rewrite unsigned_lit by lia; exact PAD
| rewrite !unsigned_lit by lia; eapply client_range_block; [exact INK' | lia | lia]
| rewrite !unsigned_lit by lia; left; lia | lia | .. ]; try alloc_side.
intros ms4 md4 (mE & A4 & r2 & e4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & STR4 & OUT4). open_ret RS4. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit k) in STR4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash CS. unstash G. unstash SVm. unstash PRES.
assert (AG4 : agree_on rsegs (OBSq ++ VBS ++ LR) mc mE) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | apply incl_refl]).
assert (PRES4 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mE).
{ eapply presxD_trans; [exact PRES|]. apply pres_presxD. eapply heap_pres_weaken; [exact HPR4 | lia | unfold QDc2.OBS; incl_tac]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FRJ; [| left; cbn; lia]. cbn [hl_segs S4L] in FRJ.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in CELL; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
assert (INp : In (q, 48) (OBSq ++ VBS ++ LR)) by (unfold QDc2.OBS; cbn; left; reflexivity).
apply (rw_cells_agree rsegs _ _ _ _ _ HDR0) in AG4 as HDR4; [| exists q, 48; split; [exact INp | cbn; lia]].
pose proof HDR4 as HDR4'. unfold QDc2.OHDR in HDR4'. cbn [fn_obj_to_json_string S4F] in HDR4'.
pose proof (lh_open_agree rsegs S4F _ _ _ _ _ _ _ _ OPEN AG4 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN4.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS AG4 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS4.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG4 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB4.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG4 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB4.
pose proof (SVAG _ _ SVm (agree_on_incl rsegs _ _ _ _ AG4 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb))) as SV4.
pose proof (jc_glob_P_pres _ _ _ _ HPR4 G) as G4.
clear MU WM MI HDR OPEN KIDS OPB JOB G ST STR SVm PRES.
destruct OUT4 as [(-> & HP4) | (Hr2 & NEWK & HP4)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mE) as WM. pose proof (munch_refl [] mE) as MU.
stash OPEN4. stash KIDS4. stash OPB4. stash JOB4. stash SV4. stash PRES4. stash G4.
reenter MOK4.
step. if_true.
unstash OPEN4. unstash KIDS4. unstash OPB4. unstash JOB4. unstash SV4. unstash PRES4. unstash G4.
apply evt_RZ_done.
eapply dc_failc with (CBS := OBSq) (REMc := REM) (sq := Sobj kidsq);
[ split; [eapply model_vm_only_trans; [exact VMa | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR | exact G4]]]]
| exact FSa | exact FRMa | exact CELL | exact FRJ | exact ERR4 | eapply (heap_perm S4L HIx); [exact HP4 | perm] | exact DC | | exact JOB4 ].
eapply (sobj_close rsegs S4F) with (TBS := lh_blocks tq tblq sizeq esq) (kvs := map kv esq);
[ reflexivity | exact OPB4 | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR4'
| exists tblq, sizeq, esq, svs; split; [reflexivity | split; [reflexivity | exact OPEN4]]
| rewrite length_map; exact LQ1 | exact LQ2 | exact KIDS4 ].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r2 _ HP4 ltac:(left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
pose proof (wmono_refl rsegs mE) as WM. pose proof (munch_refl [] mE) as MU.
stash OPEN4. stash KIDS4. stash OPB4. stash JOB4. stash NEWK. stash SV4. stash PRES4. stash G4. stash HDR4.
reenter MOK4.
step. if_falsex. step. step. step. step. step. step.
unstash OPEN4. unstash KIDS4. unstash OPB4. unstash JOB4. unstash NEWK. unstash CS. unstash SV4. unstash PRES4. unstash G4. unstash HDR4.
assert (CS4 : cstr rsegs mE r2 (Z.of_nat (length ks) + 1) ks).
{ split; [lia|]. split; [exact (proj1 (proj2 CS))|]. exists []. rewrite app_nil_r.
replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (Z.to_nat (Z.of_nat (length ks) + 1)) by reflexivity. exact NEWK. }
set (LBI := (q, 48) :: concat KBSq ++ PBSq ++ VBS ++ LR).
apply evt_RZ_done.
eapply (lh_insert_cps HIx lf_test_spec_proof model_vm_only model_vm_only_refl (64 + 8320) RESIZE3 ltac:(lia))
with (LB := LBI) (t := tq) (tbl := tblq) (size := sizeq) (es := esq) (svs := svs)
(k := r2) (kn := Z.of_nat (length ks) + 1) (ks := ks) (v := jso) (h := h) (lo := lo) (errv := e4);
[ eapply (heap_perm S4L HIx); [exact HP4 | unfold LBI, QDc2.OBS; perm]
| exact OPEN4 | exact G4 | exact CS4 | lia | lia | exact Hh | rewrite unsigned_lit by lia; exact ST4 | clia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia | exact ERR4
| reflexivity | reflexivity | exact FRMa | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
intros ms5 md5 (mF & A5 & r5 & e5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & G5 & OUT5).
destruct RS5 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR5 by lia.
assert (AG5 : agree_on rsegs LBI mE mF) by (eapply (agree_of_heap_presx rsegs S4L); [exact HPR5 | reflexivity | apply incl_refl]).
assert (HiK : incl (concat KBSq) LBI) by (intros b Hb; right; apply in_or_app; left; exact Hb).
assert (HiP : incl PBSq LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiV : incl VBS LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HiL : incl LR LBI) by (intros b Hb; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
apply (rw_cells_agree rsegs _ _ _ _ _ HDR4) in AG5 as HDR5; [| exists q, 48; split; [left; reflexivity | cbn; lia]].
unfold QDc2.OHDR in HDR5. cbn [fn_obj_to_json_string S4F] in HDR5.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS4 AG5 HiK) as KIDS5.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB4 AG5 HiP) as OPB5.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB4 AG5 HiV) as JOB5.
pose proof (SVAG _ _ SV4 (agree_on_incl rsegs _ _ _ _ AG5 ltac:(intros b Hb; apply HiL; apply in_or_app; left; exact Hb))) as SV5.
assert (PRES5 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mF).
{ eapply presxD_trans; [exact PRES4|]. apply presx_presxD.
eapply heap_presx_weaken; [exact HPR5 | lia | | intros b' Xa; exact Xa].
intros b Hb. apply HiL. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | do 2 (apply in_or_app; right); exact Hb]. }
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR5) in FRJ; [| left; cbn; lia]. cbn [hl_segs S4L] in FRJ.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR5) in CELL; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR5) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
assert (HPX : exists LX, HEAPx A5 LX mF md5) by (destruct OUT5 as [(_ & _ & _ & HP5) | (_ & tbl' & size' & es' & svs' & g & _ & _ & HP5)]; eexists; exact HP5).
destruct HPX as [LX HP5x].
pose proof (heap_model_ok _ _ _ _ _ _ HP5x) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5x) as MI5. cbn [hl_segs S4L] in MI5.
clear MU WM MI HP4 MOK4 AG5 HP5x.
pose proof (wmono_refl rsegs mF) as WM. pose proof (munch_refl [] mF) as MU.
stash KIDS5. stash OPB5. stash JOB5. stash SV5. stash PRES5. stash G5. stash OUT5.
reenter MOK5.
unstash OUT5.
destruct OUT5 as [(-> & OPEN5 & CS5 & HP5) | (-> & tbl' & size' & es' & svs' & g & STRIP & OPEN5 & HP5)].
+
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
stash OPEN5. stash CS5.
step. if_false.
unstash KIDS5. unstash OPB5. unstash JOB5. unstash SV5. unstash PRES5. unstash G5. unstash OPEN5.
apply evt_RZ_done.
eapply dc_failc with (CBS := OBSq) (REMc := (r2, Z.of_nat (length ks) + 1) :: REM) (sq := Sobj kidsq);
[ split; [eapply model_vm_only_trans; [exact VMa | eapply model_vm_only_trans; [exact VM4 | exact VM5]] | split; [exact PRES5 | split; [exact ST5 | split; [exact FR | exact G5]]]]
| eapply fsaved_trans; [exact FSa | exact FS5] | apply FRM5; exact FRMa | exact CELL | exact FRJ | exact ERR5
| eapply (heap_perm S4L HIx); [exact HP5 | unfold LBI, QDc2.OBS; perm] | exact DC | | exact JOB5 ].
eapply (sobj_close rsegs S4F) with (TBS := lh_blocks tq tblq sizeq esq) (kvs := map kv esq);
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR5
| exists tblq, sizeq, esq, svs; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map; exact LQ1 | exact LQ2 | exact KIDS5 ].
+
stash OPEN5. stash STRIP.
step. if_true.
unstash KIDS5. unstash OPB5. unstash JOB5. unstash SV5. unstash PRES5. unstash G5. unstash OPEN5. unstash STRIP.
apply evt_RZ_done.
eapply (ONEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 mF md5 A5 (kidsq ++ [vs])
(((q, 48) :: lh_blocks tq tbl' size' (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks jso]) ++ concat (KBSq ++ [VBS])) ++ PBSq) REM (le8 (wz jso)) e5);
[ split; [eapply model_vm_only_trans; [exact VMa | eapply model_vm_only_trans; [exact VM4 | exact VM5]] | split; [exact PRES5 | split; [exact ST5 | split; [exact FR | exact G5]]]]
| eapply fsaved_trans; [exact FSa | exact FS5] | apply FRM5; exact FRMa | exact FRJ | | exact ERR5
| | exact SV5 | exact DC | | ].
* unfold Qzop.dc_cell. apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL; [exact CELL | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
* rewrite concat_app. cbn [concat]. rewrite app_nil_r. eapply (heap_perm S4L HIx); [exact HP5 | unfold LBI; perm].
* eapply (sobj_close rsegs S4F) with (kvs := map kv (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks jso]));
[ reflexivity | exact OPB5 | unfold jhdr_cells; cbn [app fn_obj_to_json_string S4F]; exact HDR5
| exists tbl', size', (es' ++ [LE g r2 (Z.of_nat (length ks) + 1) ks jso]), svs'; split; [reflexivity | split; [reflexivity | exact OPEN5]]
| rewrite length_map, !length_app, (strip_length _ _ STRIP); cbn [length]; lia
| rewrite !length_app; cbn [length]; lia
| rewrite map_app, (strip_kv _ _ STRIP); cbn [map]; apply okids_app; [exact KIDS5 | apply okids_one; unfold kv; cbn [le_v]; exact JOB5] ].
* rewrite okmax_app, okmax_single. pose proof (okmax_nonneg kidsq). pose proof (odep_nonneg vs). lia.
Qed.

#[using="PUT PUTX HASH fc kids r LO LOS SPA HT SPD DAL NN JR0 Kont SVAG INK KN LQ1 LQ2 Hq OKQ ODEP ONEXT"] Lemma dc_oadd :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x24 x26 t3 t4 t5 t6 : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(mc : word -> option byte) (mdc : Model) (A2 : AS S4L HIx) (errc : word) (svs : list slotv),
HEAPx A2 (OBSq ++ VBS ++ LR) mc mdc ->
rw_cells rsegs mc q OHDRq ->
lh_open rsegs S4F mc tq tblq sizeq esq svs ->
okids rsegs S4F mc kidsq (map kv esq) KBSq -> opt_pbuf rsegs mc PBSq pbq -> jopt rsegs S4F vs mc VBS jso -> SV mc ->
cstr rsegs mc k kn ks ->
rw_cells rsegs mc (0x75e70 - 164) [C4 errc] -> rw_cells rsegs mc D [C8 (wz q)] ->
dc_inv mc mdc -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> rw_cells rsegs mc (bv_unsigned sp + -104) [C8 (wz jso)] ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D)
a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz 4294967295) (wz jso) (wz k) x23 x24 (wz ea) x26 s11 t3 t4 t5 t6)
F2 (wz 0x259e0) fc2 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until svs. intros HP HDR OPEN KIDS OPB JOB SVm CS ERR DC INV FSa FRMa FRJ CELL.
pose proof INV as (VMa & PRES & ST & FR & G). unfold Qzop.dc_frame in FR.
pose proof HDR as HDR0. unfold QDc2.OHDR in HDR. cbn [fn_obj_to_json_string S4F] in HDR.
pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu. rewrite sdepth_Sobj in LOSu.
pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
destruct (oadd_facts HIx q tq tblq sizeq esq _ _ _ _ (concat KBSq ++ PBSq ++ VBS ++ LR) HP ltac:(unfold QDc2.OBS; perm))
as ((Hpal & Hplo & Hphi & Hpimg) & (Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & D1 & D2 & KF).
destruct (oadd_pv HIx VBS q jso vs _ _ _ _ (lh_blocks tq tblq sizeq esq ++ concat KBSq ++ PBSq ++ LR) HP ltac:(unfold QDc2.OBS; perm) JOB) as (Hpv & V0 & V1).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hthi, Hbhi, V1.
assert (INK' : In (k, kn) (OBSq ++ VBS ++ LR)) by (apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact INK).
destruct (key_string HIx _ _ _ _ _ _ _ HP INK' CS) as (slack & STR & PAD & NNk & KAL & KL & KPOS & KHI & KSL).
unfold alloc_ceiling, sp_window_lo, stack_max_size in KHI.
pose proof (heap_blk_img S4L HIx _ _ _ _ k kn HP INK') as Hkimg. cbn [hl_img_lo hl_img_hi S4L] in Hkimg.
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free S4F] in THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [] mc) as MU.
stash OPEN. stash KIDS. stash OPB. stash JOB. stash CS. stash G. stash KF. stash STR. stash HDR0. stash PAD. stash KSL. stash KAL.
stash Hpimg. stash Htimg. stash Hbimg. stash Hkimg. stash SEP. stash D1. stash D2. stash SVm. stash PRES.
apply rz_evt; [exact MOK|].
step. step. step. step. step.

unstash CS. unstash G. unstash OPEN. unstash KIDS. unstash OPB. unstash JOB. unstash HDR0. unstash SVm. unstash PRES. unstash STR.
pose proof HASH as HASH'. unfold lh_char_hash_stmt in HASH'.
apply evt_RZ_done.
eapply HASH' with (LB := OBSq ++ VBS ++ LR) (lo := lo) (kp := k) (kn := kn) (ks := ks);
[ exact HP | exact INK' | exact CS | exact G | rewrite unsigned_lit by lia; exact ST | clia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | rewrite unsigned_lit by lia; reflexivity | exact FRMa | reflexivity | ].
clear HASH'.
intros ms2 md2 (mB & A3 & h & e2 & RS2 & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
destruct RS2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
assert (AG2 : agree_on rsegs (OBSq ++ VBS ++ LR) mc mB) by (eapply (agree_of_heap_presx rsegs S4L); [exact HPR2 | reflexivity | apply incl_refl]).
assert (PRES2 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mB).
{ eapply presxD_trans; [exact PRES|]. apply presx_presxD.
eapply heap_presx_weaken; [exact HPR2 | lia | unfold QDc2.OBS; incl_tac | intros b' Xa; exact Xa]. }
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in FRJ; [| left; cbn; lia]. cbn [hl_segs S4L] in FRJ.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in CELL; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
assert (INp : In (q, 48) (OBSq ++ VBS ++ LR)) by (unfold QDc2.OBS; cbn; left; reflexivity).
apply (rw_cells_agree rsegs _ _ _ _ _ HDR0) in AG2 as HDR2; [| exists q, 48; split; [exact INp | cbn; lia]].
pose proof HDR2 as HDR2'. unfold QDc2.OHDR in HDR2. cbn [fn_obj_to_json_string S4F] in HDR2.
pose proof (lh_open_agree rsegs S4F _ _ _ _ _ _ _ _ OPEN AG2 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as OPEN2.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS AG2 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS2.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG2 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB2.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB2.
pose proof (cstr_agree rsegs _ _ _ _ _ _ CS AG2 INK' ltac:(lia)) as CS2.
pose proof (SVAG _ _ SVm (agree_on_incl rsegs _ _ _ _ AG2 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb))) as SV2.
clear HP MU WM MI HDR THDR OPEN KIDS OPB JOB CS G ST STR SVm PRES.

pose proof (proj1 (cstr_bytes rsegs _ _ _ _ CS2)) as KB2.
pose proof (proj1 OPEN2) as THDR. unfold lh_hdrf in THDR. cbn [fn_lh_char_hash fn_lh_char_equal fn_lh_entry_free S4F] in THDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mB) as WM. pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp + -112)] mB) as MU.
stash OPEN2. stash KIDS2. stash OPB2. stash JOB2. stash CS2. stash G2. stash HDR2'. stash SV2. stash PRES2.
reenter MOK2.
step. step. step. step. step. step.

unstash OPEN2.
assert (BELOW : lh_below lo tq tblq sizeq esq).
{ unstash KF. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He) as (_ & _ & K2 & _). unfold_consts. lia. }
eapply evt_cut.
{ eapply (lh_lookup_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 tq tblq sizeq k lo esq svs ks) with (h := h);
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by lia;
first [exact MI | exact OPEN2 | exact BELOW | exact KB2 | exact NNk | exact ST2 | reflexivity | exact Hh | lia]. }
unfold lh_lookup_post. cbv beta. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by lia.
post_call rsegs mB.
match goal with H : lh_open rsegs S4F ?mx tq tblq sizeq esq svs |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN3; rename mx into mC end.
match goal with H : stk rsegs mC lo _ |- _ => rename H into ST3 end.
match goal with H : lookup_res tblq esq ks ?rr |- _ => rename H into RES; rename rr into re end.
match goal with H : mem_inv rsegs mC |- _ => rename H into MI3 end.
unstash KIDS2. unstash OPB2. unstash JOB2. unstash CS2. unstash G2. unstash HDR2'. unstash SV2. unstash PRES2.
assert (HP3 : HEAPx A3 (OBSq ++ VBS ++ LR) mC md2) by heap_now S4L HIx HP2 MU WM MI3.
assert (AG3 : agree_on rsegs (OBSq ++ VBS ++ LR) mB mC).
{ eapply (agree_of_munch rsegs); [exact MU | exact WM |]. intros a n Ha. cbn.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP2 Ha) as (? & _ & _ & ? & _). unfold_consts. lia. }
assert (PRES3 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mC).
{ eapply presxD_trans; [exact PRES2|]. eapply presxD_of_munch; [exact MU | exact WM |]. intros b Hb Hc Hd.
eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HP2 | unfold QDc2.OBS; incl_tac | clia | solve_clientW S4L HIx HP2 | exact Hb | exact Hc]. }
pose proof (rw_cells_agree rsegs _ _ _ _ _ HDR2' AG3 ltac:(exists q, 48; split; [exact INp | cbn; lia])) as HDR3.
pose proof (okids_agree rsegs S4F _ _ _ _ _ _ KIDS2 AG3 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; left; right; apply in_or_app; right; exact Hb)) as KIDS3.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB2 AG3 ltac:(unfold QDc2.OBS; intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb)) as OPB3.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB2 AG3 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb)) as JOB3.
pose proof (cstr_agree rsegs _ _ _ _ _ _ CS2 AG3 INK' ltac:(lia)) as CS3.
pose proof (SVAG _ _ SV2 (agree_on_incl rsegs _ _ _ _ AG3 ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb))) as SV3.
pose proof (jc_glob_P_munch _ _ _ G2 MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; unfold_consts; lia)) as G3.
match goal with H : rw_cells rsegs mC (bv_unsigned sp + -96) _ |- _ => rename H into FR3 end.
match goal with H : rw_cells rsegs mC (bv_unsigned sp + -112) _ |- _ => rename H into FRJ3 end.
match goal with H : rw_cells rsegs mC (bv_unsigned sp + -104) _ |- _ => rename H into CELL3 end.
match goal with H : rw_cells rsegs mC D _ |- _ => rename H into DC3 end.
match goal with H : rw_cells rsegs mC (482928 - 164) _ |- _ => rename H into ERR3 | H : rw_cells rsegs mC 482764 _ |- _ => rename H into ERR3 end.
step. if_falsex. step. step.
destruct RES as [-> | (j & e & Hj & -> & Hks)].
-
if_true.
apply evt_RZ_done.
eapply dc_oins;
first [exact HP3 | exact HDR3 | exact OPEN3 | exact KIDS3 | exact OPB3 | exact JOB3 | exact SV3 | exact CS3 | exact G3 | exact ERR3 | exact DC3 | exact FRJ3 | exact CELL3
| exact Hh | eapply fsaved_trans; [exact FSa | exact FS3] | apply FRM3; exact FRMa
| split; [eapply model_vm_only_trans; [exact VMa | exact VM2] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR3 | exact G3]]]] ].
-
destruct (lh_open_slot rsegs S4F _ _ _ _ _ _ _ _ _ OPEN3 Hj) as (sl & _ & Hix & _).
pose proof OPEN3 as (_ & _ & _ & _ & _ & _ & Hlen).
unfold ent_addr. if_falsex. fold (ent_addr tblq (le_ix e)).
apply evt_RZ_done.
eapply dc_odup with (cj := le8 (wz jso));
first [exact HP3 | exact HDR3 | exact OPEN3 | exact Hj | exact KIDS3 | exact OPB3 | exact JOB3 | exact SV3 | exact G3 | exact ERR3 | exact DC3 | exact FRJ3
| eapply fsaved_trans; [exact FSa | exact FS3] | apply FRM3; exact FRMa
| split; [eapply model_vm_only_trans; [exact VMa | exact VM2] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR3 | exact G3]]]]
| unfold Qzop.dc_cell; apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL3; [exact CELL3 | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity] ].
Qed.
End DcObjAdd.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Qfw3_c1 Qc3B QlEo_c1 Lib.GwApply QsjA QZAi Ql2m QqdR QYTG QiVh QjdK Q4l4 QxrO Qm2h QDgQ QzOj QSCw Qbz7 QTru Q3Uw Q0Ae QTa4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QiVh.Mq0 QRjH.Mq3.
Import QjdK Q4l4 QxrO Qm2h QDgQ QzOj.
Import QSCw Qbz7.
Import QTru Q3Uw.Mq0 Q0Ae QTa4.
Import QEQM.
Import Qfw3_c1.Mq1.
Import QCcH.
Import Qzop.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

Import Q6q3.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= rc_lia_prep; lia3. Local Ltac mkr__lia_4 := rc_lia_prep; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section StaticRW.
Variable segs : list Segment.

#[using="Type"] Lemma image_bytes_rom : forall n A bs i, image_bytes segs A n = Some bs -> (i < n)%nat ->
seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
induction n as [|n IH]; intros A bs i H Hi; [lia|].
cbn [image_bytes] in H. destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate]. injection H as <-.
destruct i as [|i].
- cbn [nth_error]. rewrite <- E. f_equal. unfold wa. f_equal. lia.
- cbn [nth_error]. rewrite <- (IH (A + 1) bs' i E' ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Definition shown (m : word -> option byte) (bs : list byte) (A : Z) (i : nat) : byte :=
match m (wa (A + Z.of_nat i)) with Some b => b | None => nth i bs (Z_to_bv 8 0) end.

#[using="Type"] Lemma bss_rw_cells : forall m A n bs,
image_bytes segs A n = Some bs -> wseg_ok segs (Z_to_bv 64 A) n = true ->
0 <= A -> A + Z.of_nat n <= 2^64 ->
rw_cells segs m A [CB n (map (shown m bs A) (seq 0 n))].
Proof.
intros m A n bs IB WS H0 H1.
pose proof (image_bytes_length segs n A bs IB) as L.
split; [split|].
- cbn. rewrite length_map, length_seq. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact H0|]. rewrite length_map, length_seq. split; [exact H1|].
intros i Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map]. rewrite Nat.add_0_l.
unfold mrd, shown. destruct (m (wa (A + Z.of_nat i))) as [b|]; [reflexivity|].
rewrite (image_bytes_rom n A bs i IB Hi). rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. reflexivity.
- cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1|].
intros k Hk. apply (store_ok_all segs m n (Z_to_bv 64 A) ltac:(rewrite unsigned_lit by lia; lia) (store_ok_wseg segs m _ _ WS) (wa (A + k))).
unfold wa. rewrite !unsigned_lit by lia. lia.
Qed.
End StaticRW.

Definition LASTERR_TXT : list Z :=
[106; 115; 111; 110; 95; 111; 98; 106; 101; 99; 116; 95; 99; 111; 112; 121; 95; 115; 101; 114; 105; 97; 108; 105;
122; 101; 114; 95; 100; 97; 116; 97; 58; 32; 111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 10].
Definition LASTERR_FMTS : list Z := LASTERR_TXT ++ [0].

#[using="Type"] Lemma lasterr_fmt_bytes_P : forall m, mem_inv rsegs m -> bytes_at rsegs m LASTERR_FMT_P (zb LASTERR_FMTS).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold LASTERR_FMT_P; lia | unfold LASTERR_FMT_P, zlength; cbn; lia]. Qed.

#[using="Type"] Lemma fp_calls_lasterr : fp_calls (length LASTERR_FMTS) LASTERR_FMTS [] = [].
Proof. vm_compute. reflexivity. Qed.

Definition lasterr_img_P := Eval vm_compute in match image_bytes rsegs LASTERR_BUF_P 256 with Some bs => bs | None => [] end.
#[using="Type"] Lemma lasterr_buf_P : forall m, rw_cells rsegs m LASTERR_BUF_P [CB 256 (map (shown m lasterr_img_P LASTERR_BUF_P) (seq 0 256))].
Proof.
intros m. apply bss_rw_cells; [vm_compute; reflexivity | vm_compute; reflexivity | unfold LASTERR_BUF_P; lia | unfold LASTERR_BUF_P; cbn; lia].
Qed.

#[using="Type"] Theorem set_last_err_P : set_last_err_spec_P.
Proof.
unfold set_last_err_spec_P, LASTERR_P, LASTERR_STK. intros until canary.
intros -> ST LO LOS SPA SPH SSP MI FRM.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO. pose proof (@rc_ceil_range RC__) as RCR.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (lasterr_buf_P m) as DST. unfold LASTERR_BUF_P in *.
set (junkd := map _ (seq 0 256)) in DST. clearbody junkd.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (479788, 479788 + 256)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 80%nat ST.
do 18 zs.

apply (proj1 (rw_cells_app rsegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.

pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS. cbv zeta in VS.
eapply evt_cut.
{ eapply VS with (D := 479788) (n := 256) (A := LASTERR_FMT_P) (VA := bv_unsigned sp + -56) (dn := 256%nat) (junkd := junkd) (fmt := LASTERR_FMTS) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [])
(lo := lo) (canary := canary) (r := 48) (o := LASTERR_TXT);
clear VS; rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, got_ssp, ssp_guard, LASTERR_FMT_P, zlength; cbn [length].
all: try reflexivity.
all: try lia.
all: try eassumption.
all: lazymatch goal with
| |- bytes_at _ _ _ _ => apply lasterr_fmt_bytes_P; assumption
| |- Forall _ LASTERR_FMTS => unfold LASTERR_FMTS, LASTERR_TXT; cbn [app]; repeat (apply Forall_cons; [split; [apply Zle_0_pos + reflexivity | reflexivity] |]); apply Forall_nil
| |- Forall no_s [] => apply Forall_nil
| |- Forall _ (fp_calls _ _ _) => rewrite fp_calls_lasterr; apply Forall_nil
| |- ssp_cells _ _ => split; [exact SSP1 | exact SSP2]
| |- _ => unfold LASTERR_FMTS, LASTERR_TXT; rewrite ?length_app; cbn [length Nat.add]; lia
end. }
cbv beta. intros ms' P.
unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.

zs. zs. zs.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?c1, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?c2 |- _ =>
assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -80) (c1 ++ c2));
[ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
split; [| exact FRM'].
intros k Hk. apply FOK. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; vm_compute; lia.
Qed.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ3T.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJ3T. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOfx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOfx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoYh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoYh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrIB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdgq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzop.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma concat_nth_split : forall {X} (bss : list (list X)) i bs,
nth_error bss i = Some bs -> concat bss = concat (firstn i bss) ++ bs ++ concat (skipn (S i) bss).
Proof.
intros X bss i bs H. rewrite (concat_firstn_skipn bss i) at 1. f_equal.
revert bss H. induction i as [|i IH]; intros [|b bss] H; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

#[using="Type"] Lemma mod16_mod8 : forall x k, x mod 16 = 0 -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof.
intros x k Hx Hk. rewrite Z.add_mod by lia. rewrite Hk, Z.add_0_r.
replace (x mod 8) with 0; [reflexivity|]. symmetry.
apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult.
Qed.

Section DcArr.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis LASTERR : set_last_err_spec_P.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (T : TSet).
Variable kids : list (option jshape).
Let r : jroot := JRtree (Sarr kids).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stk (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Hypothesis IH : forall s', In (Some s') kids -> dcopy_spec HIx (JRtree s').

Notation dc_inv := (dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 md0 LB BS lo D).
Notation dc_cell := (dc_cell sp).
Ltac dc_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact FRM0 | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact HT63 | exact LASTERR | exact PUTX | exact PUT | clia ].

#[using="PUT PUTX fc r LO LOS SPA HT SPD DAL NN JR0 Kont IH"] Lemma dc_arr_loop :
forall (n ii : nat) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (kids' : list (option jshape)) (CBS REM : list blk) (cj jk : list byte) (e : word)
(pb : Z) (PBS : list blk) (a : Z) (AL : list blk) (ps : list Z) (KBS : list (list blk)) (q : Z),
n = (length kids - ii)%nat -> (ii < length kids)%nat ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell mc cj -> rw_cells rsegs mc (0x75e70 - 164) [C4 e] ->
HEAPx A (BS ++ CBS ++ REM ++ LB) mc mdc ->
BS = ((p, 48) :: AL ++ concat KBS) ++ PBS -> opt_pbuf rsegs mc PBS pb ->
rw_cells rsegs mc p (jhdr_cells JT_ARRAY 1 (fn_arr_to_json_string S4F) pb 0 0 ++ [C8 (wz a)]) ->
alist rsegs S4F mc AL a ps -> length ps = length kids -> length KBS = length kids -> akids rsegs S4F mc kids ps KBS ->
q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> jval rsegs S4F (Sarr kids') mc CBS q 1 ->
length kids' = ii -> okmax kids' <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz (Z.of_nat (length kids))) (wz (Z.of_nat ii)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x25a80) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
induction n as [|n IHn]; intros until q; intros Hn Hii INV FS FRM1 FRJ CELL ERR HP EBS OPB HDR HAL L1 L2 KIDS Hq DC JQ LK OK; [lia|].
pose proof INV as (VM & PRES & ST & FR & G).
unfold Qzop.dc_frame in FR. unfold Qzop.dc_cell in CELL. pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu.
rewrite sdepth_Sarr in LOSu. pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
change (0x75e70 - 164) with 482764 in ERR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INp1 : In (p, 48) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [(bv_unsigned sp - 104, bv_unsigned sp - 96)] mc) as MU.

assert (Hlen : Z.of_nat (length kids) < 2^64).
{ destruct HAL as (arr & size & junk & EAL & Hl & Hsz & _). lia. }
pose proof (al_nth_in ps (Z.of_nat ii) ltac:(lia)) as NTH. rewrite Nat2Z.id in NTH.
destruct (akids_nth rsegs S4F _ _ _ _ ii _ KIDS NTH) as (k & bs & Hk & Hbs & JOB).
stash G. stash OPB. stash KIDS. stash JQ. stash JOB.
assert (AGB : forall (A' : AS S4L HIx) L' ma mda mx, HEAPx A' L' ma mda -> munch [(bv_unsigned sp - 104, bv_unsigned sp - 96)] ma mx -> wmono rsegs ma mx -> agree_on rsegs L' ma mx).
{ intros A' L' ma mda mx HPx MUx WMx. eapply (agree_of_munch rsegs); [exact MUx | exact WMx |]. intros b bk Hb. cbn.
pose proof (heap_blk S4L HIx _ _ _ _ b bk HPx Hb) as (_ & _ & _ & Hbhi & _). unfold_consts. lia. }

assert (CELLW : forall (A' : AS S4L HIx) L' ma mda mx, HEAPx A' (BS ++ L') ma mda -> jc_glob_P ma -> heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 ma ->
incl LB L' -> munch [(bv_unsigned sp - 104, bv_unsigned sp - 96)] ma mx -> wmono rsegs ma mx -> mem_inv rsegs mx ->
HEAPx A' (BS ++ L') mx mda /\ jc_glob_P mx /\ heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mx /\ agree_on rsegs (BS ++ L') ma mx).
{ intros A' L' ma mda mx HPx Gx PRx HiL MUx WMx MIx. split; [| split; [| split]].
- eapply (heap_frame S4L HIx); [exact HPx | | exact WMx | exact MIx]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HPx MUx). solve_frameW_with HPx.
- eapply jc_glob_P_outside; [exact Gx | exact MUx | exact WMx |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
- eapply presxD_trans; [exact PRx|]. eapply presxD_of_munch; [exact MUx | exact WMx |]. intros b Hb Hc Hd.
eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HPx | | clia | solve_clientW S4L HIx HPx | exact Hb | exact Hc].
intros bb Hbb. apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [apply in_or_app; left; exact Hbb | apply in_or_app; right; apply HiL; exact Hbb].
- eapply AGB; [exact HPx | exact MUx | exact WMx]. }
assert (HiAL : incl AL (BS ++ CBS ++ REM ++ LB)) by (rewrite EBS; incl_tac).
apply rz_evt; [exact MOK|].
step. stepz. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HALx : alist rsegs S4F mx AL a ps) by (eapply (alist_agree rsegs S4F); [exact HAL | eapply AGB; [exact HP | exact MU | exact WM] | exact HiAL]) end.
call (array_list_get_idx_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ AL a ps (Z.of_nat ii));
[ exact MI | exact HALx | reflexivity | reflexivity | lia | ].
replace (Z.of_nat ii <? Z.of_nat (length ps)) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
try rename MI0 into MI.
set (v := al_nth ps (Z.of_nat ii)) in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : munch _ mc m1 |- _ => rename H into MU1 end.
match goal with H : wmono rsegs mc m1 |- _ => rename H into WM1 end.

unstash OPB. unstash KIDS. unstash JQ. unstash JOB. unstash G.
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ m1 HP G PRES ltac:(incl_tac) MU1 WM1 MI) as (HP1 & G1 & PRES1 & AG1).
assert (Hibs : incl bs BS).
{ rewrite EBS. intros b Hb. apply in_or_app; left. right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb]. }
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG1 ltac:(rewrite EBS; incl_tac)) as OPB1.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL AG1 HiAL) as HAL1.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS AG1 ltac:(rewrite EBS; incl_tac)) as KIDS1.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ JQ AG1 ltac:(incl_tac)) as JQ1.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG1 ltac:(intros b Hb; apply in_or_app; left; apply Hibs; exact Hb)) as JOB1.
clear OPB HAL KIDS JQ JOB G AG1 HP MOK. try clear MU. try clear WM.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK.
pose proof (wmono_refl rsegs m1) as WM. pose proof (munch_refl [(bv_unsigned sp - 104, bv_unsigned sp - 96)] m1) as MU.

assert (AADD : forall (x1' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : Model) (A2 : AS S4L HIx) (jso : Z) (vs : option jshape) (VBS REM2 : list blk) (e2 : word),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs m2 (bv_unsigned sp + -112) [CB 8 jk] -> rw_cells rsegs m2 (bv_unsigned sp + -104) [C8 (wz jso)] -> rw_cells rsegs m2 482764 [C4 e2] ->
HEAPx A2 (VBS ++ BS ++ CBS ++ REM2 ++ LB) m2 md2 ->
opt_pbuf rsegs m2 PBS pb -> rw_cells rsegs m2 p [C4 (wz JT_ARRAY); C4 (wz 1); C8 (wz (fn_arr_to_json_string S4F)); C8 (wz pb); C8 (wz 0); C8 (wz 0); C8 (wz a)] ->
alist rsegs S4F m2 AL a ps -> akids rsegs S4F m2 kids ps KBS ->
rw_cells rsegs m2 D [C8 (wz q)] -> jval rsegs S4F (Sarr kids') m2 CBS q 1 ->
jopt rsegs S4F vs m2 VBS jso -> odep vs <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1' (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0' t1' t2' (wz p) (wz D) a0' (wz jso) a2' a3' a4' a5' a6' a7'
(wz SH_ENTRY_P) (wz 1) (wz (Z.of_nat (length kids))) (wz (Z.of_nat ii)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F2 (wz 0x25ac0) fc2 None m2 (seg_rom rsegs)) md2) T).
{ intros until e2. intros INV2 FS2 FRM2 FRJ2 CELL2 ERR2 HP2 OPB2 HDR2 HAL2 KIDS2 DC2 JQ2 JOB2 ODEP.
pose proof INV2 as (VM2 & PRES2 & ST2 & FR2 & G2). unfold Qzop.dc_frame in FR2.
destruct (sarr_open rsegs S4F _ _ _ _ _ JQ2) as (pbq & PBSq & aq & ALq & psq & KBSq & EBSq & OPBq & HDRq & HALq & Lq1 & Lq2 & KIDSq).
pose proof HALq as (arrq & sizeq & ajunk & EALq & Hlenq & Hszq & _). subst ALq.
set (LBR := VBS ++ BS ++ ((q, 48) :: concat KBSq ++ PBSq) ++ REM2 ++ LB).
assert (HPa : HEAPx A2 ((aq, 32) :: (arrq, 8 * sizeq) :: LBR) m2 md2) by (eapply (heap_perm S4L HIx); [exact HP2 | unfold LBR; rewrite EBSq; perm]).
assert (HiBS : incl BS LBR) by (unfold LBR; incl_tac).
assert (HiV : incl VBS LBR) by (unfold LBR; incl_tac).
assert (INq : In (q, 48) LBR) by (unfold LBR; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
pose proof (jopt_val rsegs S4F S4L HIx _ _ _ _ vs VBS jso HPa ltac:(intros b Hb; right; right; apply HiV; exact Hb) JOB2) as [Hj0 Hj1].
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hj1.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HPa ltac:(right; right; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
unfold jhdr_cells in HDRq. cbn [app] in HDRq.
pose proof (heap_model_ok _ _ _ _ _ _ HPa) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HPa) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [] m2) as MU2.
stash OPB2. stash HAL2. stash KIDS2. stash JOB2. stash OPBq. stash KIDSq. stash G2. stash HALq.
apply rz_evt; [exact MOK2|].
step. step. step.
unstash OPB2. unstash HAL2. unstash KIDS2. unstash JOB2. unstash OPBq. unstash KIDSq. unstash G2. unstash HALq.

apply evt_RZ_done.
eapply (array_list_add_cps HIx _ _ gp _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 F2 fc2 m2 md2 LBR lo aq arrq sizeq jso psq T);
[ exact HPa | exact HALq | lia | rewrite unsigned_lit by lia; exact ST2 | clia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR2 | rewrite unsigned_lit by lia; reflexivity | reflexivity | reflexivity | ].
intros ms4 md4 (m4 & A4 & rr & e4 & arr' & size' & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
assert (AG4 : agree_on rsegs LBR m2 m4) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | apply incl_refl]).
assert (PRES4 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m4).
{ eapply presxD_trans; [exact PRES2|]. apply pres_presxD. eapply heap_pres_weaken; [exact HPR4 | lia | unfold LBR; incl_tac]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR2; [| left; cbn; lia]. cbn [hl_segs S4L] in FR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FRJ2; [| left; cbn; lia]. cbn [hl_segs S4L] in FRJ2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in CELL2; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in DC2; [| left; cbn; lia]. cbn [hl_segs S4L] in DC2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDRq; [| eapply client_range_block; [exact INq | lia | cbn; lia]]. cbn [hl_segs S4L] in HDRq.
pose proof (rw_cells_agree rsegs _ _ _ _ _ HDR2 AG4 ltac:(exists p, 48; split; [apply HiBS; exact INp | cbn; lia])) as HDR4.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB2 AG4 ltac:(intros b Hb; apply HiBS; rewrite EBS; in_find Hb)) as OPB4.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL2 AG4 ltac:(intros b Hb; apply HiBS; rewrite EBS; in_find Hb)) as HAL4.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS2 AG4 ltac:(intros b Hb; apply HiBS; rewrite EBS; in_find Hb)) as KIDS4.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB2 AG4 HiV) as JOB4.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPBq AG4 ltac:(unfold LBR; incl_tac)) as OPBq4.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDSq AG4 ltac:(unfold LBR; incl_tac)) as KIDSq4.
pose proof (jc_glob_P_pres _ _ _ _ HPR4 G2) as G4.
apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL2; [| cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
clear HDR2 OPB2 HAL2 KIDS2 JOB2 OPBq KIDSq G2 HPa HP2 MOK2 MI2 WM2 MU2. try clear MI MU WM MOK.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m4) as WM. pose proof (munch_refl [] m4) as MU.
stash OPB4. stash HAL4. stash KIDS4. stash JOB4. stash OPBq4. stash KIDSq4. stash G4. stash OUT4.
reenter MOK4.
unstash OUT4.
destruct OUT4 as [(-> & -> & -> & ALq4) | (-> & ALq4 & _)].
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_true. step. step.
unstash OPB4. unstash HAL4. unstash KIDS4. unstash JOB4. unstash OPBq4. unstash KIDSq4. unstash G4.
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := Sarr kids') (CBS := CBS) (CBSc := VBS) (REM := REM2); dc_hyps.
all: first [ exact CELL2 | exact FRJ2 | exact ERR4 | exact DC2 | exact Hq
| eapply fsaved_trans; [exact FS2 | exact FS4] | apply FRM4; exact FRM2
| eapply (heap_perm S4L HIx); [exact HP4 | unfold LBR; rewrite EBSq; perm]
| split; [eapply model_vm_only_trans; [exact VM2 | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR2 | exact G4]]]]
| idtac ].
+ eapply (sarr_close rsegs S4F) with (AL := [(aq, 32); (arrq, 8 * sizeq)]) (KBS := KBSq) (PBS := PBSq) (pb := pbq); try eassumption; try reflexivity.
unfold jhdr_cells. cbn [app]. exact HDRq.
+ destruct vs as [s''|]; cbn [jopt] in JOB4.
* right; left. destruct JOB4 as [Hj J4]. split; [exact Hj | exists s''; exact J4].
* left. exact JOB4.
-
step. if_false. step. step.
unstash OPB4. unstash HAL4. unstash KIDS4. unstash JOB4. unstash OPBq4. unstash KIDSq4. unstash G4.
set (CBS' := ((q, 48) :: [(aq, 32); (arr', 8 * size')] ++ concat (KBSq ++ [VBS])) ++ PBSq).
assert (JQ4 : jval rsegs S4F (Sarr (kids' ++ [vs])) m4 CBS' q 1).
{ eapply (sarr_close rsegs S4F) with (ps := psq ++ [jso]); try reflexivity.
+ exact OPBq4.
+ unfold jhdr_cells. cbn [app]. exact HDRq.
+ exact ALq4.
+ rewrite !length_app. cbn [length]. lia.
+ rewrite !length_app. cbn [length]. lia.
+ apply akids_app; [exact KIDSq4 | apply akids_one; exact JOB4]. }
assert (HP4' : HEAPx A4 (BS ++ CBS' ++ REM2 ++ LB) m4 md4).
{ eapply (heap_perm S4L HIx); [exact HP4 |]. unfold CBS', LBR. rewrite concat_app. cbn [concat]. rewrite app_nil_r. perm. }
assert (OK4 : okmax (kids' ++ [vs]) <= okmax kids) by (rewrite okmax_app, okmax_single; lia).
destruct (Nat.eq_dec (S ii) (length kids)) as [Hlast | Hmore].
+
if_falsex.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in HDR4 as X. destruct X as [HDR6 _].
apply evt_RZ_done.
eapply (dc_tail0 HIx) with (d := JRtree (Sarr (kids' ++ [vs]))) (CBS := CBS') (REM := REM2) (np := 48); dc_hyps.
all: first [ exact CELL2 | exact FRJ2 | exact ERR4 | exact HP4' | exact INp | exact HDR6 | exact DC2 | exact Hq
| eapply fsaved_trans; [exact FS2 | exact FS4] | apply FRM4; exact FRM2
| split; [eapply model_vm_only_trans; [exact VM2 | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR2 | exact G4]]]]
| idtac ].
* cbn [copy_of]. eexists. split; [reflexivity|]. rewrite !sdepth_Sarr. lia.
* cbn [jroot_rep]. split; [exact Hq | exact JQ4].
+
if_truex.
replace (Z.of_nat ii + 1) with (Z.of_nat (S ii)) by lia.
apply evt_RZ_done.
eapply (IHn (S ii)) with (kids' := kids' ++ [vs]) (CBS := CBS') (REM := REM2); try first [ exact CELL2 | exact FRJ2 | exact ERR4 | exact HP4' | exact EBS | exact OPB4 | exact HDR4 | exact HAL4 | exact L1 | exact L2 | exact KIDS4 | exact Hq | exact DC2 | exact JQ4 | exact OK4 ].
* lia.
* lia.
* split; [eapply model_vm_only_trans; [exact VM2 | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR2 | exact G4]]]].
* eapply fsaved_trans; [exact FS2 | exact FS4].
* apply FRM4; exact FRM2.
* rewrite length_app. cbn [length]. lia. }

step.
destruct k as [s'|].
-
destruct JOB1 as [Hv J'].
destruct (jval_root_in rsegs S4F _ _ _ _ _ J') as (nv & INv & Hnv).
assert (INv1 : In (v, nv) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; apply Hibs; exact INv).
pose proof (heap_blk S4L HIx _ _ _ _ v nv HP1 INv1) as (_ & Hval & Hvlo & Hvhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi.
if_falsex. step. step. step. step. step. step.
replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia.

pose proof (concat_nth_split KBS ii bs Hbs) as EK.
set (LBc := ((p, 48) :: AL ++ concat (firstn ii KBS) ++ concat (skipn (S ii) KBS)) ++ PBS ++ CBS ++ REM ++ LB).
assert (PERMc : Permutation (BS ++ CBS ++ REM ++ LB) (bs ++ LBc)) by (unfold LBc; rewrite EBS, EK; perm).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ m2 HP1 G1 PRES1 ltac:(incl_tac) MU WM MI) as (HP2 & G2 & PRES2 & AG2).
pose proof (kdepth_in kids s' (nth_error_In _ _ Hk)) as DEP.
assert (OKK : okmax kids = kdepth kids) by (pose proof (sdepth_Sarr kids); pose proof (sdepth_arr kids); lia).
apply evt_RZ_done.
pose proof (IH s' (nth_error_In _ _ Hk)) as REC. unfold dcopy_spec in REC.
eapply REC with (BS := bs) (LB := LBc) (lo := lo) (p := v) (D := bv_unsigned sp + -104); clear REC;
[ eapply (heap_perm S4L HIx); [exact HP2 | exact PERMc]
| cbn [jroot_rep]; split; [exact Hv | eapply (jval_agree rsegs S4F); [exact J' | exact AG2 | intros b Hb; apply in_or_app; left; apply Hibs; exact Hb]]
| discriminate | exact G2 | exact CELL
| rewrite unsigned_lit by lia; lia | lia | apply mod16_mod8; [exact SPA | reflexivity]
| rewrite unsigned_lit by lia; exact ST | clia
| rewrite unsigned_lit by lia; cbn [rdepth]; unfold dc_stk, REC_P, DC_C; pose proof (sdepth_nonneg s'); nia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | exact FRM1 | reflexivity | reflexivity | reflexivity | ].
intros ms3 md3 m3 rv3 (RS3 & VM3 & ST3 & HPR3 & [e3 ERR3]) G3 JR3 RES3.
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp hl_volatile S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR3 by lia.

assert (PRES3 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m3).
{ eapply presxD_trans; [exact PRES2|]. apply presx_presxD.
eapply heap_presx_weaken; [eapply (presxD_presx S4L HIx) with (SP' := bv_unsigned sp); [exact HPR3 | eapply (heap_perm S4L HIx); [exact HP2 | exact PERMc] | apply incl_refl | lia | lia | clia] | lia | | intros b Xb; exact Xb].
intros b Hb. apply (Permutation_in _ PERMc). apply in_app_or in Hb; destruct Hb as [Hb|Hb]; in_find Hb. }
assert (AG3 : agree_on rsegs (BS ++ CBS ++ REM ++ LB) m2 m3).
{ eapply (presxD_agree S4L HIx); [exact HPR3 | eapply (heap_perm S4L HIx); [exact HP2 | exact PERMc] | | apply incl_refl | clia].
intros b Hb. apply (Permutation_in _ PERMc). exact Hb. }
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia | cbn; lia].
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in FRJ; [| left; cbn; lia | cbn; lia].
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia | cbn; lia].
cbn [hl_segs S4L] in FR, FRJ, DC.
pose proof (rw_cells_agree rsegs _ _ _ _ _ HDR AG3 ltac:(exists p, 48; split; [exact INp1 | cbn; lia])) as HDR3.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB1 AG3 ltac:(rewrite EBS; incl_tac)) as OPB3.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL1 AG3 HiAL) as HAL3.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS1 AG3 ltac:(rewrite EBS; incl_tac)) as KIDS3.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ JQ1 AG3 ltac:(incl_tac)) as JQ3.
clear HDR OPB1 HAL1 KIDS1 JQ1 CELL MU WM MI MOK HP1 G1 PRES1 PRES2 AG2 G2 J'.
pose proof (wmono_refl rsegs m3) as WM. pose proof (munch_refl [] m3) as MU.
stash JR3. stash OPB3. stash HAL3. stash KIDS3. stash JQ3. stash G3.
destruct RES3 as [(-> & A3 & d3 & q3 & CBS3 & REM3 & CO3 & Hq3 & CELL3 & JD3 & HP3) | (-> & A3 & q3 & CBS3 & REM3 & CELL3 & FRES3 & HP3)]; cbn [hl_segs S4L] in CELL3.
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
stash JD3. stash CO3.
reenter MOK3.
step. step. if_true.
unstash JD3. unstash CO3. unstash JR3. unstash OPB3. unstash HAL3. unstash KIDS3. unstash JQ3. unstash G3.
destruct CO3 as (s3' & -> & DEP3). cbn [jroot_rep] in JD3.
apply evt_RZ_done.
eapply (AADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 q3 (Some s3') CBS3 (REM3 ++ REM) e3);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]]
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1
| exact FRJ | exact CELL3 | exact ERR3 | eapply (heap_perm S4L HIx); [exact HP3 | unfold LBc; rewrite EBS, EK; perm]
| exact OPB3 | exact HDR3 | exact HAL3 | exact KIDS3 | exact DC | exact JQ3 | exact JD3 | cbn [odep]; lia ].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
stash FRES3.
reenter MOK3.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step. if_false. step. step.
unstash FRES3. unstash JR3. unstash JQ3. unstash G3.
apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz q3))]) in CELL3; [| cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := Sarr kids') (CBS := CBS) (CBSc := CBS3) (REM := REM3 ++ REM); dc_hyps.
all: first [ exact CELL3 | exact FRJ | exact ERR3 | exact DC | exact Hq | exact JQ3 | exact FRES3
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1
| eapply (heap_perm S4L HIx); [exact HP3 | unfold LBc; rewrite EBS, EK; perm]
| split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]] ].
-
destruct JOB1 as [Ev Ebs]. rewrite Ev. if_true. step. stepz.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ mx HP1 G1 PRES1 ltac:(incl_tac) MU WM MI) as (HP2 & G2 & PRES2 & AG2) end.
eapply (AADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ mdc A 0 None [] REM e);
[ split; [exact VM | split; [exact PRES2 | split; [exact ST | split; [exact FR | exact G2]]]] | exact FS | exact FRM1
| exact FRJ | exact CELL | exact ERR | cbn [app]; exact HP2 | | exact HDR | | | exact DC | | split; reflexivity | cbn; exact OK0 ].
+ eapply (opt_pbuf_agree rsegs); [exact OPB1 | exact AG2 | rewrite EBS; incl_tac].
+ eapply (alist_agree rsegs S4F); [exact HAL1 | exact AG2 | exact HiAL].
+ eapply (akids_agree rsegs S4F); [exact KIDS1 | exact AG2 | rewrite EBS; incl_tac].
+ eapply (jval_agree rsegs S4F); [exact JQ1 | exact AG2 | incl_tac].
Qed.

#[using="PUT PUTX fc LO LOS SPA HT SPD DAL NN JR0 Kont IH"] Lemma dc_arr :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q : Z) (CBS : list blk) (jk cj : list byte) (e : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
rw_cells rsegs mc (bv_unsigned sp + -112) [CB 8 jk] -> dc_cell mc cj -> rw_cells rsegs mc (0x75e70 - 164) [C4 e] ->
HEAPx A (BS ++ CBS ++ LB) mc mdc -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> scopy S4L S4F r mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -112)) gp (wz 0x75e70) t0 t1 t2 (wz p) (wz D) (wz 1) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x25970) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until e. intros INV FS FRM1 FRJ CELL ERR HP Hq DC SC. pose proof INV as (VM & PRES & ST & FR & G).
unfold Qzop.dc_frame in FR. unfold Qzop.dc_cell in CELL. pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu.
rewrite sdepth_Sarr in LOSu. pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
change (0x75e70 - 164) with 482764 in ERR.
cbn [scopy r] in SC.

destruct JR0 as [Hp J0].
assert (J : jval rsegs S4F (Sarr kids) mc BS p 1).
{ eapply (jval_agree rsegs S4F); [exact J0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [exact PRES | exact HP | incl_tac | incl_tac | clia]. }
clear J0.
destruct (sarr_open rsegs S4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INp1 : In (p, 48) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
assert (Hlen : Z.of_nat (length kids) < 2^64).
{ destruct HAL as (arr & size & junk & EAL & Hl & Hsz & _). lia. }
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash OPB. stash KIDS. stash SC. stash G.
apply rz_evt; [exact MOK|].
step. step. step. if_true.
step. step.

call (array_list_length_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ AL a ps);
[ exact MI | exact HAL | reflexivity | ].
try rename MI0 into MI. rewrite L1.
unstash OPB. unstash KIDS. unstash SC. unstash G.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : munch [] mc m1 |- _ => rename H into MU1 end. match goal with H : wmono rsegs mc m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPx A (BS ++ CBS ++ LB) m1 mdc).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM1 | exact MI]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU1). apply Forall_nil. }
assert (G1 : jc_glob_P m1) by (eapply jc_glob_P_outside; [exact G | exact MU1 | exact WM1 | apply Forall_nil]).
assert (PRES1 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m1).
{ eapply presxD_trans; [exact PRES|]. eapply presxD_of_munch; [exact MU1 | exact WM1 | intros; exact I]. }
assert (AG1 : agree_on rsegs (BS ++ CBS ++ LB) mc m1) by (eapply (agree_of_munch rsegs); [exact MU1 | exact WM1 | intros; exact I]).
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG1 ltac:(rewrite EBS; incl_tac)) as OPB1.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL AG1 ltac:(rewrite EBS; incl_tac)) as HAL1.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS AG1 ltac:(rewrite EBS; incl_tac)) as KIDS1.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ SC AG1 ltac:(incl_tac)) as SC1.
clear OPB HAL KIDS SC G PRES HP AG1.
step.
destruct (Nat.eq_dec (length kids) 0) as [L0 | L0].
-
rewrite L0. if_true.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in HDR as X. destruct X as [HDR6 _].
apply evt_RZ_done.
eapply (dc_tail0 HIx) with (d := JRtree (Sarr [])) (CBS := CBS) (REM := []) (np := 48); dc_hyps.
all: first [ exact CELL | exact FRJ | exact ERR | exact INp | exact HDR6 | exact DC | exact Hq | exact FS | exact FRM1
| eapply (heap_perm S4L HIx); [exact HP1 | perm]
| split; [exact VM | split; [exact PRES1 | split; [exact ST | split; [exact FR | exact G1]]]]
| idtac ].
+ cbn [copy_of]. eexists. split; [reflexivity|]. rewrite !sdepth_Sarr. cbn. lia.
+ cbn [jroot_rep]. split; [exact Hq | exact SC1].
-
if_falsex. step. step.
apply evt_RZ_done.
replace (wz 0) with (wz (Z.of_nat 0)) by reflexivity.
eapply (dc_arr_loop (length kids) 0) with (kids' := []) (CBS := CBS) (REM := []);
try first [ exact CELL | exact FRJ | exact ERR | exact EBS | exact OPB1 | exact HDR | exact HAL1 | exact L1 | exact L2 | exact KIDS1 | exact Hq | exact DC | exact SC1 | exact FS | exact FRM1 ].
+ lia.
+ lia.
+ split; [exact VM | split; [exact PRES1 | split; [exact ST | split; [exact FR | exact G1]]]].
+ eapply (heap_perm S4L HIx); [exact HP1 | perm].
+ reflexivity.
+ cbn. exact OK0.
Qed.
End DcArr.

End RC__1.
