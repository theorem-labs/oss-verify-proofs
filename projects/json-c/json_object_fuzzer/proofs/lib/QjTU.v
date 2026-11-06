(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QCcH QbFI Qwm6 QZsi QYZ0 QSui Q8zf QEoy Q9O6 QnPO QUZl QGeV Qfya Qy5Y QXEH QkLq QFqQ Q9kF Qsn5 Q2ui QCUT Q0Do QoSL QMow QlES QJBH QQIi Q6sh QQwg QvDJ QzgH Q7z8 QKTr QgTJ QCrt QmAH QcGV QNLn QtIP QU91 QBzu QmCP QPUe QrOY QdSl QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QHqi Qb5q Qi08 Q79p Qvjf QkIR QhR3 QZzg Q61C QWRO QFQR QWwJ Q4I1 Qx84 Qv81 Q6w1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 Q2ui.

Import QlES.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.
Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QHqi Qb5q.Mq2.

Import QWwJ Q4I1 Qx84.Mq0 Qv81.Mq1.

Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition B0J : QZsi.bud := QZsi.Bud 243520921600 (2^30) 15900 9 (2^28).

Lemma DPN_CHECKS : forall w ch, HSCLASS_S w ch -> Q6w1.kn_rw_cells (kn_view ch) QWRO.DP_N [QMow.C4 (Z_to_bv 64 1)] = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.
Lemma GRPWR_CHECKS : forall w ch, HSCLASS_S w ch ->
kn_has (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar (fst (GRP_O w)))) 0) (ELit 4096)) (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Heap.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
#[local] Notation LV := (LV_J E).
#[local] Notation m := (view LV mo FULL).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Instance BANDH : Band := QBzu.Band_RC Q6q3.rc_canary.
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL) (only parsing).
#[local] Notation REJ := (REJ sp E w).
#[local] Notation MTB := (MTBJ E w).
#[local] Notation FR0 := (FR0J E w).

Definition GRPJ : Z := GRPB E w.
Definition LM0J : list QCcH.blk := [(GRPJ + 64, 40)].
Definition FRJ : list (Z * Z) := (GRPJ, GRPJ + 4096) :: FR0.

Lemma GRPJ_pg : GRPJ = pg E (fst (GRP_O w)).  Proof. reflexivity. Qed.
Lemma grp_facts : GRPJ mod 4096 = 0 /\ 0 < GRPJ /\ (GRPJ + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= GRPJ)
/\ (GRPJ + 4096 <= 0x10000 \/ 0x647000 <= GRPJ) /\ GRPJ + 4096 <= atopE E.
Proof.
pose proof ((LA obj_facts) (GRP_O w) (GRP_O_in w)) as (F1 & F2 & _ & F4 & F5 & F6).
assert (SZ : snd (GRP_O w) = 4096) by (destruct w; reflexivity). rewrite SZ in *. unfold GRPJ, GRPB. tauto.
Qed.

Lemma FRJ_in : forall r, In r FRJ -> fst r < snd r /\
(   (pg E (fst (GRP_O w)) <= fst r /\ snd r <= pg E (fst (GRP_O w)) + snd (GRP_O w))
\/ (pg E (fst (META_O w)) <= fst r /\ snd r <= pg E (fst (META_O w)) + snd (META_O w))).
Proof.
intros r [<-|[<-|[]]]; cbn [fst snd].
- split; [lia|]. left. rewrite <- GRPJ_pg. replace (snd (GRP_O w)) with 4096 by (destruct w; reflexivity). lia.
- split; [lia|]. right. unfold MTBJ. replace (snd (META_O w)) with 8192 by (destruct w; reflexivity). lia.
Qed.

Lemma depot_main_hidden : QCrt.depot_n QZzg.asegs QBzu.DL_AR (QQIi.mrestrict (QgTJ.Mq1.Fof LV FRJ) m) 1.
Proof.
split; [|lia].
pose proof (Q6w1.kn_rw_cells_sound E m (kn_view ch) _ _ (MV4 main_know_view) (DPN_CHECKS w ch HCL)) as RW.
refine (QJBH.rw_cells_agree QZzg.asegs (fun a => 0x10000 <= a < 0x647000) m _ _ _ _ RW _).
- apply QmCP.agree_hide. intros x Hx Px.
apply (zone_misses_F sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL FRJ FRJ_in 0x10000 0x637000 x);
try reflexivity; try lia; [| left; unfold QFQR.in_iv; cbn [fst snd]; lia].
intros B [-> | ->].
+ pose proof ((LA obj_facts) _ (GRP_O_in w)) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
+ pose proof ((LA obj_facts) _ (META_in w ch HCL)) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
- intros a Ha. cbn [QMow.cells_size QMow.csize Nat.add] in Ha. unfold QWRO.DP_N in Ha. lia.
Qed.

Lemma grp_mapped : forall x, GRPJ <= x < GRPJ + 4096 -> m (QCUT.wa x) <> None.
Proof.
intros x Hx. destruct grp_facts as (G1 & G2 & G3 & G4 & G5). pose proof (MA main_atop_bounds) as AB.
destruct (Q6w1.kn_wr_some E m (kn_view ch) (MV4 main_know_view) (EMd Instr.M_MUL (ELit 4096) (EVar (fst (GRP_O w)))) 0 4096 GRPJ
(GRPWR_CHECKS w ch HCL) eq_refl ltac:(lia) ltac:(lia) x ltac:(lia) ltac:(lia)) as (b & Hb).
rewrite Hb. discriminate.
Qed.

Theorem HH_core : forall (s : QGeV.PState) (BLK0 : Qy5Y.Mq4.block) (Lg0 : Qfya.mled) (ms0 : machine_state),
ms_mem ms0 = FULL ->
QkLq.Mq4.RHEAP s [BLK0] m -> Q9kF.HSIM s Lg0 [BLK0] ->
Qfya.ld_live Lg0 = [(1%N, 64)] -> Qfya.ld_resv Lg0 = QXEH.ref_reserved -> Qfya.ld_groups Lg0 = [(GRPJ, 4096)] ->
((Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTB, 8192)) \/ (Qfya.ld_metas Lg0 = [(MTB, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None)) ->
QtIP.zblk BLK0 = (GRPJ + 64, 40) -> Qy5Y.Mq4.blk_slot BLK0 = (1%N, 64) -> QSui.cntm (QGeV.ps_m s) = 97 ->
QU91.Mq0.handoff_heap Qwm6.Mq4.A4L LV (PERM0_J E w) Qi08.TMAX_J Qi08.NMAX_J (@QBzu.DL_AR (QBzu.Band_RC Q6q3.rc_canary)) REJ (QBzu.DCo_jo Q6q3.rc_canary LV)
FR0 QrOY.MJ.S_AJU (BAUXJ sp) (QPUe.STAT_A Qwm6.Mq4.A4L (BOTJ sp E) (TOPJ sp) QrOY.jo_STATC) (QZsi.bM B0J) LM0J B0J (mkCfg ms0 mo).
Proof.
intros s BLK0 Lg0 ms0 Hms0 HRH HSIM HL HR HG HM HZB HSL HCNT.
destruct grp_facts as (G1 & G2 & G3 & G4 & G5). pose proof (MA main_atop_bounds) as AB. pose proof (MV4 atop_val) as AV.
assert (HRC : Q6q3.alloc_ceiling = atopE E) by exact HCEIL.
pose proof (Q79p.Mq0.KLA_main_mng sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS Lg0 (QvDJ.mkG [] 0) ms0
HRC Hms0 HR HG HM eq_refl (Z.le_refl 0)) as KLA.
assert (EFR : QtIP.FRof FR0 Lg0 = FRJ) by (unfold QtIP.FRof; rewrite HG; reflexivity).
unfold QU91.Mq0.handoff_heap, QtIP.HEAPA1. cbn [cfg_model cfg_ms]. rewrite (msview_mem LV mo ms0), Hms0.
exists (QvDJ.mkG [] 0), Lg0, (QNLn.Mq0.in_sh GRPJ 4096), BC_J, TOT_J, 22, s, [BLK0].
rewrite EFR. pose proof KLA as KL'. destruct KL' as [k1 _ k3 k4 _ _ _ _ _ _ _ _ _].
split.
{
exists QKTr.psA_init, [], [].
split; [exact (dc_run_main_hidden sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL HCAN FRJ FRJ_in)|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact QQwg.ainv_init|]. split; [exact QvDJ.GS_init|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [exact k1|]. split; [exact k3|]. split; [exact k4|].
split; [exact (Qvjf.Mq0.drv_mem_inv sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)|].
split; [constructor|].
split.
{ intros a n x [Hin|[]] Hx. injection Hin as <- <-.
unfold QgTJ.Mq1.Fof, FRJ. cbn [existsb]. unfold QgTJ.Mq1.fr_in at 1. rewrite QCUT.wa_unsigned by lia.
replace (zin x (GRPJ, GRPJ + 4096)) with true; [reflexivity|]. unfold zin. cbn [fst snd]. symmetry. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; lia|].
split; [exists 1; split; [exact depot_main_hidden| apply Z.leb_le; vm_compute; reflexivity]|].
split.
{ destruct (MV4 topp_val) as (TV & _).
pose proof (QhR3.Mq0.stk_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) as ST.
rewrite TV in ST. rewrite <- AV in ST. rewrite <- HRC in ST. exact ST. }
split; [cbn; lia| vm_compute; discriminate]. }
split; [exact KLA|].
split; [cbn; lia|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity|].
split.
{
intros r y Hr Hy. unfold QtIP.in_regs, FR0J. cbn [existsb]. rewrite orb_false_r. unfold zin. cbn [fst snd].
unfold QYZ0.doranges in Hr.
destruct HM as [[HM1 HM2]|[HM1 HM2]]; rewrite HM1, HM2 in Hr; cbn [map app In fst snd] in Hr; destruct Hr as [<-|[]]; cbn [fst snd] in Hy;
change (QUZl.round_up_pg 8192) with 8192 in Hy; unfold QUZl.PGSZ in Hy; apply andb_true_intro; (split; [apply Z.leb_le| apply Z.ltb_lt]); lia. }
split.
{
intros a n [Hin|[]]. injection Hin as <- <-. split.
- unfold QYZ0.mrange. cbn [QrOY.MJ.S_AJU QYZ0.mg_img_lo QYZ0.mg_img_hi]. unfold QrOY.MJ.AJU_IMG_HI. rewrite HRC.
split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia.
- intros x Hx. split; [|apply grp_mapped; lia].
unfold QtIP.in_regs, FRJ. cbn [existsb]. rewrite QCUT.wa_unsigned by lia.
replace (zin x (GRPJ, GRPJ + 4096)) with true; [reflexivity|]. unfold zin. cbn [fst snd]. symmetry. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
split; [cbn [map LM0J]; rewrite HZB; apply Permutation_refl|].
split; [exact HRH|].
split; [exact HSIM|].
split; [rewrite HL; cbn [map]; rewrite HSL; apply Permutation_refl|].
split; [rewrite HL; constructor; [intros []| constructor]|].
split. { constructor; [|constructor]. unfold QtIP.zblk in HZB. injection HZB as _ ->. lia. }
split. { split; [constructor; exact I|]. unfold BAUXJ. rewrite HRC. lia. }
split; [rewrite HCNT; cbn; lia|].
split; [constructor|].
exact (QkIR.Mq0.stat_main2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCAN).
Qed.
End Heap.

Lemma blk0_A : forall sec resv b g, QtIP.zblk (Q9O6.Mq3.BLK0_A sec resv b g) = (g + 64, 40) /\ Qy5Y.Mq4.blk_slot (Q9O6.Mq3.BLK0_A sec resv b g) = (1%N, 64).
Proof. intros. split; reflexivity. Qed.
Lemma blk0_B : forall sec resv b g, QtIP.zblk (QnPO.Mq2.BLK0_B sec resv b g) = (g + 64, 40) /\ Qy5Y.Mq4.blk_slot (QnPO.Mq2.BLK0_B sec resv b g) = (1%N, 64).
Proof. intros. split; reflexivity. Qed.
Lemma cntm_A : forall sec resv b g, QSui.cntm (QUZl.strip (Q8zf.ST0_A sec resv b g)) = 97.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma cntm_B : forall sec resv b g, QSui.cntm (QUZl.strip (QEoy.ST0_B sec resv b g)) = 97.
Proof. intros. vm_compute. reflexivity. Qed.

Theorem HH_main : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
(E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model) (w : bool) (ch : acs) (HCL : HSCLASS_S w ch)
(CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo)
{RC__ : Q6q3.RunConsts},
Q6q3.rc_ceil = atopE E -> Q6q3.rc_canary = ev E 45 -> Z_to_bv 64 Q6q3.rc_secret = edenot E (EBlob false 25 8 8) ->
forall ms0 : machine_state, ms_mem ms0 = FULL ->
QU91.Mq0.handoff_heap Qwm6.Mq4.A4L (LV_J E) (PERM0_J E w) Qi08.TMAX_J Qi08.NMAX_J (@QBzu.DL_AR (QBzu.Band_RC Q6q3.rc_canary)) (REJ sp E w)
(QBzu.DCo_jo Q6q3.rc_canary (LV_J E)) (FR0J E w) QrOY.MJ.S_AJU (BAUXJ sp) (QPUe.STAT_A Qwm6.Mq4.A4L (BOTJ sp E) (TOPJ sp) QrOY.jo_STATC)
(QZsi.bM B0J) (LM0J E w) B0J (mkCfg ms0 mo).
Proof.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w. destruct w; intros ch HCL CS RC__ HCEIL HCAN HSEC ms0 Hms0.
-
set (s := QGeV.mkPS (QUZl.strip (Q8zf.ST0_A Q6q3.rc_secret QXEH.ref_reserved (4096 * bv_unsigned (ev E 5)) (4096 * bv_unsigned (ev E 423)))) (4096 * bv_unsigned (ev E 5) + 8192) tt tt).
destruct (Qvjf.Mq3.mng_main_A sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo ch HCL CS HSEC HCAN HCEIL s eq_refl eq_refl)
as (Lg0 & HRH & HSIM & HL & HR & HG & HM1 & HM2).
destruct (blk0_A Q6q3.rc_secret QXEH.ref_reserved (4096 * bv_unsigned (ev E 5)) (4096 * bv_unsigned (ev E 423))) as (HZB & HSL).
exact (HH_core sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo true ch HCL CS HCEIL HCAN s _ Lg0 ms0 Hms0 HRH HSIM HL HR HG
(or_introl (conj HM1 HM2)) HZB HSL (cntm_A _ _ _ _)).
-
set (s := QGeV.mkPS (QUZl.strip (QEoy.ST0_B Q6q3.rc_secret QXEH.ref_reserved (4096 * bv_unsigned (ev E 423)) (4096 * bv_unsigned (ev E 424)))) 0 tt tt).
destruct (Qvjf.Mq4.mng_main_B sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo ch HCL CS HSEC HCAN HCEIL s eq_refl)
as (Lg0 & HRH & HSIM & HL & HR & HG & HM1 & HM2).
destruct (blk0_B Q6q3.rc_secret QXEH.ref_reserved (4096 * bv_unsigned (ev E 423)) (4096 * bv_unsigned (ev E 424))) as (HZB & HSL).
exact (HH_core sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo false ch HCL CS HCEIL HCAN s _ Lg0 ms0 Hms0 HRH HSIM HL HR HG
(or_intror (conj HM1 HM2)) HZB HSL (cntm_B _ _ _ _)).
Qed.

Lemma LM0J_40 : forall E w, Forall (fun b : QCcH.blk => snd b < 2^40) (LM0J E w).
Proof. intros. constructor; [cbn; lia| constructor]. Qed.
Lemma B0J_bB39 : QZsi.bB B0J + 2^23 <= 2^39.  Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma B0J_bQ0 : 0 <= QZsi.bQ B0J.  Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8zf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnPO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW7x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9kF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuLP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9gW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrOY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdSl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q92D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q92D. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb5q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb5q.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q79p. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvjf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvjf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkIR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhR3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvjf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUil. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7lu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7lu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx84.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx84. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv81.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvH0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition B0J : QZsi.bud := QZsi.Bud 243520921600 (2^30) 15900 9 (2^28).

Lemma DPN_CHECKS : forall w ch, HSCLASS_S w ch -> QvH0.kn_rw_cells (kn_view ch) QDw3.DP_N [QMow.C4 (Z_to_bv 64 1)] = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.
Lemma GRPWR_CHECKS : forall w ch, HSCLASS_S w ch ->
kn_has (KWr (SA (EMd Instr.M_MUL (ELit 4096) (EVar (fst (GRP_O w)))) 0) (ELit 4096)) (kn_view ch) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Section Heap.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
Context {RC__ : Q6q3.RunConsts}.
Hypothesis HCEIL : Q6q3.rc_ceil = atopE E.
Hypothesis HCAN : Q6q3.rc_canary = ev E 45.
#[local] Notation LV := (LV_J E).
#[local] Notation m := (view LV mo FULL).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Instance BANDH : Band := QuLP.Band_RC Q6q3.rc_canary.
#[local] Notation LA L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL) (only parsing).
#[local] Notation REJ := (REJ sp E w).
#[local] Notation MTB := (MTBJ E w).
#[local] Notation FR0 := (FR0J E w).

Definition GRPJ : Z := GRPB E w.
Definition LM0J : list QCcH.blk := [(GRPJ + 64, 40)].
Definition FRJ : list (Z * Z) := (GRPJ, GRPJ + 4096) :: FR0.

Lemma GRPJ_pg : GRPJ = pg E (fst (GRP_O w)).  Proof. reflexivity. Qed.
Lemma grp_facts : GRPJ mod 4096 = 0 /\ 0 < GRPJ /\ (GRPJ + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= GRPJ)
/\ (GRPJ + 4096 <= 0x10000 \/ 0x645000 <= GRPJ) /\ GRPJ + 4096 <= atopE E.
Proof.
pose proof ((LA obj_facts) (GRP_O w) (GRP_O_in w)) as (F1 & F2 & _ & F4 & F5 & F6).
assert (SZ : snd (GRP_O w) = 4096) by (destruct w; reflexivity). rewrite SZ in *. unfold GRPJ, GRPB. tauto.
Qed.

Lemma FRJ_in : forall r, In r FRJ -> fst r < snd r /\
(   (pg E (fst (GRP_O w)) <= fst r /\ snd r <= pg E (fst (GRP_O w)) + snd (GRP_O w))
\/ (pg E (fst (META_O w)) <= fst r /\ snd r <= pg E (fst (META_O w)) + snd (META_O w))).
Proof.
intros r [<-|[<-|[]]]; cbn [fst snd].
- split; [lia|]. left. rewrite <- GRPJ_pg. replace (snd (GRP_O w)) with 4096 by (destruct w; reflexivity). lia.
- split; [lia|]. right. unfold MTBJ. replace (snd (META_O w)) with 8192 by (destruct w; reflexivity). lia.
Qed.

Lemma depot_main_hidden : QCrt.depot_n QvG1.asegs QuLP.DL_AR (QQIi.mrestrict (QgTJ.Mq1.Fof LV FRJ) m) 1.
Proof.
split; [|lia].
pose proof (QvH0.kn_rw_cells_sound E m (kn_view ch) _ _ (MV4 main_know_view) (DPN_CHECKS w ch HCL)) as RW.
refine (QJBH.rw_cells_agree QvG1.asegs (fun a => 0x10000 <= a < 0x645000) m _ _ _ _ RW _).
- apply Q9gW.agree_hide. intros x Hx Px.
apply (zone_misses_F sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL FRJ FRJ_in 0x10000 0x635000 x);
try reflexivity; try lia; [| left; unfold QNwL.in_iv; cbn [fst snd]; lia].
intros B [-> | ->].
+ pose proof ((LA obj_facts) _ (GRP_O_in w)) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
+ pose proof ((LA obj_facts) _ (META_in w ch HCL)) as (_ & _ & _ & _ & OH & _). unfold pg. lia.
- intros a Ha. cbn [QMow.cells_size QMow.csize Nat.add] in Ha. unfold QDw3.DP_N in Ha. lia.
Qed.

Lemma grp_mapped : forall x, GRPJ <= x < GRPJ + 4096 -> m (QCUT.wa x) <> None.
Proof.
intros x Hx. destruct grp_facts as (G1 & G2 & G3 & G4 & G5). pose proof (MA main_atop_bounds) as AB.
destruct (QvH0.kn_wr_some E m (kn_view ch) (MV4 main_know_view) (EMd Instr.M_MUL (ELit 4096) (EVar (fst (GRP_O w)))) 0 4096 GRPJ
(GRPWR_CHECKS w ch HCL) eq_refl ltac:(lia) ltac:(lia) x ltac:(lia) ltac:(lia)) as (b & Hb).
rewrite Hb. discriminate.
Qed.

Theorem HH_core : forall (s : QGeV.PState) (BLK0 : Qy5Y.Mq4.block) (Lg0 : Qfya.mled) (ms0 : machine_state),
ms_mem ms0 = FULL ->
QkLq.Mq2.RHEAP s [BLK0] m -> Q9kF.HSIM s Lg0 [BLK0] ->
Qfya.ld_live Lg0 = [(1%N, 64)] -> Qfya.ld_resv Lg0 = QW7x.Mq0.ref_reserved -> Qfya.ld_groups Lg0 = [(GRPJ, 4096)] ->
((Qfya.ld_metas Lg0 = [] /\ Qfya.ld_brkreg Lg0 = Some (MTB, 8192)) \/ (Qfya.ld_metas Lg0 = [(MTB, 8192, 1)] /\ Qfya.ld_brkreg Lg0 = None)) ->
QtIP.zblk BLK0 = (GRPJ + 64, 40) -> Qy5Y.Mq4.blk_slot BLK0 = (1%N, 64) -> QSui.cntm (QGeV.ps_m s) = 97 ->
QU91.Mq0.handoff_heap Qwm6.Mq0.A4L LV (PERM0_J E w) QVyC.TMAX_J QVyC.NMAX_J (@QuLP.DL_AR (QuLP.Band_RC Q6q3.rc_canary)) REJ (QuLP.DCo_jo Q6q3.rc_canary LV)
FR0 QrOY.Mq0.MJ.S_AJ (BAUXJ sp) (QPUe.STAT_A Qwm6.Mq0.A4L (BOTJ sp E) (TOPJ sp) QrOY.Mq0.jo_STATC) (QZsi.bM B0J) LM0J B0J (mkCfg ms0 mo).
Proof.
intros s BLK0 Lg0 ms0 Hms0 HRH HSIM HL HR HG HM HZB HSL HCNT.
destruct grp_facts as (G1 & G2 & G3 & G4 & G5). pose proof (MA main_atop_bounds) as AB. pose proof (MV4 atop_val) as AV.
assert (HRC : Q6q3.alloc_ceiling = atopE E) by exact HCEIL.
pose proof (Q79p.KLA_main_mng sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS Lg0 (QvDJ.mkG [] 0) ms0
HRC Hms0 HR HG HM eq_refl (Z.le_refl 0)) as KLA.
assert (EFR : QtIP.FRof FR0 Lg0 = FRJ) by (unfold QtIP.FRof; rewrite HG; reflexivity).
unfold QU91.Mq0.handoff_heap, QtIP.HEAPA1. cbn [cfg_model cfg_ms]. rewrite (msview_mem LV mo ms0), Hms0.
exists (QvDJ.mkG [] 0), Lg0, (QNLn.Mq0.in_sh GRPJ 4096), BC_J, TOT_J, 22, s, [BLK0].
rewrite EFR. pose proof KLA as KL'. destruct KL' as [k1 _ k3 k4 _ _ _ _ _ _ _ _ _].
split.
{
exists QKTr.psA_init, [], [].
split; [exact (dc_run_main_hidden sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCEIL HCAN FRJ FRJ_in)|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact QQwg.ainv_init|]. split; [exact QvDJ.GS_init|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [exact k1|]. split; [exact k3|]. split; [exact k4|].
split; [exact (Qvjf.drv_mem_inv sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS)|].
split; [constructor|].
split.
{ intros a n x [Hin|[]] Hx. injection Hin as <- <-.
unfold QgTJ.Mq1.Fof, FRJ. cbn [existsb]. unfold QgTJ.Mq1.fr_in at 1. rewrite QCUT.wa_unsigned by lia.
replace (zin x (GRPJ, GRPJ + 4096)) with true; [reflexivity|]. unfold zin. cbn [fst snd]. symmetry. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
split; [cbn; lia|]. split; [cbn; lia|]. split; [cbn; lia|].
split; [exists 1; split; [exact depot_main_hidden| apply Z.leb_le; vm_compute; reflexivity]|].
split.
{ destruct (MV4 topp_val) as (TV & _).
pose proof (QhR3.stk_main sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) as ST.
rewrite TV in ST. rewrite <- AV in ST. rewrite <- HRC in ST. exact ST. }
split; [cbn; lia| vm_compute; discriminate]. }
split; [exact KLA|].
split; [cbn; lia|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity|].
split.
{
intros r y Hr Hy. unfold QtIP.in_regs, FR0J. cbn [existsb]. rewrite orb_false_r. unfold zin. cbn [fst snd].
unfold QYZ0.doranges in Hr.
destruct HM as [[HM1 HM2]|[HM1 HM2]]; rewrite HM1, HM2 in Hr; cbn [map app In fst snd] in Hr; destruct Hr as [<-|[]]; cbn [fst snd] in Hy;
change (QUZl.round_up_pg 8192) with 8192 in Hy; unfold QUZl.PGSZ in Hy; apply andb_true_intro; (split; [apply Z.leb_le| apply Z.ltb_lt]); lia. }
split.
{
intros a n [Hin|[]]. injection Hin as <- <-. split.
- unfold QYZ0.mrange. cbn [QrOY.Mq0.MJ.S_AJ QYZ0.mg_img_lo QYZ0.mg_img_hi]. unfold QrOY.Mq0.MJ.AJ_IMG_HI. rewrite HRC.
split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; lia.
- intros x Hx. split; [|apply grp_mapped; lia].
unfold QtIP.in_regs, FRJ. cbn [existsb]. rewrite QCUT.wa_unsigned by lia.
replace (zin x (GRPJ, GRPJ + 4096)) with true; [reflexivity|]. unfold zin. cbn [fst snd]. symmetry. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
split; [cbn [map LM0J]; rewrite HZB; apply Permutation_refl|].
split; [exact HRH|].
split; [exact HSIM|].
split; [rewrite HL; cbn [map]; rewrite HSL; apply Permutation_refl|].
split; [rewrite HL; constructor; [intros []| constructor]|].
split. { constructor; [|constructor]. unfold QtIP.zblk in HZB. injection HZB as _ ->. lia. }
split. { split; [constructor; exact I|]. unfold BAUXJ. rewrite HRC. lia. }
split; [rewrite HCNT; cbn; lia|].
split; [constructor|].
exact (QkIR.stat_main2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS HCAN).
Qed.
End Heap.

Lemma blk0_A : forall sec resv b g, QtIP.zblk (Q9O6.Mq3.BLK0_A sec resv b g) = (g + 64, 40) /\ Qy5Y.Mq4.blk_slot (Q9O6.Mq3.BLK0_A sec resv b g) = (1%N, 64).
Proof. intros. split; reflexivity. Qed.
Lemma blk0_B : forall sec resv b g, QtIP.zblk (QnPO.Mq2.BLK0_B sec resv b g) = (g + 64, 40) /\ Qy5Y.Mq4.blk_slot (QnPO.Mq2.BLK0_B sec resv b g) = (1%N, 64).
Proof. intros. split; reflexivity. Qed.
Lemma cntm_A : forall sec resv b g, QSui.cntm (QUZl.strip (Q8zf.ST0_A sec resv b g)) = 97.
Proof. intros. vm_compute. reflexivity. Qed.
Lemma cntm_B : forall sec resv b g, QSui.cntm (QUZl.strip (QEoy.ST0_B sec resv b g)) = 97.
Proof. intros. vm_compute. reflexivity. Qed.

Theorem HH_main : forall (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (fs : Fs.Fs) (uid hw : word)
(Hsp : valid_sp sp) (Hva : valid_argv argv) (Hve : valid_envp envp) (Hfit : entry_stack_fits sp argv envp)
(E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model) (w : bool) (ch : acs) (HCL : HSCLASS_S w ch)
(CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo)
{RC__ : Q6q3.RunConsts},
Q6q3.rc_ceil = atopE E -> Q6q3.rc_canary = ev E 45 -> Z_to_bv 64 Q6q3.rc_secret = edenot E (EBlob false 25 8 8) ->
forall ms0 : machine_state, ms_mem ms0 = FULL ->
QU91.Mq0.handoff_heap Qwm6.Mq0.A4L (LV_J E) (PERM0_J E w) QVyC.TMAX_J QVyC.NMAX_J (@QuLP.DL_AR (QuLP.Band_RC Q6q3.rc_canary)) (REJ sp E w)
(QuLP.DCo_jo Q6q3.rc_canary (LV_J E)) (FR0J E w) QrOY.Mq0.MJ.S_AJ (BAUXJ sp) (QPUe.STAT_A Qwm6.Mq0.A4L (BOTJ sp E) (TOPJ sp) QrOY.Mq0.jo_STATC)
(QZsi.bM B0J) (LM0J E w) B0J (mkCfg ms0 mo).
Proof.
intros sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w. destruct w; intros ch HCL CS RC__ HCEIL HCAN HSEC ms0 Hms0.
-
set (s := QGeV.mkPS (QUZl.strip (Q8zf.ST0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved (4096 * bv_unsigned (ev E 5)) (4096 * bv_unsigned (ev E 423)))) (4096 * bv_unsigned (ev E 5) + 8192) tt tt).
destruct (Qvjf.Mq1.mng_main_A sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo ch HCL CS HSEC HCAN HCEIL s eq_refl eq_refl)
as (Lg0 & HRH & HSIM & HL & HR & HG & HM1 & HM2).
destruct (blk0_A Q6q3.rc_secret QW7x.Mq0.ref_reserved (4096 * bv_unsigned (ev E 5)) (4096 * bv_unsigned (ev E 423))) as (HZB & HSL).
exact (HH_core sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo true ch HCL CS HCEIL HCAN s _ Lg0 ms0 Hms0 HRH HSIM HL HR HG
(or_introl (conj HM1 HM2)) HZB HSL (cntm_A _ _ _ _)).
-
set (s := QGeV.mkPS (QUZl.strip (QEoy.ST0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved (4096 * bv_unsigned (ev E 423)) (4096 * bv_unsigned (ev E 424)))) 0 tt tt).
destruct (Qvjf.Mq2.mng_main_B sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo ch HCL CS HSEC HCAN HCEIL s eq_refl)
as (Lg0 & HRH & HSIM & HL & HR & HG & HM1 & HM2).
destruct (blk0_B Q6q3.rc_secret QW7x.Mq0.ref_reserved (4096 * bv_unsigned (ev E 423)) (4096 * bv_unsigned (ev E 424))) as (HZB & HSL).
exact (HH_core sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo false ch HCL CS HCEIL HCAN s _ Lg0 ms0 Hms0 HRH HSIM HL HR HG
(or_intror (conj HM1 HM2)) HZB HSL (cntm_B _ _ _ _)).
Qed.

Lemma LM0J_40 : forall E w, Forall (fun b : QCcH.blk => snd b < 2^40) (LM0J E w).
Proof. intros. constructor; [cbn; lia| constructor]. Qed.
Lemma B0J_bB39 : QZsi.bB B0J + 2^23 <= 2^39.  Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma B0J_bQ0 : 0 <= QZsi.bQ B0J.  Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
