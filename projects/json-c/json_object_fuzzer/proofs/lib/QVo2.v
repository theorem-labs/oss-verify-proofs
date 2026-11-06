(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QpY2 QTVW QOJv QnRU QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QOJv.Mq3 QOJv.Mq4 QnRU.Mq7.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition ensure_fa_entry : Z := 0x420bc.
Definition ENSUREFA_STACK : Z := 448.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition efa_W (sp : Z) (c : Z) : list (Z * Z) :=
[ (sp - ENSUREFA_STACK, sp); (rl_T X + 2800, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8) ].

Definition efa_rel (a : AState) (c nf : Z) (r : bool * AState) : Prop :=
(r = (true, a) /\ 4 * nf <= c_mapped_fa (cls a c))
\/ (exists v, r = (true, set_cls c (set_mapped_fa v (cls a c)) a) /\ 4 * nf <= v <= kFreeArraySize /\ v mod kFreeArrayMapSize = 0
/\ c_mapped_fa (cls a c) < v)
\/ r = (false, a).

Definition efa_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c nf lo : Z) (m : word -> option byte) (v : Z)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (efa_W (bv_unsigned sp) c) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrimL (snd r) G RE X m' c v
/\ a0 = wz (if fst r then 1 else 0)
/\ efa_rel a c nf r.

Ltac efa_finish a' :=
lazymatch goal with |- efa_post _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?a _ ?c _ _ ?m _ _ _ (MS _ _ _ _ _ ?m' _) =>
unfold efa_post; do 16 eexists; split; [reflexivity|]; split; [reflexivity|];
let MU' := fresh "MU'" in
lazymatch goal with MU : munch _ m m', WM : wmono _ m m', RT : RTconst _ _ m, RS : RStats _ _ m, RL : rlay_ok _ _,
FWrt : Forall (rt_avoid _ _) _, FWst : Forall st_avoid _, FWc : Forall (wc_ok _ _ _) _,
HJS : hjunk m (rl_T _ + 2768) _, GNE : (forall c0, _ -> 1 <= c0 < kNumClasses), HCall : (forall c0, _ -> _ -> class_rep _ _ _ _ m c0 _) |- _ =>
assert (MU' : munch (efa_W (bv_unsigned sp) c) m m') by (unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?(proj1 (proj2 (proj2 kconsts))); exact MU);
split; [exact MU'|]; split; [exact WM|]; split; [assumption|]; split; [assumption|];
split; [eapply RTconst_munch; [exact RT| exact MU'| exact WM| exact FWrt]|];
split; [eapply RStats_munch; [exact RS| exact MU'| exact WM| exact FWst]|];
split; [eapply (RPrimL_reclose a a' _ _ _ _ m m' c _ _ _ RL HJS GNE HCall);
[ pose proof kconsts; lia | | reflexivity| intros; reflexivity| intros; lia| exact WM
| eapply agree_other_classes; [exact RL| lia| exact MU'| exact WM| exact FWc] |] |
split; [reflexivity| unfold efa_rel]]
end end.

Ltac efa_user :=
lazymatch goal with MU' : munch (efa_W _ ?c) ?m ?m', WM : wmono _ ?m ?m', PU : cr_pure _ _ ?c _, HU : cr_user _ _ _ ?m ?c, RL : rlay_ok ?RE ?X |- cr_user _ _ _ ?m' ?c =>
eapply cr_user_ext;
[ eapply cr_user_agree; [exact PU| exact HU| lia|];
eapply agree_on_of_munch; [exact MU'| exact WM|]; intros z Uz Hz;
apply (uzone_bounds RE X c z RL ltac:(lia)) in Uz; unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?(proj1 (proj2 (proj2 kconsts))); cbn [outside];
unfold SH, A_SHADOW_OFS in *; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia
| rewrite ?cls_set_cls_eq; reflexivity
| rewrite ?cls_set_cls_eq; reflexivity ]
end.

Lemma ensure_fa_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c nf lo v : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL a G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ENSUREFA_STACK ->
1 <= c < kNumClasses -> 0 <= nf < 2^40 ->
aimplT atn (ensure_fa (ae_L RE) a c nf) s
(efa_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c nf lo m v)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (ri_addr RE c)) (wz (reg_beg (ae_L RE) c)) (wz nf) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz ensure_fa_entry) fc None m (seg_rom asegs)).
Proof.
intros until v; intros RT RL RS RP MI ST CEIL LO Hc Hnf.
pose proof CEIL as CEIL'. idtac. unfold ENSUREFA_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX). rewrite K32 in Hc.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
assert (FWrt : Forall (rt_avoid RE X) (efa_W (bv_unsigned sp) c)).
{ unfold efa_W, ENSUREFA_STACK, ri_addr. rewrite ?KS.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [| constructor]. apply rt_avoid_gap; [exact RL| unfold SH, A_SHADOW_OFS; unfold prim_lo in *; Z.div_mod_to_equations; lia| rewrite ?KHI_eq; unfold SH, A_SHADOW_OFS; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia]. }
assert (FWst : Forall st_avoid (efa_W (bv_unsigned sp) c)).
{ unfold efa_W, ENSUREFA_STACK, ri_addr. rewrite ?KS.
constructor; [apply st_avoid_above; unfold A_ERRNO; lia|].

constructor; [intros x [Hx1 Hx2] KK; cbn [fst snd] in *; pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & [_ TH] & _);
cbn [fst snd] in TH; unfold A_ERRNO in *; clear - Hx1 Hx2 KK TH; lia|].
repeat (constructor; [apply st_avoid_above; unfold A_ERRNO, SH, A_SHADOW_OFS; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia|]). constructor. }
assert (FWc : Forall (wc_ok RE X c) (efa_W (bv_unsigned sp) c)).
{ unfold efa_W, ENSUREFA_STACK. rewrite ?KS.
constructor; [cbn; left; lia|]. constructor; [cbn; right; left; lia|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; exact Hz|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 2 right; left; rewrite KS; exact Hz|].
constructor; [| constructor]. cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz. do 3 right; left. split; cbn [fst snd]; rewrite ?KS; lia. }

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & P14 & _ & _ & G2 & G3 & G4 & G5).
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
rewrite ?KS, ?KM, ?KO in *.
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in *.
hide PAL. clear G5.
assert (QM : exists q, c_mapped_fa (cls a c) = 262144 * q /\ 0 <= q) by (exists (c_mapped_fa (cls a c) / 262144); unfold kFreeArrayMapSize in P14; Z.div_mod_to_equations; lia).
destruct QM as (qm & QMe & QM0). rewrite QMe in *. clear P14.
assert (KS8 : 536870912 = 8 * 67108864) by reflexivity.
rewrite KS8, SH_plus8 in FS.
assert (SFB : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo).
{ unhide PAL. rewrite FB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD.
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K c)))) = c_num_freed (cls a c)) by (rewrite length_map; exact P1).
pose proof (munch_refl (efa_W (bv_unsigned sp) c) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold efa_W, ENSUREFA_STACK, ri_addr in MU. rewrite ?KS in MU.
unfold ensure_fa_entry. rtc RT 24%nat K24. unfold A_INSTANCE in K24.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
step.
step. step.
rewrite (unsigned_lit nf) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
step.
destruct (Z.leb_spec (4 * nf) (262144 * qm)) as [LE|GT].
{
ifz. step. do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ensure_fa. rewrite ?QMe.
replace (4 * nf <=? 262144 * qm) with true by (symmetry; apply Z.leb_le; exact LE).
apply aimplT_ret. apply evt_done.

efa_finish a. { intros; reflexivity. }
{ apply class_repL_split. rewrite ?QMe. split; [|split; [exact PU|]].
- split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; unfold ri_addr; rewrite ?QMe; exact RI|].
split; [cbv beta delta [pc_cells]; unfold pc_addr; exact PC0|].
exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
- intros _. split; [exact FA|]. split; [eapply hjunk_wmono; [exact FJ| exact WM]|].
split; [efa_user| rewrite (proj1 (proj2 (proj2 kconsts))), KS8, SH_plus8; eapply hjunk_wmono; [exact FS| exact WM]]. }
left. split; [reflexivity| rewrite QMe; exact LE]. }

ifz.
stp. stp. step. step. stp.
rewrite (unsigned_lit (nf * 4 + 262143)) by lia.
replace (nf * 4 + 262143) with (4 * nf + 262143) by lia. rewrite (round_up18_eq (4 * nf)) by lia.
set (qn := (4 * nf + 262144 - 1) / 262144).
assert (NFA : 4 * nf <= qn * 262144 < 4 * nf + 262144) by (subst qn; Z.div_mod_to_equations; nia).
step. stp. step.
destruct (Z.ltb_spec 536870912 (qn * 262144)) as [BIG|OKS].
{
apply evt_done. unfold ensure_fa. rewrite ?QMe.
replace (4 * nf <=? 262144 * qm) with false by (symmetry; apply Z.leb_gt; lia).
unfold round_up. rewrite ?KM. change kFreeArrayMapSize with 262144. fold qn. rewrite ?KS.
replace (536870912 <? qn * 262144) with true by (symmetry; apply Z.ltb_lt; lia). apply aimplT_unr. }
ifz. unfold A_INSTANCE.
stp. step. step. step. step.
step. if_lit.
step. step. step. step. step. step.
rewrite (unsigned_lit (qn * 262144)), (unsigned_lit (262144 * qm)) by lia.
replace (262144 * qm + (reg_beg (ae_L RE) c + 3758096384)) with (fa_beg (ae_L RE) c + 262144 * qm) by (rewrite FB, RB; lia).
step.
with_mem ltac:(fun mm =>
assert (MU1 : munch (efa_W (bv_unsigned sp) c) m mm) by (unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?KS; exact MU);
assert (RT1 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU1| exact WM| exact FWrt])).
apply evt_done. unfold ensure_fa. rewrite ?QMe.
replace (4 * nf <=? 262144 * qm) with false by (symmetry; apply Z.leb_gt; lia).
unfold round_up. rewrite ?KM. change kFreeArrayMapSize with 262144. fold qn. rewrite ?KS.
replace (536870912 <? qn * 262144) with false by (symmetry; apply Z.ltb_ge; lia).
eapply aimplT_map_fixed.
{ eapply (map_with_callback_spec L RE X); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold MMAPFIXED_STACK. lia.
- unhide PAL. rewrite FB. Z.div_mod_to_equations. lia.
- Z.div_mod_to_equations. lia.
- lia.
- rewrite ?KHI_eq, FB. lia.
- rewrite FB. unfold prim_hi, prim_lo in *. lia.
- apply rt_avoid_prim; [exact RL| rewrite FB; unfold prim_lo; lia| rewrite FB; unfold prim_hi, prim_lo in *; lia]. }
intros ans ms' POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & ANS).
rewrite !(unsigned_lit (bv_unsigned sp + -48)) in * by lia.
replace (ret_pc (wz 270684)) with (wz 270684) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold MMAPFIXED_STACK in MU2. clear ST MU1 RT1.
destruct ans as [|xg]; cbn [fixed_fp] in MU2; cbn [fixed_ok].
-
contradiction.
-
destruct ANS as (-> & -> & ZNEW).
hide MU. transport_after_call asegs m0 m1 MU2 WM2. unhide MU.
assert (MU' : munch _ m m1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]). clear MU MU2 WM2 MI; rename MU' into MU.
apply aimplT_ret.
step. ifz.
step. step. if_lit.
step. step. step.

assert (SHA : SH (fa_beg (ae_L RE) c + 262144 * qm) = SH (fa_beg (ae_L RE) c) + 32768 * qm).
{ replace (262144 * qm) with (8 * (32768 * qm)) by lia. apply SH_plus8. }
assert (SHN : (qn * 262144 - 262144 * qm) / 8 = 32768 * (qn - qm)) by (Z.div_mod_to_equations; lia).
pose proof (hjunk_wmono _ _ _ _ FS WM) as FS1.
destruct (hjunk_split _ _ (SH (fa_beg (ae_L RE) c) + 32768 * qm) _ FS1 ltac:(lia)) as [_ FS2].
destruct (hjunk_split _ _ (SH (fa_beg (ae_L RE) c) + 32768 * qm + Z.of_nat (Z.to_nat (32768 * (qn - qm)))) _ FS2 ltac:(lia)) as [FS3 _].
destruct (hjunk_cells _ _ _ FS3) as [sjunk SHD]. clear FS1 FS2 FS3.
step. change (536870912 / 8) with 67108864 in MU.
call_sp_ch (poison_shadow_spec RE X) ltac:(fun PO => rewrite ?SHA, ?SHN in PO); try eassumption.
{ lia. }
{ unhide PAL. rewrite FB. Z.div_mod_to_equations. lia. }
{ Z.div_mod_to_equations. lia. }
{ lia. }
{ rewrite ?KHI_eq, FB. lia. }
{ change (2^47) with 140737488355328. rewrite FB. unfold prim_hi, prim_lo in *. lia. }
{ lia. }
{ left. lia. }
{ rewrite SHA, SHN. exact SHD. }
try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
match goal with H : RTconst RE X _ |- _ => rename H into RT3 end. rename POST into SHD.

step. call_sp (get_thread_stats_spec RE X); try eassumption; [lia|]. subst. try clear ST.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end. rename POST into RT4.
with_mem ltac:(fun mm =>
assert (MU1 : munch (efa_W (bv_unsigned sp) c) m mm) by (unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?KS; exact MU);
assert (RS1 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MU1| exact WM| exact FWst]);
destruct (RStats_mmap_words RE X mm RS1) as (w1 & w2 & STW); clear MU1 RS1).
step. step. step. step. step. step.
step. step.
step. step. do 5 step. step. step.
release_frame FR ST (bv_unsigned sp). clear STW.
apply evt_done. efa_finish (set_cls c (set_mapped_fa (qn * 262144) (cls a c)) a).
{ intros c0 Hc0. apply cls_set_cls_ne. exact Hc0. }
{ apply class_repL_split. unfold cr_cellsL, cr_pure. rewrite !cls_set_cls_eq.
cbn [set_mapped_fa c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count as_cache_inited set_cls].
split; [|split].
- split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; cbn [c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count]; unfold ri_addr; exact RI|].
split; [cbv beta delta [pc_cells]; cbn [c_count]; unfold pc_addr; exact PC0|].
exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
- clear - PU OKS NFA QMe QM0 P12 GT Hc. unfold cr_pure in PU. rewrite QMe in PU.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12' & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
repeat match goal with |- _ /\ _ => split end; first [assumption | lia | unfold kFreeArrayMapSize; apply Z_mod_mult | idtac].
- intros _. split; [exact FA|]. split.
{ eapply hjunk_merge; [eapply hjunk_wmono; [exact FJ| exact WM]|].
pose proof (cells_hjunk _ _ _ ZNEW ltac:(rewrite FB; lia)) as ZJ. cbn [cells_size csize Nat.add] in ZJ.
rewrite Nat.add_0_r, Z2Nat.id in ZJ by lia. replace (fa_beg (ae_L RE) c + 262144 * qm + (qn * 262144 - 262144 * qm)) with (fa_beg (ae_L RE) c + qn * 262144) in ZJ by lia. exact ZJ. }
split; [efa_user| rewrite (proj1 (proj2 (proj2 kconsts))), KS8, SH_plus8; eapply hjunk_wmono; [exact FS| exact WM]]. }
right; left. exists (qn * 262144). split; [reflexivity|]. rewrite (proj1 (proj2 (proj2 kconsts))), QMe. unfold kFreeArrayMapSize.
split; [lia|]. split; [apply Z_mod_mult| lia].
Qed.
End S.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME Qu3b QFd5 QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC QKTr Q6sh QQwg.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QpME.Mq0 QTVW.Mq0 QNQk.Mq4 QOJv.Mq3 QOJv.Mq4 QTVW.Mq3 Qu3b.Mq2.
Import QpME.Mq6.
Import QFd5.Mq3 QmvA.Mq2.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation mem := (word -> option byte) (only parsing).

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition poison_zero_stmt_lh (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (addr size lo : Z) (s : PStateA) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PZ_STACK ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ((KHI <= addr /\ addr + size <= 2^47) \/ (0x645000 <= addr /\ addr + size <= 0x7fff8000)) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
aimplT (at_nodeA L asegs) (clear_shadow addr size) s (pz_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz addr) (wz size) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).

Definition poison_zero_stmt_low (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (addr size lo : Z) (s : PStateA) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PZ_STACK ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x645000 <= addr -> addr + size <= 0x7fff8000 ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
aimplT (at_nodeA L asegs) (clear_shadow addr size) s (pz_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz addr) (wz size) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
End S.

Section P.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma poison_zero_spec_low : poison_zero_stmt_low RE X L.
Proof.
unfold poison_zero_stmt_low. intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD.
pose proof CEIL as CEIL'. idtac. pose proof AK as AK'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold PZ_STACK in LO.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
unfold clear_shadow, remap_range. unfold kClearShadowMmapThreshold, shadow_of, kShadowOffset, round_up, round_down, kPage.
destruct (Z.ltb_spec0 (size / 8) 18446744073709551615) as [SMALL|BIG].
{
apply aimplT_ret. eapply evt_mono.
{ eapply (poison_shadow_spec_gen_low RE X); [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| exact AAL| exact SAL| lia| lia| lia
| lia| right; exact SMALL| exact SHD]. }
cbv beta. intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & RT' & Z').
unfold pz_post, PZ_STACK. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact RT'|]. exact Z'. }

exfalso. apply BIG. clear - AK AH S0. Z.div_mod_to_equations; lia.
Qed.

Lemma poison_zero_spec_lh : poison_zero_stmt_lh RE X L.
Proof.
unfold poison_zero_stmt_lh. intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 [[AK AH]|[AK AH]] SHD.
- exact (poison_zero_spec L RE X ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo s junk
RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD).
- exact (poison_zero_spec_low ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo s junk
RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD).
Qed.
End P.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QV3O Q9Ho QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk QV3O QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc Qu3b QYyZ.Mqc.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Unset Keyed Unification.

Definition combined_entry : Z := 0x43acc.
Definition COMB_STACK : Z := 1024.

Definition ALLOC_STACK : Z := 1152.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma sz_frame : forall a LB FS G m m' W,
gcons a LB FS G RE X -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> fp_RStats RE X x \/ band_lo <= x) ->
(RTconst RE X m -> RTconst RE X m') /\ (RPrim a G RE X m -> RPrim a G RE X m') /\ (RDepot RE X m -> RDepot RE X m').
Proof.
intros a LB FS G m m' W GC MU WM HW.
assert (AG : forall P : Z -> Prop, (forall x, P x -> fp_RStats RE X x -> False) -> (forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|Z]; [exact (H1 x Px Z)| pose proof (H2 x Px); lia]. }
split; [| split].
- intros RT. eapply RTconst_frame; [exact RT| exact WM| apply AG].
+ intros x P Q. exact (fpS_excl _ _ _ _ _ _ GC x Q ltac:(do 4 right; exact P)).
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). left; exact P.
- intros RP. eapply RPrim_frame; [exact RP| exact WM| apply AG].
+ intros x P Q. exact (fpP_RStats _ _ _ _ _ _ GC x P Q).
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 2 right; left; exact P.
- intros RD. eapply RDepot_frame; [exact RD| exact WM| apply AG].
+ intros x P Q. exact (fpS_excl _ _ _ _ _ _ GC x Q ltac:(do 2 right; left; exact P)).
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 5 right; left; exact P.
Qed.

Definition alloc_W (sp : Z) (c au : Z) : list (Z * Z) :=
[ (sp - ALLOC_STACK, sp); (0x174420, 0x174421);
(rl_T X + 208, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize); (SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset); (SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8);
(SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000) ].

Definition slot_W (c i : Z) : list (Z * Z) :=
[ (slot_beg RE c i, slot_beg RE c i + class_size c); (SH (slot_beg RE c i), SH (slot_beg RE c i) + class_size c / 8) ].

Definition tzone (G : ghost) (c i : Z) (x : Z) : Prop :=
band_lo <= x \/ in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x
\/ fp_RStats RE X x \/ fp_RDepot RE X x.

Lemma tzone_frame : forall a LB FS G c i m m' W,
gcons a LB FS G RE X -> tag_at G c i = Some TQOwn -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> tzone G c i x) ->
(RPrim a G RE X m -> RPrim a G RE X m')
/\ ((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RStats RE X x) -> RStats RE X m -> RStats RE X m')
/\ ((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RDepot RE X x) -> RDepot RE X m -> RDepot RE X m').
Proof.
intros a LB FS G c i m m' W GC Ht MU WM HW.
assert (QS : forall x, in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x -> fp_RQuar a LB G RE X x).
{ intros x [H|H]; [do 5 right; left| do 6 right; left]; exists c, i, TQOwn; (split; [exact Ht| split; [reflexivity| exact H]]). }
assert (AG : forall P : Z -> Prop,
(forall x, P x -> x < band_lo) -> (forall x, P x -> fp_RQuar a LB G RE X x -> False) ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> P x -> fp_RStats RE X x -> False) ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> P x -> fp_RDepot RE X x -> False) ->
agree_on asegs P m m').
{ intros P H1 H2 H3 H4. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|[Z|Z]]]].
- pose proof (H1 x Px). lia.
- exact (H2 x Px (QS x (or_introl Z))).
- exact (H2 x Px (QS x (or_intror Z))).
- exact (H3 lo hi x Hin Hx Px Z).
- exact (H4 lo hi x Hin Hx Px Z). }
split; [| split].
- intros RP. eapply RPrim_frame; [exact RP| exact WM| apply AG].
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 2 right; left; exact P.
+ intros x P Q. exact (fpQ_RPrim _ _ _ _ _ _ GC x Q P).
+ intros lo hi x _ _ P Q. exact (fpP_RStats _ _ _ _ _ _ GC x P Q).
+ intros lo hi x _ _ P Q. exact (fpP_RDepot _ _ _ _ _ _ GC x P Q).
- intros NW RS. eapply RStats_frame; [exact RS| exact WM| apply AG].
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). right; left; exact P.
+ intros x P Q. exact (fpQ_RStats _ _ _ _ _ _ GC x Q P).
+ intros lo hi x Hin Hx P _. exact (NW lo hi x Hin Hx P).
+ intros lo hi x _ _ P Q. exact (fpS_excl _ _ _ _ _ _ GC x P ltac:(do 2 right; left; exact Q)).
- intros NW RD. eapply RDepot_frame; [exact RD| exact WM| apply AG].
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 5 right; left; exact P.
+ intros x P Q. exact (fpQ_RDepot _ _ _ _ _ _ GC x Q P).
+ intros lo hi x _ _ P Q. exact (fpS_excl _ _ _ _ _ _ GC x Q ltac:(do 2 right; left; exact P)).
+ intros lo hi x Hin Hx P _. exact (NW lo hi x Hin Hx P).
Qed.

Lemma retag_twice : forall G c i t0 t1 t2 (f : stag -> bool),
tag_at G c i = Some t0 -> 0 <= i ->
same_len (set_tag c i t2 (set_tag c i t1 G)) (set_tag c i t2 G) /\ same_tags f (set_tag c i t2 (set_tag c i t1 G)) (set_tag c i t2 G).
Proof.
intros G c i t0 t1 t2 f Ht Hi. split.
- intros c'. pose proof (same_len_set_tag c i t2 (set_tag c i t1 G) c') as A. pose proof (same_len_set_tag c i t1 G c') as B.
pose proof (same_len_set_tag c i t2 G c') as C. unfold same_len in *. lia.
- intros c' i' t _. destruct (Z.eq_dec c' c) as [->|NC]; [destruct (Z.eq_dec i' i) as [->|NI]|].
+ rewrite (tag_at_set_tag_eq _ _ _ _ _ (tag_at_set_tag_eq _ _ _ _ _ Ht)), (tag_at_set_tag_eq _ _ _ _ _ Ht). tauto.
+ rewrite !tag_at_set_tag_ne by (try lia; right; lia). tauto.
+ rewrite !tag_at_set_tag_ne by (try lia; left; lia). tauto.
Qed.

End S.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QOJv.Mqa QOJv.Mqb QnRU.Mqi.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition ensure_fa_entry : Z := 0x422e8.
Definition ENSUREFA_STACK : Z := 448.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition efa_W (sp : Z) (c : Z) : list (Z * Z) :=
[ (sp - ENSUREFA_STACK, sp); (rl_T X + 2800, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8) ].

Definition efa_rel (a : AState) (c nf : Z) (r : bool * AState) : Prop :=
(r = (true, a) /\ 4 * nf <= c_mapped_fa (cls a c))
\/ (exists v, r = (true, set_cls c (set_mapped_fa v (cls a c)) a) /\ 4 * nf <= v <= kFreeArraySize /\ v mod kFreeArrayMapSize = 0
/\ c_mapped_fa (cls a c) < v)
\/ r = (false, a).

Definition efa_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c nf lo : Z) (m : word -> option byte) (v : Z)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (efa_W (bv_unsigned sp) c) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrimL (snd r) G RE X m' c v
/\ a0 = wz (if fst r then 1 else 0)
/\ efa_rel a c nf r.

Ltac efa_finish a' :=
lazymatch goal with |- efa_post _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?a _ ?c _ _ ?m _ _ _ (MS _ _ _ _ _ ?m' _) =>
unfold efa_post; do 16 eexists; split; [reflexivity|]; split; [reflexivity|];
let MU' := fresh "MU'" in
lazymatch goal with MU : munch _ m m', WM : wmono _ m m', RT : RTconst _ _ m, RS : RStats _ _ m, RL : rlay_ok _ _,
FWrt : Forall (rt_avoid _ _) _, FWst : Forall st_avoid _, FWc : Forall (wc_ok _ _ _) _,
HJS : hjunk m (rl_T _ + 2768) _, GNE : (forall c0, _ -> 1 <= c0 < kNumClasses), HCall : (forall c0, _ -> _ -> class_rep _ _ _ _ m c0 _) |- _ =>
assert (MU' : munch (efa_W (bv_unsigned sp) c) m m') by (unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?(proj1 (proj2 (proj2 kconsts))); exact MU);
split; [exact MU'|]; split; [exact WM|]; split; [assumption|]; split; [assumption|];
split; [eapply RTconst_munch; [exact RT| exact MU'| exact WM| exact FWrt]|];
split; [eapply RStats_munch; [exact RS| exact MU'| exact WM| exact FWst]|];
split; [eapply (RPrimL_reclose a a' _ _ _ _ m m' c _ _ _ RL HJS GNE HCall);
[ pose proof kconsts; lia | | reflexivity| intros; reflexivity| intros; lia| exact WM
| eapply agree_other_classes; [exact RL| lia| exact MU'| exact WM| exact FWc] |] |
split; [reflexivity| unfold efa_rel]]
end end.

Ltac efa_user :=
lazymatch goal with MU' : munch (efa_W _ ?c) ?m ?m', WM : wmono _ ?m ?m', PU : cr_pure _ _ ?c _, HU : cr_user _ _ _ ?m ?c, RL : rlay_ok ?RE ?X |- cr_user _ _ _ ?m' ?c =>
eapply cr_user_ext;
[ eapply cr_user_agree; [exact PU| exact HU| lia|];
eapply agree_on_of_munch; [exact MU'| exact WM|]; intros z Uz Hz;
apply (uzone_bounds RE X c z RL ltac:(lia)) in Uz; unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?(proj1 (proj2 (proj2 kconsts))); cbn [outside];
unfold SH, A_SHADOW_OFS in *; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia
| rewrite ?cls_set_cls_eq; reflexivity
| rewrite ?cls_set_cls_eq; reflexivity ]
end.

Lemma ensure_fa_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c nf lo v : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL a G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ENSUREFA_STACK ->
1 <= c < kNumClasses -> 0 <= nf < 2^40 ->
aimplT atn (ensure_fa (ae_L RE) a c nf) s
(efa_post ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c nf lo m v)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (ri_addr RE c)) (wz (reg_beg (ae_L RE) c)) (wz nf) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz ensure_fa_entry) fc None m (seg_rom asegs)).
Proof.
intros until v; intros RT RL RS RP MI ST CEIL LO Hc Hnf.
pose proof CEIL as CEIL'. idtac. unfold ENSUREFA_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX). rewrite K32 in Hc.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
assert (FWrt : Forall (rt_avoid RE X) (efa_W (bv_unsigned sp) c)).
{ unfold efa_W, ENSUREFA_STACK, ri_addr. rewrite ?KS.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [| constructor]. apply rt_avoid_gap; [exact RL| unfold SH, A_SHADOW_OFS; unfold prim_lo in *; Z.div_mod_to_equations; lia| rewrite ?KHI_eq; unfold SH, A_SHADOW_OFS; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia]. }
assert (FWst : Forall st_avoid (efa_W (bv_unsigned sp) c)).
{ unfold efa_W, ENSUREFA_STACK, ri_addr. rewrite ?KS.
constructor; [apply st_avoid_above; unfold A_ERRNO; lia|].

constructor; [intros x [Hx1 Hx2] KK; cbn [fst snd] in *; pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & [_ TH] & _);
cbn [fst snd] in TH; unfold A_ERRNO in *; clear - Hx1 Hx2 KK TH; lia|].
repeat (constructor; [apply st_avoid_above; unfold A_ERRNO, SH, A_SHADOW_OFS; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia|]). constructor. }
assert (FWc : Forall (wc_ok RE X c) (efa_W (bv_unsigned sp) c)).
{ unfold efa_W, ENSUREFA_STACK. rewrite ?KS.
constructor; [cbn; left; lia|]. constructor; [cbn; right; left; lia|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; left; exact Hz|].
constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; do 2 right; left; rewrite KS; exact Hz|].
constructor; [| constructor]. cbn -[fp_cls SH Z.div]; do 2 right; intros z Hz. do 3 right; left. split; cbn [fst snd]; rewrite ?KS; lia. }

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11 & P12 & P13 & P14 & _ & _ & G2 & G3 & G4 & G5).
specialize (REG ltac:(lia)). destruct REG as (FA & FJ & HU & FS).
rewrite ?KS, ?KM, ?KO in *.
cbv beta delta [ri_cellsL] in RI. cbv beta delta [pc_cells] in PC0. unfold ri_addr, pc_addr in *.
hide PAL. clear G5.
assert (QM : exists q, c_mapped_fa (cls a c) = 262144 * q /\ 0 <= q) by (exists (c_mapped_fa (cls a c) / 262144); unfold kFreeArrayMapSize in P14; Z.div_mod_to_equations; lia).
destruct QM as (qm & QMe & QM0). rewrite QMe in *. clear P14.
assert (KS8 : 536870912 = 8 * 67108864) by reflexivity.
rewrite KS8, SH_plus8 in FS.
assert (SFB : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo).
{ unhide PAL. rewrite FB. unfold SH, A_SHADOW_OFS. unfold prim_hi, prim_lo in *. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD.
assert (LFA : Z.of_nat (length (map (fun i : Z => wz (coff c i)) (pk_fl (K c)))) = c_num_freed (cls a c)) by (rewrite length_map; exact P1).
pose proof (munch_refl (efa_W (bv_unsigned sp) c) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold efa_W, ENSUREFA_STACK, ri_addr in MU. rewrite ?KS in MU.
unfold ensure_fa_entry. rtc RT 24%nat K24. unfold A_INSTANCE in K24.
apply aimplT_from_evt.
carve_frame 48%nat ST.
do 6 step.
step.
step. step.
rewrite (unsigned_lit nf) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
step.
destruct (Z.leb_spec (4 * nf) (262144 * qm)) as [LE|GT].
{
ifz. step. do 5 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ensure_fa. rewrite ?QMe.
replace (4 * nf <=? 262144 * qm) with true by (symmetry; apply Z.leb_le; exact LE).
apply aimplT_ret. apply evt_done.

efa_finish a. { intros; reflexivity. }
{ apply class_repL_split. rewrite ?QMe. split; [|split; [exact PU|]].
- split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; unfold ri_addr; rewrite ?QMe; exact RI|].
split; [cbv beta delta [pc_cells]; unfold pc_addr; exact PC0|].
exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
- intros _. split; [exact FA|]. split; [eapply hjunk_wmono; [exact FJ| exact WM]|].
split; [efa_user| rewrite (proj1 (proj2 (proj2 kconsts))), KS8, SH_plus8; eapply hjunk_wmono; [exact FS| exact WM]]. }
left. split; [reflexivity| rewrite QMe; exact LE]. }

ifz.
stp. stp. step. step. stp.
rewrite (unsigned_lit (nf * 4 + 262143)) by lia.
replace (nf * 4 + 262143) with (4 * nf + 262143) by lia. rewrite (round_up18_eq (4 * nf)) by lia.
set (qn := (4 * nf + 262144 - 1) / 262144).
assert (NFA : 4 * nf <= qn * 262144 < 4 * nf + 262144) by (subst qn; Z.div_mod_to_equations; nia).
step. stp. step.
destruct (Z.ltb_spec 536870912 (qn * 262144)) as [BIG|OKS].
{
apply evt_done. unfold ensure_fa. rewrite ?QMe.
replace (4 * nf <=? 262144 * qm) with false by (symmetry; apply Z.leb_gt; lia).
unfold round_up. rewrite ?KM. change kFreeArrayMapSize with 262144. fold qn. rewrite ?KS.
replace (536870912 <? qn * 262144) with true by (symmetry; apply Z.ltb_lt; lia). apply aimplT_unr. }
ifz. unfold A_INSTANCE.
stp. step. step. step. step.
step. if_lit.
step. step. step. step. step. step.
rewrite (unsigned_lit (qn * 262144)), (unsigned_lit (262144 * qm)) by lia.
replace (262144 * qm + (reg_beg (ae_L RE) c + 3758096384)) with (fa_beg (ae_L RE) c + 262144 * qm) by (rewrite FB, RB; lia).
step.
with_mem ltac:(fun mm =>
assert (MU1 : munch (efa_W (bv_unsigned sp) c) m mm) by (unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?KS; exact MU);
assert (RT1 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU1| exact WM| exact FWrt])).
apply evt_done. unfold ensure_fa. rewrite ?QMe.
replace (4 * nf <=? 262144 * qm) with false by (symmetry; apply Z.leb_gt; lia).
unfold round_up. rewrite ?KM. change kFreeArrayMapSize with 262144. fold qn. rewrite ?KS.
replace (536870912 <? qn * 262144) with false by (symmetry; apply Z.ltb_ge; lia).
eapply aimplT_map_fixed.
{ eapply (map_with_callback_spec L RE X); try eassumption.
- rewrite unsigned_lit by lia. exact ST.
- rewrite unsigned_lit by lia. unfold MMAPFIXED_STACK. lia.
- unhide PAL. rewrite FB. Z.div_mod_to_equations. lia.
- Z.div_mod_to_equations. lia.
- lia.
- rewrite ?KHI_eq, FB. lia.
- rewrite FB. unfold prim_hi, prim_lo in *. lia.
- apply rt_avoid_prim; [exact RL| rewrite FB; unfold prim_lo; lia| rewrite FB; unfold prim_hi, prim_lo in *; lia]. }
intros ans ms' POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & -> & MU2 & WM2 & MI2 & ST2 & RT2 & ANS).
rewrite !(unsigned_lit (bv_unsigned sp + -48)) in * by lia.
replace (ret_pc (wz 271240)) with (wz 271240) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold MMAPFIXED_STACK in MU2. clear ST MU1 RT1.
destruct ans as [|xg]; cbn [fixed_fp] in MU2; cbn [fixed_ok].
-
contradiction.
-
destruct ANS as (-> & -> & ZNEW).
hide MU. transport_after_call asegs m0 m1 MU2 WM2. unhide MU.
assert (MU' : munch _ m m1) by (eapply munch_chain; [exact MU| exact MU2| sub_fp_solve]). clear MU MU2 WM2 MI; rename MU' into MU.
apply aimplT_ret.
step. ifz.
step. step. if_lit.
step. step. step.

assert (SHA : SH (fa_beg (ae_L RE) c + 262144 * qm) = SH (fa_beg (ae_L RE) c) + 32768 * qm).
{ replace (262144 * qm) with (8 * (32768 * qm)) by lia. apply SH_plus8. }
assert (SHN : (qn * 262144 - 262144 * qm) / 8 = 32768 * (qn - qm)) by (Z.div_mod_to_equations; lia).
pose proof (hjunk_wmono _ _ _ _ FS WM) as FS1.
destruct (hjunk_split _ _ (SH (fa_beg (ae_L RE) c) + 32768 * qm) _ FS1 ltac:(lia)) as [_ FS2].
destruct (hjunk_split _ _ (SH (fa_beg (ae_L RE) c) + 32768 * qm + Z.of_nat (Z.to_nat (32768 * (qn - qm)))) _ FS2 ltac:(lia)) as [FS3 _].
destruct (hjunk_cells _ _ _ FS3) as [sjunk SHD]. clear FS1 FS2 FS3.
step. change (536870912 / 8) with 67108864 in MU.
call_sp_ch (poison_shadow_spec RE X) ltac:(fun PO => rewrite ?SHA, ?SHN in PO); try eassumption.
{ lia. }
{ unhide PAL. rewrite FB. Z.div_mod_to_equations. lia. }
{ Z.div_mod_to_equations. lia. }
{ lia. }
{ rewrite ?KHI_eq, FB. lia. }
{ change (2^47) with 140737488355328. rewrite FB. unfold prim_hi, prim_lo in *. lia. }
{ lia. }
{ left. lia. }
{ rewrite SHA, SHN. exact SHD. }
try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
match goal with H : RTconst RE X _ |- _ => rename H into RT3 end. rename POST into SHD.

step. call_sp (get_thread_stats_spec RE X); try eassumption; [lia|]. subst. try clear ST.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end. rename POST into RT4.
with_mem ltac:(fun mm =>
assert (MU1 : munch (efa_W (bv_unsigned sp) c) m mm) by (unfold efa_W, ENSUREFA_STACK, ri_addr; rewrite ?KS; exact MU);
assert (RS1 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MU1| exact WM| exact FWst]);
destruct (RStats_mmap_words RE X mm RS1) as (w1 & w2 & STW); clear MU1 RS1).
step. step. step. step. step. step.
step. step.
step. step. do 5 step. step. step.
release_frame FR ST (bv_unsigned sp). clear STW.
apply evt_done. efa_finish (set_cls c (set_mapped_fa (qn * 262144) (cls a c)) a).
{ intros c0 Hc0. apply cls_set_cls_ne. exact Hc0. }
{ apply class_repL_split. unfold cr_cellsL, cr_pure. rewrite !cls_set_cls_eq.
cbn [set_mapped_fa c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count as_cache_inited set_cls].
split; [|split].
- split; [exists j1, j2, j3, j4; cbv beta delta [ri_cellsL]; cbn [c_mapped_user c_alloc_user c_num_freed c_mapped_fa c_count]; unfold ri_addr; exact RI|].
split; [cbv beta delta [pc_cells]; cbn [c_count]; unfold pc_addr; exact PC0|].
exists CH. unfold pc_addr. split; [exact ACH| split; [exact LCH| exact HCH]].
- clear - PU OKS NFA QMe QM0 P12 GT Hc. unfold cr_pure in PU. rewrite QMe in PU.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12' & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
repeat match goal with |- _ /\ _ => split end; first [assumption | lia | unfold kFreeArrayMapSize; apply Z_mod_mult | idtac].
- intros _. split; [exact FA|]. split.
{ eapply hjunk_merge; [eapply hjunk_wmono; [exact FJ| exact WM]|].
pose proof (cells_hjunk _ _ _ ZNEW ltac:(rewrite FB; lia)) as ZJ. cbn [cells_size csize Nat.add] in ZJ.
rewrite Nat.add_0_r, Z2Nat.id in ZJ by lia. replace (fa_beg (ae_L RE) c + 262144 * qm + (qn * 262144 - 262144 * qm)) with (fa_beg (ae_L RE) c + qn * 262144) in ZJ by lia. exact ZJ. }
split; [efa_user| rewrite (proj1 (proj2 (proj2 kconsts))), KS8, SH_plus8; eapply hjunk_wmono; [exact FS| exact WM]]. }
right; left. exists (qn * 262144). split; [reflexivity|]. rewrite (proj1 (proj2 (proj2 kconsts))), QMe. unfold kFreeArrayMapSize.
split; [lia|]. split; [apply Z_mod_mult| lia].
Qed.
End S.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC QKTr Q6sh QQwg.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QpME.Mq7 QTVW.Mq7 QNQk.Mq8 QOJv.Mqa QOJv.Mqb QTVW.Mqa Qu3b.
Import QpME.Mqc.
Import QFd5.Mq7 QmvA.Mq6.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation mem := (word -> option byte) (only parsing).

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition poison_zero_stmt_lh (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (addr size lo : Z) (s : PStateA) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PZ_STACK ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ((KHI <= addr /\ addr + size <= 2^47) \/ (0x647000 <= addr /\ addr + size <= 0x7fff8000)) ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
aimplT (at_nodeA L asegs) (clear_shadow addr size) s (pz_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz addr) (wz size) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).

Definition poison_zero_stmt_low (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (addr size lo : Z) (s : PStateA) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PZ_STACK ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x647000 <= addr -> addr + size <= 0x7fff8000 ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
aimplT (at_nodeA L asegs) (clear_shadow addr size) s (pz_post RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz addr) (wz size) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
End S.

Section P.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Lemma poison_zero_spec_low : poison_zero_stmt_low RE X L.
Proof.
unfold poison_zero_stmt_low. intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD.
pose proof CEIL as CEIL'. idtac. pose proof AK as AK'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold PZ_STACK in LO.
assert (SHa : SH addr = addr / 8 + 0x7fff8000) by reflexivity.
unfold clear_shadow, remap_range. unfold kClearShadowMmapThreshold, shadow_of, kShadowOffset, round_up, round_down, kPage.
destruct (Z.ltb_spec0 (size / 8) 18446744073709551615) as [SMALL|BIG].
{
apply aimplT_ret. eapply evt_mono.
{ eapply (poison_shadow_spec_gen_low RE X); [exact RT| exact RL| exact MI| exact ST| exact CEIL'| lia| exact AAL| exact SAL| lia| lia| lia
| lia| right; exact SMALL| exact SHD]. }
cbv beta. intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & RT' & Z').
unfold pz_post, PZ_STACK. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact RT'|]. exact Z'. }

exfalso. apply BIG. clear - AK AH S0. Z.div_mod_to_equations; lia.
Qed.

Lemma poison_zero_spec_lh : poison_zero_stmt_lh RE X L.
Proof.
unfold poison_zero_stmt_lh. intros until junk; intros RT RL MI ST CEIL LO AAL SAL S0 [[AK AH]|[AK AH]] SHD.
- exact (poison_zero_spec L RE X ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo s junk
RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD).
- exact (poison_zero_spec_low ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo s junk
RT RL MI ST CEIL LO AAL SAL S0 AK AH SHD).
Qed.
End P.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Unset Keyed Unification.

Definition combined_entry : Z := 0x438a0.
Definition COMB_STACK : Z := 1024.

Definition ALLOC_STACK : Z := 1152.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma sz_frame : forall a LB FS G m m' W,
gcons a LB FS G RE X -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> fp_RStats RE X x \/ band_lo <= x) ->
(RTconst RE X m -> RTconst RE X m') /\ (RPrim a G RE X m -> RPrim a G RE X m') /\ (RDepot RE X m -> RDepot RE X m').
Proof.
intros a LB FS G m m' W GC MU WM HW.
assert (AG : forall P : Z -> Prop, (forall x, P x -> fp_RStats RE X x -> False) -> (forall x, P x -> x < band_lo) -> agree_on asegs P m m').
{ intros P H1 H2. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|Z]; [exact (H1 x Px Z)| pose proof (H2 x Px); lia]. }
split; [| split].
- intros RT. eapply RTconst_frame; [exact RT| exact WM| apply AG].
+ intros x P Q. exact (fpS_excl _ _ _ _ _ _ GC x Q ltac:(do 4 right; exact P)).
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). left; exact P.
- intros RP. eapply RPrim_frame; [exact RP| exact WM| apply AG].
+ intros x P Q. exact (fpP_RStats _ _ _ _ _ _ GC x P Q).
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 2 right; left; exact P.
- intros RD. eapply RDepot_frame; [exact RD| exact WM| apply AG].
+ intros x P Q. exact (fpS_excl _ _ _ _ _ _ GC x Q ltac:(do 2 right; left; exact P)).
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 5 right; left; exact P.
Qed.

Definition alloc_W (sp : Z) (c au : Z) : list (Z * Z) :=
[ (sp - ALLOC_STACK, sp); (0x171d60, 0x171d61);
(rl_T X + 208, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize); (SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset); (SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8);
(SS_BASE, DP_END); (rl_dn X, rl_dn X + 0x100000); (rl_ssb X, rl_ssb X + 0x800000) ].

Definition slot_W (c i : Z) : list (Z * Z) :=
[ (slot_beg RE c i, slot_beg RE c i + class_size c); (SH (slot_beg RE c i), SH (slot_beg RE c i) + class_size c / 8) ].

Definition tzone (G : ghost) (c i : Z) (x : Z) : Prop :=
band_lo <= x \/ in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x
\/ fp_RStats RE X x \/ fp_RDepot RE X x.

Lemma tzone_frame : forall a LB FS G c i m m' W,
gcons a LB FS G RE X -> tag_at G c i = Some TQOwn -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> tzone G c i x) ->
(RPrim a G RE X m -> RPrim a G RE X m')
/\ ((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RStats RE X x) -> RStats RE X m -> RStats RE X m')
/\ ((forall lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ fp_RDepot RE X x) -> RDepot RE X m -> RDepot RE X m').
Proof.
intros a LB FS G c i m m' W GC Ht MU WM HW.
assert (QS : forall x, in_iv (slot_beg RE c i, class_size c) x \/ in_sh (slot_beg RE c i, class_size c) x -> fp_RQuar a LB G RE X x).
{ intros x [H|H]; [do 5 right; left| do 6 right; left]; exists c, i, TQOwn; (split; [exact Ht| split; [reflexivity| exact H]]). }
assert (AG : forall P : Z -> Prop,
(forall x, P x -> x < band_lo) -> (forall x, P x -> fp_RQuar a LB G RE X x -> False) ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> P x -> fp_RStats RE X x -> False) ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> P x -> fp_RDepot RE X x -> False) ->
agree_on asegs P m m').
{ intros P H1 H2 H3 H4. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro. intros lo hi Hin Hx.
destruct (HW lo hi x Hin Hx) as [Z|[Z|[Z|[Z|Z]]]].
- pose proof (H1 x Px). lia.
- exact (H2 x Px (QS x (or_introl Z))).
- exact (H2 x Px (QS x (or_intror Z))).
- exact (H3 lo hi x Hin Hx Px Z).
- exact (H4 lo hi x Hin Hx Px Z). }
split; [| split].
- intros RP. eapply RPrim_frame; [exact RP| exact WM| apply AG].
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 2 right; left; exact P.
+ intros x P Q. exact (fpQ_RPrim _ _ _ _ _ _ GC x Q P).
+ intros lo hi x _ _ P Q. exact (fpP_RStats _ _ _ _ _ _ GC x P Q).
+ intros lo hi x _ _ P Q. exact (fpP_RDepot _ _ _ _ _ _ GC x P Q).
- intros NW RS. eapply RStats_frame; [exact RS| exact WM| apply AG].
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). right; left; exact P.
+ intros x P Q. exact (fpQ_RStats _ _ _ _ _ _ GC x Q P).
+ intros lo hi x Hin Hx P _. exact (NW lo hi x Hin Hx P).
+ intros lo hi x _ _ P Q. exact (fpS_excl _ _ _ _ _ _ GC x P ltac:(do 2 right; left; exact Q)).
- intros NW RD. eapply RDepot_frame; [exact RD| exact WM| apply AG].
+ intros x P. apply (fp_lt_ceil _ _ _ _ _ _ GC). do 5 right; left; exact P.
+ intros x P Q. exact (fpQ_RDepot _ _ _ _ _ _ GC x Q P).
+ intros lo hi x _ _ P Q. exact (fpS_excl _ _ _ _ _ _ GC x Q ltac:(do 2 right; left; exact P)).
+ intros lo hi x Hin Hx P _. exact (NW lo hi x Hin Hx P).
Qed.

Lemma retag_twice : forall G c i t0 t1 t2 (f : stag -> bool),
tag_at G c i = Some t0 -> 0 <= i ->
same_len (set_tag c i t2 (set_tag c i t1 G)) (set_tag c i t2 G) /\ same_tags f (set_tag c i t2 (set_tag c i t1 G)) (set_tag c i t2 G).
Proof.
intros G c i t0 t1 t2 f Ht Hi. split.
- intros c'. pose proof (same_len_set_tag c i t2 (set_tag c i t1 G) c') as A. pose proof (same_len_set_tag c i t1 G c') as B.
pose proof (same_len_set_tag c i t2 G c') as C. unfold same_len in *. lia.
- intros c' i' t _. destruct (Z.eq_dec c' c) as [->|NC]; [destruct (Z.eq_dec i' i) as [->|NI]|].
+ rewrite (tag_at_set_tag_eq _ _ _ _ _ (tag_at_set_tag_eq _ _ _ _ _ Ht)), (tag_at_set_tag_eq _ _ _ _ _ Ht). tauto.
+ rewrite !tag_at_set_tag_ne by (try lia; right; lia). tauto.
+ rewrite !tag_at_set_tag_ne by (try lia; left; lia). tauto.
Qed.

End S.
