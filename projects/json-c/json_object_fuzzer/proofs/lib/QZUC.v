(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlCE.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhHQ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Definition tok_reset_level_B_entry : Z := 0x93470.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TokResetLvl.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Lemma lvl_shadowB : forall A LB LM FR B m md q mxd i,
HEAPAx A LB LM FR B m md -> In (q, 32 * mxd) LB -> q mod 8 = 0 -> 0 <= mxd -> (Z.of_nat i < mxd) ->
ro_cells asegs m ((q + 32 * Z.of_nat i) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md q mxd i HP Hin Hal Hm Hi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH.
replace (32 * mxd) with (8 * (4 * mxd)) in SH by lia. rewrite shadow_bytes_mul8 in SH by lia.
apply (bytes_at_repeat_sub asegs m _ _ _ (4 * i) 4) in SH; [| lia].
replace ((q + 32 * Z.of_nat i) / 8 + A_SB) with (q / 8 + A_SB + Z.of_nat (4 * i)) by (unfold A_SB; Z.div_mod_to_equations; nia).
exact (ro_cells_of_repeat asegs m _ _ 4 SH).
Qed.

Definition tok_reset_level_postB (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : config) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth mxd fl : Z) (x : tscal) (levels : list tlevel) (i : nat) (l : tlevel) (rc : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (B' : bud) (rv : word),
ret_statew A4H ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
( ((tl_cs l = None \/ rc = 1) /\ HEAPAx A' REST LM FRS B' m' md')
\/ (exists s', tl_cs l = Some s' /\ 2 <= rc /\ jval asegs A4F s' m' (tl_cbs l) (tl_cur l) (rc - 1) /\ HEAPAx A' (tl_cbs l ++ REST) LM FRS B' m' md') ) /\
tstack asegs m' q (lupd levels i lvl_reset) /\
rw_cells asegs m' r (tok_cells_g mxd fl pb depth q x) /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) me m' /\
rw_cells asegs m' A_ERRNO [C4 errv] /\
agree_on asegs P mpre m' /\
bB B - (put_costA (tl_cs l) rc (tl_cbs l) + 512) <= bB B' /\ bD B <= bD B'.

Lemma tok_reset_level_B_cps :
forall (i : nat) (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m me : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (REST LB0 P LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(q r pb depth mxd fl : Z) (x : tscal) (levels : list tlevel) (l : tlevel) (rc : Z),
nth_error levels i = Some l -> Z.of_nat i < mxd -> 1 <= mxd <= 32 -> length levels = Z.to_nat mxd ->
HEAPAx A (lvl_blocks l ++ REST) LM FRS B m md ->
REST = P ++ (r, 72) :: (q, 32 * mxd) :: LB0 ->
put_pre A4H A4F (tl_cs l) m (tl_cbs l) (tl_cur l) rc ->
((tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])) ->
tstack asegs m q levels ->
rw_cells asegs m r (tok_cells_g mxd fl pb depth q x) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 - put_stk_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) me m ->
rw_cells asegs m A_ERRNO [C4 errv] ->
put_costA (tl_cs l) rc (tl_cbs l) + 512 <= bB B ->
bv_unsigned ra mod 2 = 0 ->
(forall ms' md' A', tok_reset_level_postB ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc md REST LB0 P LM FRS B me m lo errv q r pb depth mxd fl x levels i l rc ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 (Z.of_nat i)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 tok_reset_level_B_entry) fc None m (seg_rom asegs)).
Proof.
intros until rc. intros Hl Hi MXB LEN HP EREST PP NM TS BLK ST LO LOS SPA HT HPR ERR BB RA K.
unfold put_stk_A in LOS. unfold_consts. unfold A_SB, A_TP, A_ERRNO, tok_reset_level_B_entry in *. word_range sp SPR.
assert (INrR : In (r, 72) REST) by (rewrite EREST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 32 * mxd) REST) by (rewrite EREST; apply in_or_app; right; right; left; reflexivity).
assert (INr : In (r, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INq : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
assert (INr2 : In (r, 72) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; exact INr).
assert (INq2 : In (q, 32 * mxd) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 72 HP INr2) as (_ & Hral & Hrlo & Hrhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 72 HP INr2) as Himg_r.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq2) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq2) as Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi, Hqhi.
assert (Hqr : q <> r).
{ intros ->. pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. rewrite EREST, !map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (32 * mxd) r 72 HP INq2 INr2 Hqr) as Hdqr.
pose proof (TS i l Hl) as LV. unfold srec_cells in LV.
remember (q + 32 * Z.of_nat i) as bse eqn:Hbse in LV.
unfold tok_cells_g in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
assert (SHAD : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM FRS Bx mc mdx -> In (r, 72) LBx -> In (q, 32 * mxd) LBx ->
ro_cells asegs mc (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPc Ir Iq. split.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HPc Ir) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH.
- pose proof (lvl_shadowB _ _ _ _ _ _ _ q mxd i HPc Iq ltac:(lia) ltac:(lia) Hi) as SH. unfold A_SB in SH. rewrite <- Hbse in SH. exact SH. }
destruct (SHAD _ _ _ _ m HP INr INq) as [SHr SHl].
assert (BLO : 0 < bse < 2^63 /\ q <= bse /\ bse + 32 <= q + 32 * mxd) by (subst bse; lia).
assert (Hb16 : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (Hb8 : bse mod 8 = 0) by (clear - Hb16; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(bse, bse + 32); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
a4l.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
step.
do 7 step.
step. ub_land Hral. step. if_false.
step.
step. step. step.
step.
asan_chkB.
step.
step. step.
ub_bse q bse (Z.of_nat i).
step. step. ub_lvl q bse (Z.of_nat i). step. ub_if_lit.
step. step. step. step.
ub_geu bse (Z.of_nat i * 32). ub_slti0 (Z.of_nat i).
step. ub_if_lit.
step. if_falsex.
step. ub_land Hb8. step. ub_if_lit.
asan_chkB.
stepz.
step. if_falsex.
step.
asan_chkB.
step. stepz.
step.
asan_chkB.
step. step.
try clear SHr; try clear SHl.
set (l1 := TL 0 1 (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
assert (HiL : (i < length levels)%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS1 : tstack asegs mc q (lupd levels i l1)) end.
{ subst bse. eapply (tstack_put asegs m _ q levels i l1 [(bv_unsigned sp - 64, bv_unsigned sp)]); [exact TS | lia | exact MU | exact WM | | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l1]; assumption].
intros j Hj Hne. cbn. split; [left; unfold alloc_ceiling in *; lia | exact I]. }
lazymatch goal with H : rw_cells asegs _ bse _ |- _ => rename H into LV1 end.
clear TS.
assert (PDJ : forall a n, In (a, n) P -> (a + n <= q \/ q + 32 * mxd <= a) /\ a + n <= alloc_ceiling).
{ intros a n Hin.
assert (Haq : a <> q) by (eapply (nodup_P_notq (lvl_blocks l)); [rewrite <- EREST; exact (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) | exact Hin]).
assert (INa : In (a, n) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hin).
split; [exact (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP INa INq2 Haq)|].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP INa) as (_ & _ & _ & Hahi & _). exact Hahi. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP : agree_on asegs P m mc) by (eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; destruct (PDJ a n Hin) as [D1 D2]; split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]]) end.

unfold lvl_blocks in HP. rewrite <- app_assoc in HP.
evt_done5.
assert (INq3 : In (q, 32 * mxd) (tl_cbs l ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INqR).
assert (INq4 : In (q, 32 * mxd) ((tl_cbs l ++ tl_nbs l ++ REST) ++ LM)) by (apply in_or_app; left; exact INq3).
pose proof PUT as PUTx. unfold put_stmt_A, put_stmtA in PUTx.
eapply PUTx with (s := tl_cs l) (BS := tl_cbs l) (LB := tl_nbs l ++ REST) (p := tl_cur l) (rc := rc) (lo := lo) (errv := errv);
[ heap_nowA A4L HIx HP MU WM MI | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
{ lazymatch goal with |- put_pre _ _ _ ?mc _ _ _ => assert (AG : agree_on asegs (tl_cbs l) m mc) end.
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. cbn.
assert (INa : In (a, n) ((tl_cbs l ++ tl_nbs l ++ REST) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact Hin).
assert (Haq : a <> q).
{ intros ->. refine (nodup_prefix_suffix (tl_cbs l) (tl_nbs l ++ REST) q n (32 * mxd) (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) Hin _).
apply in_or_app; right. exact INqR. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP INa INq4 Haq) as D1.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP INa) as (_ & _ & _ & Hahi & _).
split; [lia | split; [unfold alloc_ceiling in *; lia | exact I]]. }
unfold put_pre in *. destruct (tl_cs l) as [s'|]; [|exact PP].
destruct PP as (Hc & Hrc & J). split; [exact Hc|]. split; [exact Hrc|]. eapply jval_agree; [exact J | exact AG | apply incl_refl]. }
all: try eassumption.
all: try (unfold put_stk_A; lia).
all: try (unfold put_costA in *; destruct (tl_cs l); [destruct (rc =? 1)|]; lia).

intros ms2 md2 A2 (m2 & r2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR2 by lia.
assert (HPx : exists LBx, HEAPAx A2 (LBx ++ tl_nbs l ++ REST) LM FRS B2 m2 md2 /\
((LBx = [] /\ (tl_cs l = None \/ rc = 1)) \/ (exists s', tl_cs l = Some s' /\ 2 <= rc /\ LBx = tl_cbs l /\ jval asegs A4F s' m2 (tl_cbs l) (tl_cur l) (rc - 1)))).
{ destruct OUT2 as [[H1 H2] | (s' & E & R & J & H2)];
[exists []; split; [exact H2 | left; split; [reflexivity | exact H1]] | exists (tl_cbs l); split; [exact H2 | right; exists s'; repeat split; assumption]]. }
destruct HPx as (LBx & HP2 & OUTx). clear OUT2.
assert (INrN : In (r, 72) (LBx ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INrR).
assert (INqN : In (q, 32 * mxd) (LBx ++ tl_nbs l ++ REST)) by (apply in_or_app; right; apply in_or_app; right; exact INqR).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
assert (INrN0 : In (r, 72) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqN0 : In (q, 32 * mxd) (tl_nbs l ++ REST)) by (apply in_or_app; right; exact INqR).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrN0 | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqN0 | lia | cbn; lia]]. a4l.

assert (TSP : forall LBp SPp ma mb lv, heap_pres A4H LBp SPp ma mb -> In (q, 32 * mxd) LBp -> length lv = Z.to_nat mxd -> tstack asegs ma q lv -> tstack asegs mb q lv).
{ intros LBp SPp ma mb lv HPRp INp LENp TSp j lj Hj. pose proof (TSp j lj Hj) as Cj.
assert (Hjl : (j < length lv)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPRp) in Cj; [exact Cj |].
eapply client_range_block; [exact INp | lia |]. unfold srec_cells. cbn [cells_size Z.of_nat]. cbn. lia. }
apply (TSP _ _ _ _ _ HPR2 ltac:(apply in_or_app; left; exact INqN0) ltac:(rewrite lupd_length; exact LEN)) in TS1.
assert (NQ0 : ~ In (q, 32 * mxd) LB0).
{ pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. rewrite EREST in ND. exact (nodup_mid_notin _ _ _ _ _ _ _ _ (32 * mxd) ND). }
assert (NQM : ~ In (q, 32 * mxd) (LB0 ++ LM ++ fr_ivs A4L FRS)).
{ apply not_in_app3; [| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INq4)].
intros Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact (NQ0 Hx)|].
exact (nodup_prefix_suffix _ LM q (32 * mxd) (32 * mxd) (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) INq3 Hx). }
assert (HPRa : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) me m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd].
+ right; left. exists q, (32 * mxd). split; [exact INq4|]. split; [exact NQM | lia].
+ left. lia.
- eapply heap_pres_weaken; [exact HPR2 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb]]. }
assert (AGP2 : agree_on asegs P m m2).
{ eapply agree_on_trans; [exact AGP|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR2 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; right; rewrite EREST; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPR AGP PUTx.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP2) as [HB2 HD2].

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
destruct (SHAD _ _ _ _ m2 HP2 INrN INqN) as [SHr SHl].
reenterA asegs A4L HIx asegs_wx HP2.
asan_rechkB.
step. step.
ub_bse q bse (Z.of_nat i).
step. step. ub_lvl q bse (Z.of_nat i). step. ub_if_lit.
step. step. step.
ub_geu bse (Z.of_nat i * 32).
step. ub_if_lit.
step. if_falsex.
step. step.
ub_bse q bse (Z.of_nat i).
step. ub_land Hb8. step. ub_if_lit.
step.
asan_chkB.
stepz.
try clear SHr; try clear SHl.
destruct (SHAD _ _ _ _ _ ltac:(heap_nowA A4L HIx HP2 MU WM MI) INrN INqN) as [SHr SHl].
step. if_falsex.
step.
asan_chkB.
step. step.
try clear SHr; try clear SHl.
set (l2 := TL 0 1 0 None [] (tl_name l) (tl_nbs l)).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS2 : tstack asegs mc q (lupd levels i l2)) end.
{ rewrite <- (lupd_lupd levels i l1 l2). subst bse.
eapply (tstack_put asegs m2 _ q (lupd levels i l1) i l2 []); [exact TS1 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name l2]; assumption]. }
clear TS1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AGP3 : agree_on asegs P m mc) by (eapply agree_on_trans; [exact AGP2|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]]) end.
alloc_callA (hiA_free A4L HIx) blk (tl_name l) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ destruct NM as [[Hn0 _] | [Hn0 [nn Hnbs]]]; [left; exact Hn0 | right; exists nn; apply in_or_app; right; apply in_or_app; left; rewrite Hnbs; left; reflexivity]. }

intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HPR3 by lia.
assert (RAPP : forall p (L1 L2 : list blk), (forall n, ~ In (p, n) L1) -> lb_remove p (L1 ++ L2) = L1 ++ lb_remove p L2).
{ intros p L1 L2. induction L1 as [|[a0 n0] L1 IH]; intros HN; [reflexivity|]. cbn [app].
rewrite lb_remove_other; [f_equal; apply IH; intros n1 Hin; apply (HN n1); right; exact Hin | cbn; intros E; subst a0; apply (HN n0); left; reflexivity]. }
assert (NIN : forall n, ~ In (tl_name l, n) LBx).
{ intros n Hin. destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (tl_name l) n HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (_ & _ & H0 & _). lia.
- pose proof (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2)) as ND. rewrite !map_app, Hnbs in ND. cbn [map blk_addr fst app] in ND.
apply NoDup_remove_2 in ND. apply ND. apply in_or_app; left. change (tl_name l) with (blk_addr (tl_name l, n)). apply in_map. exact Hin. }
assert (ELB : lb_remove (tl_name l) (LBx ++ tl_nbs l ++ REST) = LBx ++ REST).
{ rewrite (RAPP _ _ _ NIN). f_equal. destruct NM as [[Hn0 Hnbs] | [Hn0 [nn Hnbs]]].
- rewrite Hn0, Hnbs. cbn [app]. apply lb_remove_notin. intros nn Hin.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 nn HP2 ltac:(apply in_or_app; left; apply in_or_app; right; rewrite Hnbs; exact Hin)) as (_ & _ & H0 & _). lia.
- rewrite Hnbs. cbn [app]. apply lb_remove_head. }
rewrite ELB in HPR3, HP3.
assert (INrX : In (r, 72) (LBx ++ REST)) by (apply in_or_app; right; exact INrR).
assert (INqX : In (q, 32 * mxd) (LBx ++ REST)) by (apply in_or_app; right; exact INqR).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; exact INrX | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in LV1; [| eapply client_range_block; [apply in_or_app; left; exact INqX | lia | cbn; lia]]. a4l.
apply (TSP _ _ _ _ _ HPR3 ltac:(apply in_or_app; left; exact INqX)) in TS2; [| rewrite lupd_length; exact LEN].
assert (INqN2 : In (q, 32 * mxd) ((LBx ++ tl_nbs l ++ REST) ++ LM)) by (apply in_or_app; left; exact INqN).
assert (HPRb : heap_pres A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) me m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [exact INqN2|]. split; [exact NQM | lia].
- eapply heap_pres_weaken; [exact HPR3 | lia | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb]]. }
assert (AGP4 : agree_on asegs P m m3).
{ eapply agree_on_trans; [exact AGP3|]. eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity |].
intros b Hb. apply in_or_app; left. apply in_or_app; right. rewrite EREST. apply in_or_app; left; exact Hb. }
assert (CBDJ : forall a n, In (a, n) LBx -> disjoint_from [(bse, bse + 32)] a n).
{ intros a n Hin.
assert (NEq : a <> q).
{ intros ->. exact (nodup_prefix_suffix LBx (tl_nbs l ++ REST) q n (32 * mxd) (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2)) Hin INqN0). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n q (32 * mxd) HP2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) INqN2 NEq) as DJ.
cbn. split; [lia | exact I]. }
assert (AGX3 : agree_on asegs LBx m2 m3).
{ eapply agree_on_trans; [eapply (agree_of_munch asegs); [exact MU | exact WM | exact CBDJ] |].
eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
clear MU WM MI HPRa AGP3.

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
destruct (SHAD _ _ _ _ m3 HP3 INrX INqX) as [SHr SHl].
reenterA asegs A4L HIx asegs_wx HP3.
asan_rechkB.
step. step.
ub_bse q bse (Z.of_nat i).
step. step. ub_lvl q bse (Z.of_nat i). step. ub_if_lit.
step. step. step.
ub_geu bse (Z.of_nat i * 32).
step. ub_if_lit.
step. if_falsex.
step.
ub_bse q bse (Z.of_nat i).
step. ub_land Hb8. step. ub_if_lit.
step.
asan_chkB.
stepz.
try clear SHr; try clear SHl.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TS3 : tstack asegs mc q (lupd levels i lvl_reset)) end.
{ rewrite <- (lupd_lupd levels i l2 lvl_reset). subst bse.
eapply (tstack_put asegs m3 _ q (lupd levels i l2) i lvl_reset []); [exact TS2 | rewrite lupd_length; lia | exact MU | exact WM | intros; exact I | unfold srec_cells; cbn [tl_st tl_ss tl_cur tl_name lvl_reset]; assumption]. }
do 8 step.
step.
evt_done5. apply K. unfold tok_reset_level_postB.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, (charge B2 512 (if tl_name l =? 0 then 0 else uw_cost UWptr)), (Z_to_bv 64 (bse + 24)) end.
split; [apply ret_statew_intro; [exact FS2 | exact FRM2]|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3]|].
split.
{
assert (HP4 : HEAPAx A3 (LBx ++ REST) LM FRS (charge B2 512 (if tl_name l =? 0 then 0 else uw_cost UWptr)) m4 md3) by (heap_nowA A4L HIx HP3 MU WM MI).
destruct OUTx as [[ELx Hc] | (s' & Es & Hrc & ELx & JV)].
- left. split; [exact Hc|]. rewrite ELx in HP4. exact HP4.
- right. exists s'. split; [exact Es|]. split; [exact Hrc|]. rewrite ELx in HP4. split; [| exact HP4].
eapply (jval_agree asegs A4F s' (tl_cbs l) m2 m4); [exact JV | | apply incl_refl].
rewrite <- ELx. eapply agree_on_trans; [exact AGX3|]. eapply (agree_of_munch asegs); [exact MU | exact WM | exact CBDJ]. }
split; [exact TS3|]. split; [unfold tok_cells_g; exact BLK|].
split; [release_frame FR ST3 (bv_unsigned sp); exact ST3|].
split.
{ eapply heap_pres_trans; [exact HPRb|].
eapply (heap_pres_of_munch A4H (LB0 ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros bb Hbb; apply in_or_app; apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; rewrite EREST; apply in_or_app; right; right; right; exact Hbb | right; exact Hbb] | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, (32 * mxd). split; [apply in_or_app; left; exact INqX|]. split; [exact NQM | lia]. }
split; [exact ERR3|].
split; [eapply agree_on_trans; [exact AGP4|]; eapply (agree_of_munch asegs); [exact MU | exact WM | intros a n Hin; cbn; split; [pose proof (PDJ a n Hin); lia | exact I]] |].
clear - BB BB2 BD2 HB2 HD2. unfold put_costA in *. unfold lvl_blocks in *. rewrite ?length_app in *.
destruct (tl_cs l); [destruct (rc =? 1)|]; destruct (tl_name l =? 0); cbn [bB bD charge uw_cost] in *; lia.
Qed.
End TokResetLvl.
End RC__1.
