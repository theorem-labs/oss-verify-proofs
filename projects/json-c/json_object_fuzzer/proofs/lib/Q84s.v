(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH Qtgi Qsw7 QJjn QTEu QKQo QPZI QlCE Q6WR Q7UD Qhd4 Qwm6 QlKV QJZd Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi Qsw7 QJjn. Import QTEu. Import QKQo. Import QPZI.Mq4 QlCE.Mq1.
Import Q6WR.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QJZd.Mq5 QlKV.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition json_tokener_new_A_entry : Z := 0x92ac4.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma tstack_of_zerosA : forall m k A,
rw_cells asegs m A [CB (32 * k)%nat (repeat (Z_to_bv 8 0) (32 * k))] ->
tstack asegs m A (repeat lvl_zero k).
Proof.
intros m k. induction k as [|k IH]; intros A H i l Hl.
- destruct i; discriminate.
- replace (32 * S k)%nat with (32 + 32 * k)%nat in H by lia.
rewrite repeat_app in H.
destruct (rw_cells_CB_cut asegs m A _ _ 32 H ltac:(lia)) as [H0 H1].
rewrite firstn_app, firstn_all2 in H0 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, firstn_O, app_nil_r in H0.
rewrite skipn_app, skipn_all2 in H1 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, skipn_O, app_nil_l in H1.
replace (32 + 32 * k - 32)%nat with (32 * k)%nat in H1 by lia.
destruct i as [|i].
+ cbn in Hl. injection Hl as <-. rewrite Nat2Z.inj_0, Z.mul_0_r, Z.add_0_r.
eapply rw_cells_recast; [exact H0 | cbn; repeat split | vm_compute; reflexivity | reflexivity].
+ cbn [nth_error] in Hl. specialize (IH (A + 32) H1 i l Hl).
replace (A + 32 * Z.of_nat (S i)) with (A + 32 + 32 * Z.of_nat i) by lia. exact IH.
Qed.

Definition tok_fresh32 (m : word -> option byte) (BS : list blk) (tk : Z) : Prop :=
exists stack pb PBS,
BS = [(tk, TOK_SZ); (stack, TSTACK_SZ)] ++ PBS /\
rw_cells asegs m tk (tok_cells pb 0 stack (TS (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 8 0))) /\
pbuf_fresh32 m PBS pb /\ pb <> 0 /\
tstack asegs m stack (lvl_reset :: repeat lvl_zero 31).

Lemma pbuf_fresh32_agree : forall BS m m' PBS pb, pbuf_fresh32 m PBS pb -> agree_on asegs BS m m' -> incl PBS BS -> pbuf_fresh32 m' PBS pb.
Proof.
intros BS m m' PBS pb (buf & post & E & C) AG Hi. subst PBS. exists buf, post. split; [reflexivity|].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; left; reflexivity | apply Hi; right; left; reflexivity].
Qed.

Section TokNewA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition toknew_costB : Z := (16 * 72 + 512) + (16 * 1024 + 512) + pbnew_costB + 1024.

Definition toknew_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - toknew_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, tok_fresh32 m' BS r /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

Lemma json_tokener_new_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x92b10) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - put_stk_A - 96 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 32 ->
toknew_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', toknew_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_new_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA A0 BB BD K. subst a0.
unfold_consts. unfold toknew_costB, pbnew_costB in BB. unfold put_stk_A in LOS. unfold A_SB, A_TP, A_ERRNO, json_tokener_new_A_entry in *.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. subst tp.
carve_frame 80%nat ST.
do 11 step.
step. if_falsex.
step. step. step. step.
step. step. step.

alloc_callA (hiA_calloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 HPR2 ERR2 OUT. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT as [(-> & _ & HP2) | (Hr & BLK & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. step. step. do 12 step.
evt_done5. apply K. unfold toknew_postA.
exists m2, 0, errv2, (charge B (16 * (1 * 72) + 512) (uw_cost u)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold toknew_costB, pbnew_costB; cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat (1 * 72)) with 72%nat in BLK. change (1 * 72) with 72 in HP2.
pose proof (rw_cells_recast asegs _ _ _ tok_cells0 BLK ltac:(cbn; repeat split; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as BLK'.
clear BLK. rename BLK' into BLK. unfold tok_cells0 in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 72 Hal Hlo Hhi Himg_r. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step. step. step.

alloc_callA (hiA_calloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [cbn [uw_cost bD bB charge] in *; lia]).
intros ms3 m3 md3 A3 q errv3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
clear MU WM MI ST2.
assert (EPI : forall mm (Am : ASA A4L HIx) (Bm : bud) mdm ev (Fm : bvmap 5 word) (fcm : bv 32)
(y1 yt0 yt1 yt2 x8 x9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x18 x19 x20 x21 x22 x23 x24 yt3 yt4 yt5 yt6 : word),
fsaved F Fm -> (frm0 fc -> frm0 fcm) ->
HEAPAx Am LB LM FRS Bm mm mdm -> model_vm_only (cfg_model md) (cfg_model mdm) ->
stk asegs mm lo (bv_unsigned sp + -80) ->
rw_cells asegs mm (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mm -> rw_cells asegs mm (6434400 - 164) [C4 ev] ->
bB B - ((16 * 72 + 512) + (16 * 1024 + 512) + (768 + 1024 + 512) + 1024) <= bB Bm -> bD B - uw_cost u <= bD Bm ->
AJ5 A4L HIx Am T mdm
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 6434400) yt0 yt1 yt2 x8 x9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 yt3 yt4 yt5 yt6)
Fm (Z_to_bv 64 0x92cd4) fcm None mm (seg_rom asegs))).
{ intros until yt6. intros FSm FRMm HPm VMm STm FRm HPRm ERRm BBm BDm.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPm) as MIm.
pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] mm) as MUm. pose proof (wmono_refl asegs mm) as WMm.
reenterA asegs A4L HIx asegs_wx HPm.
step. step. do 12 step.
evt_done5. apply K. unfold toknew_postA.
exists mm, 0, ev, Bm.
split; [apply ret_statew_intro; [exact FSm | exact FRMm]|]. split; [exact VMm|]. split; [release_frame FRm STm (bv_unsigned sp); exact STm|].
split; [exact HPRm|]. split; [exact ERRm|]. split; [unfold toknew_costB, pbnew_costB; lia|]. split; [exact BDm|].
left. split; [reflexivity|].
heap_nowA A4L HIx HPm MUm WMm MIm. }
destruct OUT3 as [(-> & _ & HP3) | (Hq & SBLK & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 72 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 0 r 72 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 8 r 72 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP8.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA.
stepz. step. if_true.
step. step.
clear SHr SEP0 SEP8.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 72. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms4 m4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP4 by (destruct (Z.eqb_spec r 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
replace (ret_pc (Z_to_bv 64 0x92cd4)) with (Z_to_bv 64 0x92cd4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
eapply EPI; [apply fsaved_refl | intros Hf; exact Hf | exact HP4 | eapply model_vm_only_trans; [exact VM2 | eapply model_vm_only_trans; [exact VM3 | exact VM4]] | exact ST4 | exact FR | exact HPR | exact ERR4
| cbn [bB charge] in *; lia | destruct u; cbn [bD charge uw_cost] in *; lia].
+
change (32 * 32) with 1024 in HP3.
destruct (rw_cells_CB_cut asegs _ _ _ _ 32 SBLK ltac:(cbn; lia)) as [SB0 SREST]. clear SBLK.
pose proof (rw_cells_recast asegs _ _ _ lvl_cells0 SB0 ltac:(cbn; repeat split; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as SB0'.
clear SB0. rename SB0' into SB0. unfold lvl_cells0 in SB0.
replace (skipn 32 (repeat (Z_to_bv 8 0) (Z.to_nat (32 * 32)))) with (repeat (Z_to_bv 8 0) (32 * 31)) in SREST by reflexivity.
change (Z.to_nat (32 * 32) - 32)%nat with (32 * 31)%nat in SREST. change (Z.of_nat 32) with 32 in SREST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 q 1024 Hqal Hqlo Hqhi Himg_q.
assert (Hqr : q <> r) by (intros E; pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND; cbn in ND; inversion ND as [|z l Hni Hnd]; apply Hni; left; symmetry; exact E).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 1024 r 72 HP3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hqr) as Hdqr.
shadow_nowA A4L HIx HP3 r 72 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 0 r 72 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 8 r 72 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP8.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
stash SB0. stash SREST. stash Hdqr.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA.
step. step. if_falsex.
step.
clear SHr SEP0 SEP8. unstash SB0. unstash SREST. unstash Hdqr.
lazymatch type of MU with munch _ _ ?mc =>
lazymatch type of SB0 with rw_cells _ _ _ ?cs =>
assert (SB0' : rw_cells asegs mc q cs) by (eapply rw_cells_transport; [exact SB0 | exact MU | exact WM | cbn; lia]); clear SB0; rename SB0' into SB0 end;
lazymatch type of SREST with rw_cells _ _ _ ?cs =>
assert (SR' : rw_cells asegs mc (q + 32) cs) by (eapply rw_cells_transport; [exact SREST | exact MU | exact WM | cbn; lia]); clear SREST; rename SR' into SREST end
end.

evt_done5.
eapply (printbuf_new_A_cps HIx) with (u := UWptr) (lo := lo);
[ heap_nowA A4L HIx HP3 MU WM MI | apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right] | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp - 80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try eassumption.
all: try (unfold pbnew_costB; cbn [bB bD charge uw_cost] in *; lia).
intros ms4 md4 A4 (m4 & pbr & e4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in SB0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in SREST; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
clear MU WM MI ST3.
cbn [uw_cost] in BD4.
destruct OUT4 as [(-> & HP4) | (Hpbr & [PBS [PBF HP4]])]; [| pose proof (pbuf_fresh32_pbuf _ _ _ PBF) as PB].
*
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
shadow_nowA A4L HIx HP4 r 72 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 0 r 72 HP4 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 8 r 72 HP4 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP8.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
step. asan_chkA.
stepz. step. if_true.
try clear SHr.
lazymatch type of HP4 with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx _ ?mdx =>
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPc : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx) by heap_nowA A4L HIx HP4 MU WM MI end end.
shadow_nowA A4L HIx HPc r 72 SHr. a4l. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step. step.
try clear SHr; try clear SEP0; try clear SEP8.
alloc_callA (hiA_free A4L HIx) blk q uw UWptr A4L HIx HP4 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 1024. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec q 0); unfold pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia).
intros ms5 mq5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if q =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (Z.eqb_spec q 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP4 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI BLK SB0 SREST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72)] mq5) as MU. pose proof (wmono_refl asegs mq5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 72. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); unfold pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia).
intros ms6 mq6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. a4l.
rewrite lb_remove_head in HPR6, HP6.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (Z.eqb_spec r 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP5 HPR6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. a4l.
replace (ret_pc (Z_to_bv 64 0x92cd4)) with (Z_to_bv 64 0x92cd4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
eapply EPI; [exact FS4 | exact FRM4 | exact HP6 | | exact ST6 | exact FR | exact HPR | exact ERR6 | unfold pbnew_costB in *; cbn [bB charge uw_cost] in *; lia | unfold pbnew_costB in *; cbn [bD charge uw_cost] in *; lia].
eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM4|]. eapply model_vm_only_trans; [exact VM5| exact VM6].
*
pose proof PB as (buf & bpos & size & pre & post & EPBS & Lpre & CORE). subst PBS. cbn [app] in HP4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
blk_factsA A4L HIx HP4 pbr 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP4 buf size Hbal Hblo Hbhi Himg_b.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP4) as ND. cbn [map blk_addr fst app] in ND.
apply List.NoDup_cons_iff in ND as [Hni1 ND1]. apply List.NoDup_cons_iff in ND1 as [Hni2 ND2].
assert (Hpq : pbr <> q) by (intros E; apply Hni1; right; left; congruence).
assert (Hbq : buf <> q) by (intros E; apply Hni2; left; congruence).
assert (Hpr : pbr <> r) by (intros E; apply Hni1; right; right; left; congruence).
assert (Hbr : buf <> r) by (intros E; apply Hni2; right; left; congruence).
clear Hni1 Hni2 ND2.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 q 1024 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hpq) as Hdpq.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf size q 1024 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hbq) as Hdbq.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 r 72 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hpr) as Hdpr.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf size r 72 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hbr) as Hdbr.
stash PB. stash PBF. stash Lpre. stash CORE.

apply (rw_cells_recast asegs _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in SB0;
[| cbn; repeat split | vm_compute; reflexivity | reflexivity].
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72); (q, q + 32)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.

assert (SHAD : forall Ax Bx mdx mc, HEAPAx Ax ((pbr, 16) :: (buf, size) :: (q, 1024) :: (r, 72) :: LB) LM FRS Bx mc mdx ->
ro_cells asegs mc (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ ro_cells asegs mc (q / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax Bx mdx mc HPc. split.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HPc ltac:(in_app_prefix)) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ q 1024 HPc ltac:(in_app_prefix)) as SH. unfold shad in SH.
rewrite (shadow_bytes_split 1024 4) in SH by lia. apply bytes_at_app in SH as [SH4 _].
a4l. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH4]. }
destruct (SHAD _ _ _ m4 HP4) as [SHr SHq].
reenterA asegs A4L HIx asegs_wx HP4.
step. asan_chkA.
step. step. if_falsex.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP4 MU WM MI)) as [SHr SHq] end.
step. asan_chkA.
step.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP4 MU WM MI)) as [SHr SHq] end.
step. asan_chkA.
step. norm_w32. step. if_falsex.
step. step. step. step.

step. rewrite ?zxb_zero. step. if_false.
step. step. step.
repeat match goal with |- context [Z_to_bv 64 (q + ?k + -16)] => replace (Z_to_bv 64 (q + k + -16)) with (Z_to_bv 64 q) by (f_equal; lia) end.
asan_chkA.
stepz.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP4 MU WM MI)) as [SHr SHq] end.
step. asan_chkA.
stepz.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP4 MU WM MI)) as [SHr SHq] end.
asan_chkA.
step. step.
try clear SHr; try clear SHq.

evt_done5.
pose proof PUT as PUTx. unfold put_stmt_A, put_stmtA in PUTx.
eapply PUTx with (s := None) (BS := []) (p := 0) (rc := 0) (lo := lo);
[ cbn [app]; heap_nowA A4L HIx HP4 MU WM MI | cbn; split; reflexivity | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (unfold put_stk_A; lia).
all: try (replace (bv_unsigned sp - 80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try eassumption.
all: try (cbn [put_costA]; pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP4) as [? ?]; lia).
intros ms5 md5 A5 (m5 & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & OUT5).
destruct RS5 as (uu0 & uu1 & uu2 & vv1 & vv2 & vv3 & vv4 & vv5 & vv6 & vv7 & uu3 & uu4 & uu5 & uu6 & F5 & fc5 & -> & FS5 & FRM5).
a4l. rewrite ?unsigned_lit in ST5 by lia. rewrite ?unsigned_lit in HPR5 by lia.
cbn [put_costA] in BB5.
destruct OUT5 as [[_ HP5] | (s' & Es & _)]; [| discriminate].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in BLK; [| eapply (client_range_block A4H _ _ _ _ r 72); [in_app_prefix | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in SB0; [| eapply (client_range_block A4H _ _ _ _ q 1024); [in_app_prefix | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in SREST; [| eapply (client_range_block A4H _ _ _ _ q 1024); [in_app_prefix | lia | cbn; lia]]. a4l.
assert (AG45 : agree_on asegs [(pbr, 16); (buf, size)] m4 m5).
{ eapply agree_on_trans.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn in Hb. cbn.
destruct Hb as [Hb|[Hb|Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
- eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros bb Hb; in_sub Hb]. }
assert (HPR45 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP4 | intros bb Hb; in_sub Hb | clia | solve_clientWA A4L HIx HP4].
- eapply heap_pres_weaken; [exact HPR5 | lia | intros bb Hb; in_sub Hb]. }
clear MU WM MI PUTx.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 32)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
destruct (SHAD _ _ _ m5 HP5) as [SHr SHq].
reenterA asegs A4L HIx asegs_wx HP5.
step. rewrite ?zxb_zero. step. if_false.
step. step.
asan_chkA.
stepz.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP5 MU WM MI)) as [SHr SHq] end.
step. asan_chkA.
step. step.
try clear SHr; try clear SHq.

alloc_callA (hiA_free A4L HIx) blk 0 uw UWptr A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (intros C; exfalso; lia).
all: try (cbn [bB bD charge uw_cost] in *; unfold pbnew_costB in *; lia).
all: try (cbn [Z.eqb]; pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP5) as [? ?]; lia).
intros ms7 mq7 md7 A7 r7 RS7 VM7 ST7 HPR7 ERR7 HP7. open_ret RS7. a4l.
rewrite (lb_remove_notin 0) in HP7, HPR7 by (intros nn Hin; pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ 0 nn HP5 ltac:(apply in_or_app; left; exact Hin)) as (_ & _ & H0 & _); lia).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR7) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR7) in BLK; [| eapply (client_range_block A4H _ _ _ _ r 72); [in_app_prefix | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR7) in SB0; [| eapply (client_range_block A4H _ _ _ _ q 1024); [in_app_prefix | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR7) in SREST; [| eapply (client_range_block A4H _ _ _ _ q 1024); [in_app_prefix | lia | cbn; lia]]. a4l.
assert (AG47 : agree_on asegs [(pbr, 16); (buf, size)] m4 mq7).
{ eapply agree_on_trans; [exact AG45|]. eapply agree_on_trans.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn in Hb. cbn.
destruct Hb as [Hb|[Hb|Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia.
- eapply (agree_of_heap_pres asegs A4H); [exact HPR7 | reflexivity | intros bb Hb; in_sub Hb]. }
assert (HPR47 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq7).
{ eapply heap_pres_trans; [exact HPR45|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP5 | intros bb Hb; in_sub Hb | clia | solve_clientWA A4L HIx HP5].
- eapply heap_pres_weaken; [exact HPR7 | lia | intros bb Hb; in_sub Hb]. }
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP7) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 72); (q, q + 32)] mq7) as MU.    pose proof (wmono_refl asegs mq7) as WM.
destruct (SHAD _ _ _ mq7 HP7) as [SHr SHq].
reenterA asegs A4L HIx asegs_wx HP7.
step. rewrite ?zxb_zero. step. if_false.
step. step. step.
asan_chkA.
step. stepz.
step. if_false. step.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP7 MU WM MI)) as [SHr SHq] end.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
stepz.
try clear SHr; try clear SHq.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (SHAD _ _ _ mc ltac:(heap_nowA A4L HIx HP7 MU WM MI)) as [SHr SHq] end.
step. asan_chkA.
stepz. step.
step. do 12 step.
release_frame FR ST7 (bv_unsigned sp).
try clear SHr; try clear SHq.
unstash PB. unstash PBF. unstash Lpre. unstash CORE.
evt_done5. apply K. unfold toknew_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e4, (charge B5 512 0) end.
lazymatch goal with MUf : munch _ mq7 ?mf, WMf : wmono asegs mq7 ?mf |- _ =>
assert (AG4f : agree_on asegs [(pbr, 16); (buf, size)] m4 mf)
by (eapply agree_on_trans; [exact AG47|]; eapply (agree_of_munch asegs); [exact MUf | exact WMf |]; intros bb kk Hb; cbn in Hb; cbn;
destruct Hb as [Hb|[Hb|Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia);
assert (HPRf : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mf)
by (eapply heap_pres_trans; [exact HPR47|]; eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MUf | exact WMf |];
eapply (client_outsideA A4L HIx); [exact HP7 | intros bb Hb; in_sub Hb | clia | solve_clientWA A4L HIx HP7]);
assert (HPf : HEAPAx A7 ((pbr, 16) :: (buf, size) :: (q, 1024) :: (r, 72) :: LB) LM FRS (charge B5 512 0) mf md7)
by (eapply (heapA_client_frame A4L HIx); [exact HP7 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP7 MUf); solve_frameW_withA HP7 | exact WMf | assumption])
end.
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf))] |].
split; [eapply model_vm_only_trans; [exact VM2|]; eapply model_vm_only_trans; [exact VM3|]; eapply model_vm_only_trans; [exact VM4|]; eapply model_vm_only_trans; [exact VM5 | exact VM7] |].
split; [assumption|]. split; [exact HPRf|]. split; [exact ERR7|].
split; [unfold toknew_costB, pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia|]. split; [cbn [bB bD charge uw_cost] in *; lia|].
right. split; [exact Hr|]. exists ([(r, 72); (q, 1024)] ++ [(pbr, 16); (buf, size)]). split.
-- exists q, pbr, [(pbr, 16); (buf, size)]. split; [reflexivity|]. split; [exact BLK|]. split; [| split; [exact Hpbr|]].
++ eapply pbuf_fresh32_agree; [exact PBF | exact AG4f | apply incl_refl].
++ intros i l Hl. destruct i as [|i].
** cbn in Hl. injection Hl as <-. rewrite Z.mul_0_r, Z.add_0_r.
eapply rw_cells_recast; [exact SB0 | cbn; repeat split | vm_compute; reflexivity | reflexivity].
** cbn [nth_error] in Hl.
replace (q + 32 * Z.of_nat (S i)) with (q + 32 + 32 * Z.of_nat i) by lia.
exact (tstack_of_zerosA _ 31 (q + 32) SREST i l Hl).
-- eapply (heapA_perm A4L HIx); [exact HPf | cbn [app]; perm | apply Permutation_refl | apply Permutation_refl].
Qed.
End TokNewA.
End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlCE.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition json_tokener_new_A_entry : Z := 0x932bc.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma tstack_of_zerosA : forall m k A,
rw_cells asegs m A [CB (32 * k)%nat (repeat (Z_to_bv 8 0) (32 * k))] ->
tstack asegs m A (repeat lvl_zero k).
Proof.
intros m k. induction k as [|k IH]; intros A H i l Hl.
- destruct i; discriminate.
- replace (32 * S k)%nat with (32 + 32 * k)%nat in H by lia.
rewrite repeat_app in H.
destruct (rw_cells_CB_cut asegs m A _ _ 32 H ltac:(lia)) as [H0 H1].
rewrite firstn_app, firstn_all2 in H0 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, firstn_O, app_nil_r in H0.
rewrite skipn_app, skipn_all2 in H1 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, skipn_O, app_nil_l in H1.
replace (32 + 32 * k - 32)%nat with (32 * k)%nat in H1 by lia.
destruct i as [|i].
+ cbn in Hl. injection Hl as <-. rewrite Nat2Z.inj_0, Z.mul_0_r, Z.add_0_r.
eapply rw_cells_recast; [exact H0 | cbn; repeat split | vm_compute; reflexivity | reflexivity].
+ cbn [nth_error] in Hl. specialize (IH (A + 32) H1 i l Hl).
replace (A + 32 * Z.of_nat (S i)) with (A + 32 + 32 * Z.of_nat i) by lia. exact IH.
Qed.

Definition tok_fresh32 (m : word -> option byte) (BS : list blk) (tk : Z) : Prop :=
exists stack pb PBS,
BS = [(tk, TOK_SZ); (stack, TSTACK_SZ)] ++ PBS /\
rw_cells asegs m tk (tok_cells pb 0 stack (TS (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 8 0))) /\
pbuf_fresh32 m PBS pb /\ pb <> 0 /\
tstack asegs m stack (lvl_reset :: repeat lvl_zero 31).

Lemma pbuf_fresh32_agree : forall BS m m' PBS pb, pbuf_fresh32 m PBS pb -> agree_on asegs BS m m' -> incl PBS BS -> pbuf_fresh32 m' PBS pb.
Proof.
intros BS m m' PBS pb (buf & post & E & C) AG Hi. subst PBS. exists buf, post. split; [reflexivity|].
eapply (pbuf_core_agree asegs); [exact C | exact AG | apply Hi; left; reflexivity | apply Hi; right; left; reflexivity].
Qed.

Section TokNewB.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis PUT : put_stmt_A HIx.

Definition toknew_costB : Z := (16 * 72 + 512) + (16 * 1024 + 512) + pbnew_costB + 1024.

Definition toknew_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - toknew_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, tok_fresh32 m' BS r /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

Lemma json_tokener_new_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x932fc) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - put_stk_A - 128 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 32 ->
toknew_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', toknew_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_new_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA A0 BB BD K. subst a0.
unfold_consts. unfold toknew_costB, pbnew_costB in BB. unfold put_stk_A in LOS. unfold A_SB, A_TP, A_ERRNO, json_tokener_new_A_entry in *.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. subst tp.
carve_frame 64%nat ST.
do 8 step.
step. if_falsex.
step. step. step. step.
step. step. step.

alloc_callA (hiA_calloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 m2 md2 A2 r errv2 RS VM2 ST2 HPR2 ERR2 OUT. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT as [(-> & _ & HP2) | (Hr & BLK & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. step. step. do 9 step.
evt_done5. apply K. unfold toknew_postA.
exists m2, 0, errv2, (charge B (16 * (1 * 72) + 512) (uw_cost u)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold toknew_costB, pbnew_costB; cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat (1 * 72)) with 72%nat in BLK. change (1 * 72) with 72 in HP2.
pose proof (rw_cells_recast asegs _ _ _ tok_cells0 BLK ltac:(cbn; repeat split; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as BLK'.
clear BLK. rename BLK' into BLK. unfold tok_cells0 in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 72 Hal Hlo Hhi Himg_r. a4l.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step. step. step.

alloc_callA (hiA_calloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [cbn [uw_cost bD bB charge] in *; lia]).
intros ms3 m3 md3 A3 q errv3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
clear MU WM MI ST2.
assert (EPI : forall mm (Am : ASA A4L HIx) (Bm : bud) mdm ev (Fm : bvmap 5 word) (fcm : bv 32)
(y1 yt0 yt1 yt2 x8 x9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x18 x19 x20 x21 yt3 yt4 yt5 yt6 : word) (jf : list byte),
fsaved F Fm -> (frm0 fc -> frm0 fcm) ->
HEAPAx Am LB LM FRS Bm mm mdm -> model_vm_only (cfg_model md) (cfg_model mdm) ->
stk asegs mm lo (bv_unsigned sp + -64) ->
rw_cells asegs mm (bv_unsigned sp + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mm -> rw_cells asegs mm (6444320 - 164) [C4 ev] ->
bB B - ((16 * 72 + 512) + (16 * 1024 + 512) + (768 + 1024 + 512) + 1024) <= bB Bm -> bD B - uw_cost u <= bD Bm ->
AJ5 A4L HIx Am T mdm
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6444320) yt0 yt1 yt2 x8 x9 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
Fm (Z_to_bv 64 0x933e0) fcm None mm (seg_rom asegs))).
{ intros until jf. intros FSm FRMm HPm VMm STm FRm HPRm ERRm BBm BDm.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPm) as MIm.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] mm) as MUm. pose proof (wmono_refl asegs mm) as WMm.
reenterA asegs A4L HIx asegs_wx HPm.
step. step. do 9 step.
evt_done5. apply K. unfold toknew_postA.
exists mm, 0, ev, Bm.
split; [apply ret_statew_intro; [exact FSm | exact FRMm]|]. split; [exact VMm|]. split; [release_frame FRm STm (bv_unsigned sp); exact STm|].
split; [exact HPRm|]. split; [exact ERRm|]. split; [unfold toknew_costB, pbnew_costB; lia|]. split; [exact BDm|].
left. split; [reflexivity|].
heap_nowA A4L HIx HPm MUm WMm MIm. }
destruct OUT3 as [(-> & _ & HP3) | (Hq & SBLK & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 72 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 0 r 72 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 8 r 72 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP8.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. ub_align_near Hal.
step. asan_chkB.
stepz. step. if_true.
step. step.
clear SHr SEP0 SEP8.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 72. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); destruct u; cbn [bB bD charge uw_cost] in *; lia).
intros ms4 m4 md4 A4 r4 RS4 VM4 ST4 HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP4 by (destruct (Z.eqb_spec r 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
replace (ret_pc (Z_to_bv 64 0x933e0)) with (Z_to_bv 64 0x933e0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
eapply EPI; [apply fsaved_refl | intros Hf; exact Hf | exact HP4 | eapply model_vm_only_trans; [exact VM2 | eapply model_vm_only_trans; [exact VM3 | exact VM4]] | exact ST4 | exact FR | exact HPR | exact ERR4
| cbn [bB charge] in *; lia | destruct u; cbn [bD charge uw_cost] in *; lia].
+
change (32 * 32) with 1024 in HP3.
destruct (rw_cells_CB_cut asegs _ _ _ _ 32 SBLK ltac:(cbn; lia)) as [SB0 SREST]. clear SBLK.
pose proof (rw_cells_recast asegs _ _ _ lvl_cells0 SB0 ltac:(cbn; repeat split; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as SB0'.
clear SB0. rename SB0' into SB0. unfold lvl_cells0 in SB0.
replace (skipn 32 (repeat (Z_to_bv 8 0) (Z.to_nat (32 * 32)))) with (repeat (Z_to_bv 8 0) (32 * 31)) in SREST by reflexivity.
change (Z.to_nat (32 * 32) - 32)%nat with (32 * 31)%nat in SREST. change (Z.of_nat 32) with 32 in SREST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 q 1024 Hqal Hqlo Hqhi Himg_q.
assert (Hqr : q <> r) by (intros E; pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND; cbn in ND; inversion ND as [|z l Hni Hnd]; apply Hni; left; symmetry; exact E).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q 1024 r 72 HP3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hqr) as Hdqr.
shadow_nowA A4L HIx HP3 r 72 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 0 r 72 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 8 r 72 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP8.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
stash SB0. stash SREST. stash Hdqr.
reenterA asegs A4L HIx asegs_wx HP3.
step. step. ub_align_near Hal.
step. asan_chkB.
step. step. if_falsex.
step.
clear SHr SEP0 SEP8. unstash SB0. unstash SREST. unstash Hdqr.
lazymatch type of MU with munch _ _ ?mc =>
lazymatch type of SB0 with rw_cells _ _ _ ?cs =>
assert (SB0' : rw_cells asegs mc q cs) by (eapply rw_cells_transport; [exact SB0 | exact MU | exact WM | cbn; lia]); clear SB0; rename SB0' into SB0 end;
lazymatch type of SREST with rw_cells _ _ _ ?cs =>
assert (SR' : rw_cells asegs mc (q + 32) cs) by (eapply rw_cells_transport; [exact SREST | exact MU | exact WM | cbn; lia]); clear SREST; rename SR' into SREST end
end.

evt_done5.
eapply (printbuf_new_A_cps HIx) with (u := UWptr) (lo := lo);
[ heap_nowA A4L HIx HP3 MU WM MI | apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right] | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (replace (bv_unsigned sp - 64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try eassumption.
all: try (unfold pbnew_costB; cbn [bB bD charge uw_cost] in *; lia).
intros ms4 md4 A4 (m4 & pbr & e4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
extend_presA A4L HIx HPR MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in SB0; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in SREST; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
clear MU WM MI ST3.
cbn [uw_cost] in BD4.
destruct OUT4 as [(-> & HP4) | (Hpbr & [PBS [PBF HP4]])]; [| pose proof (pbuf_fresh32_pbuf _ _ _ PBF) as PB].
*
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
shadow_nowA A4L HIx HP4 r 72 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 0 r 72 HP4 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 72 8 r 72 HP4 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP8.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
step. asan_chkB.
stepz. step. if_true.
try clear SHr.
lazymatch type of HP4 with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx _ ?mdx =>
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPc : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx) by heap_nowA A4L HIx HP4 MU WM MI end end.
shadow_nowA A4L HIx HPc r 72 SHr. a4l. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step. step.
try clear SHr; try clear SEP0; try clear SEP8.
alloc_callA (hiA_free A4L HIx) blk q uw UWptr A4L HIx HP4 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 1024. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec q 0); unfold pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia).
intros ms5 mq5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if q =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (Z.eqb_spec q 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP4 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI BLK SB0 SREST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] mq5) as MU. pose proof (wmono_refl asegs mq5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 72. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); unfold pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia).
intros ms6 mq6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. a4l.
rewrite lb_remove_head in HPR6, HP6.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (Z.eqb_spec r 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP5 HPR6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. a4l.
replace (ret_pc (Z_to_bv 64 0x933e0)) with (Z_to_bv 64 0x933e0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
eapply EPI; [exact FS4 | exact FRM4 | exact HP6 | | exact ST6 | exact FR | exact HPR | exact ERR6 | unfold pbnew_costB in *; cbn [bB charge uw_cost] in *; lia | unfold pbnew_costB in *; cbn [bD charge uw_cost] in *; lia].
eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3|]. eapply model_vm_only_trans; [exact VM4|]. eapply model_vm_only_trans; [exact VM5| exact VM6].
*
pose proof PB as (buf & bpos & size & pre & post & EPBS & Lpre & CORE). subst PBS. cbn [app] in HP4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
blk_factsA A4L HIx HP4 pbr 16 Hpal Hplo Hphi Himg_p.
blk_factsA A4L HIx HP4 buf size Hbal Hblo Hbhi Himg_b.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP4) as ND. cbn [map blk_addr fst app] in ND.
apply List.NoDup_cons_iff in ND as [Hni1 ND1]. apply List.NoDup_cons_iff in ND1 as [Hni2 ND2].
assert (Hpq : pbr <> q) by (intros E; apply Hni1; right; left; congruence).
assert (Hbq : buf <> q) by (intros E; apply Hni2; left; congruence).
assert (Hpr : pbr <> r) by (intros E; apply Hni1; right; right; left; congruence).
assert (Hbr : buf <> r) by (intros E; apply Hni2; right; left; congruence).
clear Hni1 Hni2 ND2.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 q 1024 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hpq) as Hdpq.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf size q 1024 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hbq) as Hdbq.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 r 72 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hpr) as Hdpr.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf size r 72 HP4 ltac:(in_app_prefix) ltac:(in_app_prefix) Hbr) as Hdbr.
stash PB. stash PBF. stash Lpre. stash CORE.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] m4) as MU. pose proof (wmono_refl asegs m4) as WM.

assert (SHAD : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM FRS Bx mc mdx -> In (r, 72) LBx ->
ro_cells asegs mc (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPc Ir.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r 72 HPc Ir) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH. }
pose proof (SHAD _ _ _ _ m4 HP4 ltac:(in_app_prefix)) as SHr.
reenterA asegs A4L HIx asegs_wx HP4.
step. asan_chkB.
step. step. if_falsex.
try clear SHr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SHAD _ _ _ _ mc ltac:(heap_nowA A4L HIx HP4 MU WM MI) ltac:(in_app_prefix)) as SHr end.
step. asan_chkB.
stepz.
try clear SHr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SHAD _ _ _ _ mc ltac:(heap_nowA A4L HIx HP4 MU WM MI) ltac:(in_app_prefix)) as SHr end.
step. asan_chkB.
step. norm_w32. step. if_falsex.
step. step. step. step.
try clear SHr.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPc : HEAPAx A4 (lvl_blocks lvl_zero ++ ([(pbr, 16); (buf, size)] ++ (r, 72) :: (q, 1024) :: LB)) LM FRS B4 mc md4)
by (eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP4 MU WM MI | cbn [app lvl_blocks lvl_zero tl_cbs tl_nbs]; perm | apply Permutation_refl | apply Permutation_refl]);
assert (TSc : tstack asegs mc q (repeat lvl_zero 32));
[ intros ii ll Hl; destruct ii as [|ii];
[ cbn in Hl; injection Hl as <-; rewrite Z.mul_0_r, Z.add_0_r; eapply rw_cells_recast; [exact SB0 | cbn; repeat split | vm_compute; reflexivity | reflexivity]
| cbn [nth_error] in Hl; replace (q + 32 * Z.of_nat (S ii)) with (q + 32 + 32 * Z.of_nat ii) by lia; exact (tstack_of_zerosA _ 31 (q + 32) SREST ii ll Hl) ]
| ];
assert (AG4c : agree_on asegs [(pbr, 16); (buf, size)] m4 mc)
by (eapply (agree_of_munch asegs); [exact MU | exact WM |]; intros bb kk Hb; cbn in Hb; cbn;
destruct Hb as [Hb|[Hb|Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia);
assert (HPR4c : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mc)
by (eapply heap_pres_trans; [exact HPR|]; eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP4 | intros bb Hb; in_sub Hb | clia | solve_clientWA A4L HIx HP4])
end.
evt_done5.
eapply (tok_reset_level_B_cps HIx PUT) with (i := 0%nat) (l := lvl_zero) (levels := repeat lvl_zero 32) (P := [(pbr, 16); (buf, size)]) (LB0 := LB) (LM := LM)
(REST := [(pbr, 16); (buf, size)] ++ (r, 72) :: (q, 1024) :: LB) (FRS := FRS) (B := B4) (lo := lo) (q := q) (r := r) (pb := pbr) (depth := 0) (mxd := 32) (fl := 0)
(x := TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0)) (rc := 1);
[ reflexivity | cbn; lia | lia | reflexivity | exact HPc | reflexivity
| cbn; split; reflexivity
| left; split; reflexivity
| exact TSc
| unfold tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote]; eassumption
| rewrite unsigned_lit by lia; eassumption | exact LO | rewrite unsigned_lit by lia; unfold put_stk_A; lia
| rewrite unsigned_lit by lia; clear - SPA SPR; Z.div_mod_to_equations; lia
| rewrite unsigned_lit by lia; lia
| apply heap_pres_refl | eassumption
| cbn [put_costA tl_cs lvl_zero]; unfold pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia
| rewrite unsigned_lit by lia; reflexivity | ].
intros ms5 md5 A5 (m5 & B5 & rv & RS5 & VM5 & OUT5 & TS5 & TOK5 & ST5 & HPR5 & ERR5 & AG5 & BB5 & BD5).
destruct RS5 as (uu0 & uu1 & uu2 & vv1 & vv2 & vv3 & vv4 & vv5 & vv6 & vv7 & uu3 & uu4 & uu5 & uu6 & F5 & fc5 & -> & FS5 & FRM5).
a4l. rewrite ?unsigned_lit in ST5 by lia. rewrite ?unsigned_lit in HPR5 by lia.
cbn [put_costA tl_cs lvl_zero] in BB5.
destruct OUT5 as [[_ HP5] | (s' & Es & _)]; [| discriminate Es]. cbn [app] in HP5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
assert (AG45 : agree_on asegs [(pbr, 16); (buf, size)] m4 m5) by (eapply agree_on_trans; [exact AG4c | exact AG5]).
assert (HPR45 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_pres_trans; [exact HPR4c|]. eapply heap_pres_weaken; [exact HPR5 | lia | intros bb Hb; in_sub Hb]. }
clear MU WM MI HPc TSc AG4c HPR4c SB0 SREST BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (r, r + 72)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
unfold tok_cells_g in TOK5. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK5.
change (lupd (repeat lvl_zero 32) 0 lvl_reset) with (lvl_reset :: repeat lvl_zero 31) in TS5.
stash TS5.
pose proof (SHAD _ _ _ _ m5 HP5 ltac:(cbn [app]; repeat first [left; reflexivity | right])) as SHr.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. ub_if_lit.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
stepz.
try clear SHr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (SHAD _ _ _ _ mc ltac:(heap_nowA A4L HIx HP5 MU WM MI) ltac:(cbn [app]; repeat first [left; reflexivity | right])) as SHr end.
step. asan_chkB.
stepz. step.
step. do 9 step.
release_frame FR ST5 (bv_unsigned sp).
try clear SHr.
unstash PB. unstash PBF. unstash Lpre. unstash CORE. unstash TS5.
evt_done5. apply K. unfold toknew_postA.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e4, B5 end.
lazymatch goal with MUf : munch _ m5 ?mf, WMf : wmono asegs m5 ?mf |- _ =>
assert (AG4f : agree_on asegs [(pbr, 16); (buf, size)] m4 mf)
by (eapply agree_on_trans; [exact AG45|]; eapply (agree_of_munch asegs); [exact MUf | exact WMf |]; intros bb kk Hb; cbn in Hb; cbn;
destruct Hb as [Hb|[Hb|Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia);
assert (HPRf : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mf)
by (eapply heap_pres_trans; [exact HPR45|]; eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MUf | exact WMf |];
eapply (client_outsideA A4L HIx); [exact HP5 | intros bb Hb; in_sub Hb | clia | solve_clientWA A4L HIx HP5]);
assert (HPf : HEAPAx A5 ((pbr, 16) :: (buf, size) :: (r, 72) :: (q, 1024) :: LB) LM FRS B5 mf md5)
by (eapply (heapA_client_frame A4L HIx); [exact HP5 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP5 MUf); solve_frameW_withA HP5 | exact WMf | assumption]);
assert (TSf : tstack asegs mf q (lvl_reset :: repeat lvl_zero 31))
by (eapply (tstack_transport asegs); [exact TS5 | exact MUf | exact WMf |]; intros jj Hj; cbn [length] in Hj; rewrite repeat_length in Hj;
cbn [disjoint_from]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; repeat split; try exact I; lia)
end.
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf))] |].
split; [eapply model_vm_only_trans; [exact VM2|]; eapply model_vm_only_trans; [exact VM3|]; eapply model_vm_only_trans; [exact VM4 | exact VM5] |].
split; [assumption|]. split; [exact HPRf|]. split; [assumption|].
split; [unfold toknew_costB, pbnew_costB in *; cbn [bB bD charge uw_cost] in *; lia|]. split; [cbn [bB bD charge uw_cost] in *; lia|].
right. split; [exact Hr|]. exists ([(r, 72); (q, 1024)] ++ [(pbr, 16); (buf, size)]). split.
-- exists q, pbr, [(pbr, 16); (buf, size)]. split; [reflexivity|]. split; [| split; [| split; [exact Hpbr | exact TSf]]].
++ lazymatch goal with H : rw_cells asegs _ r _ |- _ => eapply rw_cells_recast; [exact H | cbn; repeat split; reflexivity | cbn; reflexivity | reflexivity] end.
++ eapply pbuf_fresh32_agree; [exact PBF | exact AG4f | apply incl_refl].
-- eapply (heapA_perm A4L HIx); [exact HPf | cbn [app]; perm | apply Permutation_refl | apply Permutation_refl].
Qed.
End TokNewB.
End RC__1.
