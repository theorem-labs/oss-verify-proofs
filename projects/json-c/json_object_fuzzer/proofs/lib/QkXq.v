(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn Q6WR QrPc QYIF QrIB Q7UD Qhd4 Qwm6 QlKV QsKa Qekr Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.

Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qekr.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoSetScal2.
Variable HIx : heap_iface_A A4L.
Notation jo_set_scalar_A_stmt := (jo_set_scalar_A_stmt HIx).
Notation jroot_hdrA := (jroot_hdrA).
Notation blk_gran0A := (blk_gran0A HIx).

Lemma set_int64_A : jo_set_scalar_A_stmt 0x9c930.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_truex.
step. step. step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 56 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 56 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 56)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_falsex.
step. step. step.
asan_chkA.
step. rewrite sx32_small by (unfold JT_INT; lia).
step.
step. if_lit.
step.
asan_chkA.
stepz.
step.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 56 SHp. a4l. clear HPc.
asan_chkA.
stepz.
do 5 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 56. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 56) :: PBS) LB p 56 56 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 56) :: PBS) ++ LB) LM p 56 56 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 56 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists 0, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_INT in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_falsex.
step. step. step.
asan_chkA.
step. rewrite sx32_small by lia.
step.
step. if_truex.
do 4 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.

Lemma set_uint64_A : jo_set_scalar_A_stmt 0x9d314.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_truex.
step. step. step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 56 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 56 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 56)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_falsex.
step. step. step.
asan_chkA.
step. rewrite sx32_small by (unfold JT_INT; lia).
step.
step. if_lit.
step.
asan_chkA.
stepz.
step.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 56 SHp. a4l. clear HPc.
asan_chkA.
step.
stepz.
do 5 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 56. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 56) :: PBS) LB p 56 56 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 56) :: PBS) ++ LB) LM p 56 56 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 56 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists 1, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_INT in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_falsex.
step. step. step.
asan_chkA.
step. rewrite sx32_small by lia.
step.
step. if_truex.
do 4 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.

Lemma set_boolean_A : jo_set_scalar_A_stmt 0x9c2ac.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_truex.
step. step. step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_BOOLEAN) as [E | NE].
-
specialize (TB E). subst r ty. clear TI. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB. unfold jhdr_cells, JT_BOOLEAN in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 48 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_falsex.
step. step. step.
asan_chkA.
step. rewrite sx32_small by (unfold JT_BOOLEAN; lia).
step.
step. if_lit.
step.
asan_chkA.
stepz.
do 5 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 48)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists (bv_unsigned a1), junk_. split; [reflexivity|]. unfold jhdr_cells, JT_BOOLEAN. cbn [app]. rewrite Z_to_bv_bv_unsigned. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_BOOLEAN in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
step. step.
step. if_falsex.
step. step. step.
asan_chkA.
step. rewrite sx32_small by lia.
step.
step. if_truex.
do 4 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.
End AJoSetScal2.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QZDE QRUw QSL3 QT7b Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QSL3. Import QT7b.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq5 Q30W.Mq1 Qekr.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Local Ltac sepcache_on ::= fail.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Notation SB0 := 2147450880.

Lemma mod16_mod8 : forall k, k mod 16 = 0 -> k mod 8 = 0.
Proof. intros k H. Z.div_mod_to_equations. lia. Qed.

Lemma land3_of_mod8 : forall k, 0 <= k -> k mod 8 = 0 -> Z.land k 3 = 0.
Proof.
intros k Hk H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. Z.div_mod_to_equations. nia.
Qed.

Section LhHashA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variable MREL : config -> config -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis OBL_ISTRLEN : astrlen_any_spec_A HIx.

Hypothesis OBL_BLK40 : forall A LB LM FR B m md a n, HEAPAx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> n < 2^40.

Definition seed_settle_A_post (sp gp s0v : word) (s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (errv' : word),
ms' = MS (mkR x1 sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0v (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c20) fc None m' (seg_rom asegs) /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\ HEAPAx A' LB LM FRS B m' md'.

Definition seed_settle_A_stmt (SD : Z) : Prop :=
forall (x1 sp gp t0 t1 t2 s0v a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv seedv : word),
HEAPAx A LB LM FRS B m md -> lh_globA m ->
rw_cells asegs m GSEEDA [C4 seedv] -> sx32 seedv = Z_to_bv 64 (-1) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
(forall ms' md' A', seed_settle_A_post sp gp s0v s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0v (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c04) fc None m (seg_rom asegs)).

Variable SD : Z.
Hypothesis SD_ge : 4096 <= SD.
Hypothesis SEED : seed_settle_A_stmt SD.

Lemma key_stringA : forall A LB LM FRS B m md kp kn ks,
HEAPAx A LB LM FRS B m md -> In (kp, kn) LB -> cstr asegs m kp kn ks ->
exists slack, bytes_at asegs m kp (ks ++ Z_to_bv 8 0 :: slack) /\
(- (kp + Z.of_nat (length ks) + 1)) mod 8 <= Z.of_nat (length slack) /\
~ In (Z_to_bv 8 0) ks /\ kp mod 16 = 0 /\ Z.of_nat (length ks) + 1 <= kn /\ 0 < kp /\ kp + kn <= alloc_ceiling /\
kp + Z.of_nat (length ks) + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Proof.
intros A LB LM FRS B m md kp kn ks HP Hin (CL & CNZ & junk & CB).
assert (HinX : In (kp, kn) (LB ++ LM)) by (apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ kp kn HP HinX) as (Hn0 & Hal & Hlo & Hhi & _).
destruct (heapA_blk_slack A4L HIx _ _ _ _ _ _ _ kp kn HP HinX) as [g [G Lg]]. cbn [hl_segs hla_base A4L A4H] in G.
assert (NN : ~ In (Z_to_bv 8 0) ks).
{ intros X. rewrite Forall_forall in CNZ. apply (CNZ _ X). reflexivity. }
assert (LENB : length (ks ++ [Z_to_bv 8 0] ++ junk) = Z.to_nat kn) by (destruct CB as [[[Hwf _] _] _]; exact Hwf).
rewrite !length_app in LENB. cbn [length] in LENB.
assert (BB : bytes_at asegs m kp (ks ++ [Z_to_bv 8 0] ++ junk)).
{ destruct CB as [[[_ _] HB] _]. cbn in HB. rewrite app_nil_r in HB. exact HB. }
exists (junk ++ g).
assert (B2 : bytes_at asegs m kp ((ks ++ [Z_to_bv 8 0] ++ junk) ++ g)).
{ apply bytes_at_app. split; [exact BB|]. rewrite !length_app. cbn [length].
replace (kp + Z.of_nat (length ks + (1 + length junk))) with (kp + kn) by lia. exact G. }
replace ((ks ++ [Z_to_bv 8 0] ++ junk) ++ g) with (ks ++ Z_to_bv 8 0 :: junk ++ g) in B2 by (rewrite <- !app_assoc; reflexivity).
pose proof alloc_ceiling_al16 as C16.
split; [exact B2|]. split; [| split; [exact NN | split; [exact Hal | split; [exact CL | split; [exact Hlo | split; [exact Hhi|]]]]]].
- rewrite length_app.
replace (Z.of_nat (length junk + length g)) with ((kn - Z.of_nat (length ks) - 1) + Z.of_nat (length g)) by lia.
rewrite Lg.
set (x := kp + Z.of_nat (length ks) + 1) in *.
pose proof (Z.div_mod kn 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound kn 16 ltac:(lia)) as B1.
pose proof (Z.div_mod kp 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - kn mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - kn mod 16) 16 ltac:(lia)) as B3.
pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E4. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B4.
set (rn := kn mod 16) in *. set (r8 := (- x) mod 8) in *.
set (qn := kn / 16) in *. set (qb := kp / 16) in *. set (q3 := (16 - rn) / 16) in *. set (q8 := - x / 8) in *.
nia.
- rewrite length_app. rewrite Nat2Z.inj_add, Lg.
pose proof (Z.div_mod kn 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound kn 16 ltac:(lia)) as B1.
pose proof (Z.div_mod kp 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - kn mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - kn mod 16) 16 ltac:(lia)) as B3.
unfold alloc_ceiling in *. pose proof (Z.div_mod rc_ceil 16 ltac:(lia)) as E5.
set (rn := kn mod 16) in *. set (qn := kn / 16) in *. set (qb := kp / 16) in *. set (q3 := (16 - rn) / 16) in *. set (qc := rc_ceil / 16) in *.
nia.
Qed.

Lemma lh_char_hash_A_cps : forall HD, 80 + SD <= HD -> lh_char_hash_A_stmt HIx MREL HD.
Proof.
intros HD HHD. unfold lh_char_hash_A_stmt. intros until ks. intros HP INK CS G ST LO LOS SPA HT ERR TP RA FRM FRN A0 K.
word_range sp SPR. pose proof alloc_ceiling_ge as ACG. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (OBL_BLK40 _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INK)) as KN40.
destruct (key_stringA _ _ _ _ _ _ _ _ _ _ HP INK CS) as (slack & STR & PAD & NN & KAL & KL & KPOS & KHI & KSL).
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof G as (G1 & [seed G2]). unfold GHASHA in G1. unfold GSEEDA in G2.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
a4l. subst a0 tp. unfold lh_char_hash_A_entry. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 80%nat ST.
do 10 step.
step. step.
step. step.
step.
step.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPA A4L HIx A LB LM FRS B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
assert (G1' : lh_globA m1) by (split; [exact G1 | exists seed; exact G2]).
assert (HPR1 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch A4H a4_volatile _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA _ HIx); [exact HP | intros b Hb; exact Hb | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA A4L HIx HP]. }
clear GOT CELL.
destruct (bv_eqb (sx32 seed) (Z_to_bv 64 (-1))) eqn:ESEED; [change (negb true) with false | change (negb false) with true]; cbv iota.
-
evt_done5.
eapply (SEED _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md T A LB LM FRS B lo errv seed);
[exact HP1 | exact G1' | exact G2 | apply (proj1 (Fs.bv_eqb_eq _ _)); exact ESEED | ..]; a4l_goal; rewrite ?unsigned_lit by lia;
[exact ST | exact LO | lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | lia | exact ERR | exact FRM | exact FRN |].
intros ms2 md2 A2 (y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MR2 & ST2 & HPR2 & ERR2 & GL2 & HP2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2, HPR2 by lia.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
assert (HPR12 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_presx_trans; [exact HPR1|]. eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; exact Hb | intros a' Ha'; exact Ha']. }
assert (CS2 : cstr asegs m2 kp kn ks).
{ destruct CS as (CL' & CNZ & junk2 & CB). split; [exact CL'|]. split; [exact CNZ|]. exists junk2.
eapply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR12); [exact CB|]. eapply client_rangex_block; [apply in_or_app; left; exact INK | lia | cbn; lia]. }
clear STR PAD KSL AB slack MU WM MI1 HPR1 HP1 G1' G1 G2 ERR ST.
destruct (key_stringA _ _ _ _ _ _ _ _ _ _ HP2 INK CS2) as (slack & STR & PAD & _ & _ & _ & _ & _ & KSL).
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2.
step. step.
clear MU WM.
eapply (OBL_ISTRLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 md2 A2 LB LM FRS B kp kn kp lo ks slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP2 | exact INK | exact NN | exact STR | exact PAD | exact KSL | exact ST2 | exact LO | exact MI | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end.
unstash STR3.
assert (HP3 : HEAPA A4L HIx A2 LB LM FRS B m3 md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU3); solve_frameW_withA HP2 | exact WM3 | exact MI3]. }
assert (G3 : lh_globA m3).
{ eapply lh_globA_frame; [exact GL2 | exact MU3 | exact WM3 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]. }
pose proof G3 as (G31 & [seed3 G32]). unfold GHASHA in G31. unfold GSEEDA in G32.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ kp kn HP3 INK) as SHB. unfold shad in SHB. a4l.
assert (HPR23 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m2 m3).
{ eapply (heap_presx_of_munch A4H a4_volatile _ (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outsideA _ HIx); [exact HP2 | intros b Hb; exact Hb | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA A4L HIx HP2]. }
clear MU3 WM3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [] m3) as MU.
replace (ret_pc (Z_to_bv 64 658472)) with (Z_to_bv 64 658472) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold GSEEDA.
step. norm_sx32.
step. step. step.
step.
rewrite (unsigned_lit kp) by lia. rewrite (land3_of_mod8 kp) by (first [lia | apply mod16_mod8; exact KAL]).
step.
step. if_true.
eapply evt_cut; [eapply (word_pathA kp kn ks slack m3); [exact STR3 | exact MI3 | apply mod16_mod8; exact KAL | lia | exact KL | lia | exact SHB] |].
cbv beta. intros ms4 (j & Hj & (u0' & u1' & u2' & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3' & u4' & u5' & u6' & ->)).
step. step.
do 9 step.
step.
release_frame FR ST3 (bv_unsigned sp).
step.
evt_done5. apply K. unfold lh_hash_A_post.
lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?x 32)] => set (h := Z.shiftr x 32) end.
assert (Hh : 0 <= h < 2^64).
{ subst h. lazymatch goal with |- context [Z.shiftr (bv_unsigned ?w) 32] => word_range w WR end.
rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. nia. }
exists m3, h, errv2.
split; [unfold ret_statew; do 16 eexists; split; [reflexivity | split; [apply QCcH.fsaved_refl | intros H0; exact H0]] |].
split; [exact Hh|]. split; [exact MR2|]. split; [exact ST3|].
split; [eapply heap_presx_trans; [exact HPR12 | exact HPR23] |].
split; [exact ERR2|]. split; [exact G3 | exact HP3].
-
step. step.
clear MU WM.
eapply (OBL_ISTRLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md A LB LM FRS B kp kn kp lo ks slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact INK | exact NN | exact STR | exact PAD | exact KSL | exact ST | exact LO | exact MI1 | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m1 m3 MU3 WM3; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
unstash STR3.
assert (HP3 : HEAPA A4L HIx A LB LM FRS B m3 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU3); solve_frameW_withA HP1 | exact WM3 | exact MI3]. }
assert (G3 : lh_globA m3).
{ eapply lh_globA_frame; [exact G1' | exact MU3 | exact WM3 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]. }
pose proof G3 as (G31 & [seed3 G32]). unfold GHASHA in G31. unfold GSEEDA in G32.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ kp kn HP3 INK) as SHB. unfold shad in SHB. a4l.
assert (HPR13 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m1 m3).
{ eapply (heap_presx_of_munch A4H a4_volatile _ (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outsideA _ HIx); [exact HP1 | intros b Hb; exact Hb | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA A4L HIx HP1]. }
clear MU3 WM3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [] m3) as MU.
replace (ret_pc (Z_to_bv 64 658472)) with (Z_to_bv 64 658472) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. norm_sx32.
step. step. step.
step.
rewrite (unsigned_lit kp) by lia. rewrite (land3_of_mod8 kp) by (first [lia | apply mod16_mod8; exact KAL]).
step.
step. if_true.
eapply evt_cut; [eapply (word_pathA kp kn ks slack m3); [exact STR3 | exact MI3 | apply mod16_mod8; exact KAL | lia | exact KL | lia | exact SHB] |].
cbv beta. intros ms4 (j & Hj & (u0' & u1' & u2' & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3' & u4' & u5' & u6' & ->)).
step. step.
do 9 step.
step.
release_frame FR ST3 (bv_unsigned sp).
step.
evt_done5. apply K. unfold lh_hash_A_post.
lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?x 32)] => set (h := Z.shiftr x 32) end.
assert (Hh : 0 <= h < 2^64).
{ subst h. lazymatch goal with |- context [Z.shiftr (bv_unsigned ?w) 32] => word_range w WR end.
rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. nia. }
exists m3, h, errv.
split; [unfold ret_statew; do 16 eexists; split; [reflexivity | split; [apply QCcH.fsaved_refl | intros H0; exact H0]] |].
split; [exact Hh|]. split; [apply MREL_refl|]. split; [exact ST3|].
split; [eapply heap_presx_trans; [exact HPR1 | exact HPR13] |].
split; [exact ERR|]. split; [exact G3 | exact HP3].
Qed.
End LhHashA.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj QgoP Q22i QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import QSL3. Import Q22i.
Import Q7UD Qhd4 Qwm6.
Import QsKa.Mq0.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QpNt.Mq4 QsKa.Mq5 Q30W.Mq3 Q30W.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition lh_lookup_A_entry : Z := 0xa27e8.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhLookup.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.

Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Variables (m0 : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (kb kbn : Z).
Hypothesis HP0 : HEAPAx A LB LM FRS B m0 md.
Hypothesis INCL : forall b, In b (lh_blocks t tbl size es) -> In b LB.
Hypothesis KB : In (kb, kbn) LB.
Hypothesis KBlo : kb <= kp.
Hypothesis KBhi : kp + Z.of_nat (length ps) + 1 <= kb + kbn.
Hypothesis PS40 : Z.of_nat (length ps) + 1 < 2^40.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - 112 - 16 - 4096.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Definition lh_lookup_A_post : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ lh_open asegs A4F m' t tbl size es svs
/\ bytes_at asegs m' kp (ps ++ [b0])
/\ lookup_res tbl es ps r.

Definition lk_frameA (m : word -> option byte) (lv : word) : Prop :=
rw_cells asegs m (bv_unsigned sp + -112)
[C8 lv; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Notation SB0 := 2147450880.

Lemma heapA_now : forall m, munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m -> mem_inv asegs m -> HEAPAx A LB LM FRS B m md.
Proof.
intros m MU WM MI. eapply (heapA_client_frame A4L HIx); [exact HP0 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP0 MU). apply Forall_cons; [left; cbn; split; lia | apply Forall_nil].
Qed.

Lemma lh_lookup_nextA :
forall (n cnt : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (hsz hcnt hhd htl : Z),
0 <= cnt < size -> 0 <= n < size -> In size lf_sizes -> mem_inv asegs m ->
rw_cells asegs m t [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free A4F)); C8 (Z_to_bv 64 (fn_lh_char_hash A4F)); C8 (Z_to_bv 64 (fn_lh_char_equal A4F))] ->
ro_cells asegs m (t / 8 + SB0) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
0 < t -> t + 56 <= alloc_ceiling -> t / 8 + SB0 + 7 <= alloc_ceiling ->
evt asegs (fun ms' => exists a0' a1',
(cnt + 1 < size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0' a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 48)) (Z_to_bv 64 (t / 8 + 2147450883)) (Z_to_bv 64 SB0) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 40) (Z_to_bv 64 (-2))
(Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + 2147450886)) (Z_to_bv 64 (next_ix size n)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa288c) fc None m (seg_rom asegs))
\/ (cnt + 1 = size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0' a1' a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 48)) (Z_to_bv 64 (t / 8 + 2147450883)) (Z_to_bv 64 SB0) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 40) (Z_to_bv 64 (-2))
(Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + 2147450886)) (Z_to_bv 64 (next_ix size n)) t3 t4 t5 t6)
F (Z_to_bv 64 0xa2918) fc None m (seg_rom asegs)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 48)) (Z_to_bv 64 (t / 8 + 2147450883)) (Z_to_bv 64 SB0) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2))
(Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + 2147450886)) (Z_to_bv 64 n) t3 t4 t5 t6)
F (Z_to_bv 64 0xa28d8) fc None m (seg_rom asegs)).
Proof.
intros until htl. intros Hcnt Hn Hsz MI HDR SHt Ht Hth HSH.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. norm_sx32.
step.
step. norm_w32. replace (n + 1 + 0) with (n + 1) by lia.
step. rewrite ?(unsigned_lit size), ?(unsigned_lit (n + 1)) by lia.
unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NE].
- rewrite EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. norm_w32. step. rewrite (unsigned_lit size) by lia. rewrite Z.land_0_l.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_truex. apply evt_done. do 2 eexists. left. split; [lia | reflexivity].
+ if_falsex. step. apply evt_done. do 2 eexists. right. split; [lia | reflexivity].
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB'.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. norm_w32. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_truex. apply evt_done. do 2 eexists. left. split; [lia | reflexivity].
+ if_falsex. step. apply evt_done. do 2 eexists. right. split; [lia | reflexivity].
Qed.

Lemma lh_lookup_exit0A :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (m : word -> option byte) (lv : word),
mem_inv asegs m -> lh_open asegs A4F m t tbl size es svs -> bytes_at asegs m kp (ps ++ [b0]) ->
stk asegs m lo (bv_unsigned sp + -112) -> lk_frameA m lv ->
munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
evt asegs lh_lookup_A_post
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2918) fc None m (seg_rom asegs)).
Proof.
intros until lv. intros MI OPEN PS ST FR MU WM. unfold lk_frameA in FR. word_range sp SPR. unfold_consts.
step. do 14 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_A_post. do 14 eexists. exists 0. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
left. reflexivity.
Qed.

Lemma lh_lookup_exit1A :
forall (n : Z) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m : word -> option byte) (lv : word),
0 <= n < size -> In size lf_sizes -> In e es -> le_ix e = Z.to_nat n -> le_ks e = ps ->
mem_inv asegs m -> lh_open asegs A4F m t tbl size es svs -> lh_below lo t tbl size es -> bytes_at asegs m kp (ps ++ [b0]) ->
stk asegs m lo (bv_unsigned sp + -112) -> lk_frameA m lv ->
ro_cells asegs m (t / 8 + SB0) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
0 < t -> t mod 8 = 0 -> t / 8 + SB0 + 7 <= alloc_ceiling ->
munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
evt asegs lh_lookup_A_post
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 48)) (Z_to_bv 64 (t / 8 + 2147450883)) (Z_to_bv 64 SB0) x22 (Z_to_bv 64 40) (Z_to_bv 64 (-2))
(Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + 2147450886)) (Z_to_bv 64 n) t3 t4 t5 t6)
F (Z_to_bv 64 0xa2958) fc None m (seg_rom asegs)).
Proof.
intros until lv. intros Hn Hsz He Hix Hks MI OPEN BELOW PS ST FR SHt Ht Hal HSH MU WM. unfold lk_frameA in FR. word_range sp SPR. unfold_consts.
pose proof OPEN as (HDR & _). unfold lh_hdr, lh_hdrf in HDR. pose proof BELOW as (Ht0 & Htlo & Hb0 & Hb & _).
pose proof (lf_size_range size Hsz) as HSR.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. step. rewrite (unsigned_lit n) by lia. step.
do 15 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_A_post. do 14 eexists. exists (tbl + n * 40). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
right. destruct (In_nth_error _ _ He) as [j Hj]. exists j, e. split; [exact Hj|]. split; [unfold ent_addr; rewrite Hix; lia | exact Hks].
Qed.

Lemma lh_lookup_loopA :
forall (k : nat) (n cnt : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (lv : word),
Z.of_nat k = size - cnt -> 0 <= cnt < size -> 0 <= n < size ->
mem_inv asegs m ->
lh_open asegs A4F m t tbl size es svs -> lh_below lo t tbl size es ->
bytes_at asegs m kp (ps ++ [b0]) -> ~ In b0 ps ->
stk asegs m lo (bv_unsigned sp + -112) ->
lk_frameA m lv ->
munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
evt asegs lh_lookup_A_post
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 48)) (Z_to_bv 64 (t / 8 + 2147450883)) (Z_to_bv 64 SB0) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2))
(Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + 2147450886)) (Z_to_bv 64 n) t3 t4 t5 t6)
F (Z_to_bv 64 0xa288c) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until lv; intros Hk Hcnt Hn MI OPEN BELOW PS NP ST FR MU WM; [lia|].
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Htlo & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. pose proof FR as FR0. unfold lk_frameA in FR. word_range sp SPR. unfold_consts.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.

pose proof (heapA_now m MU WM MI) as HPc.
assert (Hint : In (t, 56) LB) by (apply INCL; left; reflexivity).
assert (Hinb : In (tbl, 40 * size) LB) by (apply INCL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc ltac:(apply in_or_app; left; exact Hint)) as (_ & Htal & Htpos & Hthi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tbl (40 * size) HPc ltac:(apply in_or_app; left; exact Hinb)) as (_ & Hbal & Hbpos & Hbhi & _).
unfold alloc_ceiling in Hthi, Hbhi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc Hint) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HPc Hint ltac:(cbn; lia) ltac:(apply in_or_app; left; exact Hint)) as SEPt6.
destruct (nth_error svs (Z.to_nat n)) as [sv|] eqn:Esv.
2:{ exfalso. apply nth_error_None in Esv. lia. }
pose proof (SL (Z.to_nat n) sv Esv) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
pose proof (rw_cells_bound asegs m _ _ C) as CB0. cbn [cells_size csize Nat.add] in CB0.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (Z.to_nat n) HPc Hinb ltac:(lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (Z.to_nat n) 0 tbl (40 * size) HPc Hinb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; exact Hinb)) as SEPe0.
unfold ent_addr in SHe, SEPe0. rewrite Z2Nat.id in SHe, SEPe0 by lia.
a4l.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. rewrite (unsigned_lit n) by lia. step.
replace (tbl + n * 40) with (tbl + 40 * n) by lia.
remember (tbl + 40 * n) as Bn eqn:EB.
assert (EB8 : Bn mod 8 = 0) by (subst Bn; Z.div_mod_to_equations; lia).
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. subst Bn.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (in_dec Nat.eq_dec (Z.to_nat n) (map le_ix es)) as [LIVE|DEAD].
-
apply in_map_iff in LIVE. destruct LIVE as (e & Hix & He).
destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (sv' & Esv' & Ek & Ekc & Ev & Enx & Epv). rewrite Hix, Esv in Esv'. injection Esv' as <-.
destruct (LK4 e He) as (Hk0 & HkF & Hkn31 & Hv). unfold LH_FREEDv in HkF.
destruct (lh_key_bytes asegs m es e KEYS He) as (KBY & KNZ & KL).
pose proof (Hkb e He) as Hke.
assert (Hink : In (le_k e, le_kn e) LB) by (apply INCL; right; right; apply in_map_iff; exists e; split; [reflexivity | exact He]).
rewrite Ek.
step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. step.

cbn [fn_lh_char_equal A4F]. replace (ret_pc (Z_to_bv 64 0xa1d2c)) with (Z_to_bv 64 0xa1d2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct (istrcmp_model_total (le_ks e) ps) as (kk & vv & MODEL).
pose proof (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr). rewrite length_app in Kl, Kr. cbn [length] in Kl, Kr.
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as K1.
pose proof (munch_refl [(lo, bv_unsigned sp + -112)] m) as MUk. pose proof (wmono_refl asegs m) as WMk.
eapply (lh_char_equal_A OBL_ISTRCMP) with (ls := le_ks e) (rs := ps) (lo := lo) (a := le_k e) (b := kp) (k := kk) (v := vv);
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by lia.
{ exact MODEL. }
{ eapply (unpoisoned_of_blk HIx); [exact HPc | exact Hink | lia | lia | lia]. }
{ eapply (unpoisoned_of_blk HIx); [exact HPc | exact KB | lia | lia | lia]. }
{ eapply (asan_rt_ok_of_HEAPA HIx). exact HPc. }
{ lia. }
{ pose proof (blk_app_bounds HIx _ _ _ _ _ _ _ _ _ (le_k e) (Z.of_nat (length (le_ks e)) + 1) HPc Hink ltac:(lia) ltac:(lia)). lia. }
{ lia. }
{ lia. }
{ pose proof (blk_app_bounds HIx _ _ _ _ _ _ _ _ _ kp (Z.of_nat (length ps) + 1) HPc KB ltac:(lia) ltac:(lia)). lia. }
{ intros Hkk. split; [eapply (blk_app_mem HIx); [exact HPc | exact Hink | lia | lia] | eapply (blk_app_mem HIx); [exact HPc | exact KB | lia | lia]]. }
{ left. lia. }
{ left. pose proof (blk_app_bounds HIx _ _ _ _ _ _ _ _ _ kp (Z.of_nat (length ps) + 1) HPc KB ltac:(lia) ltac:(lia)). unfold alloc_ceiling in *. lia. }
{ reflexivity. }
{ reflexivity. }
{ exact KNZ. }
{ exact NP. }
{ exact KBY. }
{ exact PS. }
{ exact ST. }
{ unfold alloc_ceiling. lia. }
{ lia. }
{ rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
{ exact MI. }
{ reflexivity. }
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MUc WMc MI2 KBY2 PS2 ST2.
transport_after_call asegs m m2 MUc WMc.
assert (OPEN' : lh_open asegs A4F m2 t tbl size es svs)
by (eapply (lh_open_frame asegs A4F _ m m2); [exact OPEN | exact BELOW | exact MUc | exact WMc | apply Forall_cons; [cbn; lia | apply Forall_nil]]).
replace (ret_pc (Z_to_bv 64 0xa28d4)) with (Z_to_bv 64 0xa28d4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear MUk WMk OPEN HPc. try clear C. try clear PS. try clear ST. try clear MI.
destruct (Z.eqb_spec (strcmp_model (le_ks e) ps) 0) as [EQ0|NE0].
+
step. if_true.
eapply (lh_lookup_exit1A n e); first [exact OPEN' | exact BELOW | exact PS2 | exact ST2 | exact MU | exact WM | exact He | exact Hix | exact Hsz | exact MI2 | eassumption | idtac];
try (unfold alloc_ceiling; lia); try lia.
apply (proj1 (strcmp_model_zero _ _ KNZ NP)). exact EQ0.
+
step. if_false.
eapply evt_cut; [eapply (lh_lookup_nextA n cnt); first [exact Hsz | exact MI2 | eassumption | unfold alloc_ceiling; lia | lia] |].
cbv beta. intros ms' (a0'' & a1'' & [[Hlt' ->] | [Heq ->]]).
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN' | exact BELOW | exact PS2 | exact NP | exact ST2 | exact FR | exact MU | exact WM | exact MI2 | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply lh_lookup_exit0A; first [exact OPEN' | exact PS2 | exact ST2 | exact FR | exact MU | exact WM | exact MI2 | lia].
-
destruct (LK2 (Z.to_nat n) sv Esv DEAD) as [EK | FK]; rewrite EK || rewrite FK; unfold LH_EMPTYv, LH_FREEDv.
+ step. if_false. step. step. if_true.
eapply lh_lookup_exit0A; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
+ step. if_true.
eapply evt_cut; [eapply (lh_lookup_nextA n cnt); first [exact Hsz | exact MI | eassumption | unfold alloc_ceiling; lia | lia] |].
cbv beta. intros ms' (a0'' & a1'' & [[Hlt' ->] | [Heq ->]]).
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN | exact BELOW | exact PS | exact NP | exact ST | exact FR0 | exact MU | exact WM | exact MI | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply lh_lookup_exit0A; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
Qed.

Lemma lh_lookup_A_spec :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (h : Z),
mem_inv asegs m0 ->
lh_open asegs A4F m0 t tbl size es svs -> lh_below lo t tbl size es ->
bytes_at asegs m0 kp (ps ++ [b0]) -> ~ In b0 ps ->
stk asegs m0 lo (bv_unsigned sp) ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 kp -> a2 = Z_to_bv 64 h -> 0 <= h < 2^64 ->
evt asegs lh_lookup_A_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_lookup_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until h. intros MI OPEN BELOW PS NP ST A0 A1 A2 Hh.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Htlo & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. word_range sp SPR. unfold_consts.
pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
pose proof (heapA_now m0 MU WM MI) as HPc.
assert (Hint : In (t, 56) LB) by (apply INCL; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc ltac:(apply in_or_app; left; exact Hint)) as (_ & Htal & Htpos & Hthi & _).
unfold alloc_ceiling in Hthi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc Hint) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HPc Hint ltac:(cbn; lia) ltac:(apply in_or_app; left; exact Hint)) as SEPt6.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ kb kbn HPc ltac:(apply in_or_app; left; exact KB)) as (_ & _ & Hkbpos & Hkbhi & _).
unfold alloc_ceiling in Hkbhi.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HPc) as [GOT CELL]. clear HPc.
a4l. unfold lh_lookup_A_entry. subst a0 a1 a2.
carve_frame 112%nat ST.
do 14 step.
do 3 step.
step. step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_false.
step. norm_sx32. step. if_falsex.
step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_false.
step. step. norm_sx32. step. step. step. step. step. stepz.
step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3.
step. rewrite remu_lit by lia.
step. sh_norm. rewrite (div8_add t 48) by lia. change (48 / 8) with 6.
step. step.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM.
eapply (lh_lookup_loopA (Z.to_nat size) (h mod size) 0);
first [exact BELOW | exact PS | exact NP | exact MU | exact WM | lia | idtac].
- assumption.
- eapply (lh_open_frame asegs A4F _ m0); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
- assumption.
- exact FR.
Qed.
End ALhLookup.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu QKQo QnCn QeuE QnP9 QnDr QJZd QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo Q8tj.
Import QSL3.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QsKa.Mq3 Q30W.Mq0 QnP9.Mq0 QsKa.Mq5 QnDr.Mq0 QJZd.Mq4 QW22.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section LoopA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).

Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6434400).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6434400 - 164).

Definition next_postA (q : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : word -> option byte) (md : config) (LB : list blk) (B : bud) (cost : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (F' : bvmap 5 word) (fc' : bv 32) (B' : bud)
(x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word),
ms' = MS (mkR x1 SPR gp TP t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 q) x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F' (Z_to_bv 64 0x9a808) fc' None m' (seg_rom asegs) /\
fsaved F1 F' /\ (frm0 fc1 -> frm0 fc') /\ model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' LB LM FRS B' m' md' /\ stk asegs m' lo (bv_unsigned sp + -112) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m' /\ rw_cells asegs m' ERRNO [C4 errv] /\
bB B - cost <= bB B' /\ bD B <= bD B'.

Lemma next_postA_w : forall q F1 fc1 F2 fc2 m1 m2 md1 md2 LB B1 B2 c1 c2 c ms md A,
fsaved F1 F2 -> (frm0 fc1 -> frm0 fc2) -> model_vm_only (cfg_model md1) (cfg_model md2) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m1 m2 ->
bB B1 - c1 <= bB B2 -> bD B1 <= bD B2 ->
next_postA q F2 fc2 m2 md2 LB B2 c2 ms md A -> c1 + c2 <= c -> next_postA q F1 fc1 m1 md1 LB B1 c ms md A.
Proof.
clear LO LOS SPA HT. intros until A. intros FS FRM VM HPR HB HD NP LE. unfold next_postA in *.
destruct NP as (m' & F' & fc' & B' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & E & FS' & FRM' & VM' & HP' & ST' & HPR' & ERR' & HB' & HD').
exists m', F', fc', B'. do 23 eexists. split; [exact E|].
split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [intros Hf; exact (FRM' (FRM Hf))|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [exact HP'|]. split; [exact ST'|].
split; [eapply heap_pres_trans; [exact HPR | exact HPR'] |]. split; [exact ERR'|]. lia.
Qed.

Lemma pop_tailA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB PBS : list blk) (x q pb ty tojs cf : Z) (T : TSet),
HEAPAx A ((x, 48) :: PBS ++ LB) LM FRS B m md ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)]) ->
opt_pbuf asegs m PBS pb ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (1 + Z.of_nat (length PBS)) <= bB B ->
(forall ms' md' A', next_postA q F1 fc1 m md LB B (512 * (1 + Z.of_nat (length PBS))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 q) x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9aa94) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HP HDR OPB ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
blk_factsA A4L HIx HP x 48 Hxal Hxlo Hxhi Hximg.
shadow_nowA A4L HIx HP x 48 SHx. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step.

clear SHx.
evt_done5.
eapply (printbuf_free_A_cps HIx) with (BS := PBS) (LB := (x, 48) :: LB) (p := pb) (lo := lo) (u := UWptr);
[ eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM MI | perm | apply Permutation_refl | apply Permutation_refl]
| intros _; apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| intros _; cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]
| .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [ exact OPB | reflexivity | lia | eassumption ].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; destruct (pb =? 0); lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & HP2).
replace (if pb =? 0 then 0 else uw_cost UWptr) with 0 in BD2 by (destruct (pb =? 0); reflexivity).
destruct RS as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
assert (HPRa : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m2).
{ eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; cbn; right; exact Hb]. }
clear MU WM MI HDR OPB ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step.

alloc_callA (hiA_free A4L HIx) blk x uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec x 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
replace (if x =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec x 0); reflexivity).
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]. }
clear MU WM MI HPRa.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step.
evt_done5. apply K. unfold next_postA.
exists m3, F2, fc2, (charge B2 512 0). do 23 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3] |].
split; [eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU); apply Forall_nil | exact WM | exact MI] |].
split; [exact ST3|]. split; [exact HPRb|]. split; [exact ERR3|].
cbn [bB bD charge uw_cost] in *. lia.
Qed.

Definition zpop (isobj : bool) (m : word -> option byte) (x q : Z) (nz : nat) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj asegs A4F m x q [] nz t tbl size es svs XBS
else exists a arr size, zarr asegs A4F m x q [] nz a arr size XBS.

Lemma pop_zeroA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q ty tojs pb cf : Z) (T : TSet),
HEAPAx A (XBS ++ LB) LM FRS B m md -> In (x, 48) XBS ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb 0 q ++ [C8 (Z_to_bv 64 cf)]) -> 0 <= ty < 2^31 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
(forall m2 (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word),
HEAPAx A (XBS ++ LB) LM FRS B m2 md ->
rw_cells asegs m2 x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)]) ->
stk asegs m2 lo (bv_unsigned sp + -112) -> rw_cells asegs m2 ERRNO [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m2 ->
agree_on asegs (others x XBS) m m2 ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR yt0 SPR gp TP yt1 yt2 ya7 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 ty) ya1 ya2 ya3 ya4 ya5 ya6 ya0
(Z_to_bv 64 q) (Z_to_bv 64 (x + 24)) x20 x21 (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 yt3 yt4 yt5 yt6)
F1 (Z_to_bv 64 0x9a9d8) fc1 None m2 (seg_rom asegs))) ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a960) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HP INx HDR Hty ST ERR KZ.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x 48 HP ltac:(apply in_or_app; left; exact INx)) as SHx.
unfold shad in SHx. apply shadow_ro_cells in SHx.
let cs := eval cbv in (shadow_cells 48) in change (shadow_cells 48) with cs in SHx. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(x + 24, x + 40); (lo, bv_unsigned sp + -112)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. asan_chkA.
step.
step. step. sh_norm. rewrite (div8_add x 4) by lia. change (4 / 8) with 0.
step. step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. if_false.
step. asan_chkA.
step. step. if_true.
step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HDR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr) =>
apply (rw_cells_recast asegs mc x _ ([c1; c2; c3; c4] ++ ([CB 16 (cells_bytes [c5; c6])] ++ rr))) in HDR;
[| cbn; repeat split; reflexivity | rewrite !cells_bytes_app; reflexivity | rewrite !cells_size_app; reflexivity ]
end;
destruct (proj1 (rw_cells_app asegs mc x _ _) HDR) as [HD4 REST]; clear HDR;
cbn [cells_size csize Nat.add] in REST; replace (x + Z.of_nat 24) with (x + 24) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (x + 24) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (x + 24 + Z.of_nat 16) with (x + 40) in TL by lia;
assert (HPc : HEAPAx A (XBS ++ LB) LM FRS B mc md) by heap_nowA A4L HIx HP MU WM MI
end.
eapply (amemset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x 48 (x + 24) 0 16 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact INx2 | exact DST | exact ST | exact MI | reflexivity | lia
| replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (apply in_or_app; left; exact INx).
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9a9cc)) with (Z_to_bv 64 0x9a9cc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (AG4 : agree_on asegs (others x XBS) m m4).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 a k HP INx2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HDR4 : rw_cells asegs m4 x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)])).
{ unfold jhdr_cells. cbn [app].
lazymatch goal with H4 : rw_cells asegs m4 x _, D4 : rw_cells asegs m4 (x + 24) _, T4 : rw_cells asegs m4 (x + 40) _ |- rw_cells _ m4 x ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr => change cs with ([c1; c2; c3; c4] ++ ([c5; c6] ++ rr)) end;
apply (proj2 (rw_cells_app asegs m4 x _ _)); cbn [cells_size csize Nat.add]; split; [exact H4|];
replace (x + Z.of_nat 24) with (x + 24) by lia;
apply (proj2 (rw_cells_app asegs m4 (x + 24) _ _)); cbn [cells_size csize Nat.add];
replace (x + 24 + Z.of_nat 16) with (x + 40) by lia; split; [| exact T4];
eapply rw_cells_recast; [exact D4 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]
end. }
assert (HPR4 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m4).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd] |]. { right; left. exists x, 48. split; [exact INx2|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix XBS (LB ++ LM) x 48 48 ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx) (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INx2)). }
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
assert (HP4 : HEAPAx A (XBS ++ LB) LM FRS B m4 md) by heap_nowA A4L HIx HP MU WM MI4.
clear HD4 DST4 TL. unfold jhdr_cells in HDR4. cbn [app] in HDR4.
try clear SHx. pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x 48 HP4 ltac:(apply in_or_app; left; exact INx)) as SHx.
unfold shad in SHx. apply shadow_ro_cells in SHx.
let cs := eval cbv in (shadow_cells 48) in change (shadow_cells 48) with cs in SHx. a4l.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32.
eapply KZ; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR4 | exact ST4 | assumption | exact HPR4 | exact AG4].
Qed.

Lemma pop_okA : forall (isobj : bool)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (nz : nat) (T : TSet),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zpop isobj m x q nz XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
(forall ms' md' A', next_postA q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9a960) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HP ZP ST ERR BB K.
unfold_consts. word_range sp SPW.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
destruct isobj.
-
destruct ZP as (t & tbl & size & es & svs & Z0).
destruct (zobj_nil_shape asegs A4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & OPEN & VZ & Lz). clear Z0. subst XBS.
pose proof (nodup_app_l' _ LB (nodup_app_l' _ LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
reenterA asegs A4L HIx asegs_wx HP.
eapply (pop_zeroA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m md A B LB _ x q JT_OBJECT _ pb t T);
[ exact HP | left; reflexivity | exact HDR | unfold JT_OBJECT, JT_ARRAY; lia | exact ST | exact ERR |].
intros m2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP2 HDR2 ST2 ERR2 HPR2 AG2.
rewrite <- app_assoc in HP2. unfold lh_blocks in HP2. cbn [app] in HP2. rewrite <- ?app_assoc in HP2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP2 t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP2 tbl (40 * size) Hbal Hblo Hbhi Himg_b.
shadow_nowA A4L HIx HP2 x 48 SHx. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
unfold jhdr_cells in HDR2. cbn [app fn_obj_to_json_string A4F] in HDR2.
assert (OPEN2 : lh_open asegs A4F m2 t tbl size es svs).
{ eapply (lh_open_agree asegs A4F); [exact OPEN | exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; exact Hb]]. }
step. step. if_falsex. step. if_falsex. step. if_falsex.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step.
clear SHx.
evt_done5.
eapply (lh_table_free_A_cps HIx _ gp _ _ SBR (Z_to_bv 64 4) _ (Z_to_bv 64 5) CM1 F1 fc1 m2 md ((x, 48) :: PBS ++ LB) LM FRS B lo t tbl size es svs T)
with (u := UWptr).
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP2 MU WM MI | unfold lh_blocks; cbn [map app]; perm | apply Permutation_refl | apply Permutation_refl]).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try exact OPEN2. all: try exact VZ.
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; lia).
all: try (unfold lh_blocks in BB; cbn [length app] in BB; rewrite ?length_app, ?length_map in BB; cbn [length] in BB; unfold blk in *; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR2; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; cbn; right; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
clear MU WM MI OPEN OPEN2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4. step.
evt_done5.
eapply pop_tailA; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR2 | exact OPB4 | exact ST4 | exact ERR4
| clear K; unfold lh_blocks in BB; cbn [length app] in *; rewrite ?length_app, ?length_map in BB; cbn [length] in BB; unfold blk in *; cbn [bB charge] in *; lia |].
intros ms5 md5 A5 NP. apply K.
eapply next_postA_w; [exact FS4 | exact FRM4 | exact VM4 | | exact BB4 | cbn [uw_cost] in BD4; lia | exact NP
| clear K; unfold lh_blocks; cbn [length app]; rewrite ?length_app, ?length_map; cbn [length]; unfold blk; lia].
eapply heap_pres_trans; [exact HPR2|]. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]].
-
destruct ZP as (a & arr & size & Z0).
destruct (zarr_nil_vals asegs A4F _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & AL). clear Z0. subst XBS.
pose proof (nodup_app_l' _ LB (nodup_app_l' _ LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
reenterA asegs A4L HIx asegs_wx HP.
eapply (pop_zeroA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m md A B LB _ x q JT_ARRAY _ pb a T);
[ exact HP | left; reflexivity | exact HDR | unfold JT_OBJECT, JT_ARRAY; lia | exact ST | exact ERR |].
intros m2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP2 HDR2 ST2 ERR2 HPR2 AG2.
cbn [app] in HP2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP2 a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HP2 arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HP2 x 48 SHx. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
unfold jhdr_cells in HDR2. cbn [app fn_arr_to_json_string A4F] in HDR2.
assert (AL2 : alist asegs A4F m2 [(a, 32); (arr, 8 * size)] a (repeat 0 nz)).
{ eapply (alist_agree asegs A4F); [exact AL | exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; exact Hb]]. }
step. step. if_falsex. step. if_truex.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step.
clear SHx.
evt_done5.
eapply (array_list_free_A_cps HIx _ _ gp (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 q) (Z_to_bv 64 (x + 24)) _ _ (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 F1 fc1 m2 md
((x, 48) :: PBS ++ LB) LM FRS B lo a T)
with (BS := [(a, 32); (arr, 8 * size)]) (ps := repeat 0 nz) (u := UWptr).
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP2 MU WM MI | perm | apply Permutation_refl | apply Permutation_refl]).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try exact AL2. all: try apply Forall_repeat0.
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; lia).
all: try (cbn [length app] in BB; unfold blk in *; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR2; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; cbn; right; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
clear MU WM MI AL AL2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4. step.
evt_done5.
eapply pop_tailA; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR2 | exact OPB4 | exact ST4 | exact ERR4
| clear K; cbn [length app] in *; unfold blk in *; cbn [bB charge] in *; lia |].
intros ms5 md5 A5 NP. apply K.
eapply next_postA_w; [exact FS4 | exact FRM4 | exact VM4 | | exact BB4 | cbn [uw_cost] in BD4; lia | exact NP
| clear K; cbn [length app]; rewrite ?length_app; cbn [length]; unfold blk; lia].
eapply heap_pres_trans; [exact HPR2|]. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]].
Qed.
End LoopA.
End RC__1.
End Mq3.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QXUB Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.

Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0 Qekr.Mq0.

Import Qw5U.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MJoSetDouble.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Lemma RTC_SERTBL : rtc_sertbl_stmt HIx.
Proof.
intros A LB LM FR B m md HP. unfold A_SERTBL_DBL. cbn [fn_dbl_to_json_string A4F]. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition SD_STK_A : Z := 64 + 4096.

Lemma set_double_A : jo_set_double_A_stmt HIx 0x9e384 SD_STK_A 512 1.
Proof.
unfold jo_set_double_A_stmt, SD_STK_A. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR BB BD A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
pose proof alloc_ceiling_range as ACR.
assert (CH0 : jo_chargeA 512 1 B B) by (split; lia).

assert (RET0 : forall n ty tojs pb udel ud, In (p, n) BS -> 48 <= n -> 0 <= ty <= 6 -> ty <> JT_DOUBLE ->
rw_cells asegs m p (jhdr_cells ty 1 tojs pb udel ud) ->
set_double_root (fn_dbl_to_json_string A4F) r = r ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 6434400) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 648068) fc None m (seg_rom asegs))).
{ intros n ty tojs pb udel ud INp N48 TY NE HDRH SDR.
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
unfold jhdr_cells in HDRH. unfold JT_DOUBLE in NE.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 8 step. step. if_falsex.
do 3 step.
asan_chkA.
step. rewrite sx32_small by lia. step. step. if_truex.
step. do 9 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0 A B BS) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact CH0.
+ exact ERR.
+ rewrite SDR.
eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ clear. destruct r as [|sd|?|]; [| destruct sd | |]; first [exact I | reflexivity]. }

assert (TAIL : forall (AX : ASA A4L HIx) (mdX : config) (BX : bud) (mc : word -> option byte) (PBS : list blk) (pbx : Z) (x y bitsX : word) (fj : list byte)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
HEAPAx AX (((p, 48) :: PBS) ++ LB) LM FRS BX mc mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mc ->
jo_chargeA 512 1 B BX ->
opt_pbuf asegs mc PBS pbx ->
rw_cells asegs mc p [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 646380); C8 (Z_to_bv 64 pbx); C8 x; C8 y; C8 bitsX] ->
rw_cells asegs mc (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -64) ->
rw_cells asegs mc 6434236 [C4 errv] ->
set_double_root (fn_dbl_to_json_string A4F) r = JRdblx (fn_dbl_to_json_string A4F) ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 p)
xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (p + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (p / 8 + 2147450880))
(Z_to_bv 64 (p / 8 + 2147450881)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 648316) fc None mc (seg_rom asegs))).
{ intros AX mdX BX mc PBS pbx x y bitsX fj xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HPX VMX HPRX CHX OPBX CELLSX FRX STX ERRX SDR.
clear RET0 HP MI WM GOT CELL RR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (p, p + 48)] mc) as MU.
cbn [app] in HPX.
blk_factsA A4L HIx HPX p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (RTC_SERTBL _ _ _ _ _ _ _ HPX) as TBC. apply ro_C8_of_bytes_at in TBC. unfold A_SERTBL_DBL in TBC. cbn [fn_dbl_to_json_string A4F] in TBC.

change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 646380); C8 (Z_to_bv 64 pbx); C8 x; C8 y; C8 bitsX]
with ([C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 646380); C8 (Z_to_bv 64 pbx)] ++ ([C8 x; C8 y] ++ [C8 bitsX])) in CELLSX.
destruct (proj1 (rw_cells_app asegs mc p _ _) CELLSX) as [HDRX RESTX]. clear CELLSX. cbn [cells_size csize Nat.add] in RESTX. replace (p + Z.of_nat 24) with (p + 24) in RESTX by lia.
destruct (proj1 (rw_cells_app asegs mc (p + 24) _ _) RESTX) as [DSTX TLX]. clear RESTX. cbn [cells_size csize Nat.add] in TLX. replace (p + 24 + Z.of_nat 16) with (p + 40) in TLX by lia.
assert (DSTB : rw_cells asegs mc (p + 24) [CB 16 (le8 x ++ le8 y)]).
{ eapply rw_cells_recast; [exact DSTX | cbn; repeat split; try exact I; rewrite length_app, !length_le8; reflexivity | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity | reflexivity]. }
clear DSTX.
a4l. reenterA asegs A4L HIx asegs_wx HPX.
step. step. step. step.
eapply OBL_AMEMSET with (ab := p) (nb := 48) (d := p + 24) (c := 0) (n := 16) (lo := lo) (old := le8 x ++ le8 y);
[ exact HPX | .. ]; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DSTB
| eassumption | exact LO | lia | clear - SPA; Z.div_mod_to_equations; lia
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mq _ =>
transport_after_call asegs mq m4 MU4 WM4; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0x9e48c)) with (Z_to_bv 64 0x9e48c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
heap_nowA_auto A4L HIx HPX HPc. shadow_nowA A4L HIx HPc p 48 SHp.
assert (SHT : ro_cells asegs m4 2147566850 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (0xe2810 / 8) HPc) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (0xe2810 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (0xe2810 / 8 + 2147450880) with 2147566850 in X. exact X. }
a4l. clear HPc.
step. rewrite ?sxb_zero. step. if_false.
step. rewrite sx32_small by lia. step. step. step. if_lit.
step. step. step. step.
step. step. step. rewrite ?zxb_zero. step. if_false.
step. rewrite ?zxb_zero. step. if_false.
step. stepz. step.
do 9 step.
evt_done5.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPX) as NDX.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ mdX mf 1 AX BX ((p, 48) :: PBS)) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [exact VMX|].
split; [release_frame FRX ST4 (bv_unsigned sp); exact ST4|]. split; [| exists errv; exact ERRX].
eapply heap_pres_trans; [exact HPRX|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPX | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ NDX) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 NDX ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HPX _ Hi). in_app_prefix.
+ exact CHX.
+ exact ERRX.
+ rewrite SDR. cbn [jroot_rep]. split; [lia|]. split; [left; reflexivity|].
exists pbx, PBS, bitsX. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPBX | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HPX ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ NDX) as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HPX ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* unfold jhdr_cells, JT_DOUBLE. cbn [app fn_dbl_to_json_string A4F hl_segs hla_base A4L A4H].
lazymatch goal with |- rw_cells _ ?mf _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
change [c1; c2; c3; c4; c5; c6; c7] with ([c1; c2; c3; c4] ++ ([c5; c6] ++ [c7]));
apply (proj2 (rw_cells_app asegs mf p _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf p _ |- _ => exact H end |];
replace (p + Z.of_nat 24) with (p + 24) by lia;
apply (proj2 (rw_cells_app asegs mf (p + 24) _ _)); cbn [cells_size csize Nat.add];
replace (p + 24 + Z.of_nat 16) with (p + 40) by lia;
split; [| match goal with H : rw_cells asegs mf (p + 40) _ |- _ => exact H end];
match goal with H : rw_cells asegs mf (p + 24) _ |- _ =>
eapply rw_cells_recast; [exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] end
end.
+ cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HPX | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPX MU); solve_frameW_withA HPX | exact WM | assumption].
+ clear - SDR. destruct r as [|sd|?|]; [| destruct sd | |]; cbn in SDR; first [exact I | discriminate SDR]. }

assert (STORE1 : forall (PBS : list blk) (pbx : Z) (bitsX : word),
BS = (p, 48) :: PBS -> opt_pbuf asegs m PBS pbx ->
rw_cells asegs m p [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 634672); C8 (Z_to_bv 64 pbx); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 bitsX] ->
set_double_root (fn_dbl_to_json_string A4F) r = JRdblx (fn_dbl_to_json_string A4F) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 6434400) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 648068) fc None m (seg_rom asegs))).
{ intros PBS pbx bitsX EBS OPB CELLS SDR. subst BS. clear RET0 TAIL RR. cbn [app] in HP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
blk_factsA A4L HIx HP p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 8 step. step. if_falsex.
do 3 step.
asan_chkA.
step. rewrite sx32_small by lia. step. step. if_lit.
step.
asan_chkA.
step.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 48 SHp. a4l. clear HPc.
step. asan_chkA.
step. step. step. step. if_lit.
step. step.
do 9 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1 A B ((p, 48) :: PBS)) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact CH0.
+ exact ERR.
+ rewrite SDR. cbn [jroot_rep]. split; [lia|]. split; [left; reflexivity|].
exists pbx, PBS, (reg_get F 10). split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ ND0) as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* unfold jhdr_cells, JT_DOUBLE. cbn [app fn_dbl_to_json_string A4F hl_segs hla_base A4L A4H]. assumption.
+ cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ clear - SDR. destruct r as [|sd|?|]; [| destruct sd | |]; cbn in SDR; first [exact I | discriminate SDR]. }
destruct r as [ | s | tojs0 | ].
-
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 8 step. step. if_truex. do 9 step.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0 A B []) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
+ exact CH0.
+ exact ERR.
+ cbn [set_double_root jroot_rep]. split; reflexivity.
+ cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ reflexivity.
-
pose proof RR as [Hp J].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
destruct (Z.eq_dec (jtype s) JT_DOUBLE) as [TD | NTD].
2:{
destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _].
eapply (RET0 n (jtype s) tojs pb udel ud INp N48 (jtype_range s) NTD HDRH).
destruct s; first [reflexivity | exfalso; apply NTD; reflexivity]. }
destruct s as [|u| | | |]; try discriminate TD. clear TD CLOSE HDR SZ N48 INp.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
destruct u.
*
destruct J as (bits & ud_ & udn & uds & -> & Hudn & CELLS & CSTR). cbn [app] in EBS. subst BS. cbn [app] in HP, ND.
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app fn_ud_to_json_string fn_free_userdata A4F hl_segs hla_base A4L A4H] in CELLS. cbn [hl_segs hla_base A4L A4H] in OPB. clear CSTR.
blk_factsA A4L HIx HP p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 8 step. step. if_falsex.
do 3 step.
asan_chkA.
step. rewrite sx32_small by lia. step. step. if_lit.
step.
asan_chkA.
step.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 48 SHp. a4l. clear HPc.
step. asan_chkA.
step. step. step. step.
if_lit.
step. asan_chkA.
step. step.
step. if_lit.
step. asan_chkA.
step. step. step.
step. step.
evt_done5.
eapply (hiA_free A4L HIx) with (p := ud_) (u := UWpaid) (lo := lo) (errv := errv);
[ heap_nowA A4L HIx HP MU WM MI | right; exists udn; right; left; reflexivity | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: split; cbn; exact I.
1: exact BB.
1: destruct (Z.eqb ud_ 0); cbn [uw_cost]; lia.
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3.
assert (Hpud : p <> ud_).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ud_ udn HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & _ & Hud0 & _).
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if ud_ =? 0 then 0 else uw_cost UWpaid) with 1 in HP3 by (destruct (Z.eqb_spec ud_ 0); [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in CELLS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in CELLS.
assert (OPB3 : opt_pbuf asegs m3 PBS pb_).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_on_trans.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni. right. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
+ exact (nodup_prefix_suffix ((p, 48) :: (ud_, udn) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
+ exact (nodup_prefix_suffix (((p, 48) :: (ud_, udn) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
+ refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
- eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb]]. }
replace (ret_pc (Z_to_bv 64 648316)) with (Z_to_bv 64 648316) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply (TAIL A3 md3 (charge B 512 1) m3 PBS pb_);
[ exact HP3 | exact VM3 | exact HPRb | unfold jo_chargeA, charge; cbn [bB bD]; split; lia | exact OPB3 | exact CELLS | exact FR | exact ST3 | exact ERR3 | reflexivity ].
*
destruct J as (bits & -> & _ & CELLS). cbn [app] in EBS.
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app fn_dbl_to_json_string A4F hl_segs hla_base A4L A4H] in CELLS. cbn [hl_segs hla_base A4L A4H] in OPB.
eapply (STORE1 PBS pb_ bits EBS OPB CELLS). reflexivity.
-
destruct RR as (Hp & Htojs & pb_ & PBS & bits & EBS & OPB & CELLS).
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app hl_segs hla_base A4L A4H] in CELLS. cbn [hl_segs hla_base A4L A4H] in OPB.
destruct Htojs as [-> | ->].
+
cbn [fn_dbl_to_json_string A4F] in CELLS.
eapply (STORE1 PBS pb_ bits EBS OPB CELLS). reflexivity.
+
cbn [fn_ud_to_json_string A4F] in CELLS. subst BS. cbn [app] in HP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
blk_factsA A4L HIx HP p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 8 step. step. if_falsex.
do 3 step.
asan_chkA.
step. rewrite sx32_small by lia. step. step. if_lit.
step.
asan_chkA.
step.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 48 SHp. a4l. clear HPc.
step. asan_chkA.
step. step. step. step. if_lit.
step. asan_chkA.
step. step.
step. if_lit.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] =>
assert (HPc : HEAPAx A ((p, 48) :: PBS ++ LB) LM FRS B mc md) by (heap_nowA A4L HIx HP MU WM MI);
eapply (TAIL A md B mc PBS pb_) end;
[ exact HPc | apply model_vm_only_refl | | exact CH0 | | eassumption | eassumption | eassumption | eassumption | reflexivity ].
* eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
-- exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
-- exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
-- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ ND0) as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
-
pose proof RR as (Hp & pb_ & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hstr & ALT).
assert (CELLS : exists rest, rw_cells asegs m p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb_ 0 0 ++ rest)).
{ destruct ALT as [(_ & _ & _ & junk & C) | (_ & pd & pdn & junk & junk2 & _ & _ & C & _)]; cbn [hl_segs hla_base A4L A4H] in C; eexists; exact C. }
destruct CELLS as [rest CELLS].
destruct (proj1 (rw_cells_app asegs m p _ _) CELLS) as [HDRH _].
eapply (RET0 (48 + cap) JT_STRING (fn_str_to_json_string A4F) pb_ 0 0); [rewrite EBS; left; reflexivity | lia | unfold JT_STRING; lia | unfold JT_STRING, JT_DOUBLE; lia | exact HDRH | reflexivity].
Qed.
End MJoSetDouble.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QSL3. Import QT7b.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqe Q30W Qekr.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Local Ltac sepcache_on ::= fail.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Notation SB0 := 2147450880.

Lemma mod16_mod8 : forall k, k mod 16 = 0 -> k mod 8 = 0.
Proof. intros k H. Z.div_mod_to_equations. lia. Qed.

Lemma land3_of_mod8 : forall k, 0 <= k -> k mod 8 = 0 -> Z.land k 3 = 0.
Proof.
intros k Hk H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. Z.div_mod_to_equations. nia.
Qed.

Section LhHashA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variable MREL : config -> config -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis OBL_ISTRLEN : astrlen_any_spec_A HIx.

Hypothesis OBL_BLK40 : forall A LB LM FR B m md a n, HEAPAx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> n < 2^40.

Definition seed_settle_A_post (sp gp s0v : word) (s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (errv' : word),
ms' = MS (mkR x1 sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0v (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2ccc) fc None m' (seg_rom asegs) /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\ HEAPAx A' LB LM FRS B m' md'.

Definition seed_settle_A_stmt (SD : Z) : Prop :=
forall (x1 sp gp t0 t1 t2 s0v a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv seedv : word),
HEAPAx A LB LM FRS B m md -> lh_globA m ->
rw_cells asegs m GSEEDA [C4 seedv] -> sx32 seedv = Z_to_bv 64 (-1) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
(forall ms' md' A', seed_settle_A_post sp gp s0v s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0v (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2cb0) fc None m (seg_rom asegs)).

Variable SD : Z.
Hypothesis SD_ge : 4096 <= SD.
Hypothesis SEED : seed_settle_A_stmt SD.

Lemma key_stringA : forall A LB LM FRS B m md kp kn ks,
HEAPAx A LB LM FRS B m md -> In (kp, kn) LB -> cstr asegs m kp kn ks ->
exists slack, bytes_at asegs m kp (ks ++ Z_to_bv 8 0 :: slack) /\
(- (kp + Z.of_nat (length ks) + 1)) mod 8 <= Z.of_nat (length slack) /\
~ In (Z_to_bv 8 0) ks /\ kp mod 16 = 0 /\ Z.of_nat (length ks) + 1 <= kn /\ 0 < kp /\ kp + kn <= alloc_ceiling /\
kp + Z.of_nat (length ks) + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Proof.
intros A LB LM FRS B m md kp kn ks HP Hin (CL & CNZ & junk & CB).
assert (HinX : In (kp, kn) (LB ++ LM)) by (apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ kp kn HP HinX) as (Hn0 & Hal & Hlo & Hhi & _).
destruct (heapA_blk_slack A4L HIx _ _ _ _ _ _ _ kp kn HP HinX) as [g [G Lg]]. cbn [hl_segs hla_base A4L A4H] in G.
assert (NN : ~ In (Z_to_bv 8 0) ks).
{ intros X. rewrite Forall_forall in CNZ. apply (CNZ _ X). reflexivity. }
assert (LENB : length (ks ++ [Z_to_bv 8 0] ++ junk) = Z.to_nat kn) by (destruct CB as [[[Hwf _] _] _]; exact Hwf).
rewrite !length_app in LENB. cbn [length] in LENB.
assert (BB : bytes_at asegs m kp (ks ++ [Z_to_bv 8 0] ++ junk)).
{ destruct CB as [[[_ _] HB] _]. cbn in HB. rewrite app_nil_r in HB. exact HB. }
exists (junk ++ g).
assert (B2 : bytes_at asegs m kp ((ks ++ [Z_to_bv 8 0] ++ junk) ++ g)).
{ apply bytes_at_app. split; [exact BB|]. rewrite !length_app. cbn [length].
replace (kp + Z.of_nat (length ks + (1 + length junk))) with (kp + kn) by lia. exact G. }
replace ((ks ++ [Z_to_bv 8 0] ++ junk) ++ g) with (ks ++ Z_to_bv 8 0 :: junk ++ g) in B2 by (rewrite <- !app_assoc; reflexivity).
pose proof alloc_ceiling_al16 as C16.
split; [exact B2|]. split; [| split; [exact NN | split; [exact Hal | split; [exact CL | split; [exact Hlo | split; [exact Hhi|]]]]]].
- rewrite length_app.
replace (Z.of_nat (length junk + length g)) with ((kn - Z.of_nat (length ks) - 1) + Z.of_nat (length g)) by lia.
rewrite Lg.
set (x := kp + Z.of_nat (length ks) + 1) in *.
pose proof (Z.div_mod kn 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound kn 16 ltac:(lia)) as B1.
pose proof (Z.div_mod kp 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - kn mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - kn mod 16) 16 ltac:(lia)) as B3.
pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E4. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B4.
set (rn := kn mod 16) in *. set (r8 := (- x) mod 8) in *.
set (qn := kn / 16) in *. set (qb := kp / 16) in *. set (q3 := (16 - rn) / 16) in *. set (q8 := - x / 8) in *.
nia.
- rewrite length_app. rewrite Nat2Z.inj_add, Lg.
pose proof (Z.div_mod kn 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound kn 16 ltac:(lia)) as B1.
pose proof (Z.div_mod kp 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - kn mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - kn mod 16) 16 ltac:(lia)) as B3.
unfold alloc_ceiling in *. pose proof (Z.div_mod rc_ceil 16 ltac:(lia)) as E5.
set (rn := kn mod 16) in *. set (qn := kn / 16) in *. set (qb := kp / 16) in *. set (q3 := (16 - rn) / 16) in *. set (qc := rc_ceil / 16) in *.
nia.
Qed.

Lemma lh_char_hash_A_cps : forall HD, 112 + SD <= HD -> lh_char_hash_A_stmt HIx MREL HD.
Proof.
intros HD HHD. unfold lh_char_hash_A_stmt. intros until ks. intros HP INK CS G ST LO LOS SPA HT ERR TP RA FRM FRN A0 K.
word_range sp SPR. pose proof alloc_ceiling_ge as ACG. pose proof (hiA_top_le A4L HIx) as HTL.
pose proof (OBL_BLK40 _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INK)) as KN40.
destruct (key_stringA _ _ _ _ _ _ _ _ _ _ HP INK CS) as (slack & STR & PAD & NN & KAL & KL & KPOS & KHI & KSL).
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof G as (G1 & [seed G2]). unfold GHASHA in G1. unfold GSEEDA in G2.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
a4l. subst a0 tp. unfold lh_char_hash_A_entry. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
do 14 step.
step. step.
step. step.
step.
step.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPA A4L HIx A LB LM FRS B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
assert (G1' : lh_globA m1) by (split; [exact G1 | exists seed; exact G2]).
assert (HPR1 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch A4H a4_volatile _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA _ HIx); [exact HP | intros b Hb; exact Hb | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA A4L HIx HP]. }
clear GOT CELL.
destruct (bv_eqb (sx32 seed) (Z_to_bv 64 (-1))) eqn:ESEED; [change (negb true) with false | change (negb false) with true]; cbv iota.
-
evt_done5.
eapply (SEED _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md T A LB LM FRS B lo errv seed);
[exact HP1 | exact G1' | exact G2 | apply (proj1 (Fs.bv_eqb_eq _ _)); exact ESEED | ..]; a4l_goal; rewrite ?unsigned_lit by lia;
[exact ST | exact LO | lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | lia | exact ERR | exact FRM | exact FRN |].
intros ms2 md2 A2 (y1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MR2 & ST2 & HPR2 & ERR2 & GL2 & HP2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2, HPR2 by lia.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
assert (HPR12 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_presx_trans; [exact HPR1|]. eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; exact Hb | intros a' Ha'; exact Ha']. }
assert (CS2 : cstr asegs m2 kp kn ks).
{ destruct CS as (CL' & CNZ & junk2 & CB). split; [exact CL'|]. split; [exact CNZ|]. exists junk2.
eapply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR12); [exact CB|]. eapply client_rangex_block; [apply in_or_app; left; exact INK | lia | cbn; lia]. }
clear STR PAD KSL AB slack MU WM MI1 HPR1 HP1 G1' G1 G2 ERR ST.
destruct (key_stringA _ _ _ _ _ _ _ _ _ _ HP2 INK CS2) as (slack & STR & PAD & _ & _ & _ & _ & _ & KSL).
pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenterA asegs A4L HIx asegs_wx HP2.
step. step.
clear MU WM.
eapply (OBL_ISTRLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 md2 A2 LB LM FRS B kp kn kp lo ks slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP2 | exact INK | exact NN | exact STR | exact PAD | exact KSL | exact ST2 | exact LO | exact MI | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m2 m3 MU3 WM3; try match goal with H : mem_inv asegs m2 |- _ => clear H end.
unstash STR3.
assert (HP3 : HEAPA A4L HIx A2 LB LM FRS B m3 md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU3); solve_frameW_withA HP2 | exact WM3 | exact MI3]. }
assert (G3 : lh_globA m3).
{ eapply lh_globA_frame; [exact GL2 | exact MU3 | exact WM3 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]. }
pose proof G3 as (G31 & [seed3 G32]). unfold GHASHA in G31. unfold GSEEDA in G32.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ kp kn HP3 INK) as SHB. unfold shad in SHB. a4l.
assert (HPR23 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m2 m3).
{ eapply (heap_presx_of_munch A4H a4_volatile _ (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outsideA _ HIx); [exact HP2 | intros b Hb; exact Hb | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA A4L HIx HP2]. }
clear MU3 WM3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [] m3) as MU.
replace (ret_pc (Z_to_bv 64 666836)) with (Z_to_bv 64 666836) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold GSEEDA.
step.
step. norm_sx32.
step. step. step.
step.
rewrite (unsigned_lit kp) by lia. rewrite (land3_of_mod8 kp) by (first [lia | apply mod16_mod8; exact KAL]).
step.
step. if_true.
eapply evt_cut; [eapply (word_pathA kp kn ks slack m3); [exact STR3 | exact MI3 | apply mod16_mod8; exact KAL | lia | exact KL | lia | exact SHB] |].
cbv beta. intros ms4 (j & Hj & (u0' & u1' & u2' & u8' & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3' & u4' & u5' & u6' & ->)).
step. step.
do 13 step.
step.
release_frame FR ST3 (bv_unsigned sp).
step.
evt_done5. apply K. unfold lh_hash_A_post.
lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?x 32)] => set (h := Z.shiftr x 32) end.
assert (Hh : 0 <= h < 2^64).
{ subst h. lazymatch goal with |- context [Z.shiftr (bv_unsigned ?w) 32] => word_range w WR end.
rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. nia. }
exists m3, h, errv2.
split; [unfold ret_statew; do 16 eexists; split; [reflexivity | split; [apply QCcH.fsaved_refl | intros H0; exact H0]] |].
split; [exact Hh|]. split; [exact MR2|]. split; [exact ST3|].
split; [eapply heap_presx_trans; [exact HPR12 | exact HPR23] |].
split; [exact ERR2|]. split; [exact G3 | exact HP3].
-
step. step.
clear MU WM.
eapply (OBL_ISTRLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md A LB LM FRS B kp kn kp lo ks slack);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact INK | exact NN | exact STR | exact PAD | exact KSL | exact ST | exact LO | exact MI1 | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | idtac].
intros x0 x1' x2 y1' y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m3 MU3 WM3 MI3 STR3 ST3.
stash STR3.
transport_after_call asegs m1 m3 MU3 WM3; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
unstash STR3.
assert (HP3 : HEAPA A4L HIx A LB LM FRS B m3 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU3); solve_frameW_withA HP1 | exact WM3 | exact MI3]. }
assert (G3 : lh_globA m3).
{ eapply lh_globA_frame; [exact G1' | exact MU3 | exact WM3 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]. }
pose proof G3 as (G31 & [seed3 G32]). unfold GHASHA in G31. unfold GSEEDA in G32.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ kp kn HP3 INK) as SHB. unfold shad in SHB. a4l.
assert (HPR13 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m1 m3).
{ eapply (heap_presx_of_munch A4H a4_volatile _ (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outsideA _ HIx); [exact HP1 | intros b Hb; exact Hb | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientWA A4L HIx HP1]. }
clear MU3 WM3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [] m3) as MU.
replace (ret_pc (Z_to_bv 64 666836)) with (Z_to_bv 64 666836) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step.
step. norm_sx32.
step. step. step.
step.
rewrite (unsigned_lit kp) by lia. rewrite (land3_of_mod8 kp) by (first [lia | apply mod16_mod8; exact KAL]).
step.
step. if_true.
eapply evt_cut; [eapply (word_pathA kp kn ks slack m3); [exact STR3 | exact MI3 | apply mod16_mod8; exact KAL | lia | exact KL | lia | exact SHB] |].
cbv beta. intros ms4 (j & Hj & (u0' & u1' & u2' & u8' & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3' & u4' & u5' & u6' & ->)).
step. step.
do 13 step.
step.
release_frame FR ST3 (bv_unsigned sp).
step.
evt_done5. apply K. unfold lh_hash_A_post.
lazymatch goal with |- context [Z_to_bv 64 (Z.shiftr ?x 32)] => set (h := Z.shiftr x 32) end.
assert (Hh : 0 <= h < 2^64).
{ subst h. lazymatch goal with |- context [Z.shiftr (bv_unsigned ?w) 32] => word_range w WR end.
rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. nia. }
exists m3, h, errv.
split; [unfold ret_statew; do 16 eexists; split; [reflexivity | split; [apply QCcH.fsaved_refl | intros H0; exact H0]] |].
split; [exact Hh|]. split; [apply MREL_refl|]. split; [exact ST3|].
split; [eapply heap_presx_trans; [exact HPR1 | exact HPR13] |].
split; [exact ERR|]. split; [exact G3 | exact HP3].
Qed.
End LhHashA.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import QSL3. Import Q22i QT7b QqWD.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import QsKa.Mq9.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QpNt.Mq8 QsKa.Mqe Q30W.Mq6 Q30W.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition lh_lookup_A_entry : Z := 0xa4c94.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhLookup.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_ISTRCMP : istrcmp_spec_U.

Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Variables (m0 : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (kb kbn : Z).
Hypothesis HP0 : HEAPAx A LB LM FRS B m0 md.
Hypothesis INCL : forall b, In b (lh_blocks t tbl size es) -> In b LB.
Hypothesis KB : In (kb, kbn) LB.
Hypothesis KBlo : kb <= kp.
Hypothesis KBhi : kp + Z.of_nat (length ps) + 1 <= kb + kbn.
Hypothesis PS40 : Z.of_nat (length ps) + 1 < 2^40.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - 128 - 16 - 4096.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Definition lh_lookup_A_post : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ lh_open asegs A4F m' t tbl size es svs
/\ bytes_at asegs m' kp (ps ++ [b0])
/\ lookup_res tbl es ps r.

Definition lk_frameA (m : word -> option byte) (junk0 : list byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -128)
[CB 8 junk0; C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 kp); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Notation SB0 := 2147450880.

Definition lk_regsA (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 : word) (n cnt : Z) (t3 t4 t5 t6 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 t) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (t + 24)) (Z_to_bv 64 (t + 48)) (Z_to_bv 64 (t / 8 + 2147450883)) (Z_to_bv 64 SB0) (Z_to_bv 64 n) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2))
(Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + 2147450886)) t3 t4 t5 t6.

Lemma heapA_now : forall m, munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m -> mem_inv asegs m -> HEAPAx A LB LM FRS B m md.
Proof.
intros m MU WM MI. eapply (heapA_client_frame A4L HIx); [exact HP0 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP0 MU). apply Forall_cons; [left; cbn; split; lia | apply Forall_nil].
Qed.

Lemma lh_lookup_nextA :
forall (n cnt : Z) (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (hsz hcnt hhd htl : Z),
0 <= cnt < size -> 0 <= n < size -> In size lf_sizes -> mem_inv asegs m ->
rw_cells asegs m t [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free A4F)); C8 (Z_to_bv 64 (fn_lh_char_hash A4F)); C8 (Z_to_bv 64 (fn_lh_char_equal A4F))] ->
ro_cells asegs m (t / 8 + SB0) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
0 < t -> t + 56 <= alloc_ceiling -> t / 8 + SB0 + 7 <= alloc_ceiling ->
evt asegs (fun ms' => exists a0' a1' a2',
(cnt + 1 < size /\
ms' = MS (lk_regsA x1 t0 t1 t2 x9 a0' a1' a2' a3 a4 a5 a6 a7 (next_ix size n) (cnt + 1) t3 t4 t5 t6) F (Z_to_bv 64 0xa4d44) fc None m (seg_rom asegs))
\/ (cnt + 1 = size /\
ms' = MS (lk_regsA x1 t0 t1 t2 x9 a0' a1' a2' a3 a4 a5 a6 a7 (next_ix size n) (cnt + 1) t3 t4 t5 t6) F (Z_to_bv 64 0xa4e00) fc None m (seg_rom asegs)))
(MS (lk_regsA x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 n cnt t3 t4 t5 t6) F (Z_to_bv 64 0xa4dc0) fc None m (seg_rom asegs)).
Proof.
intros until htl. intros Hcnt Hn Hsz MI HDR SHt Ht Hth HSH.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts. unfold lk_regsA.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. norm_sx32.
step. norm_w32.
step.
step. norm_w32.
step. rewrite ?(unsigned_lit size), ?(unsigned_lit (n + 1)) by lia.
unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NE].
- rewrite EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit size) by lia. change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_truex. apply evt_done. do 3 eexists. left. split; [lia | reflexivity].
+ if_falsex. step. apply evt_done. do 3 eexists. right. split; [lia | reflexivity].
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB'.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_truex. apply evt_done. do 3 eexists. left. split; [lia | reflexivity].
+ if_falsex. step. apply evt_done. do 3 eexists. right. split; [lia | reflexivity].
Qed.

Lemma lh_lookup_exit0A :
forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (m : word -> option byte) (junk0 : list byte),
mem_inv asegs m -> lh_open asegs A4F m t tbl size es svs -> bytes_at asegs m kp (ps ++ [b0]) ->
stk asegs m lo (bv_unsigned sp + -128) -> lk_frameA m junk0 ->
munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
evt asegs lh_lookup_A_post
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa4e00) fc None m (seg_rom asegs)).
Proof.
intros until junk0. intros MI OPEN PS ST FR MU WM. unfold lk_frameA in FR. word_range sp SPR. unfold_consts.
step. do 14 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_A_post. do 14 eexists. exists 0. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
left. reflexivity.
Qed.

Lemma lh_lookup_exit1A :
forall (n cnt : Z) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (junk0 : list byte),
0 <= n < size -> In size lf_sizes -> In e es -> le_ix e = Z.to_nat n -> le_ks e = ps ->
mem_inv asegs m -> lh_open asegs A4F m t tbl size es svs -> lh_below lo t tbl size es -> bytes_at asegs m kp (ps ++ [b0]) ->
stk asegs m lo (bv_unsigned sp + -128) -> lk_frameA m junk0 ->
ro_cells asegs m (t / 8 + SB0) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
0 < t -> t mod 8 = 0 -> t / 8 + SB0 + 7 <= alloc_ceiling -> 0 < tbl -> tbl + 40 * size < 2^64 ->
munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
evt asegs lh_lookup_A_post
(MS (lk_regsA x1 t0 t1 t2 (Z_to_bv 64 (n * 40)) a0 a1 a2 a3 a4 a5 a6 a7 n cnt t3 t4 t5 t6) F (Z_to_bv 64 0xa4e40) fc None m (seg_rom asegs)).
Proof.
intros until junk0. intros Hn Hsz He Hix Hks MI OPEN BELOW PS ST FR SHt Ht Hal HSH Hb0 Hbsz MU WM. unfold lk_frameA in FR. word_range sp SPR. unfold_consts. unfold lk_regsA.
pose proof OPEN as (HDR & _). unfold lh_hdr, lh_hdrf in HDR. pose proof BELOW as (Ht0 & Htlo & Hb0' & Hb & _).
pose proof (lf_size_range size Hsz) as HSR.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step.
step. rewrite ?(unsigned_lit (n * 40)), ?(unsigned_lit tbl) by lia.
step. ub_resolve.
step. step. step.
step. ub_resolve.
step. step. rewrite (unsigned_lit n) by lia. step.
step.
do 14 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_A_post. do 14 eexists. exists (tbl + n * 40). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
right. destruct (In_nth_error _ _ He) as [j Hj]. exists j, e. split; [exact Hj|]. split; [unfold ent_addr; rewrite Hix; lia | exact Hks].
Qed.

Lemma lh_lookup_loopA :
forall (k : nat) (n cnt : Z) (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (junk0 : list byte),
Z.of_nat k = size - cnt -> 0 <= cnt < size -> 0 <= n < size ->
mem_inv asegs m ->
lh_open asegs A4F m t tbl size es svs -> lh_below lo t tbl size es ->
bytes_at asegs m kp (ps ++ [b0]) -> ~ In b0 ps ->
stk asegs m lo (bv_unsigned sp + -128) ->
lk_frameA m junk0 ->
munch [(lo, bv_unsigned sp)] m0 m -> wmono asegs m0 m ->
evt asegs lh_lookup_A_post
(MS (lk_regsA x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 n cnt t3 t4 t5 t6) F (Z_to_bv 64 0xa4d44) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until junk0; intros Hk Hcnt Hn MI OPEN BELOW PS NP ST FR MU WM; [lia|].
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Htlo & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. pose proof FR as FR0. unfold lk_frameA in FR. word_range sp SPR. unfold_consts.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.

pose proof (heapA_now m MU WM MI) as HPc.
assert (Hint : In (t, 56) LB) by (apply INCL; left; reflexivity).
assert (Hinb : In (tbl, 40 * size) LB) by (apply INCL; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc ltac:(apply in_or_app; left; exact Hint)) as (_ & Htal & Htpos & Hthi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tbl (40 * size) HPc ltac:(apply in_or_app; left; exact Hinb)) as (_ & Hbal & Hbpos & Hbhi & _).
unfold alloc_ceiling in Hthi, Hbhi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc Hint) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HPc Hint ltac:(cbn; lia) ltac:(apply in_or_app; left; exact Hint)) as SEPt6.
destruct (nth_error svs (Z.to_nat n)) as [sv|] eqn:Esv.
2:{ exfalso. apply nth_error_None in Esv. lia. }
pose proof (SL (Z.to_nat n) sv Esv) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
pose proof (rw_cells_bound asegs m _ _ C) as CB0. cbn [cells_size csize Nat.add] in CB0.
pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl size (Z.to_nat n) HPc Hinb ltac:(lia) ltac:(lia)) as SHe.
pose proof (ent_shadow_sepA HIx _ _ _ _ _ _ _ tbl size (Z.to_nat n) 0 tbl (40 * size) HPc Hinb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply in_or_app; left; exact Hinb)) as SEPe0.
unfold ent_addr in SHe, SEPe0. rewrite Z2Nat.id in SHe, SEPe0 by lia.
a4l. unfold lk_regsA.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. rewrite (unsigned_lit n) by lia.
step.
step. step. step. ub_resolve.
step. ub_resolve.
step. step. step. step. rewrite (mul40_chk n) by lia.
step. if_false.
step. if_falsex.
replace (n * 40 + tbl) with (tbl + 40 * n) by lia.
remember (tbl + 40 * n) as Bn eqn:EB.
assert (EB8 : Bn mod 8 = 0) by (subst Bn; Z.div_mod_to_equations; lia).
step. rewrite (unsigned_lit Bn) by lia. rewrite (ub_land7 Bn EB8). step. if_false.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. subst Bn.
ub_cmp_norm.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (in_dec Nat.eq_dec (Z.to_nat n) (map le_ix es)) as [LIVE|DEAD].
-
apply in_map_iff in LIVE. destruct LIVE as (e & Hix & He).
destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (sv' & Esv' & Ek & Ekc & Ev & Enx & Epv). rewrite Hix, Esv in Esv'. injection Esv' as <-.
destruct (LK4 e He) as (Hk0 & HkF & Hkn31 & Hv). unfold LH_FREEDv in HkF.
destruct (lh_key_bytes asegs m es e KEYS He) as (KBY & KNZ & KL).
pose proof (Hkb e He) as Hke.
assert (Hink : In (le_k e, le_kn e) LB) by (apply INCL; right; right; apply in_map_iff; exists e; split; [reflexivity | exact He]).
rewrite Ek.
step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. step.

cbn [fn_lh_char_equal A4F]. replace (ret_pc (Z_to_bv 64 0xa4110)) with (Z_to_bv 64 0xa4110) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct (istrcmp_model_total (le_ks e) ps) as (kk & vv & MODEL).
pose proof (icmp_walk_nread _ _ _ _ _ _ _ MODEL) as (Kf & Kl & Kr). rewrite length_app in Kl, Kr. cbn [length] in Kl, Kr.
pose proof (icmp_walk_pos _ _ _ _ _ _ _ MODEL ltac:(lia)) as K1.
pose proof (munch_refl [(lo, bv_unsigned sp + -128)] m) as MUk. pose proof (wmono_refl asegs m) as WMk.
eapply (lh_char_equal_A OBL_ISTRCMP) with (ls := le_ks e) (rs := ps) (lo := lo) (a := le_k e) (b := kp) (k := kk) (v := vv);
rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by lia.
{ exact MODEL. }
{ eapply (unpoisoned_of_blk HIx); [exact HPc | exact Hink | lia | lia | lia]. }
{ eapply (unpoisoned_of_blk HIx); [exact HPc | exact KB | lia | lia | lia]. }
{ eapply (asan_rt_ok_of_HEAPA HIx). exact HPc. }
{ lia. }
{ pose proof (blk_app_bounds HIx _ _ _ _ _ _ _ _ _ (le_k e) (Z.of_nat (length (le_ks e)) + 1) HPc Hink ltac:(lia) ltac:(lia)). lia. }
{ lia. }
{ lia. }
{ pose proof (blk_app_bounds HIx _ _ _ _ _ _ _ _ _ kp (Z.of_nat (length ps) + 1) HPc KB ltac:(lia) ltac:(lia)). lia. }
{ intros Hkk. split; [eapply (blk_app_mem HIx); [exact HPc | exact Hink | lia | lia] | eapply (blk_app_mem HIx); [exact HPc | exact KB | lia | lia]]. }
{ left. lia. }
{ left. pose proof (blk_app_bounds HIx _ _ _ _ _ _ _ _ _ kp (Z.of_nat (length ps) + 1) HPc KB ltac:(lia) ltac:(lia)). unfold alloc_ceiling in *. lia. }
{ reflexivity. }
{ reflexivity. }
{ exact KNZ. }
{ exact NP. }
{ exact KBY. }
{ exact PS. }
{ exact ST. }
{ unfold alloc_ceiling. lia. }
{ lia. }
{ rewrite <- Zplus_mod_idemp_l, SPA. reflexivity. }
{ exact MI. }
{ reflexivity. }
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MUc WMc MI2 KBY2 PS2 ST2.
transport_after_call asegs m m2 MUc WMc.
assert (OPEN' : lh_open asegs A4F m2 t tbl size es svs)
by (eapply (lh_open_frame asegs A4F _ m m2); [exact OPEN | exact BELOW | exact MUc | exact WMc | apply Forall_cons; [cbn; lia | apply Forall_nil]]).
replace (ret_pc (Z_to_bv 64 0xa4dbc)) with (Z_to_bv 64 0xa4dbc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
clear MUk WMk OPEN HPc. try clear C. try clear PS. try clear ST. try clear MI.
destruct (Z.eqb_spec (strcmp_model (le_ks e) ps) 0) as [EQ0|NE0].
+
step. if_true.
eapply (lh_lookup_exit1A n cnt e); first [exact OPEN' | exact BELOW | exact PS2 | exact ST2 | exact MU | exact WM | exact He | exact Hix | exact Hsz | exact MI2 | eassumption | idtac];
try (unfold alloc_ceiling; lia); try lia.
apply (proj1 (strcmp_model_zero _ _ KNZ NP)). exact EQ0.
+
step. if_false.
eapply evt_cut; [eapply (lh_lookup_nextA n cnt); first [exact Hsz | exact MI2 | eassumption | unfold alloc_ceiling; lia | lia] |].
cbv beta. intros ms' (a0'' & a1'' & a2'' & [[Hlt' ->] | [Heq ->]]).
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN' | exact BELOW | exact PS2 | exact NP | exact ST2 | exact FR | exact MU | exact WM | exact MI2 | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* unfold lk_regsA. eapply lh_lookup_exit0A; first [exact OPEN' | exact PS2 | exact ST2 | exact FR | exact MU | exact WM | exact MI2 | lia].
-
destruct (LK2 (Z.to_nat n) sv Esv DEAD) as [EK | FK]; rewrite EK || rewrite FK; unfold LH_EMPTYv, LH_FREEDv.
+ step. if_false. step. step. if_true.
eapply lh_lookup_exit0A; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
+ step. if_true.
eapply evt_cut; [eapply (lh_lookup_nextA n cnt); first [exact Hsz | exact MI | eassumption | unfold alloc_ceiling; lia | lia] |].
cbv beta. intros ms' (a0'' & a1'' & a2'' & [[Hlt' ->] | [Heq ->]]).
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN | exact BELOW | exact PS | exact NP | exact ST | exact FR0 | exact MU | exact WM | exact MI | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* unfold lk_regsA. eapply lh_lookup_exit0A; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
Qed.

Lemma lh_lookup_A_spec :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (h : Z),
mem_inv asegs m0 ->
lh_open asegs A4F m0 t tbl size es svs -> lh_below lo t tbl size es ->
bytes_at asegs m0 kp (ps ++ [b0]) -> ~ In b0 ps ->
stk asegs m0 lo (bv_unsigned sp) ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 kp -> a2 = Z_to_bv 64 h -> 0 <= h < 2^64 ->
evt asegs lh_lookup_A_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_lookup_A_entry) fc None m0 (seg_rom asegs)).
Proof.
intros until h. intros MI OPEN BELOW PS NP ST A0 A1 A2 Hh.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Htlo & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. word_range sp SPR. unfold_consts.
pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
pose proof (heapA_now m0 MU WM MI) as HPc.
assert (Hint : In (t, 56) LB) by (apply INCL; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc ltac:(apply in_or_app; left; exact Hint)) as (_ & Htal & Htpos & Hthi & _).
unfold alloc_ceiling in Hthi.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HPc Hint) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HPc Hint ltac:(cbn; lia) ltac:(apply in_or_app; left; exact Hint)) as SEPt6.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ kb kbn HPc ltac:(apply in_or_app; left; exact KB)) as (_ & _ & Hkbpos & Hkbhi & _).
unfold alloc_ceiling in Hkbhi.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HPc) as [GOT CELL]. clear HPc.
a4l. unfold lh_lookup_A_entry. subst a0 a1 a2.
carve_frame 128%nat ST.
do 14 step.
stepz.
step. if_falsex.
step.
step. rewrite (unsigned_lit t) by lia. rewrite (ub_land7 t) by (clear -Htal; Z.div_mod_to_equations; lia).
step. if_false.
do 3 step.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. norm_sx32. step. if_falsex.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. norm_sx32. step. if_falsex.
step. step. step.
step. rewrite remu_lit by lia.
step. step. step. stepz.
step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3.
step. sh_norm. rewrite (div8_add t 48) by lia. change (48 / 8) with 6.
step. step.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM.
eapply (lh_lookup_loopA (Z.to_nat size) (h mod size) 0);
first [exact BELOW | exact PS | exact NP | exact MU | exact WM | lia | idtac].
- assumption.
- eapply (lh_open_frame asegs A4F _ m0); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
- assumption.
- unfold lk_frameA. eassumption.
Qed.
End ALhLookup.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo Q8tj.
Import QSL3.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QpNt.Mq8 QsKa.Mqc Q30W.Mq4 QnP9 QsKa.Mqe QnDr QJZd.Mqd QW22.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section LoopA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).

Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6444320).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6444320 - 164).

Definition spillA (m : word -> option byte) : Prop := exists bs, rw_cells asegs m (bv_unsigned sp + -112) [CB 8 bs].

Ltac spl1 mq :=
match goal with
| S : rw_cells _ mq (bv_unsigned _ + -112) [_] |- _ =>
let bs := fresh "sbs" in let S2 := fresh "SPL" in
destruct (rw_cells_forget asegs _ _ _ S) as [bs S2]; cbn [cells_size csize Nat.add] in S2; eexists; exact S2
| S : rw_cells _ ?ma (bv_unsigned _ + -112) [_], H : heap_pres A4H _ _ ?ma ?mb |- _ =>
lazymatch mb with ma => fail | _ => idtac end;
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ H) in S; [ spl1 mq | left; cbn; lia ]
| |- _ => fail 1 "spill slot: no slot hypothesis / heap_pres chain to the current memory"
end.
Ltac spl := lazymatch goal with
| |- spillA _ ?mq /\ _ => split; [spl1 mq|] | |- spillA ?mq /\ _ => split; [spl1 mq|]
| |- spillA _ ?mq => spl1 mq | |- spillA ?mq => spl1 mq | |- _ => idtac end.
Ltac hpw H := eapply heap_pres_weaken; [exact H | lia | intros b' Hb'; exact Hb'].

Definition next_postA (q : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : word -> option byte) (md : config) (LB : list blk) (B : bud) (cost : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (F' : bvmap 5 word) (fc' : bv 32) (B' : bud)
(x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word),
ms' = MS (mkR x1 SPR gp TP t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 q) x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F' (Z_to_bv 64 0x9be3c) fc' None m' (seg_rom asegs) /\
fsaved F1 F' /\ (frm0 fc1 -> frm0 fc') /\ model_vm_only (cfg_model md) (cfg_model md') /\
HEAPAx A' LB LM FRS B' m' md' /\ spillA m' /\ stk asegs m' lo (bv_unsigned sp + -112) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -104) m m' /\ rw_cells asegs m' ERRNO [C4 errv] /\
bB B - cost <= bB B' /\ bD B <= bD B'.

Lemma next_postA_w : forall q F1 fc1 F2 fc2 m1 m2 md1 md2 LB B1 B2 c1 c2 c ms md A,
fsaved F1 F2 -> (frm0 fc1 -> frm0 fc2) -> model_vm_only (cfg_model md1) (cfg_model md2) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -104) m1 m2 ->
bB B1 - c1 <= bB B2 -> bD B1 <= bD B2 ->
next_postA q F2 fc2 m2 md2 LB B2 c2 ms md A -> c1 + c2 <= c -> next_postA q F1 fc1 m1 md1 LB B1 c ms md A.
Proof.
clear LO LOS SPA HT. intros until A. intros FS FRM VM HPR HB HD NP LE. unfold next_postA in *.
destruct NP as (m' & F' & fc' & B' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & E & FS' & FRM' & VM' & HP' & [sbsHP'x SPLHP'x] & ST' & HPR' & ERR' & HB' & HD').
exists m', F', fc', B'. do 23 eexists. split; [exact E|].
split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [intros Hf; exact (FRM' (FRM Hf))|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [exact HP'|]. spl; split; [exact ST'|].
split; [eapply heap_pres_trans; [hpw HPR | hpw HPR'] |]. split; [exact ERR'|]. lia.
Qed.

Lemma pop_tailA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB PBS : list blk) (x q pb ty tojs cf : Z) (T : TSet),
HEAPAx A ((x, 48) :: PBS ++ LB) LM FRS B m md ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)]) ->
opt_pbuf asegs m PBS pb ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * (1 + Z.of_nat (length PBS)) <= bB B ->
spillA m ->
(forall ms' md' A', next_postA q F1 fc1 m md LB B (512 * (1 + Z.of_nat (length PBS))) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 q) x19 x20 x21 x22 SBR (Z_to_bv 64 4) x25 (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c100) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HP HDR OPB ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
blk_factsA A4L HIx HP x 48 Hxal Hxlo Hxhi Hximg.
shadow_nowA A4L HIx HP x 48 SHx. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
bstep. asan_chkA.
bstep. bstep.

clear SHx.
evt_done5.
eapply (printbuf_free_A_cps HIx) with (BS := PBS) (LB := (x, 48) :: LB) (p := pb) (lo := lo) (u := UWptr);
[ eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM MI | perm | apply Permutation_refl | apply Permutation_refl]
| intros _; apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| intros _; cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]
| .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [ exact OPB | reflexivity | lia | eassumption ].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; destruct (pb =? 0); lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & HP2).
replace (if pb =? 0 then 0 else uw_cost UWptr) with 0 in BD2 by (destruct (pb =? 0); reflexivity).
destruct RS as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR2 by lia.
assert (HPRa : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m2).
{ eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; cbn; right; exact Hb]. }
clear MU WM MI HDR OPB ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. bstep.

alloc_callA (hiA_free A4L HIx) blk x uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec x 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
replace (if x =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec x 0); reflexivity).
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m3).
{ eapply heap_pres_trans; [hpw HPRa|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]. }
clear MU WM MI HPRa.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (munch_refl [] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep.
evt_done5. apply K. unfold next_postA.
exists m3, F2, fc2, (charge B2 512 0). do 23 eexists.
split; [reflexivity|]. split; [exact FS2|]. split; [exact FRM2|].
split; [eapply model_vm_only_trans; [exact VM2 | exact VM3] |].
split; [eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3 MU); apply Forall_nil | exact WM | exact MI] |].
spl; split; [exact ST3|]. split; [hpw HPRb|]. split; [exact ERR3|].
cbn [bB bD charge uw_cost] in *. lia.
Qed.

Definition zpop (isobj : bool) (m : word -> option byte) (x q : Z) (nz : nat) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj asegs A4F m x q [] nz t tbl size es svs XBS
else exists a arr size, zarr asegs A4F m x q [] nz a arr size XBS.

Lemma pop_zeroA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q ty tojs pb cf : Z) (T : TSet),
HEAPAx A (XBS ++ LB) LM FRS B m md -> In (x, 48) XBS ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb 0 q ++ [C8 (Z_to_bv 64 cf)]) -> 0 <= ty < 2^31 ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
(forall m2 (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 : word),
HEAPAx A (XBS ++ LB) LM FRS B m2 md ->
rw_cells asegs m2 x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)]) ->
stk asegs m2 lo (bv_unsigned sp + -112) -> rw_cells asegs m2 ERRNO [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m2 ->
agree_on asegs (others x XBS) m m2 ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR yt0 SPR gp TP yt1 yt2 ya7 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 ty) ya1 ya2 ya3 ya4 ya5 ya6 ya0
(Z_to_bv 64 q) (Z_to_bv 64 (x + 24)) x20 x21 (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4)
(Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 yt3 yt4 yt5 yt6)
F1 (Z_to_bv 64 0x9c03c) fc1 None m2 (seg_rom asegs))) ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9bfc4) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HP INx HDR Hty ST ERR KZ.
unfold_consts. word_range sp SPW.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INx).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x 48 HP ltac:(apply in_or_app; left; exact INx)) as SHx.
unfold shad in SHx. apply shadow_ro_cells in SHx.
let cs := eval cbv in (shadow_cells 48) in change (shadow_cells 48) with cs in SHx. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(x + 24, x + 40); (lo, bv_unsigned sp + -112)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
bstep. asan_chkA.
bstep.
bstep. bstep. sh_norm. rewrite (div8_add x 4) by lia. change (4 / 8) with 0.
bstep. bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. if_false.
bstep. asan_chkA.
bstep. bstep. if_true.
bstep. bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HDR with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr) =>
apply (rw_cells_recast asegs mc x _ ([c1; c2; c3; c4] ++ ([CB 16 (cells_bytes [c5; c6])] ++ rr))) in HDR;
[| cbn; repeat split; reflexivity | rewrite !cells_bytes_app; reflexivity | rewrite !cells_size_app; reflexivity ]
end;
destruct (proj1 (rw_cells_app asegs mc x _ _) HDR) as [HD4 REST]; clear HDR;
cbn [cells_size csize Nat.add] in REST; replace (x + Z.of_nat 24) with (x + 24) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (x + 24) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (x + 24 + Z.of_nat 16) with (x + 40) in TL by lia;
assert (HPc : HEAPAx A (XBS ++ LB) LM FRS B mc md) by heap_nowA A4L HIx HP MU WM MI
end.
eapply (amemset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x 48 (x + 24) 0 16 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact INx2 | exact DST | exact ST | exact MI | reflexivity | lia
| replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (apply in_or_app; left; exact INx).
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9c030)) with (Z_to_bv 64 0x9c030) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (AG4 : agree_on asegs (others x XBS) m m4).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a k Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as (Hk & _ & _ & Hahi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 a k HP INx2 ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi. cbn. lia. }
assert (HDR4 : rw_cells asegs m4 x (jhdr_cells ty 0 tojs pb 0 0 ++ [C8 (Z_to_bv 64 cf)])).
{ unfold jhdr_cells. cbn [app].
lazymatch goal with H4 : rw_cells asegs m4 x _, D4 : rw_cells asegs m4 (x + 24) _, T4 : rw_cells asegs m4 (x + 40) _ |- rw_cells _ m4 x ?cs =>
lazymatch cs with ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rr => change cs with ([c1; c2; c3; c4] ++ ([c5; c6] ++ rr)) end;
apply (proj2 (rw_cells_app asegs m4 x _ _)); cbn [cells_size csize Nat.add]; split; [exact H4|];
replace (x + Z.of_nat 24) with (x + 24) by lia;
apply (proj2 (rw_cells_app asegs m4 (x + 24) _ _)); cbn [cells_size csize Nat.add];
replace (x + 24 + Z.of_nat 16) with (x + 40) by lia; split; [| exact T4];
eapply rw_cells_recast; [exact D4 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]
end. }
assert (HPR4 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m4).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; rewrite <- app_assoc; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd] |]. { right; left. exists x, 48. split; [exact INx2|]. split; [| lia].
exact (not_in_app3 _ _ _ _ (nodup_prefix_suffix XBS (LB ++ LM) x 48 48 ltac:(pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDx; rewrite <- app_assoc in NDx; exact NDx) INx) (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INx2)). }
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
assert (HP4 : HEAPAx A (XBS ++ LB) LM FRS B m4 md) by heap_nowA A4L HIx HP MU WM MI4.
clear HD4 DST4 TL. unfold jhdr_cells in HDR4. cbn [app] in HDR4.
try clear SHx. pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x 48 HP4 ltac:(apply in_or_app; left; exact INx)) as SHx.
unfold shad in SHx. apply shadow_ro_cells in SHx.
let cs := eval cbv in (shadow_cells 48) in change (shadow_cells 48) with cs in SHx. a4l.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32.
eapply KZ; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR4 | exact ST4 | assumption | exact HPR4 | exact AG4].
Qed.

Lemma pop_okA : forall (isobj : bool)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LB XBS : list blk) (x q : Z) (nz : nat) (T : TSet),
HEAPAx A (XBS ++ LB) LM FRS B m md ->
zpop isobj m x q nz XBS ->
stk asegs m lo (bv_unsigned sp + -112) -> rw_cells asegs m ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS) <= bB B ->
spillA m ->
(forall ms' md' A', next_postA q F1 fc1 m md LB B (512 * Z.of_nat (length XBS)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9bfc4) fc1 None m (seg_rom asegs)).
Proof.
intros until T. intros HP ZP ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
destruct isobj.
-
destruct ZP as (t & tbl & size & es & svs & Z0).
destruct (zobj_nil_shape asegs A4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & OPEN & VZ & Lz). clear Z0. subst XBS.
pose proof (nodup_app_l' _ LB (nodup_app_l' _ LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
pose proof OPEN as (_ & _ & _ & _ & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
reenterA asegs A4L HIx asegs_wx HP.
eapply (pop_zeroA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m md A B LB _ x q JT_OBJECT _ pb t T);
[ exact HP | left; reflexivity | exact HDR | unfold JT_OBJECT, JT_ARRAY; lia | exact ST | exact ERR |].
intros m2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP2 HDR2 ST2 ERR2 HPR2 AG2.
rewrite <- app_assoc in HP2. unfold lh_blocks in HP2. cbn [app] in HP2. rewrite <- ?app_assoc in HP2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP2 t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP2 tbl (40 * size) Hbal Hblo Hbhi Himg_b.
shadow_nowA A4L HIx HP2 x 48 SHx. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
unfold jhdr_cells in HDR2. cbn [app fn_obj_to_json_string A4F] in HDR2.
assert (OPEN2 : lh_open asegs A4F m2 t tbl size es svs).
{ eapply (lh_open_agree asegs A4F); [exact OPEN | exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; exact Hb]]. }
bstep. bstep. if_falsex. bstep. if_falsex. bstep. if_falsex.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep.
clear SHx.
evt_done5.
eapply (lh_table_free_A_cps HIx _ gp _ _ SBR (Z_to_bv 64 4) _ (Z_to_bv 64 5) CM1 F1 fc1 m2 md ((x, 48) :: PBS ++ LB) LM FRS B lo t tbl size es svs T)
with (u := UWptr).
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP2 MU WM MI | unfold lh_blocks; cbn [map app]; perm | apply Permutation_refl | apply Permutation_refl]).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try exact OPEN2. all: try exact VZ.
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; lia).
all: try (unfold lh_blocks in BB; cbn [length app] in BB; rewrite ?length_app, ?length_map in BB; cbn [length] in BB; unfold blk in *; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR2; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; cbn; right; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
clear MU WM MI OPEN OPEN2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4. bstep.
evt_done5.
eapply pop_tailA; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR2 | exact OPB4 | exact ST4 | exact ERR4
| clear K; unfold lh_blocks in BB; cbn [length app] in *; rewrite ?length_app, ?length_map in BB; cbn [length] in BB; unfold blk in *; cbn [bB charge] in *; lia | spl |].
intros ms5 md5 A5 NP. apply K.
eapply next_postA_w; [exact FS4 | exact FRM4 | exact VM4 | | exact BB4 | cbn [uw_cost] in BD4; lia | exact NP
| clear K; unfold lh_blocks; cbn [length app]; rewrite ?length_app, ?length_map; cbn [length]; unfold blk; lia].
eapply heap_pres_trans; [hpw HPR2|]. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]].
-
destruct ZP as (a & arr & size & Z0).
destruct (zarr_nil_vals asegs A4F _ _ _ _ _ _ _ _ Z0) as (pb & PBS & EX & OPB & HDR & AL). clear Z0. subst XBS.
pose proof (nodup_app_l' _ LB (nodup_app_l' _ LM (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP))) as ND.
reenterA asegs A4L HIx asegs_wx HP.
eapply (pop_zeroA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m md A B LB _ x q JT_ARRAY _ pb a T);
[ exact HP | left; reflexivity | exact HDR | unfold JT_OBJECT, JT_ARRAY; lia | exact ST | exact ERR |].
intros m2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt0 yt1 yt2 yt3 yt4 yt5 yt6 HP2 HDR2 ST2 ERR2 HPR2 AG2.
cbn [app] in HP2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 x 48 Hxal Hxlo Hxhi Hximg.
blk_factsA A4L HIx HP2 a 32 Haal Halo Hahi Himg_a.
blk_factsA A4L HIx HP2 arr (8 * size) Hral Hrlo Hrhi Himg_r.
shadow_nowA A4L HIx HP2 x 48 SHx. a4l.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
unfold jhdr_cells in HDR2. cbn [app fn_arr_to_json_string A4F] in HDR2.
assert (AL2 : alist asegs A4F m2 [(a, 32); (arr, 8 * size)] a (repeat 0 nz)).
{ eapply (alist_agree asegs A4F); [exact AL | exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; exact Hb]]. }
bstep. bstep. if_falsex. bstep. if_truex.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep.
clear SHx.
evt_done5.
eapply (array_list_free_A_cps HIx _ _ gp (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 q) (Z_to_bv 64 (x + 24)) _ _ (Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 F1 fc1 m2 md
((x, 48) :: PBS ++ LB) LM FRS B lo a T)
with (BS := [(a, 32); (arr, 8 * size)]) (ps := repeat 0 nz) (u := UWptr).
all: a4l_goal; rewrite ?unsigned_lit by lia.
all: try (eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP2 MU WM MI | perm | apply Permutation_refl | apply Permutation_refl]).
all: try (apply uw_at_ptr; lia).
all: try (cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]).
all: try exact AL2. all: try apply Forall_repeat0.
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; lia).
all: try (cbn [length app] in BB; unfold blk in *; lia).
all: try first [eassumption | reflexivity | lia].
intros ms4 md4 A4 (m4 & r4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & HP4).
destruct RS4 as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in HDR2; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
assert (OPB4 : opt_pbuf asegs m4 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; cbn; right; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
clear MU WM MI AL AL2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
pose proof (munch_refl [] m4) as MU. pose proof (wmono_refl asegs m4) as WM.
reenterA asegs A4L HIx asegs_wx HP4. bstep.
evt_done5.
eapply pop_tailA; [exact HP4 | unfold jhdr_cells; cbn [app]; exact HDR2 | exact OPB4 | exact ST4 | exact ERR4
| clear K; cbn [length app] in *; unfold blk in *; cbn [bB charge] in *; lia | spl |].
intros ms5 md5 A5 NP. apply K.
eapply next_postA_w; [exact FS4 | exact FRM4 | exact VM4 | | exact BB4 | cbn [uw_cost] in BD4; lia | exact NP
| clear K; cbn [length app]; rewrite ?length_app; cbn [length]; unfold blk; lia].
eapply heap_pres_trans; [hpw HPR2|]. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; cbn; right; apply in_or_app; apply in_app_or in Hb; destruct Hb; [left; apply in_or_app; right; assumption | right; assumption]].
Qed.
End LoopA.
End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.

Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5 Qekr.

Import Qw5U.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MJoSetDouble.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Lemma RTC_SERTBL : rtc_sertbl_stmt HIx.
Proof.
intros A LB LM FR B m md HP. unfold A_SERTBL_DBL. cbn [fn_dbl_to_json_string A4F]. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition SD_STK_A : Z := 64 + 4096.

Lemma set_double_A : jo_set_double_A_stmt HIx 0x9fedc SD_STK_A 512 1.
Proof.
unfold jo_set_double_A_stmt, SD_STK_A. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR BB BD A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
pose proof alloc_ceiling_range as ACR.
assert (CH0 : jo_chargeA 512 1 B B) by (split; lia).

assert (RET0 : forall n ty tojs pb udel ud, In (p, n) BS -> 48 <= n -> 0 <= ty <= 6 -> ty <> JT_DOUBLE ->
rw_cells asegs m p (jhdr_cells ty 1 tojs pb udel ud) ->
set_double_root (fn_dbl_to_json_string A4F) r = r ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 6444320) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 655068) fc None m (seg_rom asegs))).
{ intros n ty tojs pb udel ud INp N48 TY NE HDRH SDR.
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
unfold jhdr_cells in HDRH. unfold JT_DOUBLE in NE.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 bstep. bstep. if_falsex.
do 3 bstep.
asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep. if_truex.
bstep. do 10 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0 A B BS) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact CH0.
+ exact ERR.
+ rewrite SDR.
eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ clear. destruct r as [|sd|?|]; [| destruct sd | |]; first [exact I | reflexivity]. }

assert (TAIL : forall (AX : ASA A4L HIx) (mdX : config) (BX : bud) (mc : word -> option byte) (PBS : list blk) (pbx : Z) (x y bitsX : word)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word),
HEAPAx AX (((p, 48) :: PBS) ++ LB) LM FRS BX mc mdX ->
model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mc ->
jo_chargeA 512 1 B BX ->
opt_pbuf asegs mc PBS pbx ->
rw_cells asegs mc p [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 653260); C8 (Z_to_bv 64 pbx); C8 x; C8 y; C8 bitsX] ->
rw_cells asegs mc (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk asegs mc lo (bv_unsigned sp + -64) ->
rw_cells asegs mc 6444156 [C4 errv] ->
set_double_root (fn_dbl_to_json_string A4F) r = JRdblx (fn_dbl_to_json_string A4F) ->
AJ5 A4L HIx AX T mdX
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 p)
xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (p + 24)) (Z_to_bv 64 2147450880) xs4 (Z_to_bv 64 (p / 8 + 2147450880))
(Z_to_bv 64 (p / 8 + 2147450881)) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 655332) fc None mc (seg_rom asegs))).
{ intros AX mdX BX mc PBS pbx x y bitsX xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 HPX VMX HPRX CHX OPBX CELLSX FRX STX ERRX SDR.
clear RET0 HP MI WM GOT CELL RR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPX) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (p, p + 48)] mc) as MU.
cbn [app] in HPX.
blk_factsA A4L HIx HPX p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (RTC_SERTBL _ _ _ _ _ _ _ HPX) as TBC. apply ro_C8_of_bytes_at in TBC. unfold A_SERTBL_DBL in TBC. cbn [fn_dbl_to_json_string A4F] in TBC.

change [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 653260); C8 (Z_to_bv 64 pbx); C8 x; C8 y; C8 bitsX]
with ([C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 653260); C8 (Z_to_bv 64 pbx)] ++ ([C8 x; C8 y] ++ [C8 bitsX])) in CELLSX.
destruct (proj1 (rw_cells_app asegs mc p _ _) CELLSX) as [HDRX RESTX]. clear CELLSX. cbn [cells_size csize Nat.add] in RESTX. replace (p + Z.of_nat 24) with (p + 24) in RESTX by lia.
destruct (proj1 (rw_cells_app asegs mc (p + 24) _ _) RESTX) as [DSTX TLX]. clear RESTX. cbn [cells_size csize Nat.add] in TLX. replace (p + 24 + Z.of_nat 16) with (p + 40) in TLX by lia.
assert (DSTB : rw_cells asegs mc (p + 24) [CB 16 (le8 x ++ le8 y)]).
{ eapply rw_cells_recast; [exact DSTX | cbn; repeat split; try exact I; rewrite length_app, !length_le8; reflexivity | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity | reflexivity]. }
clear DSTX.
a4l. reenterA asegs A4L HIx asegs_wx HPX.
bstep. bstep. bstep. bstep.
eapply OBL_AMEMSET with (ab := p) (nb := 48) (d := p + 24) (c := 0) (n := 16) (lo := lo) (old := le8 x ++ le8 y);
[ exact HPX | .. ]; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DSTB
| eassumption | exact LO | lia | clear - SPA; Z.div_mod_to_equations; lia
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mq _ =>
transport_after_call asegs mq m4 MU4 WM4; try match goal with H : mem_inv asegs mq |- _ => clear H end; clear MU4 WM4 end.
replace (ret_pc (Z_to_bv 64 0x9fff4)) with (Z_to_bv 64 0x9fff4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
heap_nowA_auto A4L HIx HPX HPc. shadow_nowA A4L HIx HPc p 48 SHp.
assert (SHT : ro_cells asegs m4 2147568090 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (0xe4ed0 / 8) HPc) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (0xe4ed0 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (0xe4ed0 / 8 + 2147450880) with 2147568090 in X. exact X. }
a4l. clear HPc.
bstep. rewrite ?sxb_zero. bstep. if_false.
bstep. rewrite sx32_small by lia. bstep. bstep. bstep. if_lit.
bstep. bstep. bstep. bstep.
bstep. bstep. bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstepz. bstep.
do 10 bstep.
evt_done5.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPX) as NDX.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ mdX mf 1 AX BX ((p, 48) :: PBS)) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [exact VMX|].
split; [release_frame FRX ST4 (bv_unsigned sp); exact ST4|]. split; [| exists errv; exact ERRX].
eapply heap_pres_trans; [exact HPRX|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPX | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ NDX) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 NDX ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HPX _ Hi). in_app_prefix.
+ exact CHX.
+ exact ERRX.
+ rewrite SDR. cbn [jroot_rep]. split; [lia|]. split; [left; reflexivity|].
exists pbx, PBS, bitsX. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPBX | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HPX ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ NDX) as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HPX ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* unfold jhdr_cells, JT_DOUBLE. cbn [app fn_dbl_to_json_string A4F hl_segs hla_base A4L A4H].
lazymatch goal with |- rw_cells _ ?mf _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
change [c1; c2; c3; c4; c5; c6; c7] with ([c1; c2; c3; c4] ++ ([c5; c6] ++ [c7]));
apply (proj2 (rw_cells_app asegs mf p _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf p _ |- _ => exact H end |];
replace (p + Z.of_nat 24) with (p + 24) by lia;
apply (proj2 (rw_cells_app asegs mf (p + 24) _ _)); cbn [cells_size csize Nat.add];
replace (p + 24 + Z.of_nat 16) with (p + 40) by lia;
split; [| match goal with H : rw_cells asegs mf (p + 40) _ |- _ => exact H end];
match goal with H : rw_cells asegs mf (p + 24) _ |- _ =>
eapply rw_cells_recast; [exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] end
end.
+ cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HPX | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPX MU); solve_frameW_withA HPX | exact WM | assumption].
+ clear - SDR. destruct r as [|sd|?|]; [| destruct sd | |]; cbn in SDR; first [exact I | discriminate SDR]. }

assert (STORE1 : forall (PBS : list blk) (pbx : Z) (bitsX : word),
BS = (p, 48) :: PBS -> opt_pbuf asegs m PBS pbx ->
rw_cells asegs m p [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1); C8 (Z_to_bv 64 640512); C8 (Z_to_bv 64 pbx); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 bitsX] ->
set_double_root (fn_dbl_to_json_string A4F) r = JRdblx (fn_dbl_to_json_string A4F) ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp (Z_to_bv 64 6444320) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 655068) fc None m (seg_rom asegs))).
{ intros PBS pbx bitsX EBS OPB CELLS SDR. subst BS. clear RET0 TAIL RR. cbn [app] in HP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
blk_factsA A4L HIx HP p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 bstep. bstep. if_falsex.
do 3 bstep.
asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep. if_lit.
bstep.
asan_chkA.
bstep.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 48 SHp. a4l. clear HPc.
bstep. asan_chkA.
bstep. bstep. bstep. bstep. if_lit.
bstep. bstep.
do 10 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1 A B ((p, 48) :: PBS)) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact CH0.
+ exact ERR.
+ rewrite SDR. cbn [jroot_rep]. split; [lia|]. split; [left; reflexivity|].
exists pbx, PBS, (reg_get F 10). split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ ND0) as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* unfold jhdr_cells, JT_DOUBLE. cbn [app fn_dbl_to_json_string A4F hl_segs hla_base A4L A4H]. assumption.
+ cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ clear - SDR. destruct r as [|sd|?|]; [| destruct sd | |]; cbn in SDR; first [exact I | discriminate SDR]. }
destruct r as [ | s | tojs0 | ].
-
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 bstep. bstep. if_truex. do 10 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0 A B []) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
+ exact CH0.
+ exact ERR.
+ cbn [set_double_root jroot_rep]. split; reflexivity.
+ cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
+ reflexivity.
-
pose proof RR as [Hp J].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F s m BS p 1 J ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
destruct (Z.eq_dec (jtype s) JT_DOUBLE) as [TD | NTD].
2:{
destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _].
eapply (RET0 n (jtype s) tojs pb udel ud INp N48 (jtype_range s) NTD HDRH).
destruct s; first [reflexivity | exfalso; apply NTD; reflexivity]. }
destruct s as [|u| | | |]; try discriminate TD. clear TD CLOSE HDR SZ N48 INp.
destruct J as (pb_ & PBS & REST & EBS & OPB & J).
destruct u.
*
destruct J as (bits & ud_ & udn & uds & -> & Hudn & CELLS & CSTR). cbn [app] in EBS. subst BS. cbn [app] in HP, ND.
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app fn_ud_to_json_string fn_free_userdata A4F hl_segs hla_base A4L A4H] in CELLS. cbn [hl_segs hla_base A4L A4H] in OPB. clear CSTR.
blk_factsA A4L HIx HP p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 bstep. bstep. if_falsex.
do 3 bstep.
asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep. if_lit.
bstep.
asan_chkA.
bstep.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 48 SHp. a4l. clear HPc.
bstep. asan_chkA.
bstep. bstep. bstep. bstep.
if_lit.
bstep. asan_chkA.
bstep. bstep.
bstep. if_lit.
bstep. asan_chkA.
bstep. bstep. bstep.
bstep. bstep.
evt_done5.
eapply (hiA_free A4L HIx) with (p := ud_) (u := UWpaid) (lo := lo) (errv := errv);
[ heap_nowA A4L HIx HP MU WM MI | right; exists udn; right; left; reflexivity | .. ].
all: rewrite ?unsigned_lit by lia.
1: eassumption.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: cbn [hl_segs hl_tp hla_base A4L A4H]; unfold A_TP; eassumption.
1: reflexivity.
1: reflexivity.
1: split; cbn; exact I.
1: exact BB.
1: destruct (Z.eqb ud_ 0); cbn [uw_cost]; lia.
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3.
cbn [hl_segs hl_tp hla_base A4L A4H] in ST3, HPR3, ERR3, HP3. unfold A_TP in ERR3.
assert (Hpud : p <> ud_).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ud_ udn HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & _ & Hud0 & _).
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
replace (if ud_ =? 0 then 0 else uw_cost UWpaid) with 1 in HP3 by (destruct (Z.eqb_spec ud_ 0); [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs hla_base A4L A4H] in FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in CELLS; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs hla_base A4L A4H] in CELLS.
assert (OPB3 : opt_pbuf asegs m3 PBS pb_).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply agree_on_trans.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. cbn in ND. inversion ND as [|x_ l_ Hni Hnd]; subst. apply Hni. right. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3).
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
+ exact (nodup_prefix_suffix ((p, 48) :: (ud_, udn) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
+ exact (nodup_prefix_suffix (((p, 48) :: (ud_, udn) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
+ refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
- eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb]]. }
replace (ret_pc (Z_to_bv 64 655332)) with (Z_to_bv 64 655332) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply (TAIL A3 md3 (charge B 512 1) m3 PBS pb_);
[ exact HP3 | exact VM3 | exact HPRb | unfold jo_chargeA, charge; cbn [bB bD]; split; lia | exact OPB3 | exact CELLS | exact FR | exact ST3 | exact ERR3 | reflexivity ].
*
destruct J as (bits & -> & _ & CELLS). cbn [app] in EBS.
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app fn_dbl_to_json_string A4F hl_segs hla_base A4L A4H] in CELLS. cbn [hl_segs hla_base A4L A4H] in OPB.
eapply (STORE1 PBS pb_ bits EBS OPB CELLS). reflexivity.
-
destruct RR as (Hp & Htojs & pb_ & PBS & bits & EBS & OPB & CELLS).
unfold jhdr_cells, JT_DOUBLE in CELLS. cbn [app hl_segs hla_base A4L A4H] in CELLS. cbn [hl_segs hla_base A4L A4H] in OPB.
destruct Htojs as [-> | ->].
+
cbn [fn_dbl_to_json_string A4F] in CELLS.
eapply (STORE1 PBS pb_ bits EBS OPB CELLS). reflexivity.
+
cbn [fn_ud_to_json_string A4F] in CELLS. subst BS. cbn [app] in HP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
blk_factsA A4L HIx HP p 48 Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 bstep. bstep. if_falsex.
do 3 bstep.
asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep. if_lit.
bstep.
asan_chkA.
bstep.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 48 SHp. a4l. clear HPc.
bstep. asan_chkA.
bstep. bstep. bstep. bstep. if_lit.
bstep. asan_chkA.
bstep. bstep.
bstep. if_lit.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] =>
assert (HPc : HEAPAx A ((p, 48) :: PBS ++ LB) LM FRS B mc md) by (heap_nowA A4L HIx HP MU WM MI);
eapply (TAIL A md B mc PBS pb_) end;
[ exact HPc | apply model_vm_only_refl | | exact CH0 | | eassumption | eassumption | eassumption | eassumption | reflexivity ].
* eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].
intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
-- exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
-- exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
-- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof (nodup_app_l' _ _ ND0) as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
-
pose proof RR as (Hp & pb_ & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hstr & ALT).
assert (CELLS : exists rest, rw_cells asegs m p (jhdr_cells JT_STRING 1 (fn_str_to_json_string A4F) pb_ 0 0 ++ rest)).
{ destruct ALT as [(_ & _ & _ & junk & C) | (_ & pd & pdn & junk & junk2 & _ & _ & C & _)]; cbn [hl_segs hla_base A4L A4H] in C; eexists; exact C. }
destruct CELLS as [rest CELLS].
destruct (proj1 (rw_cells_app asegs m p _ _) CELLS) as [HDRH _].
eapply (RET0 (48 + cap) JT_STRING (fn_str_to_json_string A4F) pb_ 0 0); [rewrite EBS; left; reflexivity | lia | unfold JT_STRING; lia | unfold JT_STRING, JT_DOUBLE; lia | exact HDRH | reflexivity].
Qed.
End MJoSetDouble.
End RC__1.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qekr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qekr.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoSetScal2.
Variable HIx : heap_iface_A A4L.
Notation jo_set_scalar_A_stmt := (jo_set_scalar_A_stmt HIx).
Notation jroot_hdrA := (jroot_hdrA).
Notation blk_gran0A := (blk_gran0A HIx).

Lemma set_int64_A : jo_set_scalar_A_stmt 0x9e27c.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_truex.
bstep. bstep. bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 56 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 56 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 56)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep. rewrite sx32_small by (unfold JT_INT; lia).
bstep.
bstep. if_lit.
bstep.
asan_chkA.
bstepz.
bstep.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 56 SHp. a4l. clear HPc.
asan_chkA.
bstepz.
do 5 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 56. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 56) :: PBS) LB p 56 56 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 56) :: PBS) ++ LB) LM p 56 56 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 56 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists 0, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_INT in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep. rewrite sx32_small by lia.
bstep.
bstep. if_truex.
do 4 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.

Lemma set_uint64_A : jo_set_scalar_A_stmt 0x9ed0c.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_truex.
bstep. bstep. bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_INT) as [E | NE].
-
specialize (TI E). subst r ty. clear TB. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB.
unfold jhdr_cells, JT_INT in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 56 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 56 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 56)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep. rewrite sx32_small by (unfold JT_INT; lia).
bstep.
bstep. if_lit.
bstep.
asan_chkA.
bstepz.
bstep.
try clear SHp. heap_nowA_auto A4L HIx HP HPc. shadow_nowA A4L HIx HPc p 56 SHp. a4l. clear HPc.
asan_chkA.
bstep.
bstepz.
do 5 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 56. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 56) :: PBS) LB p 56 56 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 56) :: PBS) ++ LB) LM p 56 56 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 56)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 56 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists 1, a1, junk_. split; [reflexivity|]. split; [lia|]. unfold jhdr_cells, JT_INT. cbn [app]. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_INT in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep. rewrite sx32_small by lia.
bstep.
bstep. if_truex.
do 4 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.

Lemma set_boolean_A : jo_set_scalar_A_stmt 0x9db50.
Proof.
unfold jo_set_scalar_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA) RR A0 K.
unfold_consts. unfold A_ERRNO, A_TP in *. subst a0 tp. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m) as WM.
destruct (jroot_null_decA r) as [-> | NN].
{
destruct RR as [-> ->]. cbn [app] in HP.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_truex.
bstep. bstep. bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
- unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; exact Hb | clia | solve_clientWA A4L HIx HP].
- exact ERR.
- cbn [jroot_rep]. split; reflexivity.
- cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jroot_hdrA r m BS p RR NN ND) as (n & ty & tojs & pb & udel & ud & rest & INp & SZ & N48 & TY & HDR & TB & TI).
assert (Hp : p <> 0) by (destruct r; [exfalso; exact (NN eq_refl) | exact (proj1 RR) ..]).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
blk_factsA A4L HIx HP p n Hpal Hplo Hphi Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
pose proof (blk_gran0A _ _ _ _ _ _ _ p n 0 HP INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.

destruct (proj1 (rw_cells_app asegs m p _ _) HDR) as [HDRH _]. unfold jhdr_cells in HDRH.
destruct (Z.eq_dec ty JT_BOOLEAN) as [E | NE].
-
specialize (TB E). subst r ty. clear TI. destruct RR as [_ J].
destruct J as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS, OPB. unfold jhdr_cells, JT_BOOLEAN in CELLS. cbn [app] in CELLS.
subst REST. cbn [app] in EBS. subst BS. clear HDR HDRH SH0. cbn [app] in HP.
blk_factsA A4L HIx HP p 48 Hpal2 Hplo2 Hphi2 Hpimg2. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg2.
shadow_nowA A4L HIx HP p 48 SHp.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (p, p + 48)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep. rewrite sx32_small by (unfold JT_BOOLEAN; lia).
bstep.
bstep. if_lit.
bstep.
asan_chkA.
bstepz.
do 5 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 1) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |]. apply Forall_cons; [| apply Forall_nil].
right; left. exists p, 48. cbn [fst snd]. split; [in_app_prefix|]. split; [| lia].

intro Hi. apply in_app_or in Hi as [Hi|Hi]; [| apply in_app_or in Hi as [Hi|Hi]].
* exact (nodup_prefix_suffix ((p, 48) :: PBS) LB p 48 48 (nodup_app_l' _ _ ND0) ltac:(left; reflexivity) Hi).
* exact (nodup_prefix_suffix (((p, 48) :: PBS) ++ LB) LM p 48 48 ND0 ltac:(left; reflexivity) Hi).
* refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hi). in_app_prefix.
+ exact ERR.
+ cbn [jroot_rep]. split; [exact Hp|].
exists pb_, PBS, [(p, 48)]. split; [reflexivity|]. split.
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |].
intros a k Hin. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh.
assert (NEa : p <> a).
{ intros <-. pose proof ND as ND'. cbn in ND'. inversion ND' as [|x_ l_ Hni Hnd]; subst. apply Hni. exact (in_map blk_addr _ _ Hin). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p 48 a k HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; apply in_or_app; left; exact Hin) NEa).
split; [lia | split; [lia | exact I]].
* exists (bv_unsigned a1), junk_. split; [reflexivity|]. unfold jhdr_cells, JT_BOOLEAN. cbn [app]. rewrite Z_to_bv_bv_unsigned. assumption.
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
-
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. unfold JT_BOOLEAN in NE.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 16%nat ST.
bstep. bstep.
bstep. if_falsex.
bstep. bstep. bstep.
asan_chkA.
bstep. rewrite sx32_small by lia.
bstep.
bstep. if_truex.
do 4 bstep.
evt_done5.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] => eapply (K _ md mf 0) end.
+ unfold jo_post_frameA. split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|]. split; [| exists errv; exact ERR].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros ? Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb] | clia | solve_clientWA A4L HIx HP].
+ exact ERR.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m _ BS BS); [exact RR | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hh. split; [lia | exact I].
+ eapply (heapA_client_frame A4L HIx); [exact HP | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU); solve_frameW_withA HP | exact WM | assumption].
Qed.
End AJoSetScal2.
End RC__1.
