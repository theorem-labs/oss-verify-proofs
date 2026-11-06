(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QnCn Q7UD Qhd4 Qwm6 QlKV Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import QnCn.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlNew.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition array_list_new2_A_entry : Z := 0xa0394.
Definition al_new2_costB (isz : Z) : Z := 2048 + 128 * isz.

Definition array_list_new2_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (isz lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - al_new2_costB isz <= bB B' /\ bD B <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists arr, alist asegs A4F m' [(r, 32); (arr, 8 * isz)] r [] /\ HEAPAx A' ([(r, 32); (arr, 8 * isz)] ++ LB) LM FRS B' m' md') ).

Lemma array_list_new2_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (isz lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 (fn_arr_entry_free A4F) -> a1 = Z_to_bv 64 isz -> 1 <= isz -> 8 * isz < 2^32 ->
al_new2_costB isz <= bB B -> 0 <= bD B ->
(forall ms' md' A', array_list_new2_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B isz lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_new2_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 Hisz1 Hisz2 BB BD K.
unfold_consts. unfold al_new2_costB in BB. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
subst a0 a1 tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold array_list_new2_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 5 step.
step. if_falsex.
step. step.
step. step. step.
step. step.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [exact I | lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 6 step.
evt_done5. apply K. unfold array_list_new2_A_post.
exists m2, 0, e2, (charge B (16 * 32 + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold al_new2_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 32) with 32%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2) as [GOT CELL].
blk_factsA A4L HIx HP2 r 32 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 32 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 0 r 32 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 3 r 32 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step.
asan_chkA.
step.
step.
asan_chkA.
stepz.
step.
asan_chkA.
stepz.
step. rewrite (unsigned_lit isz) by lia. rewrite (Z.shiftl_mul_pow2 isz 3) by lia. change (2^3) with 8.
step. step. step.

clear SHr.
alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (cbn [uw_pre uw_ok uw_key uw_cost bB bD charge]; first [exact I | lia]).
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
lazymatch goal with BLKc : rw_cells asegs _ r _ |- _ =>
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLKc; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]] end.
clear MU WM MI ST2 GOT CELL.
destruct OUT3 as [(-> & _ & HP3) | (Hq & [junk1 BLK1] & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 32 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 0 r 32 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m3) as MU.
pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step.
asan_chk0.
step. step. stepz.
step. if_false.
step.

clear SHr.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 32. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; exact I).
all: try (destruct (Z.eqb_spec r 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (Z.eqb_spec r 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU.
pose proof (wmono_refl asegs m5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
do 7 step.
evt_done5. apply K. unfold array_list_new2_A_post.
exists m5, 0, e3, (charge (charge (charge B (16 * 32 + 512) (uw_cost UWptr)) (16 * (isz * 8) + 512) (uw_cost UWptr)) 512 0).
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR5 | split; [| split; [| left; auto]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM5]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
* unfold al_new2_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 q (isz * 8) Hqal Hqlo Hqhi Himg_q.
assert (Hqr : q <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (isz * 8) r 32 HP3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hqr) as Hdj.
shadow_nowA A4L HIx HP3 r 32 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 0 r 32 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m3) as MU.
pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step.
asan_chk0.
step. step. step.
step. if_truex.
do 6 step.
evt_done5. apply K. unfold array_list_new2_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e3, (charge (charge B (16 * 32 + 512) (uw_cost UWptr)) (16 * (isz * 8) + 512) (uw_cost UWptr)) end.
split; [| split; [| split; [| split; [ | split; [ | split; [| split; [| right]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP3].
* eassumption.
* unfold al_new2_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
* split; [exact Hr|]. exists q. split.
-- exists q, isz, junk1. split; [reflexivity|]. split; [cbn; lia|]. split; [lia|]. split.
++ cbn [length Z.of_nat].
lazymatch goal with |- rw_cells _ ?mf _ _ =>
lazymatch goal with H1 : rw_cells asegs mf r _ |- _ => exact H1 end end.
++ cbn [map length Z.of_nat app]. rewrite Z.sub_0_r. replace (8 * isz) with (isz * 8) by lia.
first [ exact BLK1
| lazymatch goal with |- rw_cells _ ?mf _ _ => eapply (rw_cells_transport asegs _ m3 mf); [exact BLK1 | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end ].
-- assert (HP3' : HEAPAx A3 ((r, 32) :: (q, 8 * isz) :: LB) LM FRS (charge (charge B (16 * 32 + 512) (uw_cost UWptr)) (16 * (isz * 8) + 512) (uw_cost UWptr)) m3 md3).
{ replace (8 * isz) with (isz * 8) by lia.
exact (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP3 (perm_swap (r, 32) (q, isz * 8) LB) (Permutation_refl LM) (Permutation_refl FRS)). }
cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP3' | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3' MU). solve_frameW_withA HP3'.
Qed.
End AAlNew.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition printbuf_reset_A_entry : Z := 0x9a64c.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma printbuf_reset_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (pb buf bpos cap lo : Z) (content : list byte)
(Q : machine_state -> Prop),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' : word) m',
munch [(buf, buf + 1); (pb + 8, pb + 12); (bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
pbuf_core asegs m' pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 content) -> stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pb + 8)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_reset_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros HP (Hbp & Hcap & Hlen & PBS & PBUF) ST LO LOS RA K.
unfold printbuf_reset_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
assert (Hne : pb <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as DISJ.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as SHb. unfold shad in SHb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0b.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP1b.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap 0 buf cap HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPb0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap 0 pb 16 HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPb0p.
a4l.

assert (HRS : exists v, ro_cells asegs m (buf / 8 + 2147450880) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8))).
{ destruct (Z.lt_ge_cases cap 8) as [Hs | Hb8].
- exists cap. split; [| right; lia].
pose proof (shadow_tail asegs m (buf / 8 + 2147450880) cap ltac:(lia) ltac:(Z.div_mod_to_equations; lia) SHb) as X.
rewrite (Z.div_small cap 8), Z.add_0_r, (Z.mod_small cap 8) in X by lia. exact X.
- exists 0. split; [| left; reflexivity]. exact (shadow_head0 asegs m _ cap Hb8 SHb). }
clear SHb. destruct HRS as (v & SHB & Hv).
destruct content as [|c0 content']; [cbn in Hlen; lia|].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat PBUF ltac:(lia)) as [PB0 PB1]. clear PBUF. cbn [firstn skipn] in PB0, PB1.
apply (rw_cells_recast asegs _ _ _ [C1 c0]) in PB0; [| cbn; auto | reflexivity | reflexivity].
stash PB1.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(buf, buf + 1); (pb + 8, pb + 12); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step.
step. step. step.
asan_chk0.
step.

pose proof (ov_read1_of_ro asegs _ _ _ SHB) as HR.
step. step. sh_norm.
try replace (2147450880 + buf / 8) with (buf / 8 + 2147450880) by lia.
step. rewrite (sxb_small v) by lia. clear HR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STORE : forall y3 y4 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) y3 y4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a684) fc None mc (seg_rom asegs)))
end.
{ intros y3 y4.
stepz.
step.
asan_chkA.
stepz.
step. step. step.
unstash PB1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (rw_cells_transport asegs _ m mf) in PB1; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
eapply K; [exact MU | exact WM | assumption | | release_frame FR ST (bv_unsigned sp); exact ST].
unfold pbuf_core. split; [lia|]. split; [lia|]. split; [cbn [length app skipn] in *; rewrite ?skipn_O; lia|]. split; [eassumption|].
match goal with P0 : rw_cells asegs ?mf buf [C1 _] |- _ =>
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in P0; [| cbn; auto | reflexivity | reflexivity];
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ P0 PB1) as J end.
replace (1 + (Z.to_nat cap - 1))%nat with (Z.to_nat cap) in J by lia. cbn [skipn app]. exact J. }
step.
destruct Hv as [-> | Hvp].
- if_false. apply STORE.
- if_truex. step. rewrite (unsigned_lit buf) by lia. rewrite land7_mod8 by lia.
step. if_truex. apply STORE.
Qed.
End WithIface.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import QnCn.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AAlNew.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition array_list_new2_A_entry : Z := 0xa2270.
Definition al_new2_costB (isz : Z) : Z := 2048 + 128 * isz.

Definition array_list_new2_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (isz lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - al_new2_costB isz <= bB B' /\ bD B <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists arr, alist asegs A4F m' [(r, 32); (arr, 8 * isz)] r [] /\ HEAPAx A' ([(r, 32); (arr, 8 * isz)] ++ LB) LM FRS B' m' md') ).

Lemma array_list_new2_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (isz lo : Z) (errv : word),
HEAPAx A LB LM FRS B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 (fn_arr_entry_free A4F) -> a1 = Z_to_bv 64 isz -> 1 <= isz -> 8 * isz < 2^32 ->
al_new2_costB isz <= bB B -> 0 <= bD B ->
(forall ms' md' A', array_list_new2_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B isz lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 array_list_new2_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until errv. intros HP ST LO LOS SPA HT ERR TP RA A0 A1 Hisz1 Hisz2 BB BD K.
unfold_consts. unfold al_new2_costB in BB. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
subst a0 a1 tp. a4l. reenterA asegs A4L HIx asegs_wx HP. unfold array_list_new2_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 5 bstep.
bstep. if_falsex.
bstep. bstep.
bstep. bstep. bstep.
bstep. bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; first [exact I | lia]).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 6 bstep.
evt_done5. apply K. unfold array_list_new2_A_post.
exists m2, 0, e2, (charge B (16 * 32 + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold al_new2_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 32) with 32%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2) as [GOT CELL].
blk_factsA A4L HIx HP2 r 32 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 32 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 0 r 32 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 3 r 32 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP3.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex.
bstep.
asan_chkA.
bstep.
bstep.
asan_chkA.
bstepz.
bstep.
asan_chkA.
bstepz.
bstep. rewrite (unsigned_lit isz) by lia. rewrite (Z.shiftl_mul_pow2 isz 3) by lia. change (2^3) with 8.
bstep. bstep. bstep.

clear SHr.
alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (cbn [uw_pre uw_ok uw_key uw_cost bB bD charge]; first [exact I | lia]).
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
lazymatch goal with BLKc : rw_cells asegs _ r _ |- _ =>
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLKc; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]] end.
clear MU WM MI ST2 GOT CELL.
destruct OUT3 as [(-> & _ & HP3) | (Hq & [junk1 BLK1] & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 r 32 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 0 r 32 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m3) as MU.
pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep.
asan_chk0.
bstep. bstep. bstepz.
bstep. if_false.
bstep.

clear SHr.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 32. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; exact I).
all: try (destruct (Z.eqb_spec r 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (Z.eqb_spec r 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST3.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU.
pose proof (wmono_refl asegs m5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
do 7 bstep.
evt_done5. apply K. unfold array_list_new2_A_post.
exists m5, 0, e3, (charge (charge (charge B (16 * 32 + 512) (uw_cost UWptr)) (16 * (isz * 8) + 512) (uw_cost UWptr)) 512 0).
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR5 | split; [| split; [| left; auto]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM5]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
* unfold al_new2_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 q (isz * 8) Hqal Hqlo Hqhi Himg_q.
assert (Hqr : q <> r).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (isz * 8) r 32 HP3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hqr) as Hdj.
shadow_nowA A4L HIx HP3 r 32 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 32 0 r 32 HP3 ltac:(right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 32)] m3) as MU.
pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep.
asan_chk0.
bstep. bstep. bstep.
bstep. if_truex.
do 6 bstep.
evt_done5. apply K. unfold array_list_new2_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e3, (charge (charge B (16 * 32 + 512) (uw_cost UWptr)) (16 * (isz * 8) + 512) (uw_cost UWptr)) end.
split; [| split; [| split; [| split; [ | split; [ | split; [| split; [| right]]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; right; right; exact Hb | clia | solve_clientWA A4L HIx HP3].
* eassumption.
* unfold al_new2_costB. cbn [bB charge]. lia.
* cbn [bD charge uw_cost]. lia.
* split; [exact Hr|]. exists q. split.
-- exists q, isz, junk1. split; [reflexivity|]. split; [cbn; lia|]. split; [lia|]. split.
++ cbn [length Z.of_nat].
lazymatch goal with |- rw_cells _ ?mf _ _ =>
lazymatch goal with H1 : rw_cells asegs mf r _ |- _ => exact H1 end end.
++ cbn [map length Z.of_nat app]. rewrite Z.sub_0_r. replace (8 * isz) with (isz * 8) by lia.
first [ exact BLK1
| lazymatch goal with |- rw_cells _ ?mf _ _ => eapply (rw_cells_transport asegs _ m3 mf); [exact BLK1 | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; lia] end ].
-- assert (HP3' : HEAPAx A3 ((r, 32) :: (q, 8 * isz) :: LB) LM FRS (charge (charge B (16 * 32 + 512) (uw_cost UWptr)) (16 * (isz * 8) + 512) (uw_cost UWptr)) m3 md3).
{ replace (8 * isz) with (isz * 8) by lia.
exact (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP3 (perm_swap (r, 32) (q, isz * 8) LB) (Permutation_refl LM) (Permutation_refl FRS)). }
cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP3' | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP3' MU). solve_frameW_withA HP3'.
Qed.
End AAlNew.
End RC__1.
End Mq2.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition printbuf_reset_A_entry : Z := 0x9bc54.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma printbuf_reset_A :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (pb buf bpos cap lo : Z) (content : list byte)
(Q : machine_state -> Prop),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 ->
(forall (a1' a2' a3' a4' : word) m',
munch [(buf, buf + 1); (pb + 8, pb + 12); (bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
pbuf_core asegs m' pb buf 0 cap ([Z_to_bv 8 0] ++ skipn 1 content) -> stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pb + 8)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_reset_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros HP (Hbp & Hcap & Hlen & PBS & PBUF) ST LO LOS RA K.
unfold printbuf_reset_A_entry in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
assert (Hne : pb <> buf).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst. apply Hni. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb 16 buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as DISJ.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as SHb. unfold shad in SHb.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP1.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 0 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP0b.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 buf cap HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP1b.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap 0 buf cap HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEPb0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ buf cap 0 pb 16 HP ltac:(right; left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPb0p.
a4l.

assert (HRS : exists v, ro_cells asegs m (buf / 8 + 2147450880) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8))).
{ destruct (Z.lt_ge_cases cap 8) as [Hs | Hb8].
- exists cap. split; [| right; lia].
pose proof (shadow_tail asegs m (buf / 8 + 2147450880) cap ltac:(lia) ltac:(Z.div_mod_to_equations; lia) SHb) as X.
rewrite (Z.div_small cap 8), Z.add_0_r, (Z.mod_small cap 8) in X by lia. exact X.
- exists 0. split; [| left; reflexivity]. exact (shadow_head0 asegs m _ cap Hb8 SHb). }
clear SHb. destruct HRS as (v & SHB & Hv).
destruct content as [|c0 content']; [cbn in Hlen; lia|].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat PBUF ltac:(lia)) as [PB0 PB1]. clear PBUF. cbn [firstn skipn] in PB0, PB1.
apply (rw_cells_recast asegs _ _ _ [C1 c0]) in PB0; [| cbn; auto | reflexivity | reflexivity].
stash PB1.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(buf, buf + 1); (pb + 8, pb + 12); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep.
bstep. bstep. bstep.
asan_chk0.
bstep.

pose proof (ov_read1_of_ro asegs _ _ _ SHB) as HR.
bstep. bstep. sh_norm.
try replace (2147450880 + buf / 8) with (buf / 8 + 2147450880) by lia.
bstep. rewrite (sxb_small v) by lia. clear HR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STORE : forall y3 y4 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pb) (Z_to_bv 64 buf) (Z_to_bv 64 2147450880) y3 y4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9bc9c) fc None mc (seg_rom asegs)))
end.
{ intros y3 y4.
bstepz.
bstep.
asan_chkA.
bstepz.
bstep. bstep. bstep.
unstash PB1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (rw_cells_transport asegs _ m mf) in PB1; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
eapply K; [exact MU | exact WM | assumption | | release_frame FR ST (bv_unsigned sp); exact ST].
unfold pbuf_core. split; [lia|]. split; [lia|]. split; [cbn [length app skipn] in *; rewrite ?skipn_O; lia|]. split; [eassumption|].
match goal with P0 : rw_cells asegs ?mf buf [C1 _] |- _ =>
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in P0; [| cbn; auto | reflexivity | reflexivity];
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ P0 PB1) as J end.
replace (1 + (Z.to_nat cap - 1))%nat with (Z.to_nat cap) in J by lia. cbn [skipn app]. exact J. }
bstep.
destruct Hv as [-> | Hvp].
- if_false. apply STORE.
- if_truex. bstep. rewrite (unsigned_lit buf) by lia. rewrite land7_mod8 by lia.
bstep. if_truex. apply STORE.
Qed.
End WithIface.
End RC__1.
