(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5 QNQk.Mq1.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Ltac ifT := unfold_cond; cond_unsig; if_true.
Ltac ifF := unfold_cond; cond_unsig; if_false.

Definition rt_mem_cells (m : mem) : Prop :=
shadow_base asegs m
/\ ro_cells asegs m 0x0e5dc0 [C8 (wz 0x0f07e8); C8 (wz 0x0f07f0); C8 (wz 0x0f07e0); C8 (wz 0x0e7db0)]
/\ ro_cells asegs m 0x0f07e0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)].

Local Ltac rtacc := intros m RC; unfold rt_consts_at in RC; decompose [and] RC; assumption.

Lemma rt_1589b8_guard {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e6b80 [C8 (wz 0x642ea0)].
Proof. rtacc. Qed.

Lemma rt_683ae0 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x642ea0 [C8 band_guard].
Proof. rtacc. Qed.

Lemma rt_157bb0 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e5da8 [C8 (wz 0x181628); C8 (wz 0x0ed2f8)].
Proof. rtacc. Qed.
Lemma rt_157bc8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e5dc0 [C8 (wz 0x0f07e8); C8 (wz 0x0f07f0); C8 (wz 0x0f07e0); C8 (wz 0x0e7db0)].
Proof. rtacc. Qed.

Lemma rt_1588c8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e6928 [C8 (wz 0x0f07d9)].
Proof. rtacc. Qed.
Lemma rt_15a5a8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e7d58 [C8 (wz 0xdbd10)].
Proof. rtacc. Qed.
Lemma rt_15a5f8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e7da8 [C8 (wz 0xdb34c); C8 (wz 0xdb750)].
Proof. rtacc. Qed.

Lemma rt_159b60 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e7c48 [C8 (wz 0xdb250)].
Proof. rtacc. Qed.

Lemma rt_159bb8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e7c60 [C8 (wz 0xd3500)].
Proof. rtacc. Qed.
Lemma rt_159c68 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e7c78 [C8 (wz 0xd8fe8); C8 (wz 0xd385c)].
Proof. rtacc. Qed.
Lemma rt_161720 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0f07d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof. rtacc. Qed.
Lemma rt_161728 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0f07e0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)].
Proof. rtacc. Qed.

Lemma rt_1f25bc {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x18167c [C1 (Z_to_bv 8 1)].
Proof. rtacc. Qed.
Lemma rt_1f2663 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x181723 [C1 (Z_to_bv 8 1)].
Proof. rtacc. Qed.

Lemma rt_mem_cells_of {BAND : Band} : forall m, shadow_base asegs m -> rt_consts_at asegs m -> rt_mem_cells m.
Proof.
intros m SB RC. exact (conj SB (conj (rt_157bc8 _ RC) (rt_161728 _ RC))).
Qed.

Definition rt_wzone (iv : Z * Z) : Prop :=
snd iv <= 0x0e23f0 \/ (0x0e7e00 <= fst iv /\ snd iv <= 0x0ea960) \/ (0x0ed400 <= fst iv /\ snd iv <= 0x0ef35c)
\/ (0x0f07fc <= fst iv /\ snd iv <= 0x17f5a0) \/ (0x181726 <= fst iv /\ snd iv <= 0x1819a0) \/ (0x1819a1 <= fst iv /\ snd iv <= 0x642ea0)
\/ (0x642ea8 <= fst iv /\ snd iv <= 0x643120) \/ 0x643128 <= fst iv.

Ltac rt_wzones := repeat (apply Forall_cons; [unfold rt_wzone; cbn [fst snd]; lia|]); apply Forall_nil.
Ltac zforalls := repeat (apply Forall_cons; [cbv beta; unfold rt_wzone; cbn [fst snd]; rewrite ?KHI_eq; lia|]); apply Forall_nil.

Local Ltac rt_disj HW :=
lazymatch type of HW with Forall _ ?W =>
assert (D : forall A n, ((0x0e23f0 <= A /\ A + n <= 0x0e7e00) \/ (0x0ea960 <= A /\ A + n <= 0x0ed400) \/ (0x0ef35c <= A /\ A + n <= 0x0f07fc)
\/ (0x17f5a0 <= A /\ A + n <= 0x181726) \/ (0x1819a0 <= A /\ A + n <= 0x1819a1) \/ (0x642ea0 <= A /\ A + n <= 0x642ea8) \/ (0x643120 <= A /\ A + n <= 0x643128)) -> disjoint_from W A n)
by (intros A n H; clear - HW H; induction HW as [|[lo hi] W' H1 HW IH]; cbn in *; [exact I|]; unfold rt_wzone in H1; cbn in H1; split; [lia| exact IH])
end.

Lemma rt_mem_cells_munch : forall m m' W, rt_mem_cells m -> munch W m m' ->
Forall rt_wzone W -> rt_mem_cells m'.
Proof.
intros m m' W ((S1 & S2) & K1 & K2) MU HW. rt_disj HW.
unfold rt_mem_cells, shadow_base. unfold A_SHADOW_GOT, A_SHADOW_CELL in *.
repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

Lemma rt_consts_at_munch {BAND : Band} : forall m m' W, rt_consts_at asegs m -> munch W m m' -> wmono asegs m m' ->
Forall rt_wzone W -> rt_consts_at asegs m'.
Proof.
intros m m' W RC MU WM HW. rt_disj HW.
unfold rt_consts_at in *.
repeat match goal with |- _ /\ _ => split end;
first [ eapply ro_cells_transport; [| exact MU| apply D; cbn; lia]; apply RC
| eapply rw_cells_transport; [| exact MU| exact WM| apply D; cbn; lia]; apply RC ].
Qed.

Lemma shadow_base_munch : forall m m' W, shadow_base asegs m -> munch W m m' ->
Forall rt_wzone W -> shadow_base asegs m'.
Proof.
intros m m' W [S1 S2] MU HW. rt_disj HW.
unfold shadow_base, A_SHADOW_GOT, A_SHADOW_CELL in *. split; (eapply ro_cells_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

Lemma m2s_spec7 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
rt_mem_cells m -> 0 <= p -> p < 2^47 -> (p + 1 <= 0x7fff8000 \/ KHI <= p) ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz m2s_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros ((K5a & K5) & K19 & K1) P0 K2p REG. rewrite ?KHI_eq in REG. unfold m2s_entry. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in *.
step. stp. stp.
step. stp. stp. stp.
step. destruct REG as [LOW|K1p].
{
ifT. stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia. }
ifF.
step. step. step. step. step. step.
stp. step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia.
Qed.

Lemma miz_spec7 {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n lo : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
zrd m A n -> 0 < n -> n <= 2^40 -> 0x645000 <= A -> A + n <= KHI ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' _ => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz miz_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST CEIL LO ZR N0 N40 ALO AHI.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AHI.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold miz_entry.
carve_frame 16%nat ST.
istep. istep.
step. step. step. step. step. ifz.
step. step. step. stp. stp.
rewrite (unsigned_lit (A + 7)), (unsigned_lit (A + n)) by lia. rewrite !land_m8 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ZR' : zrd mc A n) by (eapply zrd_munch; [exact ZR| exact MU| exact WM| intros x Hx; cbn; lia]) end.
set (ab := A + 7 - (A + 7) mod 8). set (ae := A + n - (A + n) mod 8).
assert (AB : A <= ab < A + 8 /\ ab mod 8 = 0) by (subst ab; Z.div_mod_to_equations; lia).
assert (AE : A + n - 8 < ae <= A + n /\ ae mod 8 = 0) by (subst ae; Z.div_mod_to_equations; lia).
clearbody ab ae.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a6' : word, ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 16 a6' R)) FF (wz 0x754f8) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ab A) as [X1|X1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. step. ifz. step. stp.
eapply (miz_bloop (Z.to_nat (A + n - (A + 1))) (A + 1)); [exact ZR'| reflexivity| lia| lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3' a6'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a6' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a3'' a5' : word, ms2 = MS (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 15 a5' R)) FF (wz 0x7550c) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ae ab) as [X2|X2].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. eapply (miz_wloop (Z.to_nat (ae - ab)) ab); [exact ZR'| reflexivity| lia| lia| Z.div_mod_to_equations; lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3'' a5'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a3'' & a5' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall a0' a2' a4',
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m (fun a0'' _ => a0'' = wz 1))
(MS (mkR ra (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0' (wz 0) a2' a3'' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x7552c) fc None mc (seg_rom asegs)))
end.
{ intros a0' a2' a4'. stp. step. step.
release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity. }
step. destruct (Z_lt_le_dec ae A) as [X3|X3].
{ ifz. apply TAIL. }
ifz. step. destruct (Z_le_gt_dec (A + n) ae) as [X4|X4].
{ ifz. apply TAIL. }
ifz. stp. rewrite (unsigned_lit ae) by lia. replace (A + n + - ae) with (A + n - ae) by lia.
eapply (miz_eloop (Z.to_nat (A + n - ae)) ae); [exact ZR'| reflexivity| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a0' a2' a4'. apply TAIL.
Qed.

Local Ltac rip_tail7 FR ST usp RTM :=
do 10 step; release_frame FR ST usp;
step; apply evt_done; unfold rpost; do 16 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|]; split; [reflexivity| exact RTM].

Lemma rip_spec7 {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
rt_mem_cells m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> 0 <= dst -> dst + n + 8 <= 2^47 -> (dst + n + 8 <= 0x7fff8000 \/ KHI <= dst) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ rt_mem_cells m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RTM MI ST CEIL LO SO [N0 N43] D0 K2d REG.
pose proof CEIL as CEIL'. idtac. pose proof REG as REG'.
rewrite ?KHI_eq in REG.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold rip_entry.
carve_frame 64%nat ST.
do 8 istep.
step. ifz.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RTM1 : rt_mem_cells mc) by (eapply rt_mem_cells_munch; [exact RTM| exact MU| rt_wzones]) end.
pose proof RTM1 as ((K5a & K5) & K19 & K1). unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. stp.
step. stp. stp. stp.

step.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' a4' a5' a6' a7' t0' : word,
ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 14 a4' (@bvmap_set 5 word 15 a5'
(@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' (@bvmap_set 5 word 5 t0' (@bvmap_set 5 word 18 (wz (n + dst)) R))))))))
FF (wz 0x65280) fcc rv mm ro))
end.
{ destruct REG as [LOW|K1d].
- ifT.
stp. step. ifT.
apply evt_done. do 7 eexists. simp_regs. reflexivity.
- ifF.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp.
step. ifF.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
apply evt_done. do 7 eexists. simp_regs. reflexivity. }
intros ms0 (a2c & a3c & a4c & a5c & a6c & a7c & t0c & ->). simp_regs.
step. ifF.
stp. stp. stp.
rewrite (unsigned_lit (dst + 7)), (unsigned_lit (n + dst)) by lia. rewrite !land_m8 by lia.
set (ab8 := dst + 7 - (dst + 7) mod 8). set (ae8 := n + dst - (n + dst) mod 8).
assert (AB : dst <= ab8 < dst + 8 /\ ab8 mod 8 = 0 /\ ab8 = (dst + 7) / 8 * 8) by (subst ab8; Z.div_mod_to_equations; lia).
assert (AE : dst + n - 8 < ae8 <= dst + n /\ ae8 mod 8 = 0 /\ ae8 = (dst + n) / 8 * 8) by (subst ae8; Z.div_mod_to_equations; lia).
clearbody ab8 ae8. clear K5a K5 K19 K1.
step. call0 m2s_spec7; [exact RTM1| lia| lia| rewrite ?KHI_eq; clear - AB REG N0; lia|]. subst_words.
step. step. step. call0 m2s_spec7; [exact RTM1| lia| lia| rewrite ?KHI_eq; clear - AE REG N0; Z.div_mod_to_equations; lia|]. subst_words.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | exact N0]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (shadow_ok_first _ dst n SO' N0) as (v0 & B0 & R0 & C0).
destruct (shadow_ok_last _ dst n SO' N0) as (v1 & B1 & R1 & C1).
pose proof RTM1 as ((K5a & K5) & K19 & K1). unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.

step. stp. stp. rewrite (unsigned_lit dst) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
step.
rewrite (sxb_b8 v0) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' : word, ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' R)) FF (wz 0x652bc) fcc rv mm ro))
end.
{ step. destruct C0 as [->|C0].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit dst), land7 by lia. step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a2' & a3' & ->). simp_regs.

stp. stp. stp. rewrite (unsigned_lit (n + dst + -1)) by lia.
replace (2147450880 + (n + dst + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
step. rewrite (sxb_b8 v1) by lia.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' a2'' : word, ms2 = MS (@bvmap_set 5 word 11 a1' (@bvmap_set 5 word 12 a2'' R)) FF (wz 0x65310) fcc rv mm ro))
end.
{ step. destruct C1 as [->|C1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit (n + dst + -1)), land7 by lia. replace ((n + dst + -1) mod 8) with ((dst + n - 1) mod 8) by (f_equal; lia).
step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a1' & a2'' & ->). simp_regs.

pose proof (shadow_ok_zrd _ dst n SO' N0) as ZR. destruct AB as (AB1 & AB2 & AB3). destruct AE as (AE1 & AE2 & AE3).
rewrite <- AB3, <- AE3 in ZR.
assert (SHB : 0x7fff8000 <= SH ab8 /\ SH ae8 <= 0x10007fff8000 /\ 8 * (SH ae8 - SH ab8) = ae8 - ab8).
{ rewrite !SH_eq. clear - AB1 AB2 AE1 AE2 D0 REG K2d N0. Z.div_mod_to_equations. lia. }
clear K5a K5 K19 K1.
step. destruct (Z_le_gt_dec (SH ae8) (SH ab8)) as [X5|X5].
{ ifz. rip_tail7 FR ST (bv_unsigned sp) RTM1. }
ifz. stp. rewrite ?(unsigned_lit (SH ae8)), ?(unsigned_lit (SH ab8)) by lia. replace (SH ae8 + - SH ab8) with (SH ae8 - SH ab8) by lia.
step. step.
call_u miz_spec7.
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ZR. } { lia. } { clear - SHB AB1 AE1 N43; Z.div_mod_to_equations; lia. } { lia. } { rewrite ?KHI_eq. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rt_mem_cells_munch _ _ _ RTM MU ltac:(rt_wzones)) as RTM2 end.
step. ifz. rip_tail7 FR ST' (bv_unsigned sp) RTM2.
Qed.

Lemma u_nm65 : forall n, 1 <= n <= 64 -> bv_unsigned (wz (n + -65)) = 18446744073709551551 + n.
Proof. intros n Hn. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

Lemma rw_cells_apart : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW.
eapply (rw_cells_agree asegs (fun a => A <= a < A + Z.of_nat (cells_size cs))); [eapply agree_on_of_munch; [exact MU| exact WM|]| exact RC| intros a Ha; exact Ha].
intros x Hx _. clear MU. induction HW as [|[lo hi] W H HW IH]; cbn; [exact I|]. cbn in H. split; [lia| exact IH].
Qed.
Lemma rw_cells_below : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW. eapply rw_cells_apart; [exact RC| exact MU| exact WM|].
eapply Forall_impl; [| exact HW]. cbv beta. intros iv H. left. exact H.
Qed.

Lemma shadow_ok_zrd_head : forall m dst n, shadow_ok m dst n -> 0 < n -> zrd m (SH dst) (SH (dst + n - 1) - SH dst).
Proof.
intros m dst n SO N0 i Hi. rewrite !SH_eq in Hi.
destruct (SO i ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
assert (v = 0) as -> by (Z.div_mod_to_equations; lia).
match type of B with bytes_at _ _ ?a _ => replace (SH dst + i) with a; [exact B|] end.
rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma slow_flag_zero : forall r v, 0 <= v < 8 -> 0 <= r < 8 -> (v = 0 \/ r < v) ->
Z.land (bv_unsigned (v_sltu (wz 0) (wz v))) (bv_unsigned (wz (Z.lxor (bv_unsigned (v_slt (wz r) (wz v))) 1))) = 0.
Proof.
intros r v Hv Hr C. unfold v_sltu, c_ltu, bv_ltu, v_slt, c_lts, bv_lts.
rewrite !signed_small, !unsigned_lit by lia. change (bv_unsigned (wz 0)) with 0.
destruct (Z.ltb_spec0 0 v); destruct (Z.ltb_spec0 r v); cbn -[Z.land]; try reflexivity; try lia.
Qed.

Definition ash {BAND : Band} (m : mem) : Prop :=
zrd m 0x7fffa000 0x2610 /\ zrd m (SH band_lo) (KHI - SH band_lo) /\ zrd m 0x800c06b8 0x88.

Lemma ash_munch {BAND : Band} : forall m m' W, ash m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= 0x7fffa000 \/ (0x7fffc610 <= fst iv /\ snd iv <= 0x800c06b8) \/ (0x800c0740 <= fst iv /\ snd iv <= SH band_lo) \/ 0x10007fff8000 <= fst iv) W ->
ash m'.
Proof.
intros m m' W (Z1 & Z2 & Z3) MU WM HW.
assert (D : forall x, (0x7fffa000 <= x < 0x7fffc610 \/ SH band_lo <= x < 0x10007fff8000 \/ 0x800c06b8 <= x < 0x800c0740) -> outside W x).
{ intros x Hx. clear - HW Hx. induction HW as [|[lo hi] W' H1 HW IH]; cbn in *; [exact I|]. split; [unfold SH, A_SHADOW_OFS in *; lia| exact IH]. }
split; [| split]; (eapply zrd_munch; [eassumption| exact MU| exact WM| intros x Hx; apply D; unfold KHI in *; lia]).
Qed.

Definition szone {BAND : Band} (p n : Z) : Prop :=
(0x10000 <= p /\ p + n <= 0x23080) \/ (band_lo + 64 <= p /\ p + n + 8 <= 2^47) \/ (0x6435c0 <= p /\ p + n <= 0x643a00).

Definition rng_ok (m : mem) (p n : Z) : Prop :=
0 <= p /\ p + n + 8 <= 2^47
/\ (0 < n -> shadow_ok m p n)
/\ (64 < n -> (p + n + 8 <= 0x7fff8000 \/ KHI <= p) /\ n <= 2^43)
/\ (0 < n <= 64 -> (exists w : word, rw_cells asegs m (8 * (SH p / 8)) [C8 w])
/\ (exists w : word, rw_cells asegs m (8 * (SH (p + n - 1) / 8)) [C8 w])).

Lemma zrd_hjunk : forall m A n, zrd m A n -> 0x645000 <= A -> A + n <= 2^64 -> hjunk m A (A + n).
Proof.
intros m A n ZR HA HN. split; [lia|]. split; [lia|].
- intros a Ha. destruct (ZR (a - A) ltac:(lia)) as (B0 & B1 & B2). specialize (B2 0%nat ltac:(cbn; lia)). cbn in B2.
replace (A + (a - A) + 0) with a in B2 by lia. rewrite a_mrd_overlay in B2 by (rewrite wa_unsigned by lia; lia).
exists (b8 0). exact B2.
Qed.

Lemma zrd_C8 : forall m A n a, zrd m A n -> 0x645000 <= A -> A <= a -> a + 8 <= A + n -> exists w : word, rw_cells asegs m a [C8 w].
Proof.
intros m A n a ZR HA H1 H2. apply hjunk_C8.
assert (HN : A + n <= 2^64) by (destruct (ZR (n - 1) ltac:(lia)) as (_ & B & _); cbn in B; lia).
pose proof (zrd_hjunk _ _ _ ZR HA HN) as (K1 & K2 & K3).
split; [lia|]. split; [lia|]. intros x Hx. apply K3. lia.
Qed.

Lemma zrd_shadow_ok : forall m A n p k, zrd m A n -> 0 < k -> 0 <= p -> A <= SH p -> SH (p + k - 1) + 1 <= A + n -> shadow_ok m p k.
Proof.
intros m A n p k ZR K0 P0 H1 H2 j Hj Hjk. exists 0. split; [| left; reflexivity].
replace (SH (p / 8 * 8) + j) with (A + (SH (p / 8 * 8) + j - A)) by lia. apply ZR.
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Lemma rng_ok_of_ash {BAND : Band} : forall m p n, ash m -> szone p n -> 0 <= n -> rng_ok m p n.
Proof.
intros m p n (Z1 & Z2 & Z3) SZ N0.  unfold szone in SZ. unfold rng_ok.
destruct SZ as [(A1 & A2)|[(B1 & B2)|(C1 & C2)]].
- split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
+ intros K. eapply (zrd_shadow_ok _ _ _ _ _ Z1); [lia| lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia].
+ intros K. split; (eapply (zrd_C8 _ _ _ _ Z1); [lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia]).
- split; [lia|]. split; [lia|]. split; [| split; [intros; rewrite ?KHI_eq; lia|]].
+ intros K. eapply (zrd_shadow_ok _ _ _ _ _ Z2); [lia| lia| ..]; rewrite !SH_eq; unfold KHI; Z.div_mod_to_equations; lia.
+ intros K. split; (eapply (zrd_C8 _ _ _ _ Z2); rewrite !SH_eq; unfold KHI; Z.div_mod_to_equations; lia).
- split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
+ intros K. eapply (zrd_shadow_ok _ _ _ _ _ Z3); [lia| lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia].
+ intros K. split; (eapply (zrd_C8 _ _ _ _ Z3); [lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia]).
Qed.

Lemma rng_ok_munch : forall m m' p n W, rng_ok m p n -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => 8 * (SH (p + n - 1) / 8) + 8 <= fst iv \/ snd iv <= 8 * (SH p / 8)) W -> rng_ok m' p n.
Proof.
intros m m' p n W (P0 & P47 & SO & BIG & NB) MU WM HW.
assert (D : forall x, 8 * (SH p / 8) <= x < 8 * (SH (p + n - 1) / 8) + 8 -> outside W x).
{ intros x Hx. clear - HW Hx. induction HW as [|[lo hi] W' H1 HW IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
split; [lia|]. split; [lia|]. split; [| split; [exact BIG|]].
- intros K. eapply shadow_ok_munch; [apply SO; exact K| exact MU| exact WM| | exact K].
intros x Hx. apply D. rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
- intros K. destruct (NB K) as [[w1 W1] [w2 W2]]. split.
+ exists w1. eapply rw_cells_apart; [exact W1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H; cbn in *.
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
+ exists w2. eapply rw_cells_apart; [exact W2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H; cbn in *.
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Definition tryinit_entry : Z := 0x6aae0.

Lemma tryinit_spec7 {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (lo : Z),
ro_cells asegs m 0x0f07d8 [C1 (b8 1); C1 (b8 1)] -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' _ => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz tryinit_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros K MI ST CEIL LO.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold tryinit_entry.
carve_frame 16%nat ST.
istep. istep. istep.
stp. stp. step. stp. step. step. ifz.
step. step. release_frame FR ST (bv_unsigned sp).
step. step.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity.
Qed.

Definition asaninited_entry : Z := 0x69bd0.

Lemma asaninited_spec7 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
ro_cells asegs m 0x0f07d8 [C1 (b8 1); C1 (b8 1)] ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asaninited_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros K. unfold asaninited_entry.
step. stp. step. stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity| reflexivity].
Qed.

Lemma qslow_loop_a1 : forall (pc : Z), (pc = 0x5297c \/ pc = 0x523ec \/ pc = 0x4fe38 \/ pc = 0x52b5c) ->
forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz e) (wz e) (wz 0) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (pc + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz p) (wz e) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom asegs)).
Proof.
intros pc [-> |[-> |[-> | ->]]];
(induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ]).
Qed.

Definition ISH {BAND : Band} (m : mem) : Prop := ash m /\ rt_consts_at asegs m /\ shadow_base asegs m.

Lemma ISH_munch {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma ISH_munch_zone {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (0x0e7e00 <= fst iv /\ snd iv <= 0x0ea960) \/ (0x181726 <= fst iv /\ snd iv <= 0x1819a0) \/ (0x1819a1 <= fst iv /\ snd iv <= 0x642ea0) \/ (0x643128 <= fst iv /\ snd iv <= 0x7fffa000) \/ band_lo <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma szone_sub {BAND : Band} : forall p n p' n', szone p n -> p <= p' -> p' + n' <= p + n -> 0 <= n' -> szone p' n'.
Proof. intros p n p' n' SZ H1 H2 H3. unfold szone in *. lia. Qed.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg QUxU QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QUxU QNwL QYnC QSsj QmP7.Mq0 QpY2.Mq1.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma RChunks_open {BAND : Band} : forall a LB G RE X m p A n,
RChunks a LB G RE X m -> In (p, A, n) LB -> chunk_rep a G RE m p A n.
Proof. intros a LB G RE X m p A n [H _] Hin. exact (H p A n Hin). Qed.

Lemma RChunks_sub {BAND : Band} : forall a a' LB LB' G G' RE X m,
RChunks a LB G RE X m ->
(forall b, In b LB' -> In b LB) ->
(forall e, In e (as_reg a) -> In e (as_reg a')) ->
(forall p A n c i, In (p, A, n) LB' -> tag_at G c i = Some (TLive p) -> tag_at G' c i = Some (TLive p)) ->
RChunks a' LB' G' RE X m.
Proof.
intros a a' LB LB' G G' RE X m [H1 H2] SUB REG TAGS. split.
- intros p A n Hin. pose proof (H1 p A n (SUB _ Hin)) as CR. destruct p as [id n0|mb n0]; cbn [chunk_rep] in *.
+ destruct CR as (E & i & Ht & HA & CM). split; [exact E|]. exists i. split; [| split; [exact HA| exact CM]].
eapply TAGS; [exact Hin| exact Ht].
+ destruct CR as (E & Hr & HA & CM). split; [exact E|]. split; [apply REG; exact Hr|]. split; [exact HA| exact CM].
- intros p A n p' A' n' z Hin Hin' NE. apply H2; [apply SUB; exact Hin| apply SUB; exact Hin'| exact NE].
Qed.

Lemma RChunks_ext {BAND : Band} : forall a a' LB G G' RE X m,
RChunks a LB G RE X m -> (forall e, In e (as_reg a) -> In e (as_reg a')) -> same_tags is_live G G' -> RChunks a' LB G' RE X m.
Proof.
intros a a' LB G G' RE X m H REG ST. eapply RChunks_sub; [exact H| intros b Hb; exact Hb| exact REG|].
intros p A n c i _ Ht. apply (proj1 (ST c i (TLive p) eq_refl)). exact Ht.
Qed.

Lemma aptr_eqb_refl' : forall p, aptr_eqb p p = true.
Proof. intros [i n|a n]; cbn; rewrite ?N.eqb_refl, ?Z.eqb_refl; reflexivity. Qed.

Lemma aptr_eqb_true : forall p q, aptr_eqb p q = true -> p = q.
Proof.
intros [i1 n1|a1 n1] [i2 n2|a2 n2] E; cbn in E; try discriminate;
apply andb_prop in E as [E1 E2]; [apply N.eqb_eq in E1| apply Z.eqb_eq in E1]; apply Z.eqb_eq in E2; subst; reflexivity.
Qed.

Lemma In_alb_remove : forall p LB b, In b (alb_remove p LB) <-> In b LB /\ ablk_id b <> p.
Proof.
intros p LB b. unfold alb_remove. rewrite <- !list_elem_of_In, list_elem_of_filter, list_elem_of_In. split.
- intros [H1 H2]. split; [exact H2|]. intros E. rewrite E, aptr_eqb_refl' in H1. exact H1.
- intros [H1 H2]. split; [| exact H1]. destruct (aptr_eqb (ablk_id b) p) eqn:E; [| exact I].
exfalso. apply H2. apply aptr_eqb_true. exact E.
Qed.

Lemma RChunks_drop {BAND : Band} : forall a a' LB G G' RE X m p A n,
RChunks a LB G RE X m -> In (p, A, n) LB -> List.NoDup (map ablk_id LB) ->
(forall e, In e (as_reg a) -> In e (as_reg a')) ->
(forall c i q, q <> p -> tag_at G c i = Some (TLive q) -> tag_at G' c i = Some (TLive q)) ->
RChunks a' (alb_remove p LB) G' RE X m.
Proof.
intros a a' LB G G' RE X m p A n H Hin ND REG TAGS. eapply RChunks_sub; [exact H| | exact REG|].
- intros b Hb. exact (proj1 (proj1 (In_alb_remove _ _ _) Hb)).
- intros q Aq nq c i Hq Ht. apply In_alb_remove in Hq as [Hq NE]. cbn [ablk_id fst] in NE. exact (TAGS c i q NE Ht).
Qed.

Lemma drop_tags_retag : forall G p c0 i0 t c i q,
tag_at G c0 i0 = Some (TLive p) -> q <> p -> tag_at G c i = Some (TLive q) -> tag_at (set_tag c0 i0 t G) c i = Some (TLive q).
Proof.
intros G p c0 i0 t c i q Hp NE Hq. pose proof (tag_at_Some_lt _ _ _ _ Hp) as [I0 _].
destruct (Z.eq_dec c c0) as [->|NC]; [destruct (Z.eq_dec i i0) as [->|NI]|].
- rewrite Hp in Hq. inversion Hq. subst. congruence.
- rewrite tag_at_set_tag_ne by lia. exact Hq.
- rewrite tag_at_set_tag_ne by lia. exact Hq.
Qed.

Lemma RPrim_ext : forall a a' G G' RE X m,
RPrim a G RE X m -> (forall c, cls a' c = cls a c) -> as_cache_inited a' = as_cache_inited a ->
same_len G G' -> same_tags tag_prim G G' -> RPrim a' G' RE X m.
Proof.
intros a a' G G' RE X m (K & HJ & GNE & HC) EC EI SL ST. exists K. split; [exact HJ|]. split.
- intros c NE. apply GNE. intros E. apply NE. pose proof (SL c) as L. rewrite E in L. destruct (G' c); [reflexivity| cbn in L; lia].
- intros c Hc. specialize (HC c Hc). destruct HC as (CC & PU & REG).
assert (TP : forall i t, tag_prim t = true -> (tag_at G c i = Some t <-> tag_at G' c i = Some t)) by (intros i t Ht; exact (ST c i t Ht)).
split; [|split].
+ unfold cr_cells in *. rewrite EC, EI. exact CC.
+ unfold cr_pure in *. rewrite EC, EI.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
rewrite <- (count_tag_same (stag_eqb TFree) G G' c SL), <- (count_tag_same (stag_eqb TCached) G G' c SL).
2,3: intros c1 i1 t1 Ht1; apply ST; destruct t1; cbn in Ht1; try discriminate; reflexivity.
pose proof (SL c) as L. rewrite <- L.
assert (T5 : forall i, In i (pk_fl (K c)) -> tag_at G' c i = Some TFree).
{ intros i Hi. apply (proj1 (TP i TFree eq_refl)). apply P5. exact Hi. }
assert (T6 : forall i, In i (pk_ca (K c)) -> tag_at G' c i = Some TCached).
{ intros i Hi. apply (proj1 (TP i TCached eq_refl)). apply P6. exact Hi. }
repeat match goal with |- _ /\ _ => split end; try assumption; lia.
+ intros Hc1. specialize (REG Hc1). unfold cr_region in *. rewrite EC.
destruct REG as (FA & FJ & SLT & UT & SS & US & UJ & FS).
split; [exact FA|]. split; [exact FJ|]. split; [| split; [exact UT| split; [| split; [exact US| split; [exact UJ| exact FS]]]]].
* intros i t Ht Hp. apply (SLT i t); [apply (proj2 (TP i t Hp)); exact Ht| exact Hp].
* intros i t Ht Hp. apply (SS i t); [apply (proj2 (TP i t Hp)); exact Ht| exact Hp].
Qed.

Lemma RPrim_retag : forall a G RE X m c i t0 t,
RPrim a G RE X m -> tag_at G c i = Some t0 -> tag_prim t0 = false -> tag_prim t = false ->
RPrim a (set_tag c i t G) RE X m.
Proof.
intros a G RE X m c i t0 t RP Ht F0 F1. eapply RPrim_ext; [exact RP| intros; reflexivity| reflexivity| apply same_len_set_tag|].
eapply same_tags_set_tag; eassumption.
Qed.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUvT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QUvT QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QpY2.Mq8 QNQk.Mq2.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition unwind_impl_entry : Z := 0x6b878.
Definition unwind_stack : Z := 144.

Lemma sel_and : forall b t x, 0 <= b < t -> t < 2^64 -> 0 <= x < 2^64 ->
wz (Z.land (bv_unsigned (wz (0 + - bv_unsigned (v_sltu (wz b) (wz t))))) (bv_unsigned (wz x))) = wz x.
Proof.
intros b t x Hb Ht Hx. rewrite v_sltu_b2z. rewrite !(unsigned_lit b), !(unsigned_lit t), !(unsigned_lit x) by lia.
replace (b <? t) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. rewrite (unsigned_lit 1) by lia.
rewrite unsigned_lit_wrap. change ((0 + - (1)) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma and_all_ones : forall x, 0 <= x < 2^64 -> Z.land (bv_unsigned (wz (0 + -1))) x = x.
Proof.
intros x Hx. rewrite unsigned_lit_wrap. change ((0 + -1) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
apply Z.mod_small. lia.
Qed.

Lemma land7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma bytes_u64s : forall (k : nat) (bs : list byte), length bs = (8 * k)%nat -> exists ws : list word, length ws = k /\ u64s ws = bs.
Proof.
induction k as [|k IH]; intros bs LB.
- destruct bs; [| cbn in LB; lia]. exists []. split; reflexivity.
- destruct bs as [|y0 bs]; [cbn in LB; lia|]. destruct bs as [|y1 bs]; [cbn in LB; lia|]. destruct bs as [|y2 bs]; [cbn in LB; lia|].
destruct bs as [|y3 bs]; [cbn in LB; lia|]. destruct bs as [|y4 bs]; [cbn in LB; lia|]. destruct bs as [|y5 bs]; [cbn in LB; lia|].
destruct bs as [|y6 bs]; [cbn in LB; lia|]. destruct bs as [|y7 bs]; [cbn in LB; lia|].
destruct (IH bs ltac:(cbn [length] in LB; lia)) as (ws & LW & EW).
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7]) :: ws). split; [cbn [length]; lia|].
cbn [u64s]. rewrite le8_of_bytes by reflexivity. rewrite EW. reflexivity.
Qed.

Lemma cells_bytes_map_C8 : forall ws : list word, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_C8 : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma cells_wf_map_C8 : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws as [|w ws IH]; cbn; [exact I| split; [exact I| exact IH]]. Qed.
Lemma u64s_app : forall a b : list word, u64s (a ++ b) = u64s a ++ u64s b.
Proof. induction a as [|w a IH]; intros b; [reflexivity|]. cbn [app u64s]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma cells_u64arr : forall m A (ws : list word), rw_cells asegs m A (map C8 ws) -> u64arr asegs m A ws.
Proof.
intros m A ws [[_ BA] WR]. rewrite cells_bytes_map_C8 in BA. rewrite cells_size_map_C8 in WR. split; [exact BA|].
replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws)) by lia. exact WR.
Qed.
Lemma u64arr_cells : forall m A (ws : list word), u64arr asegs m A ws -> rw_cells asegs m A (map C8 ws).
Proof.
intros m A ws [BA WR]. split; [split; [apply cells_wf_map_C8| rewrite cells_bytes_map_C8; exact BA]|].
rewrite cells_size_map_C8. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact WR.
Qed.

Definition unw_obj (obj sz : Z) (q : list word) (rest : list byte) (bp : Z) : list cell :=
[C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ++ map C8 q ++ [CB 2000 rest; C8 (wz bp)].

Lemma unw_obj_open : forall m obj sz (q : list word) (rest : list byte) bp, length q = 5%nat ->
rw_cells asegs m obj (unw_obj obj sz q rest bp) ->
exists (qs : list word) (rest2 : list byte),
Z.of_nat (length qs) = 30
/\ rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m (obj + 16) qs
/\ rw_cells asegs m (obj + 256) [CB 1800 rest2; C8 (wz bp)].
Proof.
intros m obj sz q rest bp LQ H.
assert (LR : length rest = 2000%nat).
{ destruct H as [[WF _] _]. unfold unw_obj in WF. apply cells_wf_app in WF. destruct WF as [_ WF]. apply cells_wf_app in WF. destruct WF as [_ WF]. cbn in WF. tauto. }
destruct (bytes_u64s 25 (firstn 200 rest) ltac:(rewrite length_take; lia)) as (ws & LW & EW).
exists (q ++ ws), (skipn 200 rest).
assert (H2 : rw_cells asegs m obj ([C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ++ map C8 (q ++ ws) ++ [CB 1800 (skipn 200 rest); C8 (wz bp)])).
{ eapply rw_cells_recast'; [exact H| |].
- apply cells_wf_app. split; [cbn; tauto|]. apply cells_wf_app. split; [apply cells_wf_map_C8|]. cbn. rewrite length_skipn. lia.
- unfold unw_obj. rewrite !cells_bytes_app, !cells_bytes_map_C8, u64s_app, EW. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
rewrite <- (firstn_skipn 200 rest) at 3. rewrite <- !app_assoc. reflexivity. }
apply (proj1 (rw_cells_app asegs m obj _ _)) in H2. destruct H2 as [HD H2].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H2.
apply (proj1 (rw_cells_app asegs m (obj + 16) _ _)) in H2. destruct H2 as [HQ HR].
rewrite cells_size_map_C8, length_app, LQ, LW in HR. cbn [Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in HR.
replace (obj + 16 + 240) with (obj + 256) in HR by lia.
split; [rewrite length_app, LQ, LW; reflexivity|]. split; [exact HD|]. split; [apply cells_u64arr; exact HQ| exact HR].
Qed.

Lemma unw_obj_close : forall m obj sz (qs : list word) (rest2 : list byte) bp, Z.of_nat (length qs) = 30 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs ->
rw_cells asegs m (obj + 256) [CB 1800 rest2; C8 (wz bp)] ->
exists (q : list word) (rest' : list byte), length q = 5%nat /\ rw_cells asegs m obj (unw_obj obj sz q rest' bp).
Proof.
intros m obj sz qs rest2 bp LQ HD Q HR.
assert (LR : length rest2 = 1800%nat) by (destruct HR as [[WF _] _]; cbn in WF; tauto).
exists (firstn 5 qs), (u64s (skipn 5 qs) ++ rest2). split; [rewrite length_take; lia|].
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ++ map C8 qs ++ [CB 1800 rest2; C8 (wz bp)])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). split; [exact HD|].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
apply (proj2 (rw_cells_app asegs m (obj + 16) _ _)). split; [apply u64arr_cells; exact Q|].
rewrite cells_size_map_C8. replace (obj + 16 + Z.of_nat (8 * length qs)) with (obj + 256) by lia. exact HR. }
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. apply cells_wf_app. split; [cbn; tauto|]. apply cells_wf_app. split; [apply cells_wf_map_C8|]. cbn.
rewrite length_app, u64s_length, length_skipn. lia.
- unfold unw_obj. rewrite !cells_bytes_app, !cells_bytes_map_C8. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
rewrite <- (firstn_skipn 5 qs) at 3. rewrite u64s_app, <- !app_assoc. reflexivity.
Qed.

Lemma readable_le8 : forall (m : word -> option byte) a, 0 <= a -> a + 8 <= 2^64 ->
(forall x, a <= x < a + 8 -> exists b, mrd asegs m (wa x) = Some b) -> exists w : word, bytes_at asegs m a (le8 w).
Proof.
intros m a A0 A1 R.
destruct (R a ltac:(lia)) as (b0 & E0). destruct (R (a + 1) ltac:(lia)) as (b1 & E1). destruct (R (a + 2) ltac:(lia)) as (b2 & E2).
destruct (R (a + 3) ltac:(lia)) as (b3 & E3). destruct (R (a + 4) ltac:(lia)) as (b4 & E4). destruct (R (a + 5) ltac:(lia)) as (b5 & E5).
destruct (R (a + 6) ltac:(lia)) as (b6 & E6). destruct (R (a + 7) ltac:(lia)) as (b7 & E7).
exists (wz (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])). rewrite le8_of_bytes by reflexivity.
split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
destruct i as [|i]; [rewrite Z.add_0_r; exact E0|]. destruct i as [|i]; [exact E1|]. destruct i as [|i]; [exact E2|]. destruct i as [|i]; [exact E3|].
destruct i as [|i]; [exact E4|]. destruct i as [|i]; [exact E5|]. destruct i as [|i]; [exact E6|]. destruct i as [|i]; [exact E7| lia].
Qed.

Lemma readable_munch_above : forall W (m m' : word -> option byte) lo hi,
munch W m m' -> (forall x, lo <= x -> outside W x) -> 0 <= lo -> hi <= 2^64 ->
(forall x, lo <= x < hi -> exists b, mrd asegs m (wa x) = Some b) ->
forall x, lo <= x < hi -> exists b, mrd asegs m' (wa x) = Some b.
Proof.
intros W m m' lo hi MU OUT L0 H1 R x Hx. destruct (R x Hx) as (b & E). exists b. unfold mrd in *. rewrite (MU (wa x)); [exact E|].
rewrite wa_unsigned by lia. apply OUT. lia.
Qed.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma take_upd_snoc : forall {A} (l : list A) n x, (n < length l)%nat ->
take (S n) (upd l n x) = take n l ++ [x].
Proof.
intros A l n x Hn. rewrite upd_firstn_skipn by exact Hn.
rewrite take_app_ge by (rewrite length_take; lia). rewrite length_take, Nat.min_l by lia.
replace (S n - n)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma read_le8 : forall m a (w : word) a', bytes_at asegs m a (le8 w) -> a' = wa a -> ov_read_bytes asegs m a' 8 = Some (le8 w).
Proof.
intros m a w a' B ->. pose proof (bytes_at_read asegs m a (le8 w) 0 8 B ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as R.
rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all2 in R by (rewrite length_le8; lia). exact R.
Qed.

Definition unw_exit (ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(obj pcv : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a5 a6 a7 : word) (m' : word -> option byte) (qs' : list word) (sz' : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) a2 (wz 4096) (wz (obj + 16)) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x84540) fc None m' (seg_rom asegs)
/\ munch [(obj + 8, obj + 12); (obj + 16, obj + 256)] m m' /\ wmono asegs m m'
/\ (mem_inv asegs m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C4 (wz sz'); C4 (wz 0)]
/\ u64arr asegs m' (obj + 16) qs' /\ Z.of_nat (length qs') = 30 /\ 1 <= sz' <= 30).

Definition unw_next (ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(obj pcv v : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a6 a7 : word) (m' : word -> option byte) (qs' : list word) (sz' v' : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v') (wz 4096) (wz (obj + 16)) (wz sz') a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x84504) fc None m' (seg_rom asegs)
/\ munch [(obj + 8, obj + 12); (obj + 16, obj + 256)] m m' /\ wmono asegs m m'
/\ (mem_inv asegs m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C4 (wz sz'); C4 (wz 0)]
/\ u64arr asegs m' (obj + 16) qs' /\ Z.of_nat (length qs') = 30 /\ 1 <= sz' <= 30
/\ v < v' /\ unw_valid RE v').

Lemma unw_tail : forall (v sz : Z) (qs : list word) m
(ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (obj pcv : Z) (W : list (Z * Z)) (m0 : word -> option byte),
munch W m0 m -> wmono asegs m0 m -> W = [(obj + 8, obj + 12); (obj + 16, obj + 256)] ->
mem_inv asegs m ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs -> Z.of_nat (length qs) = 30 -> 1 <= sz <= 30 ->
0 <= v -> ae_stack_top RE <= 2^47 + 32768 -> unw_valid RE v ->
(exists fp2 : word, bytes_at asegs m (v - 16) (le8 fp2)) ->
evt asegs (fun ms' => unw_exit ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv m0 ms'
\/ unw_next ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv v m0 ms')
(MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v) (wz 4096) (wz (obj + 16)) (wz sz) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84528) fc None m (seg_rom asegs)).
Proof.
intros until m0; intros MU WM -> MI HD Q LQ SZR V0 TOPB VV (fp2 & FP2).
destruct VV as (VV1 & VV2 & VV3). unfold ae_stack_bottom in VV1.
pose proof (bv_unsigned_in_range 64 fp2) as FR2. change (bv_modulus 64) with (2^64) in FR2.
pose proof (read_le8 m (v - 16) fp2 (wz (v + -16)) FP2 ltac:(unfold wa; f_equal; lia)) as RD2.
istep. istep. if_cases E3; zify_cond E3.
{ apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
istep. if_cases E4; zify_cond E4.
{ apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
do 3 istep. if_cases E5; zify_cond E5.
2: { apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
apply evt_done. right. unfold unw_next. rewrite <- (Z_to_bv_lit_self fp2).
do 3 eexists. exists qs, sz, (bv_unsigned fp2). split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ|]. split; [exact SZR|].
split; [lia|]. unfold unw_valid, ae_stack_bottom. rewrite <- (land7 (bv_unsigned fp2)) by lia. lia.
Qed.

Lemma unw_body : forall (v sz : Z) (qs : list word) m
(ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (obj pcv : Z),
mem_inv asegs m ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs -> Z.of_nat (length qs) = 30 -> 1 <= sz <= 30 ->
0 <= pcv < 2^64 -> 0 <= obj -> obj + 2064 <= v -> ae_stack_top RE <= 2^47 + 32768 ->
unw_valid RE v ->
(forall x, v - 16 <= x < ae_stack_top RE -> exists b, mrd asegs m (wa x) = Some b) ->
evt asegs (fun ms' => unw_exit ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv m ms'
\/ unw_next ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv v m ms')
(MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v) (wz 4096) (wz (obj + 16)) (wz sz) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84504) fc None m (seg_rom asegs)).
Proof.
intros until pcv; intros MI HD Q LQ SZR PB OLO OV TOPB VV URD.
pose proof VV as (VV1 & VV2 & VV3). unfold ae_stack_bottom in VV1.
destruct (readable_le8 m (v - 8) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply URD; lia)) as (ra2 & RA2).
destruct (readable_le8 m (v - 16) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply URD; lia)) as (fp2 & FP2).
pose proof (bv_unsigned_in_range 64 ra2) as RR. change (bv_modulus 64) with (2^64) in RR.
pose proof (munch_refl [(obj + 8, obj + 12); (obj + 16, obj + 256)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (read_le8 m (v - 8) ra2 (wz (v + -8)) RA2 ltac:(unfold wa; f_equal; lia)) as RD1.
istep. if_cases E0; zify_cond E0.
{
apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
istep. istep. if_cases E1; zify_cond E1.
{
apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
istep. if_cases E2.
{
eapply (unw_tail v sz qs m); [exact MU| exact WM| reflexivity| exact MI| exact HD| exact Q| exact LQ| exact SZR| lia| exact TOPB| exact VV| exists fp2; exact FP2]. }

assert (SZ30 : sz < 30) by (rewrite ?(unsigned_lit sz) in E0 by lia; lia).
istep. rewrite (unsigned_lit sz), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mul_comm sz 8).
do 3 istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_store_ok asegs mc (obj + 16) qs sz (wa (obj + 16 + 8 * sz)) Q ltac:(lia) eq_refl) as SOK end.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc (obj + 16) qs sz ra2 Q ltac:(lia)) as Q1 end.
clear Q. store_done.
assert (LQ1 : Z.of_nat (length (upd qs (Z.to_nat sz) ra2)) = 30) by (rewrite upd_length; exact LQ).
eapply (unw_tail v (sz + 1) (upd qs (Z.to_nat sz) ra2)); [exact MU| exact WM| reflexivity| assumption| exact HD| exact Q1| exact LQ1| lia| lia| exact TOPB| exact VV| exists fp2; exact FP2].
Qed.

Lemma unw_loop : forall (k : nat) (v sz : Z) (qs : list word) m
(ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (obj pcv : Z),
mem_inv asegs m ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs -> Z.of_nat (length qs) = 30 -> 1 <= sz <= 30 ->
0 <= pcv < 2^64 -> 0 <= obj -> obj + 2064 <= v -> ae_stack_top RE <= 2^47 + 32768 ->
unw_valid RE v -> ae_stack_top RE - v <= Z.of_nat k ->
(forall x, v - 16 <= x < ae_stack_top RE -> exists b, mrd asegs m (wa x) = Some b) ->
evt asegs (unw_exit ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv m)
(MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v) (wz 4096) (wz (obj + 16)) (wz sz) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84504) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until pcv; intros MI HD Q LQ SZR PB OLO OV TOPB VV DIST URD.
{ exfalso. destruct VV as (_ & VV2 & _). lia. }
eapply evt_cut; [eapply (unw_body v sz qs m); eassumption|].
cbv beta. intros ms' [EX|NX]; [apply evt_done; exact EX|].
destruct NX as (a6' & a7' & m' & qs' & sz' & v' & -> & MU & WM & MI' & HD' & Q' & LQ' & SZR' & LT & VAL).
assert (VB : ae_stack_top RE - 0x800000 < v /\ v < ae_stack_top RE - 16) by (destruct VV as (V1 & V2 & _); unfold ae_stack_bottom in V1; lia).
eapply evt_mono.
{ eapply (IH v' sz' qs' m'); try eassumption; try lia.
eapply (readable_munch_above _ m m' (v' - 16) (ae_stack_top RE)); [exact MU| intros x Hx; cbn [outside]; lia| lia| lia|].
intros x Hx. apply URD. lia. }
cbv beta. intros ms'' (a2'' & a5'' & a6'' & a7'' & m'' & qs'' & sz'' & E & MU2 & WM2 & REST).
exists a2'', a5'', a6'', a7'', m'', qs'', sz''. split; [exact E|].
split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]| exact REST].
Qed.

Definition unw_fin (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(obj pcv : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (qs : list word) (sz : Z),
ms' = MS (mkR (wz 0x6b994) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84540) fc None m' (seg_rom asegs)
/\ munch [(obj + 8, obj + 12); (obj + 16, obj + 256)] m m' /\ wmono asegs m m'
/\ (mem_inv asegs m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m' (obj + 16) qs /\ Z.of_nat (length qs) = 30 /\ 1 <= sz <= 30).

Lemma unwind_impl_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (obj pcv bp : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - unwind_stack ->
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest bp) ->
rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] ->
unw_readable asegs RE m (bp - 16) ->
0 <= pcv < 2^64 -> bv_unsigned sp <= obj -> obj + 2080 <= bp -> bp < 2^64 ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(obj + 8, obj + 12); (obj + 16, obj + 256); (obj + 2056, obj + 2064); (bv_unsigned sp - unwind_stack, bv_unsigned sp); (rl_T X + 3168, rl_T X + 3169)] lo m
(fun _ m' => exists (sz : Z) (q : list word) (rest' : list byte),
rw_cells asegs m' obj (unw_obj obj sz q rest' bp) /\ length q = 5%nat
/\ rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)]
/\ 1 <= sz <= 30 /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz obj) (wz pcv) (wz bp) (wz 0) (wz 1) (wz 30) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz unwind_impl_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros RT RL MI ST CEIL LO OBJ TU URD0 PB OLO OHI BHI.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold unwind_impl_entry, unwind_stack in *.
obj_facts RL.
pose proof (munch_refl [(obj + 8, obj + 12); (obj + 16, obj + 256); (obj + 2056, obj + 2064); (bv_unsigned sp - 144, bv_unsigned sp); (rl_T X + 3168, rl_T X + 3169)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold unw_obj in OBJ. cbn [map app] in OBJ.
carve_frame 80%nat ST.
step_until 0x69bd0.
call0 (asan_inited_spec RE X). { rt_solve RT RL. } { assumption. }
subst_words. step_until 0. if_false_u.
istep. call_u (get_current_thread_spec RE X).
{ rt_solve RT RL. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
istep. if_false_u.

step_until 0. if_false.

assert (TOPF : 0x7fff7fffff60 <= ae_stack_top RE < 2^47 + 0x8000 /\ ae_stack_top RE mod 4096 = 0).
{ destruct RL as ((R1 & R2) & R3 & R4 & R5 & _). lia. }
unfold ae_stack_bottom in *.
rt_T_now RT RL TT. istep. step_until 0. if_true. step_until 0x6b8ec.
rewrite (sel_and (ae_stack_top RE - 8388608) (ae_stack_top RE) (ae_stack_top RE)) by lia.
istep. step_until 0. if_true. step_until 0x6b8f8.
rewrite (sel_and (ae_stack_top RE - 8388608) (ae_stack_top RE) (ae_stack_top RE - 8388608)) by lia.
clear TT. step_until 0. if_false. step_until 0x84aa0.

carve_frame 64%nat STK.
step_until 0x84ad8. rewrite (unsigned_lit bp), land_ones64 by lia.
step_until 0. if_false. step_until 0. if_true. step_until 0. if_true. step_until 0x84444.
release_frame FR0 STK (bv_unsigned sp - 80).

carve_frame 64%nat STK. replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in FR0, STK by lia.
rt_now RT RL 18%nat K18. rt_now RT RL 8%nat K8.
step_until 0. if_false. step_until 0. clear K18 K8. if_false. step_until 0.
rewrite (unsigned_lit (ae_stack_top RE)), Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
assert (TD : 1 <= ae_stack_top RE / 4096 < 2^40) by (Z.div_mod_to_equations; lia).
if_true_u. step_until 0. if_false_u.

match goal with H : rw_cells asegs _ obj _ |- _ => rename H into OBJ1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
change (rw_cells asegs mc obj (unw_obj obj 1 [wz pcv; q1; q2; q3; q4] rest bp)) in OBJ1;
destruct (unw_obj_open mc obj 1 [wz pcv; q1; q2; q3; q4] rest bp eq_refl OBJ1) as (qs0 & rest2 & LQ0 & HD & Q & OBJR); clear OBJ1;
pose proof (munch_refl [(obj + 8, obj + 12); (obj + 16, obj + 256)] mc) as MU1; pose proof (wmono_refl asegs mc) as WM1;
assert (URD : forall x, bp - 16 <= x < ae_stack_top RE -> exists b, mrd asegs mc (wa x) = Some b)
by (eapply (readable_munch_above _ m mc (bp - 16) (ae_stack_top RE)); [exact MU| intros y Hy; cbn [outside]; lia| lia| lia| intros y Hy; apply URD0; lia])
end.
eapply evt_cut with (P := unw_fin (wz (bv_unsigned sp + -144)) gp (wz A_TP) _ _ _ _ _ _ _ s9 s10 s11 F fc obj pcv _).
{
istep. if_cases V1; zify_cond V1.
{ apply evt_done. unfold unw_fin. do 18 eexists. exists qs0, 1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ0| lia]. }
step_until 0. if_cases V2; zify_cond V2.
{ apply evt_done. unfold unw_fin. do 18 eexists. exists qs0, 1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ0| lia]. }
step_until 0. if_cases V3; zify_cond V3.
{ apply evt_done. unfold unw_fin. do 18 eexists. exists qs0, 1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ0| lia]. }
step_until 0x84504.
eapply evt_mono.
{ eapply (unw_loop (Z.to_nat (ae_stack_top RE - bp)) bp 1 qs0); [assumption| exact HD| exact Q| exact LQ0| lia| exact PB| lia| lia| lia| | lia| exact URD].
unfold unw_valid, ae_stack_bottom. rewrite <- (land7 bp) by lia. lia. }
cbv beta. intros ms' (a2' & a5' & a6' & a7' & m' & qs' & sz' & -> & MU2 & WM2 & MI' & HD' & Q' & LQ' & SZR').
unfold unw_fin. do 18 eexists. exists qs', sz'. split; [reflexivity|].
split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|]. split; [exact HD'|]. split; [exact Q'|]. split; [exact LQ'| exact SZR']. }

clear HD Q MU1 WM1 URD.
lazymatch goal with |- forall ms', unw_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc ms' -> _ => post_call_u asegs mc end.
match goal with H : rw_cells asegs _ obj _ |- _ => rename H into HD end.
match goal with H : u64arr asegs _ (obj + 16) ?q, H1 : Z.of_nat (length ?q) = 30, H2 : 1 <= ?z, H3 : ?z <= 30 |- _ =>
rename H into Q; rename H1 into LQ; rename q into qs; rename z into sz; assert (SZR : 1 <= sz <= 30) by (split; [exact H2| exact H3]) end.

step_until 0x6b994. release_frame FR0 STK (bv_unsigned sp + -80).
step_until 0. release_frame FR STK (bv_unsigned sp).
match goal with H : rw_cells asegs _ (obj + 256) _ |- _ => rename H into OBJR2 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
destruct (unw_obj_close mc obj sz qs rest2 bp LQ ltac:(assumption) ltac:(assumption) OBJR2) as (q5 & rest' & LQ5 & OBJF) end.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].
exists sz, q5, rest'.
split; [exact OBJF|]. split; [exact LQ5|]. split; [assumption|]. split; [exact SZR|].
rt_solve RT RL.
Qed.
End Walk.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QTVW Q61C QWRO Qu4g QFQR QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import Qc27 Q13u QHig.
Import Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO Qu4g QFQR QmP7 QKBN QmP7.Mq1 QpY2.Mqb.
Import QlES. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma RChunks_open {BAND : Band} : forall a LB G RE X m p A n,
RChunks a LB G RE X m -> In (p, A, n) LB -> chunk_rep a G RE m p A n.
Proof. intros a LB G RE X m p A n [H _] Hin. exact (H p A n Hin). Qed.

Lemma RChunks_sub {BAND : Band} : forall a a' LB LB' G G' RE X m,
RChunks a LB G RE X m ->
(forall b, In b LB' -> In b LB) ->
(forall e, In e (as_reg a) -> In e (as_reg a')) ->
(forall p A n c i, In (p, A, n) LB' -> tag_at G c i = Some (TLive p) -> tag_at G' c i = Some (TLive p)) ->
RChunks a' LB' G' RE X m.
Proof.
intros a a' LB LB' G G' RE X m [H1 H2] SUB REG TAGS. split.
- intros p A n Hin. pose proof (H1 p A n (SUB _ Hin)) as CR. destruct p as [id n0|mb n0]; cbn [chunk_rep] in *.
+ destruct CR as (E & i & Ht & HA & CM). split; [exact E|]. exists i. split; [| split; [exact HA| exact CM]].
eapply TAGS; [exact Hin| exact Ht].
+ destruct CR as (E & Hr & HA & CM). split; [exact E|]. split; [apply REG; exact Hr|]. split; [exact HA| exact CM].
- intros p A n p' A' n' z Hin Hin' NE. apply H2; [apply SUB; exact Hin| apply SUB; exact Hin'| exact NE].
Qed.

Lemma RChunks_ext {BAND : Band} : forall a a' LB G G' RE X m,
RChunks a LB G RE X m -> (forall e, In e (as_reg a) -> In e (as_reg a')) -> same_tags is_live G G' -> RChunks a' LB G' RE X m.
Proof.
intros a a' LB G G' RE X m H REG ST. eapply RChunks_sub; [exact H| intros b Hb; exact Hb| exact REG|].
intros p A n c i _ Ht. apply (proj1 (ST c i (TLive p) eq_refl)). exact Ht.
Qed.

Lemma aptr_eqb_refl' : forall p, aptr_eqb p p = true.
Proof. intros [i n|a n]; cbn; rewrite ?N.eqb_refl, ?Z.eqb_refl; reflexivity. Qed.

Lemma aptr_eqb_true : forall p q, aptr_eqb p q = true -> p = q.
Proof.
intros [i1 n1|a1 n1] [i2 n2|a2 n2] E; cbn in E; try discriminate;
apply andb_prop in E as [E1 E2]; [apply N.eqb_eq in E1| apply Z.eqb_eq in E1]; apply Z.eqb_eq in E2; subst; reflexivity.
Qed.

Lemma In_alb_remove : forall p LB b, In b (alb_remove p LB) <-> In b LB /\ ablk_id b <> p.
Proof.
intros p LB b. unfold alb_remove. rewrite <- !list_elem_of_In, list_elem_of_filter, list_elem_of_In. split.
- intros [H1 H2]. split; [exact H2|]. intros E. rewrite E, aptr_eqb_refl' in H1. exact H1.
- intros [H1 H2]. split; [| exact H1]. destruct (aptr_eqb (ablk_id b) p) eqn:E; [| exact I].
exfalso. apply H2. apply aptr_eqb_true. exact E.
Qed.

Lemma RChunks_drop {BAND : Band} : forall a a' LB G G' RE X m p A n,
RChunks a LB G RE X m -> In (p, A, n) LB -> List.NoDup (map ablk_id LB) ->
(forall e, In e (as_reg a) -> In e (as_reg a')) ->
(forall c i q, q <> p -> tag_at G c i = Some (TLive q) -> tag_at G' c i = Some (TLive q)) ->
RChunks a' (alb_remove p LB) G' RE X m.
Proof.
intros a a' LB G G' RE X m p A n H Hin ND REG TAGS. eapply RChunks_sub; [exact H| | exact REG|].
- intros b Hb. exact (proj1 (proj1 (In_alb_remove _ _ _) Hb)).
- intros q Aq nq c i Hq Ht. apply In_alb_remove in Hq as [Hq NE]. cbn [ablk_id fst] in NE. exact (TAGS c i q NE Ht).
Qed.

Lemma drop_tags_retag : forall G p c0 i0 t c i q,
tag_at G c0 i0 = Some (TLive p) -> q <> p -> tag_at G c i = Some (TLive q) -> tag_at (set_tag c0 i0 t G) c i = Some (TLive q).
Proof.
intros G p c0 i0 t c i q Hp NE Hq. pose proof (tag_at_Some_lt _ _ _ _ Hp) as [I0 _].
destruct (Z.eq_dec c c0) as [->|NC]; [destruct (Z.eq_dec i i0) as [->|NI]|].
- rewrite Hp in Hq. inversion Hq. subst. congruence.
- rewrite tag_at_set_tag_ne by lia. exact Hq.
- rewrite tag_at_set_tag_ne by lia. exact Hq.
Qed.

Lemma RPrim_ext : forall a a' G G' RE X m,
RPrim a G RE X m -> (forall c, cls a' c = cls a c) -> as_cache_inited a' = as_cache_inited a ->
same_len G G' -> same_tags tag_prim G G' -> RPrim a' G' RE X m.
Proof.
intros a a' G G' RE X m (K & HJ & GNE & HC) EC EI SL ST. exists K. split; [exact HJ|]. split.
- intros c NE. apply GNE. intros E. apply NE. pose proof (SL c) as L. rewrite E in L. destruct (G' c); [reflexivity| cbn in L; lia].
- intros c Hc. specialize (HC c Hc). destruct HC as (CC & PU & REG).
assert (TP : forall i t, tag_prim t = true -> (tag_at G c i = Some t <-> tag_at G' c i = Some t)) by (intros i t Ht; exact (ST c i t Ht)).
split; [|split].
+ unfold cr_cells in *. rewrite EC, EI. exact CC.
+ unfold cr_pure in *. rewrite EC, EI.
destruct PU as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & G1 & G2 & G3 & G4 & G5).
rewrite <- (count_tag_same (stag_eqb TFree) G G' c SL), <- (count_tag_same (stag_eqb TCached) G G' c SL).
2,3: intros c1 i1 t1 Ht1; apply ST; destruct t1; cbn in Ht1; try discriminate; reflexivity.
pose proof (SL c) as L. rewrite <- L.
assert (T5 : forall i, In i (pk_fl (K c)) -> tag_at G' c i = Some TFree).
{ intros i Hi. apply (proj1 (TP i TFree eq_refl)). apply P5. exact Hi. }
assert (T6 : forall i, In i (pk_ca (K c)) -> tag_at G' c i = Some TCached).
{ intros i Hi. apply (proj1 (TP i TCached eq_refl)). apply P6. exact Hi. }
repeat match goal with |- _ /\ _ => split end; try assumption; lia.
+ intros Hc1. specialize (REG Hc1). unfold cr_region in *. rewrite EC.
destruct REG as (FA & FJ & SLT & UT & SS & US & UJ & FS).
split; [exact FA|]. split; [exact FJ|]. split; [| split; [exact UT| split; [| split; [exact US| split; [exact UJ| exact FS]]]]].
* intros i t Ht Hp. apply (SLT i t); [apply (proj2 (TP i t Hp)); exact Ht| exact Hp].
* intros i t Ht Hp. apply (SS i t); [apply (proj2 (TP i t Hp)); exact Ht| exact Hp].
Qed.

Lemma RPrim_retag : forall a G RE X m c i t0 t,
RPrim a G RE X m -> tag_at G c i = Some t0 -> tag_prim t0 = false -> tag_prim t = false ->
RPrim a (set_tag c i t G) RE X m.
Proof.
intros a G RE X m c i t0 t RP Ht F0 F1. eapply RPrim_ext; [exact RP| intros; reflexivity| reflexivity| apply same_len_set_tag|].
eapply same_tags_set_tag; eassumption.
Qed.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1 QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QUvT.Mq0 QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QpY2.Mqi QNQk.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition unwind_impl_entry : Z := 0x6bc50.
Definition unwind_stack : Z := 144.

Lemma sel_and : forall b t x, 0 <= b < t -> t < 2^64 -> 0 <= x < 2^64 ->
wz (Z.land (bv_unsigned (wz (0 + - bv_unsigned (v_sltu (wz b) (wz t))))) (bv_unsigned (wz x))) = wz x.
Proof.
intros b t x Hb Ht Hx. rewrite v_sltu_b2z. rewrite !(unsigned_lit b), !(unsigned_lit t), !(unsigned_lit x) by lia.
replace (b <? t) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. rewrite (unsigned_lit 1) by lia.
rewrite unsigned_lit_wrap. change ((0 + - (1)) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma and_all_ones : forall x, 0 <= x < 2^64 -> Z.land (bv_unsigned (wz (0 + -1))) x = x.
Proof.
intros x Hx. rewrite unsigned_lit_wrap. change ((0 + -1) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
apply Z.mod_small. lia.
Qed.

Lemma land7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma bytes_u64s : forall (k : nat) (bs : list byte), length bs = (8 * k)%nat -> exists ws : list word, length ws = k /\ u64s ws = bs.
Proof.
induction k as [|k IH]; intros bs LB.
- destruct bs; [| cbn in LB; lia]. exists []. split; reflexivity.
- destruct bs as [|y0 bs]; [cbn in LB; lia|]. destruct bs as [|y1 bs]; [cbn in LB; lia|]. destruct bs as [|y2 bs]; [cbn in LB; lia|].
destruct bs as [|y3 bs]; [cbn in LB; lia|]. destruct bs as [|y4 bs]; [cbn in LB; lia|]. destruct bs as [|y5 bs]; [cbn in LB; lia|].
destruct bs as [|y6 bs]; [cbn in LB; lia|]. destruct bs as [|y7 bs]; [cbn in LB; lia|].
destruct (IH bs ltac:(cbn [length] in LB; lia)) as (ws & LW & EW).
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7]) :: ws). split; [cbn [length]; lia|].
cbn [u64s]. rewrite le8_of_bytes by reflexivity. rewrite EW. reflexivity.
Qed.

Lemma cells_bytes_map_C8 : forall ws : list word, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u64s]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_C8 : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma cells_wf_map_C8 : forall ws : list word, cells_wf (map C8 ws).
Proof. induction ws as [|w ws IH]; cbn; [exact I| split; [exact I| exact IH]]. Qed.
Lemma u64s_app : forall a b : list word, u64s (a ++ b) = u64s a ++ u64s b.
Proof. induction a as [|w a IH]; intros b; [reflexivity|]. cbn [app u64s]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma cells_u64arr : forall m A (ws : list word), rw_cells asegs m A (map C8 ws) -> u64arr asegs m A ws.
Proof.
intros m A ws [[_ BA] WR]. rewrite cells_bytes_map_C8 in BA. rewrite cells_size_map_C8 in WR. split; [exact BA|].
replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws)) by lia. exact WR.
Qed.
Lemma u64arr_cells : forall m A (ws : list word), u64arr asegs m A ws -> rw_cells asegs m A (map C8 ws).
Proof.
intros m A ws [BA WR]. split; [split; [apply cells_wf_map_C8| rewrite cells_bytes_map_C8; exact BA]|].
rewrite cells_size_map_C8. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact WR.
Qed.

Definition unw_obj (obj sz : Z) (q : list word) (rest : list byte) (bp : Z) : list cell :=
[C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ++ map C8 q ++ [CB 2000 rest; C8 (wz bp)].

Lemma unw_obj_open : forall m obj sz (q : list word) (rest : list byte) bp, length q = 5%nat ->
rw_cells asegs m obj (unw_obj obj sz q rest bp) ->
exists (qs : list word) (rest2 : list byte),
Z.of_nat (length qs) = 30
/\ rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m (obj + 16) qs
/\ rw_cells asegs m (obj + 256) [CB 1800 rest2; C8 (wz bp)].
Proof.
intros m obj sz q rest bp LQ H.
assert (LR : length rest = 2000%nat).
{ destruct H as [[WF _] _]. unfold unw_obj in WF. apply cells_wf_app in WF. destruct WF as [_ WF]. apply cells_wf_app in WF. destruct WF as [_ WF]. cbn in WF. tauto. }
destruct (bytes_u64s 25 (firstn 200 rest) ltac:(rewrite length_take; lia)) as (ws & LW & EW).
exists (q ++ ws), (skipn 200 rest).
assert (H2 : rw_cells asegs m obj ([C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ++ map C8 (q ++ ws) ++ [CB 1800 (skipn 200 rest); C8 (wz bp)])).
{ eapply rw_cells_recast'; [exact H| |].
- apply cells_wf_app. split; [cbn; tauto|]. apply cells_wf_app. split; [apply cells_wf_map_C8|]. cbn. rewrite length_skipn. lia.
- unfold unw_obj. rewrite !cells_bytes_app, !cells_bytes_map_C8, u64s_app, EW. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
rewrite <- (firstn_skipn 200 rest) at 3. rewrite <- !app_assoc. reflexivity. }
apply (proj1 (rw_cells_app asegs m obj _ _)) in H2. destruct H2 as [HD H2].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H2.
apply (proj1 (rw_cells_app asegs m (obj + 16) _ _)) in H2. destruct H2 as [HQ HR].
rewrite cells_size_map_C8, length_app, LQ, LW in HR. cbn [Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ] in HR.
replace (obj + 16 + 240) with (obj + 256) in HR by lia.
split; [rewrite length_app, LQ, LW; reflexivity|]. split; [exact HD|]. split; [apply cells_u64arr; exact HQ| exact HR].
Qed.

Lemma unw_obj_close : forall m obj sz (qs : list word) (rest2 : list byte) bp, Z.of_nat (length qs) = 30 ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs ->
rw_cells asegs m (obj + 256) [CB 1800 rest2; C8 (wz bp)] ->
exists (q : list word) (rest' : list byte), length q = 5%nat /\ rw_cells asegs m obj (unw_obj obj sz q rest' bp).
Proof.
intros m obj sz qs rest2 bp LQ HD Q HR.
assert (LR : length rest2 = 1800%nat) by (destruct HR as [[WF _] _]; cbn in WF; tauto).
exists (firstn 5 qs), (u64s (skipn 5 qs) ++ rest2). split; [rewrite length_take; lia|].
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ++ map C8 qs ++ [CB 1800 rest2; C8 (wz bp)])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). split; [exact HD|].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
apply (proj2 (rw_cells_app asegs m (obj + 16) _ _)). split; [apply u64arr_cells; exact Q|].
rewrite cells_size_map_C8. replace (obj + 16 + Z.of_nat (8 * length qs)) with (obj + 256) by lia. exact HR. }
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. apply cells_wf_app. split; [cbn; tauto|]. apply cells_wf_app. split; [apply cells_wf_map_C8|]. cbn.
rewrite length_app, u64s_length, length_skipn. lia.
- unfold unw_obj. rewrite !cells_bytes_app, !cells_bytes_map_C8. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
rewrite <- (firstn_skipn 5 qs) at 3. rewrite u64s_app, <- !app_assoc. reflexivity.
Qed.

Lemma readable_le8 : forall (m : word -> option byte) a, 0 <= a -> a + 8 <= 2^64 ->
(forall x, a <= x < a + 8 -> exists b, mrd asegs m (wa x) = Some b) -> exists w : word, bytes_at asegs m a (le8 w).
Proof.
intros m a A0 A1 R.
destruct (R a ltac:(lia)) as (b0 & E0). destruct (R (a + 1) ltac:(lia)) as (b1 & E1). destruct (R (a + 2) ltac:(lia)) as (b2 & E2).
destruct (R (a + 3) ltac:(lia)) as (b3 & E3). destruct (R (a + 4) ltac:(lia)) as (b4 & E4). destruct (R (a + 5) ltac:(lia)) as (b5 & E5).
destruct (R (a + 6) ltac:(lia)) as (b6 & E6). destruct (R (a + 7) ltac:(lia)) as (b7 & E7).
exists (wz (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])). rewrite le8_of_bytes by reflexivity.
split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
destruct i as [|i]; [rewrite Z.add_0_r; exact E0|]. destruct i as [|i]; [exact E1|]. destruct i as [|i]; [exact E2|]. destruct i as [|i]; [exact E3|].
destruct i as [|i]; [exact E4|]. destruct i as [|i]; [exact E5|]. destruct i as [|i]; [exact E6|]. destruct i as [|i]; [exact E7| lia].
Qed.

Lemma readable_munch_above : forall W (m m' : word -> option byte) lo hi,
munch W m m' -> (forall x, lo <= x -> outside W x) -> 0 <= lo -> hi <= 2^64 ->
(forall x, lo <= x < hi -> exists b, mrd asegs m (wa x) = Some b) ->
forall x, lo <= x < hi -> exists b, mrd asegs m' (wa x) = Some b.
Proof.
intros W m m' lo hi MU OUT L0 H1 R x Hx. destruct (R x Hx) as (b & E). exists b. unfold mrd in *. rewrite (MU (wa x)); [exact E|].
rewrite wa_unsigned by lia. apply OUT. lia.
Qed.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma take_upd_snoc : forall {A} (l : list A) n x, (n < length l)%nat ->
take (S n) (upd l n x) = take n l ++ [x].
Proof.
intros A l n x Hn. rewrite upd_firstn_skipn by exact Hn.
rewrite take_app_ge by (rewrite length_take; lia). rewrite length_take, Nat.min_l by lia.
replace (S n - n)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma read_le8 : forall m a (w : word) a', bytes_at asegs m a (le8 w) -> a' = wa a -> ov_read_bytes asegs m a' 8 = Some (le8 w).
Proof.
intros m a w a' B ->. pose proof (bytes_at_read asegs m a (le8 w) 0 8 B ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as R.
rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all2 in R by (rewrite length_le8; lia). exact R.
Qed.

Definition unw_exit (ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(obj pcv : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a5 a6 a7 : word) (m' : word -> option byte) (qs' : list word) (sz' : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) a2 (wz 4096) (wz (obj + 16)) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x84918) fc None m' (seg_rom asegs)
/\ munch [(obj + 8, obj + 12); (obj + 16, obj + 256)] m m' /\ wmono asegs m m'
/\ (mem_inv asegs m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C4 (wz sz'); C4 (wz 0)]
/\ u64arr asegs m' (obj + 16) qs' /\ Z.of_nat (length qs') = 30 /\ 1 <= sz' <= 30).

Definition unw_next (ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(obj pcv v : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a6 a7 : word) (m' : word -> option byte) (qs' : list word) (sz' v' : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v') (wz 4096) (wz (obj + 16)) (wz sz') a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x848dc) fc None m' (seg_rom asegs)
/\ munch [(obj + 8, obj + 12); (obj + 16, obj + 256)] m m' /\ wmono asegs m m'
/\ (mem_inv asegs m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C4 (wz sz'); C4 (wz 0)]
/\ u64arr asegs m' (obj + 16) qs' /\ Z.of_nat (length qs') = 30 /\ 1 <= sz' <= 30
/\ v < v' /\ unw_valid RE v').

Lemma unw_tail : forall (v sz : Z) (qs : list word) m
(ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (obj pcv : Z) (W : list (Z * Z)) (m0 : word -> option byte),
munch W m0 m -> wmono asegs m0 m -> W = [(obj + 8, obj + 12); (obj + 16, obj + 256)] ->
mem_inv asegs m ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs -> Z.of_nat (length qs) = 30 -> 1 <= sz <= 30 ->
0 <= v -> ae_stack_top RE <= 2^47 + 32768 -> unw_valid RE v ->
(exists fp2 : word, bytes_at asegs m (v - 16) (le8 fp2)) ->
evt asegs (fun ms' => unw_exit ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv m0 ms'
\/ unw_next ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv v m0 ms')
(MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v) (wz 4096) (wz (obj + 16)) (wz sz) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84900) fc None m (seg_rom asegs)).
Proof.
intros until m0; intros MU WM -> MI HD Q LQ SZR V0 TOPB VV (fp2 & FP2).
destruct VV as (VV1 & VV2 & VV3). unfold ae_stack_bottom in VV1.
pose proof (bv_unsigned_in_range 64 fp2) as FR2. change (bv_modulus 64) with (2^64) in FR2.
pose proof (read_le8 m (v - 16) fp2 (wz (v + -16)) FP2 ltac:(unfold wa; f_equal; lia)) as RD2.
istep. istep. if_cases E3; zify_cond E3.
{ apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
istep. if_cases E4; zify_cond E4.
{ apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
do 3 istep. if_cases E5; zify_cond E5.
2: { apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
apply evt_done. right. unfold unw_next. rewrite <- (Z_to_bv_lit_self fp2).
do 3 eexists. exists qs, sz, (bv_unsigned fp2). split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ|]. split; [exact SZR|].
split; [lia|]. unfold unw_valid, ae_stack_bottom. rewrite <- (land7 (bv_unsigned fp2)) by lia. lia.
Qed.

Lemma unw_body : forall (v sz : Z) (qs : list word) m
(ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (obj pcv : Z),
mem_inv asegs m ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs -> Z.of_nat (length qs) = 30 -> 1 <= sz <= 30 ->
0 <= pcv < 2^64 -> 0 <= obj -> obj + 2064 <= v -> ae_stack_top RE <= 2^47 + 32768 ->
unw_valid RE v ->
(forall x, v - 16 <= x < ae_stack_top RE -> exists b, mrd asegs m (wa x) = Some b) ->
evt asegs (fun ms' => unw_exit ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv m ms'
\/ unw_next ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv v m ms')
(MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v) (wz 4096) (wz (obj + 16)) (wz sz) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x848dc) fc None m (seg_rom asegs)).
Proof.
intros until pcv; intros MI HD Q LQ SZR PB OLO OV TOPB VV URD.
pose proof VV as (VV1 & VV2 & VV3). unfold ae_stack_bottom in VV1.
destruct (readable_le8 m (v - 8) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply URD; lia)) as (ra2 & RA2).
destruct (readable_le8 m (v - 16) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply URD; lia)) as (fp2 & FP2).
pose proof (bv_unsigned_in_range 64 ra2) as RR. change (bv_modulus 64) with (2^64) in RR.
pose proof (munch_refl [(obj + 8, obj + 12); (obj + 16, obj + 256)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (read_le8 m (v - 8) ra2 (wz (v + -8)) RA2 ltac:(unfold wa; f_equal; lia)) as RD1.
istep. if_cases E0; zify_cond E0.
{
apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
istep. istep. if_cases E1; zify_cond E1.
{
apply evt_done. left. unfold unw_exit. do 5 eexists. exists qs, sz. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ| exact SZR]. }
istep. if_cases E2.
{
eapply (unw_tail v sz qs m); [exact MU| exact WM| reflexivity| exact MI| exact HD| exact Q| exact LQ| exact SZR| lia| exact TOPB| exact VV| exists fp2; exact FP2]. }

assert (SZ30 : sz < 30) by (rewrite ?(unsigned_lit sz) in E0 by lia; lia).
istep. rewrite (unsigned_lit sz), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mul_comm sz 8).
do 3 istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_store_ok asegs mc (obj + 16) qs sz (wa (obj + 16 + 8 * sz)) Q ltac:(lia) eq_refl) as SOK end.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc (obj + 16) qs sz ra2 Q ltac:(lia)) as Q1 end.
clear Q. store_done.
assert (LQ1 : Z.of_nat (length (upd qs (Z.to_nat sz) ra2)) = 30) by (rewrite upd_length; exact LQ).
eapply (unw_tail v (sz + 1) (upd qs (Z.to_nat sz) ra2)); [exact MU| exact WM| reflexivity| assumption| exact HD| exact Q1| exact LQ1| lia| lia| exact TOPB| exact VV| exists fp2; exact FP2].
Qed.

Lemma unw_loop : forall (k : nat) (v sz : Z) (qs : list word) m
(ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (obj pcv : Z),
mem_inv asegs m ->
rw_cells asegs m obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)] ->
u64arr asegs m (obj + 16) qs -> Z.of_nat (length qs) = 30 -> 1 <= sz <= 30 ->
0 <= pcv < 2^64 -> 0 <= obj -> obj + 2064 <= v -> ae_stack_top RE <= 2^47 + 32768 ->
unw_valid RE v -> ae_stack_top RE - v <= Z.of_nat k ->
(forall x, v - 16 <= x < ae_stack_top RE -> exists b, mrd asegs m (wa x) = Some b) ->
evt asegs (unw_exit ra sp gp tp t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc obj pcv m)
(MS (mkR ra sp gp tp t0 t1 t2 (wz 30) (wz (ae_stack_top RE + -16)) (wz obj) (wz pcv) (wz v) (wz 4096) (wz (obj + 16)) (wz sz) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x848dc) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until pcv; intros MI HD Q LQ SZR PB OLO OV TOPB VV DIST URD.
{ exfalso. destruct VV as (_ & VV2 & _). lia. }
eapply evt_cut; [eapply (unw_body v sz qs m); eassumption|].
cbv beta. intros ms' [EX|NX]; [apply evt_done; exact EX|].
destruct NX as (a6' & a7' & m' & qs' & sz' & v' & -> & MU & WM & MI' & HD' & Q' & LQ' & SZR' & LT & VAL).
assert (VB : ae_stack_top RE - 0x800000 < v /\ v < ae_stack_top RE - 16) by (destruct VV as (V1 & V2 & _); unfold ae_stack_bottom in V1; lia).
eapply evt_mono.
{ eapply (IH v' sz' qs' m'); try eassumption; try lia.
eapply (readable_munch_above _ m m' (v' - 16) (ae_stack_top RE)); [exact MU| intros x Hx; cbn [outside]; lia| lia| lia|].
intros x Hx. apply URD. lia. }
cbv beta. intros ms'' (a2'' & a5'' & a6'' & a7'' & m'' & qs'' & sz'' & E & MU2 & WM2 & REST).
exists a2'', a5'', a6'', a7'', m'', qs'', sz''. split; [exact E|].
split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]| exact REST].
Qed.

Definition unw_fin (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(obj pcv : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (qs : list word) (sz : Z),
ms' = MS (mkR (wz 0x6bd6c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x84918) fc None m' (seg_rom asegs)
/\ munch [(obj + 8, obj + 12); (obj + 16, obj + 256)] m m' /\ wmono asegs m m'
/\ (mem_inv asegs m'
/\ rw_cells asegs m' obj [C8 (wz (obj + 16)); C4 (wz sz); C4 (wz 0)]
/\ u64arr asegs m' (obj + 16) qs /\ Z.of_nat (length qs) = 30 /\ 1 <= sz <= 30).

Lemma unwind_impl_spec : forall ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo (obj pcv bp : Z) (q0 q1 q2 q3 q4 : word) (rest : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - unwind_stack ->
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest bp) ->
rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] ->
unw_readable asegs RE m (bp - 16) ->
0 <= pcv < 2^64 -> bv_unsigned sp <= obj -> obj + 2080 <= bp -> bp < 2^64 ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(obj + 8, obj + 12); (obj + 16, obj + 256); (obj + 2056, obj + 2064); (bv_unsigned sp - unwind_stack, bv_unsigned sp); (rl_T X + 3168, rl_T X + 3169)] lo m
(fun _ m' => exists (sz : Z) (q : list word) (rest' : list byte),
rw_cells asegs m' obj (unw_obj obj sz q rest' bp) /\ length q = 5%nat
/\ rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)]
/\ 1 <= sz <= 30 /\ RTconst RE X m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz obj) (wz pcv) (wz bp) (wz 0) (wz 1) (wz 30) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz unwind_impl_entry) fc None m (seg_rom asegs)).
Proof.
intros until rest; intros RT RL MI ST CEIL LO OBJ TU URD0 PB OLO OHI BHI.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold unwind_impl_entry, unwind_stack in *.
obj_facts RL.
pose proof (munch_refl [(obj + 8, obj + 12); (obj + 16, obj + 256); (obj + 2056, obj + 2064); (bv_unsigned sp - 144, bv_unsigned sp); (rl_T X + 3168, rl_T X + 3169)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold unw_obj in OBJ. cbn [map app] in OBJ.
carve_frame 80%nat ST.
step_until 0x69fa8.
call0 (asan_inited_spec RE X). { rt_solve RT RL. } { assumption. }
subst_words. step_until 0. if_false_u.
istep. call_u (get_current_thread_spec RE X).
{ rt_solve RT RL. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.
istep. if_false_u.

step_until 0. if_false.

assert (TOPF : 0x7fff7fffff60 <= ae_stack_top RE < 2^47 + 0x8000 /\ ae_stack_top RE mod 4096 = 0).
{ destruct RL as ((R1 & R2) & R3 & R4 & R5 & _). lia. }
unfold ae_stack_bottom in *.
rt_T_now RT RL TT. istep. step_until 0. if_true. step_until 0x6bcc4.
rewrite (sel_and (ae_stack_top RE - 8388608) (ae_stack_top RE) (ae_stack_top RE)) by lia.
istep. step_until 0. if_true. step_until 0x6bcd0.
rewrite (sel_and (ae_stack_top RE - 8388608) (ae_stack_top RE) (ae_stack_top RE - 8388608)) by lia.
clear TT. step_until 0. if_false. step_until 0x84e78.

carve_frame 64%nat STK.
step_until 0x84eb0. rewrite (unsigned_lit bp), land_ones64 by lia.
step_until 0. if_false. step_until 0. if_true. step_until 0. if_true. step_until 0x8481c.
release_frame FR0 STK (bv_unsigned sp - 80).

carve_frame 64%nat STK. replace (bv_unsigned sp + -80 + -64) with (bv_unsigned sp + -144) in FR0, STK by lia.
rt_now RT RL 18%nat K18. rt_now RT RL 8%nat K8.
step_until 0. if_false. step_until 0. clear K18 K8. if_false. step_until 0.
rewrite (unsigned_lit (ae_stack_top RE)), Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096.
assert (TD : 1 <= ae_stack_top RE / 4096 < 2^40) by (Z.div_mod_to_equations; lia).
if_true_u. step_until 0. if_false_u.

match goal with H : rw_cells asegs _ obj _ |- _ => rename H into OBJ1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
change (rw_cells asegs mc obj (unw_obj obj 1 [wz pcv; q1; q2; q3; q4] rest bp)) in OBJ1;
destruct (unw_obj_open mc obj 1 [wz pcv; q1; q2; q3; q4] rest bp eq_refl OBJ1) as (qs0 & rest2 & LQ0 & HD & Q & OBJR); clear OBJ1;
pose proof (munch_refl [(obj + 8, obj + 12); (obj + 16, obj + 256)] mc) as MU1; pose proof (wmono_refl asegs mc) as WM1;
assert (URD : forall x, bp - 16 <= x < ae_stack_top RE -> exists b, mrd asegs mc (wa x) = Some b)
by (eapply (readable_munch_above _ m mc (bp - 16) (ae_stack_top RE)); [exact MU| intros y Hy; cbn [outside]; lia| lia| lia| intros y Hy; apply URD0; lia])
end.
eapply evt_cut with (P := unw_fin (wz (bv_unsigned sp + -144)) gp (wz A_TP) _ _ _ _ _ _ _ s9 s10 s11 F fc obj pcv _).
{
istep. if_cases V1; zify_cond V1.
{ apply evt_done. unfold unw_fin. do 18 eexists. exists qs0, 1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ0| lia]. }
step_until 0. if_cases V2; zify_cond V2.
{ apply evt_done. unfold unw_fin. do 18 eexists. exists qs0, 1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ0| lia]. }
step_until 0. if_cases V3; zify_cond V3.
{ apply evt_done. unfold unw_fin. do 18 eexists. exists qs0, 1. split; [reflexivity|].
split; [exact MU1|]. split; [exact WM1|]. split; [assumption|]. split; [exact HD|]. split; [exact Q|]. split; [exact LQ0| lia]. }
step_until 0x848dc.
eapply evt_mono.
{ eapply (unw_loop (Z.to_nat (ae_stack_top RE - bp)) bp 1 qs0); [assumption| exact HD| exact Q| exact LQ0| lia| exact PB| lia| lia| lia| | lia| exact URD].
unfold unw_valid, ae_stack_bottom. rewrite <- (land7 bp) by lia. lia. }
cbv beta. intros ms' (a2' & a5' & a6' & a7' & m' & qs' & sz' & -> & MU2 & WM2 & MI' & HD' & Q' & LQ' & SZR').
unfold unw_fin. do 18 eexists. exists qs', sz'. split; [reflexivity|].
split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|]. split; [exact HD'|]. split; [exact Q'|]. split; [exact LQ'| exact SZR']. }

clear HD Q MU1 WM1 URD.
lazymatch goal with |- forall ms', unw_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc ms' -> _ => post_call_u asegs mc end.
match goal with H : rw_cells asegs _ obj _ |- _ => rename H into HD end.
match goal with H : u64arr asegs _ (obj + 16) ?q, H1 : Z.of_nat (length ?q) = 30, H2 : 1 <= ?z, H3 : ?z <= 30 |- _ =>
rename H into Q; rename H1 into LQ; rename q into qs; rename z into sz; assert (SZR : 1 <= sz <= 30) by (split; [exact H2| exact H3]) end.

step_until 0x6bd6c. release_frame FR0 STK (bv_unsigned sp + -80).
step_until 0. release_frame FR STK (bv_unsigned sp).
match goal with H : rw_cells asegs _ (obj + 256) _ |- _ => rename H into OBJR2 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
destruct (unw_obj_close mc obj sz qs rest2 bp LQ ltac:(assumption) ltac:(assumption) OBJR2) as (q5 & rest' & LQ5 & OBJF) end.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].
exists sz, q5, rest'.
split; [exact OBJF|]. split; [exact LQ5|]. split; [assumption|]. split; [exact SZR|].
rt_solve RT RL.
Qed.
End Walk.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Ltac ifT := unfold_cond; cond_unsig; if_true.
Ltac ifF := unfold_cond; cond_unsig; if_false.

Definition rt_mem_cells (m : mem) : Prop :=
shadow_base asegs m
/\ ro_cells asegs m 0x0e81c0 [C8 (wz 0x0f2ea8); C8 (wz 0x0f2eb0); C8 (wz 0x0f2ea0); C8 (wz 0x0ea1d0)]
/\ ro_cells asegs m 0x0f2ea0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)].

Local Ltac rtacc := intros m RC; unfold rt_consts_at in RC; decompose [and] RC; assumption.

Lemma rt_1589b8_guard {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e8f90 [C8 (wz 0x645560)].
Proof. rtacc. Qed.

Lemma rt_683ae0 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x645560 [C8 band_guard].
Proof. rtacc. Qed.

Lemma rt_157bb0 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e81a8 [C8 (wz 0x183ce8); C8 (wz 0x0ef9b8)].
Proof. rtacc. Qed.
Lemma rt_157bc8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e81c0 [C8 (wz 0x0f2ea8); C8 (wz 0x0f2eb0); C8 (wz 0x0f2ea0); C8 (wz 0x0ea1d0)].
Proof. rtacc. Qed.

Lemma rt_1588c8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0e8d28 [C8 (wz 0x0f2e99)].
Proof. rtacc. Qed.
Lemma rt_15a5a8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0ea178 [C8 (wz 0xde3d4)].
Proof. rtacc. Qed.
Lemma rt_15a5f8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0ea1c8 [C8 (wz 0xdda10); C8 (wz 0xdde14)].
Proof. rtacc. Qed.

Lemma rt_159b60 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0ea068 [C8 (wz 0xdd914)].
Proof. rtacc. Qed.

Lemma rt_159bb8 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0ea080 [C8 (wz 0xd5bc4)].
Proof. rtacc. Qed.
Lemma rt_159c68 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0ea098 [C8 (wz 0xdb6ac); C8 (wz 0xd5f20)].
Proof. rtacc. Qed.
Lemma rt_161720 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0f2e98 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof. rtacc. Qed.
Lemma rt_161728 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x0f2ea0 [C8 (wz 0x7fffffffffff); C8 (wz 0); C8 (wz 0)].
Proof. rtacc. Qed.

Lemma rt_1f25bc {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x183d3c [C1 (Z_to_bv 8 1)].
Proof. rtacc. Qed.
Lemma rt_1f2663 {BAND : Band} : forall m, rt_consts_at asegs m -> ro_cells asegs m 0x183de3 [C1 (Z_to_bv 8 1)].
Proof. rtacc. Qed.

Lemma rt_mem_cells_of {BAND : Band} : forall m, shadow_base asegs m -> rt_consts_at asegs m -> rt_mem_cells m.
Proof.
intros m SB RC. exact (conj SB (conj (rt_157bc8 _ RC) (rt_161728 _ RC))).
Qed.

Definition rt_wzone (iv : Z * Z) : Prop :=
snd iv <= 0x0e4ab8 \/ (0x0ea220 <= fst iv /\ snd iv <= 0x0ed040) \/ (0x0efac0 <= fst iv /\ snd iv <= 0x0f1a1c)
\/ (0x0f2ebc <= fst iv /\ snd iv <= 0x181c60) \/ (0x183de6 <= fst iv /\ snd iv <= 0x184060) \/ (0x184061 <= fst iv /\ snd iv <= 0x645560)
\/ (0x645568 <= fst iv /\ snd iv <= 0x6457e0) \/ 0x6457e8 <= fst iv.

Ltac rt_wzones := repeat (apply Forall_cons; [unfold rt_wzone; cbn [fst snd]; lia|]); apply Forall_nil.
Ltac zforalls := repeat (apply Forall_cons; [cbv beta; unfold rt_wzone; cbn [fst snd]; rewrite ?KHI_eq; lia|]); apply Forall_nil.

Local Ltac rt_disj HW :=
lazymatch type of HW with Forall _ ?W =>
assert (D : forall A n, ((0x0e4ab8 <= A /\ A + n <= 0x0ea220) \/ (0x0ed040 <= A /\ A + n <= 0x0efac0) \/ (0x0f1a1c <= A /\ A + n <= 0x0f2ebc)
\/ (0x181c60 <= A /\ A + n <= 0x183de6) \/ (0x184060 <= A /\ A + n <= 0x184061) \/ (0x645560 <= A /\ A + n <= 0x645568) \/ (0x6457e0 <= A /\ A + n <= 0x6457e8)) -> disjoint_from W A n)
by (intros A n H; clear - HW H; induction HW as [|[lo hi] W' H1 HW IH]; cbn in *; [exact I|]; unfold rt_wzone in H1; cbn in H1; split; [lia| exact IH])
end.

Lemma rt_mem_cells_munch : forall m m' W, rt_mem_cells m -> munch W m m' ->
Forall rt_wzone W -> rt_mem_cells m'.
Proof.
intros m m' W ((S1 & S2) & K1 & K2) MU HW. rt_disj HW.
unfold rt_mem_cells, shadow_base. unfold A_SHADOW_GOT, A_SHADOW_CELL in *.
repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

Lemma rt_consts_at_munch {BAND : Band} : forall m m' W, rt_consts_at asegs m -> munch W m m' -> wmono asegs m m' ->
Forall rt_wzone W -> rt_consts_at asegs m'.
Proof.
intros m m' W RC MU WM HW. rt_disj HW.
unfold rt_consts_at in *.
repeat match goal with |- _ /\ _ => split end;
first [ eapply ro_cells_transport; [| exact MU| apply D; cbn; lia]; apply RC
| eapply rw_cells_transport; [| exact MU| exact WM| apply D; cbn; lia]; apply RC ].
Qed.

Lemma shadow_base_munch : forall m m' W, shadow_base asegs m -> munch W m m' ->
Forall rt_wzone W -> shadow_base asegs m'.
Proof.
intros m m' W [S1 S2] MU HW. rt_disj HW.
unfold shadow_base, A_SHADOW_GOT, A_SHADOW_CELL in *. split; (eapply ro_cells_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

Lemma m2s_spec7 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (p : Z),
rt_mem_cells m -> 0 <= p -> p < 2^47 -> (p + 1 <= 0x7fff8000 \/ KHI <= p) ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz (SH p)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz m2s_entry) fc None m (seg_rom asegs)).
Proof.
intros until p; intros ((K5a & K5) & K19 & K1) P0 K2p REG. rewrite ?KHI_eq in REG. unfold m2s_entry. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in *.
step. stp. stp.
step. stp. stp. stp.
step. destruct REG as [LOW|K1p].
{
ifT. stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia. }
ifF.
step. step. step. step. step. step.
stp. step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity|]. rewrite (unsigned_lit p) by lia. rewrite Z.shiftr_div_pow2, SH_eq by lia. f_equal. lia.
Qed.

Lemma miz_spec7 {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A n lo : Z),
mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
zrd m A n -> 0 < n -> n <= 2^40 -> 0x647000 <= A -> A + n <= KHI ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' _ => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz miz_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros MI ST CEIL LO ZR N0 N40 ALO AHI.
pose proof CEIL as CEIL'. idtac. rewrite ?KHI_eq in AHI.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold miz_entry.
carve_frame 16%nat ST.
istep. istep.
step. step. step. step. step. ifz.
step. step. step. stp. stp.
rewrite (unsigned_lit (A + 7)), (unsigned_lit (A + n)) by lia. rewrite !land_m8 by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (ZR' : zrd mc A n) by (eapply zrd_munch; [exact ZR| exact MU| exact WM| intros x Hx; cbn; lia]) end.
set (ab := A + 7 - (A + 7) mod 8). set (ae := A + n - (A + n) mod 8).
assert (AB : A <= ab < A + 8 /\ ab mod 8 = 0) by (subst ab; Z.div_mod_to_equations; lia).
assert (AE : A + n - 8 < ae <= A + n /\ ae mod 8 = 0) by (subst ae; Z.div_mod_to_equations; lia).
clearbody ab ae.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a6' : word, ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 16 a6' R)) FF (wz 0x758d0) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ab A) as [X1|X1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. step. ifz. step. stp.
eapply (miz_bloop (Z.to_nat (A + n - (A + 1))) (A + 1)); [exact ZR'| reflexivity| lia| lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3' a6'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a6' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a3'' a5' : word, ms2 = MS (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 15 a5' R)) FF (wz 0x758e4) fcc rv mm ro))
end.
{ step. destruct (Z_le_gt_dec ae ab) as [X2|X2].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. eapply (miz_wloop (Z.to_nat (ae - ab)) ab); [exact ZR'| reflexivity| lia| lia| Z.div_mod_to_equations; lia| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a3'' a5'. apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a3'' & a5' & ->). simp_regs.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (TAIL : forall a0' a2' a4',
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m (fun a0'' _ => a0'' = wz 1))
(MS (mkR ra (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0' (wz 0) a2' a3'' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x75904) fc None mc (seg_rom asegs)))
end.
{ intros a0' a2' a4'. stp. step. step.
release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity. }
step. destruct (Z_lt_le_dec ae A) as [X3|X3].
{ ifz. apply TAIL. }
ifz. step. destruct (Z_le_gt_dec (A + n) ae) as [X4|X4].
{ ifz. apply TAIL. }
ifz. stp. rewrite (unsigned_lit ae) by lia. replace (A + n + - ae) with (A + n - ae) by lia.
eapply (miz_eloop (Z.to_nat (A + n - ae)) ae); [exact ZR'| reflexivity| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a0' a2' a4'. apply TAIL.
Qed.

Local Ltac rip_tail7 FR ST usp RTM :=
do 10 step; release_frame FR ST usp;
step; apply evt_done; unfold rpost; do 16 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|]; split; [reflexivity| exact RTM].

Lemma rip_spec7 {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst n lo : Z),
rt_mem_cells m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 80 ->
shadow_ok m dst n -> 0 < n <= 2^43 -> 0 <= dst -> dst + n + 8 <= 2^47 -> (dst + n + 8 <= 0x7fff8000 \/ KHI <= dst) ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 80, bv_unsigned sp)] lo m
(fun a0' m' => a0' = wz 0 /\ rt_mem_cells m'))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz rip_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros RTM MI ST CEIL LO SO [N0 N43] D0 K2d REG.
pose proof CEIL as CEIL'. idtac. pose proof REG as REG'.
rewrite ?KHI_eq in REG.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold rip_entry.
carve_frame 64%nat ST.
do 8 istep.
step. ifz.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RTM1 : rt_mem_cells mc) by (eapply rt_mem_cells_munch; [exact RTM| exact MU| rt_wzones]) end.
pose proof RTM1 as ((K5a & K5) & K19 & K1). unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step. stp. stp.
step. stp. stp. stp.

step.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' a4' a5' a6' a7' t0' : word,
ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 14 a4' (@bvmap_set 5 word 15 a5'
(@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' (@bvmap_set 5 word 5 t0' (@bvmap_set 5 word 18 (wz (n + dst)) R))))))))
FF (wz 0x65658) fcc rv mm ro))
end.
{ destruct REG as [LOW|K1d].
- ifT.
stp. step. ifT.
apply evt_done. do 7 eexists. simp_regs. reflexivity.
- ifF.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
stp.
step. ifF.
step. step. step. step. step. step. stp.
step. ifz.
step. step. step. stp. stp.
step. ifz. step. ifz.
apply evt_done. do 7 eexists. simp_regs. reflexivity. }
intros ms0 (a2c & a3c & a4c & a5c & a6c & a7c & t0c & ->). simp_regs.
step. ifF.
stp. stp. stp.
rewrite (unsigned_lit (dst + 7)), (unsigned_lit (n + dst)) by lia. rewrite !land_m8 by lia.
set (ab8 := dst + 7 - (dst + 7) mod 8). set (ae8 := n + dst - (n + dst) mod 8).
assert (AB : dst <= ab8 < dst + 8 /\ ab8 mod 8 = 0 /\ ab8 = (dst + 7) / 8 * 8) by (subst ab8; Z.div_mod_to_equations; lia).
assert (AE : dst + n - 8 < ae8 <= dst + n /\ ae8 mod 8 = 0 /\ ae8 = (dst + n) / 8 * 8) by (subst ae8; Z.div_mod_to_equations; lia).
clearbody ab8 ae8. clear K5a K5 K19 K1.
step. call0 m2s_spec7; [exact RTM1| lia| lia| rewrite ?KHI_eq; clear - AB REG N0; lia|]. subst_words.
step. step. step. call0 m2s_spec7; [exact RTM1| lia| lia| rewrite ?KHI_eq; clear - AE REG N0; Z.div_mod_to_equations; lia|]. subst_words.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MU| exact WM| | exact N0]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (shadow_ok_first _ dst n SO' N0) as (v0 & B0 & R0 & C0).
destruct (shadow_ok_last _ dst n SO' N0) as (v1 & B1 & R1 & C1).
pose proof RTM1 as ((K5a & K5) & K19 & K1). unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.

step. stp. stp. rewrite (unsigned_lit dst) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
step.
rewrite (sxb_b8 v0) by lia.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a2' a3' : word, ms1 = MS (@bvmap_set 5 word 12 a2' (@bvmap_set 5 word 13 a3' R)) FF (wz 0x65694) fcc rv mm ro))
end.
{ step. destruct C0 as [->|C0].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit dst), land7 by lia. step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms1 (a2' & a3' & ->). simp_regs.

stp. stp. stp. rewrite (unsigned_lit (n + dst + -1)) by lia.
replace (2147450880 + (n + dst + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
step. rewrite (sxb_b8 v1) by lia.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms2 => exists a1' a2'' : word, ms2 = MS (@bvmap_set 5 word 11 a1' (@bvmap_set 5 word 12 a2'' R)) FF (wz 0x656e8) fcc rv mm ro))
end.
{ step. destruct C1 as [->|C1].
- ifz. apply evt_done. do 2 eexists. simp_regs. reflexivity.
- ifz. stp. rewrite (unsigned_lit (n + dst + -1)), land7 by lia. replace ((n + dst + -1) mod 8) with ((dst + n - 1) mod 8) by (f_equal; lia).
step. unfold_cond. rewrite !signed_small by lia. if_lit.
apply evt_done. do 2 eexists. simp_regs. reflexivity. }
intros ms2 (a1' & a2'' & ->). simp_regs.

pose proof (shadow_ok_zrd _ dst n SO' N0) as ZR. destruct AB as (AB1 & AB2 & AB3). destruct AE as (AE1 & AE2 & AE3).
rewrite <- AB3, <- AE3 in ZR.
assert (SHB : 0x7fff8000 <= SH ab8 /\ SH ae8 <= 0x10007fff8000 /\ 8 * (SH ae8 - SH ab8) = ae8 - ab8).
{ rewrite !SH_eq. clear - AB1 AB2 AE1 AE2 D0 REG K2d N0. Z.div_mod_to_equations. lia. }
clear K5a K5 K19 K1.
step. destruct (Z_le_gt_dec (SH ae8) (SH ab8)) as [X5|X5].
{ ifz. rip_tail7 FR ST (bv_unsigned sp) RTM1. }
ifz. stp. rewrite ?(unsigned_lit (SH ae8)), ?(unsigned_lit (SH ab8)) by lia. replace (SH ae8 + - SH ab8) with (SH ae8 - SH ab8) by lia.
step. step.
call_u miz_spec7.
{ assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. } { exact ZR. } { lia. } { clear - SHB AB1 AE1 N43; Z.div_mod_to_equations; lia. } { lia. } { rewrite ?KHI_eq. lia. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (rt_mem_cells_munch _ _ _ RTM MU ltac:(rt_wzones)) as RTM2 end.
step. ifz. rip_tail7 FR ST' (bv_unsigned sp) RTM2.
Qed.

Lemma u_nm65 : forall n, 1 <= n <= 64 -> bv_unsigned (wz (n + -65)) = 18446744073709551551 + n.
Proof. intros n Hn. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

Lemma rw_cells_apart : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW.
eapply (rw_cells_agree asegs (fun a => A <= a < A + Z.of_nat (cells_size cs))); [eapply agree_on_of_munch; [exact MU| exact WM|]| exact RC| intros a Ha; exact Ha].
intros x Hx _. clear MU. induction HW as [|[lo hi] W H HW IH]; cbn; [exact I|]. cbn in H. split; [lia| exact IH].
Qed.
Lemma rw_cells_below : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW. eapply rw_cells_apart; [exact RC| exact MU| exact WM|].
eapply Forall_impl; [| exact HW]. cbv beta. intros iv H. left. exact H.
Qed.

Lemma shadow_ok_zrd_head : forall m dst n, shadow_ok m dst n -> 0 < n -> zrd m (SH dst) (SH (dst + n - 1) - SH dst).
Proof.
intros m dst n SO N0 i Hi. rewrite !SH_eq in Hi.
destruct (SO i ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
assert (v = 0) as -> by (Z.div_mod_to_equations; lia).
match type of B with bytes_at _ _ ?a _ => replace (SH dst + i) with a; [exact B|] end.
rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma slow_flag_zero : forall r v, 0 <= v < 8 -> 0 <= r < 8 -> (v = 0 \/ r < v) ->
Z.land (bv_unsigned (v_sltu (wz 0) (wz v))) (bv_unsigned (wz (Z.lxor (bv_unsigned (v_slt (wz r) (wz v))) 1))) = 0.
Proof.
intros r v Hv Hr C. unfold v_sltu, c_ltu, bv_ltu, v_slt, c_lts, bv_lts.
rewrite !signed_small, !unsigned_lit by lia. change (bv_unsigned (wz 0)) with 0.
destruct (Z.ltb_spec0 0 v); destruct (Z.ltb_spec0 r v); cbn -[Z.land]; try reflexivity; try lia.
Qed.

Definition ash {BAND : Band} (m : mem) : Prop :=
zrd m 0x7fffa000 0x2618 /\ zrd m (SH band_lo) (KHI - SH band_lo) /\ zrd m 0x800c0b90 0x88.

Lemma ash_munch {BAND : Band} : forall m m' W, ash m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= 0x7fffa000 \/ (0x7fffc618 <= fst iv /\ snd iv <= 0x800c0b90) \/ (0x800c0c18 <= fst iv /\ snd iv <= SH band_lo) \/ 0x10007fff8000 <= fst iv) W ->
ash m'.
Proof.
intros m m' W (Z1 & Z2 & Z3) MU WM HW.
assert (D : forall x, (0x7fffa000 <= x < 0x7fffc618 \/ SH band_lo <= x < 0x10007fff8000 \/ 0x800c0b90 <= x < 0x800c0c18) -> outside W x).
{ intros x Hx. clear - HW Hx. induction HW as [|[lo hi] W' H1 HW IH]; cbn in *; [exact I|]. split; [unfold SH, A_SHADOW_OFS in *; lia| exact IH]. }
split; [| split]; (eapply zrd_munch; [eassumption| exact MU| exact WM| intros x Hx; apply D; unfold KHI in *; lia]).
Qed.

Definition szone {BAND : Band} (p n : Z) : Prop :=
(0x10000 <= p /\ p + n <= 0x230c0) \/ (band_lo + 64 <= p /\ p + n + 8 <= 2^47) \/ (0x645c80 <= p /\ p + n <= 0x6460c0).

Definition rng_ok (m : mem) (p n : Z) : Prop :=
0 <= p /\ p + n + 8 <= 2^47
/\ (0 < n -> shadow_ok m p n)
/\ (64 < n -> (p + n + 8 <= 0x7fff8000 \/ KHI <= p) /\ n <= 2^43)
/\ (0 < n <= 64 -> (exists w : word, rw_cells asegs m (8 * (SH p / 8)) [C8 w])
/\ (exists w : word, rw_cells asegs m (8 * (SH (p + n - 1) / 8)) [C8 w])).

Lemma zrd_hjunk : forall m A n, zrd m A n -> 0x647000 <= A -> A + n <= 2^64 -> hjunk m A (A + n).
Proof.
intros m A n ZR HA HN. split; [lia|]. split; [lia|].
- intros a Ha. destruct (ZR (a - A) ltac:(lia)) as (B0 & B1 & B2). specialize (B2 0%nat ltac:(cbn; lia)). cbn in B2.
replace (A + (a - A) + 0) with a in B2 by lia. rewrite a_mrd_overlay in B2 by (rewrite wa_unsigned by lia; lia).
exists (b8 0). exact B2.
Qed.

Lemma zrd_C8 : forall m A n a, zrd m A n -> 0x647000 <= A -> A <= a -> a + 8 <= A + n -> exists w : word, rw_cells asegs m a [C8 w].
Proof.
intros m A n a ZR HA H1 H2. apply hjunk_C8.
assert (HN : A + n <= 2^64) by (destruct (ZR (n - 1) ltac:(lia)) as (_ & B & _); cbn in B; lia).
pose proof (zrd_hjunk _ _ _ ZR HA HN) as (K1 & K2 & K3).
split; [lia|]. split; [lia|]. intros x Hx. apply K3. lia.
Qed.

Lemma zrd_shadow_ok : forall m A n p k, zrd m A n -> 0 < k -> 0 <= p -> A <= SH p -> SH (p + k - 1) + 1 <= A + n -> shadow_ok m p k.
Proof.
intros m A n p k ZR K0 P0 H1 H2 j Hj Hjk. exists 0. split; [| left; reflexivity].
replace (SH (p / 8 * 8) + j) with (A + (SH (p / 8 * 8) + j - A)) by lia. apply ZR.
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Lemma rng_ok_of_ash {BAND : Band} : forall m p n, ash m -> szone p n -> 0 <= n -> rng_ok m p n.
Proof.
intros m p n (Z1 & Z2 & Z3) SZ N0.  unfold szone in SZ. unfold rng_ok.
destruct SZ as [(A1 & A2)|[(B1 & B2)|(C1 & C2)]].
- split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
+ intros K. eapply (zrd_shadow_ok _ _ _ _ _ Z1); [lia| lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia].
+ intros K. split; (eapply (zrd_C8 _ _ _ _ Z1); [lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia]).
- split; [lia|]. split; [lia|]. split; [| split; [intros; rewrite ?KHI_eq; lia|]].
+ intros K. eapply (zrd_shadow_ok _ _ _ _ _ Z2); [lia| lia| ..]; rewrite !SH_eq; unfold KHI; Z.div_mod_to_equations; lia.
+ intros K. split; (eapply (zrd_C8 _ _ _ _ Z2); rewrite !SH_eq; unfold KHI; Z.div_mod_to_equations; lia).
- split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
+ intros K. eapply (zrd_shadow_ok _ _ _ _ _ Z3); [lia| lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia].
+ intros K. split; (eapply (zrd_C8 _ _ _ _ Z3); [lia| rewrite SH_eq; Z.div_mod_to_equations; lia| rewrite SH_eq; Z.div_mod_to_equations; lia]).
Qed.

Lemma rng_ok_munch : forall m m' p n W, rng_ok m p n -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => 8 * (SH (p + n - 1) / 8) + 8 <= fst iv \/ snd iv <= 8 * (SH p / 8)) W -> rng_ok m' p n.
Proof.
intros m m' p n W (P0 & P47 & SO & BIG & NB) MU WM HW.
assert (D : forall x, 8 * (SH p / 8) <= x < 8 * (SH (p + n - 1) / 8) + 8 -> outside W x).
{ intros x Hx. clear - HW Hx. induction HW as [|[lo hi] W' H1 HW IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
split; [lia|]. split; [lia|]. split; [| split; [exact BIG|]].
- intros K. eapply shadow_ok_munch; [apply SO; exact K| exact MU| exact WM| | exact K].
intros x Hx. apply D. rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
- intros K. destruct (NB K) as [[w1 W1] [w2 W2]]. split.
+ exists w1. eapply rw_cells_apart; [exact W1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H; cbn in *.
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
+ exists w2. eapply rw_cells_apart; [exact W2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H; cbn in *.
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Definition tryinit_entry : Z := 0x6aeb8.

Lemma tryinit_spec7 {BAND : Band} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (lo : Z),
ro_cells asegs m 0x0f2e98 [C1 (b8 1); C1 (b8 1)] -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 16 ->
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 16, bv_unsigned sp)] lo m
(fun a0' _ => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz tryinit_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros K MI ST CEIL LO.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold tryinit_entry.
carve_frame 16%nat ST.
istep. istep. istep.
stp. stp. step. stp. step. step. ifz.
step. step. release_frame FR ST (bv_unsigned sp).
step. step.
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. reflexivity.
Qed.

Definition asaninited_entry : Z := 0x69fa8.

Lemma asaninited_spec7 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m,
ro_cells asegs m 0x0f2e98 [C1 (b8 1); C1 (b8 1)] ->
evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (fun a0' => a0' = wz 1))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz asaninited_entry) fc None m (seg_rom asegs)).
Proof.
intros until m; intros K. unfold asaninited_entry.
step. stp. step. stp. stp. step.
apply evt_done. unfold leaf_post. do 15 eexists. split; [reflexivity| reflexivity].
Qed.

Lemma qslow_loop_a1 : forall (pc : Z), (pc = 0x52d54 \/ pc = 0x527c4 \/ pc = 0x50210 \/ pc = 0x52f34) ->
forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz e) (wz e) (wz 0) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (pc + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz p) (wz e) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom asegs)).
Proof.
intros pc [-> |[-> |[-> | ->]]];
(induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ]).
Qed.

Definition ISH {BAND : Band} (m : mem) : Prop := ash m /\ rt_consts_at asegs m /\ shadow_base asegs m.

Lemma ISH_munch {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma ISH_munch_zone {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (0x0ea220 <= fst iv /\ snd iv <= 0x0ed040) \/ (0x183de6 <= fst iv /\ snd iv <= 0x184060) \/ (0x184061 <= fst iv /\ snd iv <= 0x645560) \/ (0x6457e8 <= fst iv /\ snd iv <= 0x7fffa000) \/ band_lo <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma szone_sub {BAND : Band} : forall p n p' n', szone p n -> p <= p' -> p' + n' <= p + n -> 0 <= n' -> szone p' n'.
Proof. intros p n p' n' SZ H1 H2 H3. unfold szone in *. lia. Qed.
