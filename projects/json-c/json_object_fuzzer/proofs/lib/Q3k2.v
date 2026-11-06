(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QbrW QbVh QEpW QZDE QWxq_c1 QHnV QCcH QfLs Qsw7 QJjn Q7UD Qwm6 QlKV QwAs QMow QlES QmAH QvG1 Qp4j Q9Ho QnRU QpY2 QpzM QXE1 Qr5k QHRw Qvzz QCFK QVl3 QCiC QteI QX7n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.

Import QHnV QCcH QfLs Qsw7 QJjn.
Import Q7UD Qwm6.Mq0 QlKV.Mq6.

Import QlES.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module OE := QbrW.
Module DE := QwAs.Mq0.
Module OC := QbVh.
Module VB := QmAH.
Module IK := Q9Ho.Mq0.
Module IKG := QXE1.Mq0.
Module FP_ := QnRU.Mq4.
Module SJ := QVl3.Mq0.
Module VJ := QCFK.Mq0.
Module VS := Qvzz.Mq0.

Lemma msteps_D2O : forall segs a b, DE.msteps segs a b -> OE.msteps segs a b.
Proof. intros segs a b H. induction H; [apply OE.msteps_refl | eapply OE.msteps_cons; [exact H | exact IHmsteps]]. Qed.
Lemma evt_D2O : forall segs (Q : machine_state -> Prop) ms, DE.evt segs Q ms -> OE.evt segs Q ms.
Proof. intros segs Q ms (ms' & H & HQ). exists ms'. split; [apply msteps_D2O; exact H | exact HQ]. Qed.

Section Inst.
Context {BAND : Band}.

Definition isnp_pre0 (sp a0 a1 : word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (need lo : Z) : Prop :=
a0 = Z_to_bv 64 D /\ a1 = Z_to_bv 64 n /\
rw_cells asegs m D [CB dn junkd] /\ @IKG.ISH BAND m /\
need <= Z.of_nat dn /\ need <= n < 2^63 /\
stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - 8160 /\ band_lo <= lo /\ bv_unsigned sp + 16 <= 2^47 /\
mem_inv asegs m /\ frm0 fc /\
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) /\
dappJ D (Z.of_nat dn) /\ (forall k, 0 < k <= need -> rng_okJ m D k).

Lemma rng_ok_of_J : forall m p n, rng_okJ m p n -> IK.rng_ok m p n.
Proof.
intros m p n (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
intros Hn. destruct (H5 Hn) as ((w1 & R1) & (w2 & R2)).
split; [exists w1; exact (proj1 (VB.rw_cells_D asegs m _ [OC.C8 w1]) R1) | exists w2; exact (proj1 (VB.rw_cells_D asegs m _ [OC.C8 w2]) R2)].
Qed.

Lemma dec_text_nonul : forall i, ~ In (Z_to_bv 8 0) (QteI.Mq1.zb (VJ.dec_text i)).
Proof.
intros i Hin. unfold QteI.Mq1.zb in Hin. apply in_map_iff in Hin as (c & Hc & Hin).
assert (R : 45 <= c < 58).
{ unfold VJ.dec_text in Hin. pose proof (Qi1S.Mq0.dec_digits_range) as DR.
destruct (i <? 0); [| destruct (i =? 0)].
- destruct Hin as [<- | Hin]; [lia|]. specialize (DR (- i)). rewrite Forall_forall in DR. specialize (DR c Hin). lia.
- destruct Hin as [<- | []]. lia.
- specialize (DR i). rewrite Forall_forall in DR. specialize (DR c Hin). lia. }
apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc. replace (bv_modulus 8) with 256 in Hc by reflexivity.
rewrite Z.mod_small in Hc by lia. rewrite Z.mod_small in Hc by lia. lia.
Qed.

Lemma signed_facts : forall a : word, - 2 ^ 63 <= bv_signed a < 2 ^ 63 /\ bv_unsigned a = bv_signed a mod 2 ^ 64.
Proof.
intros a. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
rewrite zb_signed. destruct (Z.ltb_spec0 (bv_unsigned a) (2^63)).
- split; [lia|]. rewrite Z.mod_small by lia. reflexivity.
- split; [lia|]. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ssp_of_ISHG : forall m, IKG.ISH m -> FP_.ssp_cells m band_guard.
Proof. intros m H. apply QX7n.Mq0.ssp_of_ISH. apply IKG.ISH_to_AR. exact H. Qed.

Theorem snp_ld_raw :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre0 sp a0 a1 fc m D n dn junkd 21 lo -> a2 = Z_to_bv 64 A_FMT_LD ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (fun r o => 1 <= r <= 20 /\ ~ In (Z_to_bv 8 0) o) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros PRE Ha2.
destruct PRE as (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
destruct (signed_facts a3) as [SR SE].
pose proof (VJ.dec_text_length (bv_signed a3) ltac:(lia)) as L.
apply evt_D2O. eapply DE.evt_mono.
- eapply (SJ.snprintf_ld_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n (bv_signed a3) dn junkd lo band_guard);
[ exact Ha0 | exact Ha1 | exact Ha2 | exact SR | exact SE | exact (proj1 (VB.rw_cells_D asegs m D [OC.CB dn junkd]) DST) | exact RT | lia | exact Hn
| exact ST | exact LOS | exact BLO | exact SP47 | exact (ssp_of_ISHG m RT) | exact MI | exact FRM | exact DD1 | exact DAPP
| intros k Hk; apply rng_ok_of_J; apply RD; exact Hk ].
- intros ms' (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & ST' & _ & CELLS).
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', (QCiC.Mq1.zlength (VJ.dec_text (bv_signed a3))),
(QteI.Mq1.zb (VJ.dec_text (bv_signed a3))).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|]. split; [exact ST'|].
split; [unfold QCiC.Mq1.zlength, QteI.Mq1.zb; rewrite length_map; reflexivity|].
split; [split; [exact L | apply dec_text_nonul]|].
apply (proj2 (VB.rw_cells_D asegs m' D [OC.CB dn _])).
unfold QteI.Mq1.zb in *. rewrite length_map. exact CELLS.
Qed.

Theorem snp_lu_raw :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre0 sp a0 a1 fc m D n dn junkd 21 lo -> a2 = Z_to_bv 64 A_FMT_LU ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (fun r o => 1 <= r <= 20 /\ ~ In (Z_to_bv 8 0) o) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros PRE Ha2.
destruct PRE as (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
pose proof (bv_unsigned_in_range 64 a3) as UR. unfold bv_modulus in UR. change (2 ^ Z.of_N 64) with (2^64) in UR.
pose proof (VJ.dec_text_length (bv_unsigned a3) ltac:(lia)) as L.
apply evt_D2O. eapply DE.evt_mono.
- eapply (SJ.snprintf_lu_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n dn junkd lo band_guard);
[ exact Ha0 | exact Ha1 | exact Ha2 | exact (proj1 (VB.rw_cells_D asegs m D [OC.CB dn junkd]) DST) | exact RT | lia | exact Hn
| exact ST | exact LOS | exact BLO | exact SP47 | exact (ssp_of_ISHG m RT) | exact MI | exact FRM | exact DD1 | exact DAPP
| intros k Hk; apply rng_ok_of_J; apply RD; exact Hk ].
- cbv zeta. intros ms' (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & ST' & _ & CELLS).
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', (QCiC.Mq1.zlength (VJ.dec_text (bv_unsigned a3))),
(QteI.Mq1.zb (VJ.dec_text (bv_unsigned a3))).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|]. split; [exact ST'|].
split; [unfold QCiC.Mq1.zlength, QteI.Mq1.zb; rewrite length_map; reflexivity|].
split; [split; [exact L | apply dec_text_nonul]|].
apply (proj2 (VB.rw_cells_D asegs m' D [OC.CB dn _])).
unfold QteI.Mq1.zb in *. rewrite length_map. exact CELLS.
Qed.

Theorem snp_u00cc_raw :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre0 sp a0 a1 fc m D n dn junkd 7 lo -> a2 = Z_to_bv 64 A_FMT_U00CC ->
0 <= c1 < 256 -> a3 = Z_to_bv 64 c1 -> 0 <= c2 < 256 -> a4 = Z_to_bv 64 c2 ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (fun r o => o = map (Z_to_bv 8) [92; 117; 48; 48; c1; c2]) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros PRE Ha2 Hc1 Ha3 Hc2 Ha4.
destruct PRE as (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
apply evt_D2O. eapply DE.evt_mono.
- eapply (SJ.snprintf_u00cc_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n c1 c2 dn junkd lo band_guard);
[ exact Ha0 | exact Ha1 | exact Ha2 | lia | subst a3; rewrite unsigned_lit by lia; reflexivity | lia | subst a4; rewrite unsigned_lit by lia; reflexivity
| exact (proj1 (VB.rw_cells_D asegs m D [OC.CB dn junkd]) DST) | exact RT | lia | exact Hn
| exact ST | exact LOS | exact BLO | exact SP47 | exact (ssp_of_ISHG m RT) | exact MI | exact FRM | exact DD1 | exact DAPP
| intros k Hk; apply rng_ok_of_J; apply RD; exact Hk ].
- cbv zeta. intros ms' (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & ST' & _ & CELLS).
rewrite (Z.mod_small c1) in CELLS by lia. rewrite (Z.mod_small c2) in CELLS by lia.
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', 6, (map (Z_to_bv 8) [92; 117; 48; 48; c1; c2]).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|]. split; [exact ST'|].
split; [reflexivity|]. split; [reflexivity|].
apply (proj2 (VB.rw_cells_D asegs m' D [OC.CB dn _])). exact CELLS.
Qed.
End Inst.

Section Wrap.
Context {RC__ : Q6q3.RunConsts}.
Context {BAND : Band}.
Hypothesis BCAP : band_lo <= Q6q3.alloc_ceiling + 4096.

Lemma munch_floor : forall lo lo' hi D E m m', lo <= lo' -> munch [(lo', hi); (D, E)] m m' -> munch [(lo, hi); (D, E)] m m'.
Proof. intros lo lo' hi D E m m' H MU x Hx. apply MU. cbn [outside] in *. destruct Hx as (H1 & H2 & _). split; [lia | split; [exact H2 | exact I]]. Qed.

Lemma isnp_post_floor : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (D : Z) (dn : nat) (junkd : list byte)
(P : Z -> list byte -> Prop) (lo lo' : Z) (m : word -> option byte) (ms' : machine_state),
lo <= lo' -> lo' <= bv_unsigned sp -> stk asegs m lo lo' -> (D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) ->
isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd P lo' m ms' ->
isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd P lo m ms'.
Proof.
intros until ms'. intros Hl Hh STL DD (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & r & o & -> & MU & WM & MI' & FRM' & FREG & ST' & Hr & HP & CELLS).
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', r, o.
split; [reflexivity|]. split; [eapply munch_floor; eassumption|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|].
split.
{ eapply (stk_merge asegs m' lo lo' (bv_unsigned sp)); [ | exact ST' | lia].
eapply (stk_transport_disjoint asegs _ m m'); [exact STL | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
split; [exact Hr|]. split; [exact HP | exact CELLS].
Qed.

Lemma isnp_pre_floor : forall sp a0 a1 fc m D n dn junkd need lo,
isnp_pre (@IKG.ISH BAND) Q6q3.alloc_ceiling sp a0 a1 fc m D n dn junkd need lo ->
lo <= bv_unsigned sp - 8160 /\ bv_unsigned sp - 8160 <= bv_unsigned sp /\ stk asegs m lo (bv_unsigned sp - 8160) /\
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) /\
isnp_pre0 sp a0 a1 fc m D n dn junkd need (bv_unsigned sp - 8160).
Proof.
intros until lo. intros (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
unfold SNP_STACK_A in LOS.
destruct (stk_split asegs m lo (bv_unsigned sp - 8160) (bv_unsigned sp) ST ltac:(lia)) as [STL STH].
split; [lia|]. split; [lia|]. split; [exact STL|]. split; [exact DD1|].
unfold isnp_pre0. split; [exact Ha0|]. split; [exact Ha1|]. split; [exact DST|]. split; [exact RT|]. split; [exact Hdn|]. split; [exact Hn|].
split; [exact STH|]. split; [lia|]. split; [lia|]. split; [exact SP47|]. split; [exact MI|]. split; [exact FRM|].
split; [destruct DD1 as [H|H]; [left; lia | right; exact H]|]. split; [exact DAPP | exact RD].
Qed.

Theorem isnprintf_ld_inst : isnprintf_ld_stmt (@IKG.ISH BAND) Q6q3.alloc_ceiling.
Proof.
unfold isnprintf_ld_stmt, isnprintf_l_stmt. intros until lo. intros PRE Ha2.
destruct (isnp_pre_floor _ _ _ _ _ _ _ _ _ _ _ PRE) as (H1 & H2 & STL & DD & PRE0).
eapply OE.evt_mono; [eapply snp_ld_raw; [exact PRE0 | exact Ha2] |].
intros ms' POST. eapply isnp_post_floor; [exact H1 | exact H2 | exact STL | exact DD | exact POST].
Qed.
Theorem isnprintf_lu_inst : isnprintf_lu_stmt (@IKG.ISH BAND) Q6q3.alloc_ceiling.
Proof.
unfold isnprintf_lu_stmt, isnprintf_l_stmt. intros until lo. intros PRE Ha2.
destruct (isnp_pre_floor _ _ _ _ _ _ _ _ _ _ _ PRE) as (H1 & H2 & STL & DD & PRE0).
eapply OE.evt_mono; [eapply snp_lu_raw; [exact PRE0 | exact Ha2] |].
intros ms' POST. eapply isnp_post_floor; [exact H1 | exact H2 | exact STL | exact DD | exact POST].
Qed.
Theorem isnprintf_u00cc_inst : isnprintf_u00cc_stmt (@IKG.ISH BAND) Q6q3.alloc_ceiling.
Proof.
unfold isnprintf_u00cc_stmt. intros until lo. intros PRE Ha2 Hc1 Ha3 Hc2 Ha4.
destruct (isnp_pre_floor _ _ _ _ _ _ _ _ _ _ _ PRE) as (H1 & H2 & STL & DD & PRE0).
eapply OE.evt_mono; [eapply snp_u00cc_raw; [exact PRE0 | exact Ha2 | exact Hc1 | exact Ha3 | exact Hc2 | exact Ha4] |].
intros ms' POST. eapply isnp_post_floor; [exact H1 | exact H2 | exact STL | exact DD | exact POST].
Qed.
End Wrap.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHRw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvzz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCFK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVl3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QX7n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QdTa.mkr__lia_6. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module OE := QbrW.
Module DE := QwAs.Mq0.
Module OC := QbVh.
Module VB := QmAH.
Module IK := Q9Ho.
Module IKG := QXE1.
Module FP_ := QnRU.
Module SJ := QVl3.
Module VJ := QCFK.
Module VS := Qvzz.

Lemma msteps_D2O : forall segs a b, DE.msteps segs a b -> OE.msteps segs a b.
Proof. intros segs a b H. induction H; [apply OE.msteps_refl | eapply OE.msteps_cons; [exact H | exact IHmsteps]]. Qed.
Lemma evt_D2O : forall segs (Q : machine_state -> Prop) ms, DE.evt segs Q ms -> OE.evt segs Q ms.
Proof. intros segs Q ms (ms' & H & HQ). exists ms'. split; [apply msteps_D2O; exact H | exact HQ]. Qed.

Section Inst.
Context {BAND : Band}.

Definition isnp_pre0 (sp a0 a1 : word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (need lo : Z) : Prop :=
a0 = Z_to_bv 64 D /\ a1 = Z_to_bv 64 n /\
rw_cells asegs m D [CB dn junkd] /\ @IKG.ISH BAND m /\
need <= Z.of_nat dn /\ need <= n < 2^63 /\
stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - 8160 /\ band_lo <= lo /\ bv_unsigned sp + 16 <= 2^47 /\
mem_inv asegs m /\ frm0 fc /\
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) /\
dappJ D (Z.of_nat dn) /\ (forall k, 0 < k <= need -> rng_okJ m D k).

Lemma rng_ok_of_J : forall m p n, rng_okJ m p n -> IK.rng_ok m p n.
Proof.
intros m p n (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
intros Hn. destruct (H5 Hn) as ((w1 & R1) & (w2 & R2)).
split; [exists w1; exact (proj1 (VB.rw_cells_D asegs m _ [OC.C8 w1]) R1) | exists w2; exact (proj1 (VB.rw_cells_D asegs m _ [OC.C8 w2]) R2)].
Qed.

Lemma dec_text_nonul : forall i, ~ In (Z_to_bv 8 0) (QteI.Mqb.zb (VJ.dec_text i)).
Proof.
intros i Hin. unfold QteI.Mqb.zb in Hin. apply in_map_iff in Hin as (c & Hc & Hin).
assert (R : 45 <= c < 58).
{ unfold VJ.dec_text in Hin. pose proof (Qi1S.dec_digits_range) as DR.
destruct (i <? 0); [| destruct (i =? 0)].
- destruct Hin as [<- | Hin]; [lia|]. specialize (DR (- i)). rewrite Forall_forall in DR. specialize (DR c Hin). lia.
- destruct Hin as [<- | []]. lia.
- specialize (DR i). rewrite Forall_forall in DR. specialize (DR c Hin). lia. }
apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc. replace (bv_modulus 8) with 256 in Hc by reflexivity.
rewrite Z.mod_small in Hc by lia. rewrite Z.mod_small in Hc by lia. lia.
Qed.

Lemma signed_facts : forall a : word, - 2 ^ 63 <= bv_signed a < 2 ^ 63 /\ bv_unsigned a = bv_signed a mod 2 ^ 64.
Proof.
intros a. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
rewrite zb_signed. destruct (Z.ltb_spec0 (bv_unsigned a) (2^63)).
- split; [lia|]. rewrite Z.mod_small by lia. reflexivity.
- split; [lia|]. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ssp_of_ISHG : forall m, IKG.ISH m -> FP_.ssp_cells m band_guard.
Proof. intros m H. apply QX7n.ssp_of_ISH. apply IKG.ISH_to_AR. exact H. Qed.

Theorem snp_ld_raw :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre0 sp a0 a1 fc m D n dn junkd 21 lo -> a2 = Z_to_bv 64 A_FMT_LD ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (fun r o => 1 <= r <= 20 /\ ~ In (Z_to_bv 8 0) o) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros PRE Ha2.
destruct PRE as (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
destruct (signed_facts a3) as [SR SE].
pose proof (VJ.dec_text_length (bv_signed a3) ltac:(lia)) as L.
apply evt_D2O. eapply DE.evt_mono.
- eapply (SJ.snprintf_ld_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n (bv_signed a3) dn junkd lo band_guard);
[ exact Ha0 | exact Ha1 | exact Ha2 | exact SR | exact SE | exact (proj1 (VB.rw_cells_D asegs m D [OC.CB dn junkd]) DST) | exact RT | lia | exact Hn
| exact ST | exact LOS | exact BLO | exact SP47 | exact (ssp_of_ISHG m RT) | exact MI | exact FRM | exact DD1 | exact DAPP
| intros k Hk; apply rng_ok_of_J; apply RD; exact Hk ].
- intros ms' (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & ST' & _ & CELLS).
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', (QCiC.Mq1.zlength (VJ.dec_text (bv_signed a3))),
(QteI.Mqb.zb (VJ.dec_text (bv_signed a3))).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|]. split; [exact ST'|].
split; [unfold QCiC.Mq1.zlength, QteI.Mqb.zb; rewrite length_map; reflexivity|].
split; [split; [exact L | apply dec_text_nonul]|].
apply (proj2 (VB.rw_cells_D asegs m' D [OC.CB dn _])).
unfold QteI.Mqb.zb in *. rewrite length_map. exact CELLS.
Qed.

Theorem snp_lu_raw :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre0 sp a0 a1 fc m D n dn junkd 21 lo -> a2 = Z_to_bv 64 A_FMT_LU ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (fun r o => 1 <= r <= 20 /\ ~ In (Z_to_bv 8 0) o) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros PRE Ha2.
destruct PRE as (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
pose proof (bv_unsigned_in_range 64 a3) as UR. unfold bv_modulus in UR. change (2 ^ Z.of_N 64) with (2^64) in UR.
pose proof (VJ.dec_text_length (bv_unsigned a3) ltac:(lia)) as L.
apply evt_D2O. eapply DE.evt_mono.
- eapply (SJ.snprintf_lu_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n dn junkd lo band_guard);
[ exact Ha0 | exact Ha1 | exact Ha2 | exact (proj1 (VB.rw_cells_D asegs m D [OC.CB dn junkd]) DST) | exact RT | lia | exact Hn
| exact ST | exact LOS | exact BLO | exact SP47 | exact (ssp_of_ISHG m RT) | exact MI | exact FRM | exact DD1 | exact DAPP
| intros k Hk; apply rng_ok_of_J; apply RD; exact Hk ].
- cbv zeta. intros ms' (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & ST' & _ & CELLS).
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', (QCiC.Mq1.zlength (VJ.dec_text (bv_unsigned a3))),
(QteI.Mqb.zb (VJ.dec_text (bv_unsigned a3))).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|]. split; [exact ST'|].
split; [unfold QCiC.Mq1.zlength, QteI.Mqb.zb; rewrite length_map; reflexivity|].
split; [split; [exact L | apply dec_text_nonul]|].
apply (proj2 (VB.rw_cells_D asegs m' D [OC.CB dn _])).
unfold QteI.Mqb.zb in *. rewrite length_map. exact CELLS.
Qed.

Theorem snp_u00cc_raw :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D n c1 c2 : Z) (dn : nat) (junkd : list byte) (lo : Z),
isnp_pre0 sp a0 a1 fc m D n dn junkd 7 lo -> a2 = Z_to_bv 64 A_FMT_U00CC ->
0 <= c1 < 256 -> a3 = Z_to_bv 64 c1 -> 0 <= c2 < 256 -> a4 = Z_to_bv 64 c2 ->
evt asegs (isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd (fun r o => o = map (Z_to_bv 8) [92; 117; 48; 48; c1; c2]) lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_SNPRINTF_STUB) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros PRE Ha2 Hc1 Ha3 Hc2 Ha4.
destruct PRE as (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
apply evt_D2O. eapply DE.evt_mono.
- eapply (SJ.snprintf_u00cc_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D n c1 c2 dn junkd lo band_guard);
[ exact Ha0 | exact Ha1 | exact Ha2 | lia | subst a3; rewrite unsigned_lit by lia; reflexivity | lia | subst a4; rewrite unsigned_lit by lia; reflexivity
| exact (proj1 (VB.rw_cells_D asegs m D [OC.CB dn junkd]) DST) | exact RT | lia | exact Hn
| exact ST | exact LOS | exact BLO | exact SP47 | exact (ssp_of_ISHG m RT) | exact MI | exact FRM | exact DD1 | exact DAPP
| intros k Hk; apply rng_ok_of_J; apply RD; exact Hk ].
- cbv zeta. intros ms' (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FREG & ST' & _ & CELLS).
rewrite (Z.mod_small c1) in CELLS by lia. rewrite (Z.mod_small c2) in CELLS by lia.
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', 6, (map (Z_to_bv 8) [92; 117; 48; 48; c1; c2]).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|]. split; [exact ST'|].
split; [reflexivity|]. split; [reflexivity|].
apply (proj2 (VB.rw_cells_D asegs m' D [OC.CB dn _])). exact CELLS.
Qed.
End Inst.

Section Wrap.
Context {RC__ : Q6q3.RunConsts}.
Context {BAND : Band}.
Hypothesis BCAP : band_lo <= Q6q3.alloc_ceiling + 4096.

Lemma munch_floor : forall lo lo' hi D E m m', lo <= lo' -> munch [(lo', hi); (D, E)] m m' -> munch [(lo, hi); (D, E)] m m'.
Proof. intros lo lo' hi D E m m' H MU x Hx. apply MU. cbn [outside] in *. destruct Hx as (H1 & H2 & _). split; [lia | split; [exact H2 | exact I]]. Qed.

Lemma isnp_post_floor : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (D : Z) (dn : nat) (junkd : list byte)
(P : Z -> list byte -> Prop) (lo lo' : Z) (m : word -> option byte) (ms' : machine_state),
lo <= lo' -> lo' <= bv_unsigned sp -> stk asegs m lo lo' -> (D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) ->
isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd P lo' m ms' ->
isnp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd P lo m ms'.
Proof.
intros until ms'. intros Hl Hh STL DD (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & Ft & fc' & m' & r & o & -> & MU & WM & MI' & FRM' & FREG & ST' & Hr & HP & CELLS).
exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, Ft, fc', m', r, o.
split; [reflexivity|]. split; [eapply munch_floor; eassumption|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FREG|].
split.
{ eapply (stk_merge asegs m' lo lo' (bv_unsigned sp)); [ | exact ST' | lia].
eapply (stk_transport_disjoint asegs _ m m'); [exact STL | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
split; [exact Hr|]. split; [exact HP | exact CELLS].
Qed.

Lemma isnp_pre_floor : forall sp a0 a1 fc m D n dn junkd need lo,
isnp_pre (@IKG.ISH BAND) Q6q3.alloc_ceiling sp a0 a1 fc m D n dn junkd need lo ->
lo <= bv_unsigned sp - 8160 /\ bv_unsigned sp - 8160 <= bv_unsigned sp /\ stk asegs m lo (bv_unsigned sp - 8160) /\
(D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D) /\
isnp_pre0 sp a0 a1 fc m D n dn junkd need (bv_unsigned sp - 8160).
Proof.
intros until lo. intros (Ha0 & Ha1 & DST & RT & Hdn & Hn & ST & LOS & BLO & SP47 & MI & FRM & DD1 & DAPP & RD).
unfold SNP_STACK_A in LOS.
destruct (stk_split asegs m lo (bv_unsigned sp - 8160) (bv_unsigned sp) ST ltac:(lia)) as [STL STH].
split; [lia|]. split; [lia|]. split; [exact STL|]. split; [exact DD1|].
unfold isnp_pre0. split; [exact Ha0|]. split; [exact Ha1|]. split; [exact DST|]. split; [exact RT|]. split; [exact Hdn|]. split; [exact Hn|].
split; [exact STH|]. split; [lia|]. split; [lia|]. split; [exact SP47|]. split; [exact MI|]. split; [exact FRM|].
split; [destruct DD1 as [H|H]; [left; lia | right; exact H]|]. split; [exact DAPP | exact RD].
Qed.

Theorem isnprintf_ld_inst : isnprintf_ld_stmt (@IKG.ISH BAND) Q6q3.alloc_ceiling.
Proof.
unfold isnprintf_ld_stmt, isnprintf_l_stmt. intros until lo. intros PRE Ha2.
destruct (isnp_pre_floor _ _ _ _ _ _ _ _ _ _ _ PRE) as (H1 & H2 & STL & DD & PRE0).
eapply OE.evt_mono; [eapply snp_ld_raw; [exact PRE0 | exact Ha2] |].
intros ms' POST. eapply isnp_post_floor; [exact H1 | exact H2 | exact STL | exact DD | exact POST].
Qed.
Theorem isnprintf_lu_inst : isnprintf_lu_stmt (@IKG.ISH BAND) Q6q3.alloc_ceiling.
Proof.
unfold isnprintf_lu_stmt, isnprintf_l_stmt. intros until lo. intros PRE Ha2.
destruct (isnp_pre_floor _ _ _ _ _ _ _ _ _ _ _ PRE) as (H1 & H2 & STL & DD & PRE0).
eapply OE.evt_mono; [eapply snp_lu_raw; [exact PRE0 | exact Ha2] |].
intros ms' POST. eapply isnp_post_floor; [exact H1 | exact H2 | exact STL | exact DD | exact POST].
Qed.
Theorem isnprintf_u00cc_inst : isnprintf_u00cc_stmt (@IKG.ISH BAND) Q6q3.alloc_ceiling.
Proof.
unfold isnprintf_u00cc_stmt. intros until lo. intros PRE Ha2 Hc1 Ha3 Hc2 Ha4.
destruct (isnp_pre_floor _ _ _ _ _ _ _ _ _ _ _ PRE) as (H1 & H2 & STL & DD & PRE0).
eapply OE.evt_mono; [eapply snp_u00cc_raw; [exact PRE0 | exact Ha2 | exact Hc1 | exact Ha3 | exact Hc2 | exact Ha4] |].
intros ms' POST. eapply isnp_post_floor; [exact H1 | exact H2 | exact STL | exact DD | exact POST].
Qed.
End Wrap.

