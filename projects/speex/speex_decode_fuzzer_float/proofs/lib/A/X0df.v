(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0j6
X0id X0go X0i7 X0hz X0ge X0hs X0gu
X0fy X0fg X0da X0g4 X0d8 X0fq X0eo X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc
X0dd X0de.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X19p X18y X179 X18s X18k X16z X18d X17f X16j X161 X13v X16p X13t X16b X159 X15l X14p X14t X13u X14q X13w X13x X13y X13z.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X179 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X159 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13z.
Import ListNotations.
Open Scope Z_scope.

Lemma artm_eq : forall Σ Σ' mo, lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
intros Σ Σ' mo E1 E2 E3 (A1 & A2 & A3 & A4 & AS).
unfold ARTM_A, artm_sys, confined0, rt_maps in *. rewrite E1, E2, E3. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
exact AS.
Qed.

Lemma rt_eager_fp : forall Σ c i n p D' l, 1 <= c <= 31 -> rt_eager (set_ql (free_p Σ c i n p D') l) = rt_eager Σ.
Proof.
intros Σ c i n p D' l Hc. unfold rt_eager, set_ql, free_p. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity].
Qed.

Lemma fe_dep : forall Σ m tr, ART_A Σ m -> (In tr T_MAIN /\ (1 <= length tr <= 5)%nat) ->
depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) /\ dep_inv (fst (depot_put (dep Σ) tr)).
Proof.
intros Σ m tr HA Htr. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
assert (TRM : In tr T_MAIN /\ (length tr <= 5)%nat) by (destruct Htr as (H1 & H2); split; [exact H1 | lia]).
destruct TRM as (TRM & TRL).
split; [apply (qc_depot_ok_put_ok _ _ _ _ _ DOK DN); lia | exact (dep_inv_put _ _ DINV TRM ltac:(lia))].
Qed.

Theorem rta_free_app : forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x638c98 ->
ART_A Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)] -> nth_error (r_st (pr Σ 24)) j0 = Some CkBatch ->
(length ents < 1021)%nat -> X16j.qbytes (ql Σ) + n <= 0x100000 ->
cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RTA Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n pre j0 ents
FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HQL Hj0 HL HBY.
intros TT cf Hc0 Hk.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
assert (W1 : evt bsegs
(fun ms => exists (tr : list Z) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ ART_A (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
(pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])) m'
/\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo usp
/\ rt_pres (live_remove (p_ubeg (l_SB (lay Σ)) c i n) (live Σ)) (frames Σ) usp m m')
(entry_st ra sp gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)).
{ eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
ART0 MI0 CALL UWOK Hc Hn)|].
intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
eapply evt_mono; [apply (app_run Σ c i n (fst (depot_put (dep Σ) tr)) pre j0 ents usp (ART_wf Σ m ART0) Hc Hn HQL Hj0 Hsp
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
eq_refl ART4 Dok MI4 ST4 HLO HLO2 Husp ICF FR4 HL HBY)|].
intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & -> & ART' & MI' & WM' & ST' & MWa).
exists tr, z3, z0, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m'. split; [reflexivity|].
split; [exact (c_ART _ _ (app_wf Σ m c i n _ pre j0 ents ART0 Hc Hn Dok Dinv HQL HL HBY) ART')|].
split; [exact MI'|]. split; [exact (wmono_trans bsegs _ _ _ WM4 WM')|]. split; [exact ST'|].
intros a Ha. rewrite (MWa a).
- exact (RP4 a Ha).
- pose proof (geo_of_ART Σ m ART0) as HG.
assert (HO : outside (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 j0) usp) (bv_unsigned a)).
{ apply (kv_client Σ _ [(24, j0); (24, j0)] [] [] usp HG
(se_img Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_slot Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_secmap Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
ltac:(apply Forall_forall; intros; exact I) (live_remove (p_ubeg (l_SB (lay Σ)) c i n) (live Σ))); [|exact Ha].
intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
pose proof (ART_wf Σ m ART0) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
lazymatch type of W1 with evt bsegs _ ?X => assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc0).
intros c1 Hc1. apply Hk. apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [v Hc1].
exists (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
(pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])), v.
split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. eapply AST_conseq; [exact Hc1| |].
- intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & ART' & MI' & WM' & ST' & RP').
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [split; [exact ART' | split; [exact MI' | exact ST']]|]. exact RP'.
- intros mo (HM & HP). split; [|exact HP].
cbn [ARTM RTA]. apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_fp; exact Hc | exact HM].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma artm_eq : forall Σ Σ' mo, lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
intros Σ Σ' mo E1 E2 E3 (A1 & A2 & A3 & A4 & AS).
unfold ARTM_A, artm_sys, confined0, rt_maps in *. rewrite E1, E2, E3. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
exact AS.
Qed.

Lemma rt_eager_fp : forall Σ c i n p D' l, 1 <= c <= 31 -> rt_eager (set_ql (free_p Σ c i n p D') l) = rt_eager Σ.
Proof.
intros Σ c i n p D' l Hc. unfold rt_eager, set_ql, free_p. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity].
Qed.

Lemma fe_dep : forall Σ m tr, ART_A Σ m -> (In tr T_MAIN /\ (1 <= length tr <= 5)%nat) ->
depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) /\ dep_inv (fst (depot_put (dep Σ) tr)).
Proof.
intros Σ m tr HA Htr. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
assert (TRM : In tr T_MAIN /\ (length tr <= 5)%nat) by (destruct Htr as (H1 & H2); split; [exact H1 | lia]).
destruct TRM as (TRM & TRL).
split; [apply (qc_depot_ok_put_ok _ _ _ _ _ DOK DN); lia | exact (dep_inv_put _ _ DINV TRM ltac:(lia))].
Qed.

Theorem rta_free_app : forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (pre : list (Z * list (Z * Z))) j0 (ents : list (Z * Z)),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x630458 ->
ART_A Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents)] -> nth_error (r_st (pr Σ 24)) j0 = Some CkBatch ->
(length ents < 1021)%nat -> X0fy.qbytes (ql Σ) + n <= 0x100000 ->
cps asegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RTA Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n pre j0 ents
FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HQL Hj0 HL HBY.
intros TT cf Hc0 Hk.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
assert (W1 : evt asegs
(fun ms => exists (tr : list Z) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
/\ ART_A (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
(pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])) m'
/\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo usp
/\ rt_pres (live_remove (p_ubeg (l_SB (lay Σ)) c i n) (live Σ)) (frames Σ) usp m m')
(entry_st ra sp gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)).
{ eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
ART0 MI0 CALL UWOK Hc Hn)|].
intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
eapply evt_mono; [apply (app_run Σ c i n (fst (depot_put (dep Σ) tr)) pre j0 ents usp (ART_wf Σ m ART0) Hc Hn HQL Hj0 Hsp
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
eq_refl ART4 Dok MI4 ST4 HLO HLO2 Husp ICF FR4 HL HBY)|].
intros ms P. destruct P as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m' & -> & ART' & MI' & WM' & ST' & MWa).
exists tr, z3, z0, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m'. split; [reflexivity|].
split; [exact (c_ART _ _ (app_wf Σ m c i n _ pre j0 ents ART0 Hc Hn Dok Dinv HQL HL HBY) ART')|].
split; [exact MI'|]. split; [exact (wmono_trans asegs _ _ _ WM4 WM')|]. split; [exact ST'|].
intros a Ha. rewrite (MWa a).
- exact (RP4 a Ha).
- pose proof (geo_of_ART Σ m ART0) as HG.
assert (HO : outside (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 j0) usp) (bv_unsigned a)).
{ apply (kv_client Σ _ [(24, j0); (24, j0)] [] [] usp HG
(se_img Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_grant Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_slot Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_shad_app Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
(se_secmap Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp) (se_stack Σ j0 j0 CkBatch CkBatch usp HG Hj0 Hj0 Hsp)
ltac:(apply Forall_forall; intros; exact I) (live_remove (p_ubeg (l_SB (lay Σ)) c i n) (live Σ))); [|exact Ha].
intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
pose proof (ART_wf Σ m ART0) as (_ & _ & HV & _). destruct HV as (_ & _ & V3 & _).
destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & ->)|(s & Hs & Hq & Hsn & ->)].
+ left. exists c', i'. split; [exact Hc'|]. split; [exact Hn'|]. split; [reflexivity|].
intros [E|[E|[]]]; injection E as <- <-; rewrite Hj0 in Hn'; discriminate.
+ right. destruct (In_nth_error _ _ Hs) as (k & Hk'). exists k, s. split; [exact Hk'|]. split; [exact Hq|]. split; [exact Hsn|].
split; [reflexivity | intros []]. }
revert HO. apply sub_fp_covered. unfold W_E. cbn [all_covered covered]. clear - Hsp.
split; [left; split; lia|]. split; [right; right; right; left; split; lia|]. split; [right; right; right; right; right; left; split; lia | exact I]. }
lazymatch type of W1 with evt asegs _ ?X => assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc0).
intros c1 Hc1. apply Hk. apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [v Hc1].
exists (set_ql (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)))
(pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents ++ [(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16, n)])])), v.
split; [|split; [reflexivity | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. eapply AST_conseq; [exact Hc1| |].
- intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & ART' & MI' & WM' & ST' & RP').
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [split; [exact ART' | split; [exact MI' | exact ST']]|]. exact RP'.
- intros mo (HM & HP). split; [|exact HP].
cbn [ARTM RTA]. apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_fp; exact Hc | exact HM].
Qed.
