(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf
X0id X0i7 X0hz X0ge X0hs
X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc
X0e6 X0dd X0de X0dg X0di X0df X0dj X0dk X0dl.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X140 X144 X145 X146.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X141 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X143 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X144 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X145 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X146.
Import ListNotations.
Open Scope Z_scope.

Lemma rt_eager_ext : forall Σ Σ', (forall k, r_muser (pr Σ' k) = r_muser (pr Σ k) /\ r_mfa (pr Σ' k) = r_mfa (pr Σ k)) ->
sec Σ' = sec Σ -> sec_nres Σ' = sec_nres Σ -> rt_eager Σ' = rt_eager Σ.
Proof.
intros Σ Σ' H E1 E2. unfold rt_eager. rewrite E1, E2. f_equal. f_equal. apply sum_cls_ext. intros k _.
destruct (H (Z.of_nat k)) as (X1 & X2). rewrite X1, X2. reflexivity.
Qed.

Lemma rt_eager_new : forall Σ c i n p D' cal jB M k, rt_eager (enq_new (free_p Σ c i n p D') cal jB M k) = rt_eager Σ.
Proof.
intros Σ c i n p D' cal jB M k. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
cbn [enq_new set_ql pop24 free_p pr].
destruct (Z.eqb_spec k' 24) as [->|_]; [destruct (Z.eqb_spec 24 c) as [<-|_] | destruct (Z.eqb_spec k' c) as [->|_]];
unfold upd_reg; cbn [r_muser r_mfa]; split; reflexivity.
Qed.

Theorem rta_free_new2 : drain_stmt -> forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (cal : list Z) (jB j0 : nat) (st0 : ckst),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x638c98 ->
ART_A Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
ca Σ 24 = cal ++ [Z.of_nat jB] -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
(j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
\/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat) ->
cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RTA Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
intros DRAIN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n cal jB j0 st0
FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HCA Hj0 Hvar.
intros TT cf Hc0 Hk.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
evt bsegs (fun ms => exists tr : list Z,
enq_post (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
(live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms) ms).
{ intros ms <-.
eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
ART0 MI0 CALL UWOK Hc Hn)|].
intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
eapply evt_mono; [apply (new_enq Σ m c i n tr cal jB j0 st0 usp ART0 Hc Hn HCA Hj0 Hvar Hsp Dok Dinv
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
eq_refl ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4)|].
intros ms P. exists tr. exact P. }
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
intros c1 Hc1. apply AST_exI in Hc1 as [tr Hc1].
apply (fin_from_enq DRAIN Σ (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (p_ubeg (l_SB (lay Σ)) c i n) TT c1 FDO MST
eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp); [|exact Hk].
eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP). split; [|exact HP].
apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_new | exact HM].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma rt_eager_ext : forall Σ Σ', (forall k, r_muser (pr Σ' k) = r_muser (pr Σ k) /\ r_mfa (pr Σ' k) = r_mfa (pr Σ k)) ->
sec Σ' = sec Σ -> sec_nres Σ' = sec_nres Σ -> rt_eager Σ' = rt_eager Σ.
Proof.
intros Σ Σ' H E1 E2. unfold rt_eager. rewrite E1, E2. f_equal. f_equal. apply sum_cls_ext. intros k _.
destruct (H (Z.of_nat k)) as (X1 & X2). rewrite X1, X2. reflexivity.
Qed.

Lemma rt_eager_new : forall Σ c i n p D' cal jB M k, rt_eager (enq_new (free_p Σ c i n p D') cal jB M k) = rt_eager Σ.
Proof.
intros Σ c i n p D' cal jB M k. apply rt_eager_ext; [|reflexivity | reflexivity]. intros k'.
cbn [enq_new set_ql pop24 free_p pr].
destruct (Z.eqb_spec k' 24) as [->|_]; [destruct (Z.eqb_spec 24 c) as [<-|_] | destruct (Z.eqb_spec k' c) as [->|_]];
unfold upd_reg; cbn [r_muser r_mfa]; split; reflexivity.
Qed.

Theorem rta_free_new2 : drain_stmt -> forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (cal : list Z) (jB j0 : nat) (st0 : ckst),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n) -> tp = Z_to_bv 64 0x630458 ->
ART_A Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
ca Σ 24 = cal ++ [Z.of_nat jB] -> nth_error (r_st (pr Σ 24)) j0 = Some st0 ->
(j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
\/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat) ->
cps asegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RTA Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
intros DRAIN Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n cal jB j0 st0
FDO MST -> -> ART0 MI0 CALL UWOK Hc Hn HCA Hj0 Hvar.
intros TT cf Hc0 Hk.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (Husp : usp + 16 <= USTACK_TOP) by exact SPT.
assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 (p_ubeg (l_SB (lay Σ)) c i n)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
evt asegs (fun ms => exists tr : list Z,
enq_post (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
(live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ms) ms).
{ intros ms <-.
eapply evt_cut; [exact (segA_evt Σ c i n ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
ART0 MI0 CALL UWOK Hc Hn)|].
intros ms P. destruct P as (tr & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m4 & -> & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
eapply evt_mono; [apply (new_enq Σ m c i n tr cal jB j0 st0 usp ART0 Hc Hn HCA Hj0 Hvar Hsp Dok Dinv
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m4 lo
eq_refl ART4 MI4 WM4 ST4 HLO HLO2 Husp RP4 ICF FR4)|].
intros ms P. exists tr. exact P. }
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
intros c1 Hc1. apply AST_exI in Hc1 as [tr Hc1].
apply (fin_from_enq DRAIN Σ (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n)
PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo (p_ubeg (l_SB (lay Σ)) c i n) TT c1 FDO MST
eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp); [|exact Hk].
eapply AST_conseq; [exact Hc1 | intros ms H; exact H|]. intros mo (HM & HP). split; [|exact HP].
apply (artm_eq Σ); [reflexivity | reflexivity | apply rt_eager_new | exact HM].
Qed.
