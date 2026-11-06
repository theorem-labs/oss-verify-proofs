(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf
X0id X0i7 X0hz X0ge X0hs
X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc
X0e6 X0dd X0de X0dg X0di X0df X0dj X0dk X0dl X0dm X0dn X0do X0dp
X0dq X0dx X0dy X0dz X0e0 X0e1 X0e2 X0e3 X0dr X0ds X0dt X0f4 X0g3.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X18s X18k X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X140 X144 X145 X146 X147 X148 X149 X14a X14b X14i X14j X14k X14l X14m X14n X14o X14c X14d X14e X15p X16o.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X141 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X143 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X144 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X145 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X146 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X147 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X148 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X149 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o.
Import ListNotations.
Open Scope Z_scope.

Theorem rta_free_sec : drain_stmt -> fixed_commit_node ->
forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (k : nat) (s : secst),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (s_ubeg s) -> tp = Z_to_bv 64 0x638c98 ->
ART_A Σ m -> mem_inv bsegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
nth_error (sec Σ) k = Some s -> s_quar s = false ->
cps bsegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RTA Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (s_ubeg s) lo m).
Proof.
intros DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k s
FDO MST -> -> ART0 MI0 CALL UWOK Hk Hq.
intros TT cf Hc0 Hk'.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
assert (HLO2 : lo + 0x10000 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (Husp : bv_unsigned sp + 16 <= USTACK_TOP) by exact SPT.
assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 (s_ubeg s)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
evt bsegs (segA_post_s Σ k s ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (segA_evt_s Σ k s ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
ART0 MI0 CALL UWOK Hk Hq)).
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
intros c1 Hc1.
apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [m4 Hc1].
pose proof Hc1 as (_ & (_ & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
pose proof (free_s_wf Σ m k s _ ART0 Hk Hq Dok Dinv) as HW1.
pose proof (pend_e_s Σ m k s (fst (depot_put (dep Σ) tr)) ART0 Hk Hq) as HP.
assert (Hc1' : AST SEGTOP_A (rtA_allow (free_s Σ k s (fst (depot_put (dep Σ) tr))))
(eq (enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (s_mb s + 6128) (s_n s) gp y0 y1 y2 y3 y4 y5
s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4))
(fun mo => ARTM_A (free_s Σ k s (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
{ eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
intros mo (HM & HP'). split; [|exact HP']. apply (artm_maps Σ); [reflexivity | apply (rt_maps_fs Σ k s _ Hk) | apply (rt_eager_fs Σ k s _ Hk) | exact HM]. }
exact (enq_stage Σ (free_s Σ k s (fst (depot_put (dep Σ) tr))) PMc
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m m4 lo
(s_mb s + 6128) (s_n s) (s_ubeg s) TT
DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk' c1 Hc1').
Qed.

Theorem rta_free : drain_stmt -> fixed_commit_node -> free_contract RTA.
Proof.
intros DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
FDO MST Hin Ea0 Etp HA MI CALL UWOK.
pose proof (ART_wf Σ m HA) as (_ & _ & (_ & _ & V3 & _) & _).
destruct (V3 p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & Hsn & ->)].
- exact (rta_free_prim DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
c i n FDO MST Ea0 Etp HA MI CALL UWOK Hc Hn).
- destruct (In_nth_error _ _ Hs) as (k & Hk).
exact (rta_free_sec DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
k s FDO MST Ea0 Etp HA MI CALL UWOK Hk Hq).
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Theorem rta_free_sec : drain_stmt -> fixed_commit_node ->
forall (Σ : rtsA) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (k : nat) (s : secst),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 (s_ubeg s) -> tp = Z_to_bv 64 0x630458 ->
ART_A Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo -> unwind_ch m ra s0 sp ->
nth_error (sec Σ) k = Some s -> s_quar s = false ->
cps asegs (ASTA RTA Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF RTA Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (s_ubeg s) lo m).
Proof.
intros DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k s
FDO MST -> -> ART0 MI0 CALL UWOK Hk Hq.
intros TT cf Hc0 Hk'.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
assert (HLO : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL, STACK_WIN in *; lia).
assert (HLO2 : lo + 0x10000 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (Husp : bv_unsigned sp + 16 <= USTACK_TOP) by exact SPT.
assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 (s_ubeg s)) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m) ms ->
evt asegs (segA_post_s Σ k s ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms)
by (intros ms <-; exact (segA_evt_s Σ k s ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
ART0 MI0 CALL UWOK Hk Hq)).
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
intros c1 Hc1.
apply AST_exI in Hc1 as [tr Hc1]. apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [m4 Hc1].
pose proof Hc1 as (_ & (_ & ART4 & Htr & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
pose proof (free_s_wf Σ m k s _ ART0 Hk Hq Dok Dinv) as HW1.
pose proof (pend_e_s Σ m k s (fst (depot_put (dep Σ) tr)) ART0 Hk Hq) as HP.
assert (Hc1' : AST SEGTOP_A (rtA_allow (free_s Σ k s (fst (depot_put (dep Σ) tr))))
(eq (enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (s_mb s + 6128) (s_n s) gp y0 y1 y2 y3 y4 y5
s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4))
(fun mo => ARTM_A (free_s Σ k s (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
{ eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
intros mo (HM & HP'). split; [|exact HP']. apply (artm_maps Σ); [reflexivity | apply (rt_maps_fs Σ k s _ Hk) | apply (rt_eager_fs Σ k s _ Hk) | exact HM]. }
exact (enq_stage Σ (free_s Σ k s (fst (depot_put (dep Σ) tr))) PMc
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m m4 lo
(s_mb s + 6128) (s_n s) (s_ubeg s) TT
DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk' c1 Hc1').
Qed.

Theorem rta_free : drain_stmt -> fixed_commit_node -> free_contract RTA.
Proof.
intros DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
FDO MST Hin Ea0 Etp HA MI CALL UWOK.
pose proof (ART_wf Σ m HA) as (_ & _ & (_ & _ & V3 & _) & _).
destruct (V3 p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & Hsn & ->)].
- exact (rta_free_prim DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
c i n FDO MST Ea0 Etp HA MI CALL UWOK Hc Hn).
- destruct (In_nth_error _ _ Hs) as (k & Hk).
exact (rta_free_sec DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
k s FDO MST Ea0 Etp HA MI CALL UWOK Hk Hq).
Qed.
