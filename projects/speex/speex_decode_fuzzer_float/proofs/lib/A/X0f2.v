(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf X0j6 X0gd
X0id X0i7 X0hz X0ge X0hs
X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dc
X0e6 X0dd X0de X0dg X0di X0df X0dj X0dk X0dp X0dq X0e3 X0g3
X0fm X0fn.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV RL_freeW RL_freeX RL_freeY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition rl_segA_post (Σ : rtsA) (c : Z) (i : nat) (n : Z) (tr : list Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m'
/\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m'
/\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
/\ rt_pres (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) (bv_unsigned sp) m m'
/\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
/\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46714)
s0 (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16)) s2 s3 s4 s5 s6.

Definition rl_dealloc_entry (sp gp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(p : Z) (m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x46714) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0 (Z_to_bv 64 p)
(Z_to_bv 64 INST) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom asegs).

Theorem rl_dealloc_prim : drain_stmt -> fixed_commit_node ->
forall (Σ : rtsA) PMc (ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (tr : list Z) (tb : list word),
fdfs_only PMc -> mat_stable PMc ->
ART_A Σ m -> mem_inv asegs m ->
1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) -> 1 <= n ->
l_ACEIL (lay Σ) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
stk asegs m lo (bv_unsigned sp + -2128) ->
rw_cells asegs m (bv_unsigned sp + -2056) [C8 (Z_to_bv 64 (bv_unsigned sp + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))] ->
u64arr asegs m (bv_unsigned sp + -2040) (wr_trace tr tb) -> length tb = 255%nat -> In tr T_MAIN /\ (1 <= length tr <= 5)%nat ->
icpt_frame m (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
cps asegs (ASTA RTA Σ PMc (eq (rl_dealloc_entry sp gp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (p_ubeg (l_SB (lay Σ)) c i n) m)))
(rl_postF Σ PMc F fc ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
intros DRAIN FC Σ PMc ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n tr tb
FDO MST ART0 MI0 Hc Hn Hn1 HLO HLO2 Husp ST BC TB HTB Htr ICF0.
intros TT cf Hc0 Hk.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - HLO HLO2; lia).
assert (W1 : forall ms, eq (rl_dealloc_entry sp gp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (p_ubeg (l_SB (lay Σ)) c i n) m) ms ->
evt asegs (rl_segA_post Σ c i n tr ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms).
{ intros ms <-. unfold rl_dealloc_entry. fold usp.
replace (p_ubeg (l_SB (lay Σ)) c i n) with (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16) by (unfold p_ubeg; clear; lia).
eapply evt_mono.
{ apply (segA_run Σ m c i n usp lo tr tb s0 s2 s3 s4 s5 ART0 Hc Hn Hn1 Hsp Husp HLO HLO2 ST MI0 BC TB HTB Htr). }
intros ms P. destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m' & -> & ART' & MI' & WM' & MW' & ST' & FR').
unfold rl_segA_post, enq_entry_st. fold usp. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, m'. split; [reflexivity|].
split; [replace (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16) with (p_abeg (l_SB (lay Σ)) c i + rz_size n) in ART' by (clear; lia); exact ART'|].
split; [exact MI'|]. split; [exact WM'|]. split; [exact ST'|]. split.
{ intros a Ha. exact (MW' a (sa_client Σ m c i n usp ART0 Hc Hn Hn1 Hsp _ Ha)). }
split; [|exact FR'].
apply (icpt_frame_transport (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp)
m m' usp ra s0 s1 s2 s3 s4 s5 ICF0 MW' WM').
pose proof (sa_geo Σ m c i n ART0 Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
unfold W_A1. cbn [disjoint_from].
clear - K20 K23 K26 K27 K31 K33 K4 Hsp. unfold SHB in *. repeat split; try exact I; lia. }
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
intros c1 Hc1. unfold rl_segA_post in Hc1.
apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [m4 Hc1].
pose proof Hc1 as (_ & (_ & ART4 & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
pose proof (free_p_wf Σ m c i n _ ART0 Hc Hn Dok Dinv) as HW1.
pose proof (pend_e_p _ c i n (pend_free_p Σ m c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)) ART0 Hc Hn)) as HP.
assert (Hc1' : AST SEGTOP_A (rtA_allow (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))))
(eq (enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n gp y0 y1 y2 y3 y4 y5
s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4))
(fun mo => ARTM_A (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
{ eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
intros mo (HM & HP'). split; [|exact HP']. apply (artm_eq Σ); [reflexivity | reflexivity | apply X0dp.rt_eager_fp | exact HM]. }
exact (enq_stage Σ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) PMc
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m m4 lo
(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n (p_ubeg (l_SB (lay Σ)) c i n) TT
DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk c1 Hc1').
Qed.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0g8 X0gf X0gg X0gh X04b X0d7 X0bw X0eo X0f1
X0en X0fd X0fp X0fl X0fj X0fo X0j5 X0ft X0ek.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X19p X16y X18y X18s X18k X16z X18d X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13x X14r X13y X13z X141 X143 X140 X144 X145 X14a X14b X14o X16o X167 X168.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X16t X170 X171 X172 X0v9 X13s X12h X159 X15m X158 X15y X16a X166 X164 X169 X19o X16e X155.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X141 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X143 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X144 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X145 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X167 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X168.
Import RL_stmt RL_A2 RL_G RL_FH RL_freeV RL_freeW RL_freeX RL_freeY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition rl_segA_post (Σ : rtsA) (c : Z) (i : nat) (n : Z) (tr : list Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms = enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n gp t0' t1' t2' a5' a6' a7' s7 s8 s9 s10 s11
t3' t4' t5' t6' F fc m'
/\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m'
/\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (bv_unsigned sp + -2208)
/\ rt_pres (live_remove (p_abeg (l_SB (lay Σ)) c i + rz_size n) (live Σ)) (frames Σ) (bv_unsigned sp) m m'
/\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
/\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 0x46800)
s0 (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16)) s2 s3 s4 s5 s6.

Definition rl_dealloc_entry (sp gp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(p : Z) (m : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x46800) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0 (Z_to_bv 64 p)
(Z_to_bv 64 INST) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2056)) (Z_to_bv 64 1) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom bsegs).

Theorem rl_dealloc_prim : drain_stmt -> fixed_commit_node ->
forall (Σ : rtsA) PMc (ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) c i n (tr : list Z) (tb : list word),
fdfs_only PMc -> mat_stable PMc ->
ART_A Σ m -> mem_inv bsegs m ->
1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) -> 1 <= n ->
l_ACEIL (lay Σ) <= lo -> lo + 0x10000 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
stk bsegs m lo (bv_unsigned sp + -2128) ->
rw_cells bsegs m (bv_unsigned sp + -2056) [C8 (Z_to_bv 64 (bv_unsigned sp + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))] ->
u64arr bsegs m (bv_unsigned sp + -2040) (wr_trace tr tb) -> length tb = 255%nat -> In tr T_MAIN /\ (1 <= length tr <= 5)%nat ->
icpt_frame m (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
cps bsegs (ASTA RTA Σ PMc (eq (rl_dealloc_entry sp gp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (p_ubeg (l_SB (lay Σ)) c i n) m)))
(rl_postF Σ PMc F fc ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (p_ubeg (l_SB (lay Σ)) c i n) lo m).
Proof.
intros DRAIN FC Σ PMc ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c i n tr tb
FDO MST ART0 MI0 Hc Hn Hn1 HLO HLO2 Husp ST BC TB HTB Htr ICF0.
intros TT cf Hc0 Hk.
set (usp := bv_unsigned sp) in *.
assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - HLO HLO2; lia).
assert (W1 : forall ms, eq (rl_dealloc_entry sp gp t0 t1 t2 s0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (p_ubeg (l_SB (lay Σ)) c i n) m) ms ->
evt bsegs (rl_segA_post Σ c i n tr ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m) ms).
{ intros ms <-. unfold rl_dealloc_entry. fold usp.
replace (p_ubeg (l_SB (lay Σ)) c i n) with (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16) by (unfold p_ubeg; clear; lia).
eapply evt_mono.
{ apply (segA_run Σ m c i n usp lo tr tb s0 s2 s3 s4 s5 ART0 Hc Hn Hn1 Hsp Husp HLO HLO2 ST MI0 BC TB HTB Htr). }
intros ms P. destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m' & -> & ART' & MI' & WM' & MW' & ST' & FR').
unfold rl_segA_post, enq_entry_st. fold usp. exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, m'. split; [reflexivity|].
split; [replace (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 + 16) with (p_abeg (l_SB (lay Σ)) c i + rz_size n) in ART' by (clear; lia); exact ART'|].
split; [exact MI'|]. split; [exact WM'|]. split; [exact ST'|]. split.
{ intros a Ha. exact (MW' a (sa_client Σ m c i n usp ART0 Hc Hn Hn1 Hsp _ Ha)). }
split; [|exact FR'].
apply (icpt_frame_transport (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp)
m m' usp ra s0 s1 s2 s3 s4 s5 ICF0 MW' WM').
pose proof (sa_geo Σ m c i n ART0 Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
unfold W_A1. cbn [disjoint_from].
clear - K20 K23 K26 K27 K31 K33 K4 Hsp. unfold SHB in *. repeat split; try exact I; lia. }
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc0).
intros c1 Hc1. unfold rl_segA_post in Hc1.
apply AST_exI in Hc1 as [y0 Hc1]. apply AST_exI in Hc1 as [y1 Hc1]. apply AST_exI in Hc1 as [y2 Hc1].
apply AST_exI in Hc1 as [y3 Hc1]. apply AST_exI in Hc1 as [y4 Hc1]. apply AST_exI in Hc1 as [y5 Hc1]. apply AST_exI in Hc1 as [y6 Hc1].
apply AST_exI in Hc1 as [y7 Hc1]. apply AST_exI in Hc1 as [y8 Hc1]. apply AST_exI in Hc1 as [y9 Hc1]. apply AST_exI in Hc1 as [m4 Hc1].
pose proof Hc1 as (_ & (_ & ART4 & MI4 & WM4 & ST4 & RP4 & ICF & FR4) & _ & _).
destruct (fe_dep Σ m tr ART0 Htr) as (Dok & Dinv).
pose proof (free_p_wf Σ m c i n _ ART0 Hc Hn Dok Dinv) as HW1.
pose proof (pend_e_p _ c i n (pend_free_p Σ m c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr)) ART0 Hc Hn)) as HP.
assert (Hc1' : AST SEGTOP_A (rtA_allow (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))))
(eq (enq_entry_st (bv_unsigned sp) (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n gp y0 y1 y2 y3 y4 y5
s7 s8 s9 s10 s11 y6 y7 y8 y9 F fc m4))
(fun mo => ARTM_A (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) mo /\ PMc mo) c1).
{ eapply AST_conseq; [exact Hc1 | intros ms (E & _); symmetry; exact E |].
intros mo (HM & HP'). split; [|exact HP']. apply (artm_eq Σ); [reflexivity | reflexivity | apply X14a.rt_eager_fp | exact HM]. }
exact (enq_stage Σ (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) PMc
ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 F fc m m4 lo
(p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n (p_ubeg (l_SB (lay Σ)) c i n) TT
DRAIN FC FDO MST HW1 HP eq_refl eq_refl eq_refl eq_refl eq_refl HLO HLO2 Husp ART4 MI4 WM4 ST4 RP4 ICF FR4 Hk c1 Hc1').
Qed.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X170 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X171 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X172 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X159 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X158 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X166 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X164 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X169 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X155.

Lemma live_remove_cons_ne : forall p q n l, q <> p -> live_remove p ((q, n) :: l) = (q, n) :: live_remove p l.
Proof. intros p q n l H. unfold live_remove. cbn. replace (q =? p) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.

Lemma In_live_remove : forall p q n l, In (q, n) l -> q <> p -> In (q, n) (live_remove p l).
Proof.
intros p q n l He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
split; [| apply stdpp.base.list_elem_of_In; exact He]. cbn [fst]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

Lemma rbk_old : forall Σ' m' p n0, n0 <= 64512 -> ART_A Σ' m' -> In (p, n0) (live Σ') ->
exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ' c)) i = Some (CkAlloc n0) /\ p = p_ubeg (l_SB (lay Σ')) c i n0.
Proof.
intros Σ' m' p n0 Hn0 HA' Hin'. pose proof (ART_wf Σ' m' HA') as (_ & _ & (_ & _ & V3 & _) & HSW & _).
destruct (V3 p n0 Hin') as [X|(s & Hs & Hq & Hsn & E)]; [exact X|].
exfalso. destruct HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s Hs) as ((Tn1 & _) & _). lia.
Qed.

Lemma rbk_slot : forall Σ' m' p n0, n0 <= 64512 -> ART_A Σ' m' -> In (p, n0) (live Σ') ->
exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ' c)) i = Some (CkAlloc n0) /\ p = p_ubeg (l_SB (lay Σ')) c i n0
/\ p_abeg (l_SB (lay Σ')) c i + 16 <= p /\ p + n0 <= p_abeg (l_SB (lay Σ')) c i + ClassSize c.
Proof.
intros Σ' m' p n0 Hn0 HA' Hin'. destruct (geo_live Σ' m' HA' p n0 Hin') as [(c & i & Hc & Hni & E & Y1 & Y2 & _)|(s & Hs & _ & Hsn & _)].
- exists c, i. split; [exact Hc|]. split; [exact Hni|]. split; [exact E|]. split; [exact Y1 | exact Y2].
- exfalso. pose proof (ART_wf Σ' m' HA') as (_ & _ & _ & HSW & _). destruct HSW as (_ & _ & _ & SW4 & _).
pose proof (proj1 (Forall_forall _ _) SW4 s Hs) as ((Tn1 & _) & _). lia.
Qed.

Lemma rbk_aclient_rm : forall p (l : list (Z * Z)) q0 k0 fr u u' x, u' <= u -> q0 <> p ->
aclient (live_remove p l) fr u x -> aclient (live_remove p ((q0, k0) :: l)) fr u' x.
Proof.
intros p l q0 k0 fr u u' x Hu Hq [H|[H|[H|H]]]; [left; lia | right; left; exact H | | right; right; right; exact H].
right; right; left. destruct H as (p' & n' & Hi & Hx). exists p', n'. split; [|exact Hx]. rewrite (live_remove_cons_ne p q0 k0 l Hq). right. exact Hi.
Qed.

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem)
(p n0 n lo : Z) (bs : list byte) (tr : list Z) (tb : list word) (jp jq jr : list byte).
Hypothesis DRAIN : drain_stmt.
Hypothesis FC : fixed_commit_node.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis Hn0 : n0 <= 64512.
Hypothesis Hin : In (p, n0) (live Σ).
Hypothesis HBS : bytes_at bsegs m p bs.
Hypothesis HLB : Z.of_nat (length bs) = n0.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x10000 + 80 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis MU1 : munch (W_fn (l_T (lay Σ)) (bv_unsigned sp)) m m1.
Hypothesis WM1 : wmono bsegs m m1.
Hypothesis IC1 : rw_cells bsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells bsegs m1 (bv_unsigned sp + -72) [CB 8 jp].
Hypothesis IC3 : rw_cells bsegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr bsegs m1 (bv_unsigned sp + -2120) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells bsegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis IC5 : rw_cells bsegs m1 (bv_unsigned sp + -2144) [CB 8 jq].
Hypothesis IC6 : rw_cells bsegs m1 (bv_unsigned sp + -2160) [CB 8 jr; C8 (Z_to_bv 64 0x68770)].
Hypothesis IC7 : rw_cells bsegs m1 (bv_unsigned sp + -2208)
[C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 realloc_pc); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x466f0)].
Hypothesis Htr : In tr T_MAIN /\ (1 <= length tr <= 5)%nat.
#[local] Notation usp := (bv_unsigned sp).

Lemma rbk_agree : forall (m' : mem) a j, rt_pres (live Σ) (frames Σ) (usp + -2208) m1 m' -> usp + -2208 <= a -> a + j <= USTACK_TOP ->
agree_on (fun x => a <= x < a + j) m1 m'.
Proof. intros m' a j P H1 H2 x Hx. apply P. left. lia. Qed.

Definition rl_B_post (Σ1 : rtsA) (q : Z) : machine_state -> Prop := fun ms =>
exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem),
ms = rl_dealloc_entry (Z_to_bv 64 (usp + -80)) gp t0' t1' t2' (Z_to_bv 64 (usp + -2136)) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc p m3
/\ ART_A Σ1 m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 lo (usp + -2208)
/\ rt_pres (live Σ) (frames Σ) usp m m3
/\ bytes_at bsegs m3 q (firstn (Z.to_nat (Z.min n0 n)) bs)
/\ rw_cells bsegs m3 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells bsegs m3 (usp + -72) [CB 8 jp] /\ rw_cells bsegs m3 (usp + -80) [C8 (Z_to_bv 64 usp)]
/\ icpt_frame m3 (usp + -80) ra s0 s1 s2 s3 s4 s5
/\ rw_cells bsegs m3 (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
/\ u64arr bsegs m3 (usp + -2120) (wr_trace tr tb).

Lemma rbk_B : forall (Σ1 : rtsA) (q : Z), live Σ1 = (q, n) :: live Σ -> frames Σ1 = frames Σ -> rtA_sp0 Σ1 = rtA_sp0 Σ -> 0 < q -> q + n < USTACK_TOP ->
forall ms, (exists m2, ret_stF F fc (Z_to_bv 64 0x4676c) (Z_to_bv 64 (usp + -2136 + -72)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
(Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 (Z_to_bv 64 q) m2 ms
/\ ART_A Σ1 m2 /\ mem_inv bsegs m2 /\ wmono bsegs m1 m2 /\ stk bsegs m2 lo (usp + -2136 + -72)
/\ rt_pres (live Σ) (frames Σ) (usp + -2136 + -72) m1 m2 /\ wr_at bsegs m2 q n /\ acc bsegs m2 q n) ->
evt bsegs (rl_B_post Σ1 q) ms.
Proof using HA Hin HBS HLB Hn Hn0 LOW LOR SPT MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6 IC7 Htr.
intros Σ1 q HL HF HS Hq0 HqU ms (m2 & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->) & ART2 & MI2 & WM2 & ST2 & PR2 & WR2 & AC2).
replace (usp + -2136 + -72) with (usp + -2208) in * by lia.
rewrite (ret_pc_even 0x4676c) by (lia || reflexivity).
assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by lia.
assert (AG : forall a j, usp + -2208 <= a -> a + j <= USTACK_TOP -> agree_on (fun x => a <= x < a + j) m1 m2)
by (intros a j H1 H2; exact (rbk_agree m2 a j PR2 H1 H2)).

assert (Hin1 : In (p, n0) (live Σ1)) by (rewrite HL; right; exact Hin).
assert (Hinq : In (q, n) (live Σ1)) by (rewrite HL; left; reflexivity).
destruct (rbk_old Σ1 m2 p n0 Hn0 ART2 Hin1) as (c & i & Hc & Hni & Ep).
assert (Hn01 : 1 <= n0).
{ pose proof (ART_wf Σ1 m2 ART2) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hni)) as X. cbv beta iota in X. clear - X; lia. }
destruct (ART_chunk Σ1 m2 ART2) as [CP _]. destruct (CP c i (CkAlloc n0) Hc Hni) as (WrA & (b1 & ctx & Hb1 & HD) & _). clear CP.
pose proof (sa_geo Σ1 m2 c i n0 ART2 Hc Hni Hn01) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
set (M := p_abeg (l_SB (lay Σ1)) c i + rz_size n0 - 16) in *.
assert (EpM : p = M + 16) by (rewrite Ep; unfold p_ubeg, M; lia).
pose proof (rta_live_range Σ1 m2 q n ART2 Hinq) as (_ & Rq & _). pose proof (rta_live_range Σ1 m2 p n0 ART2 Hin1) as (Rp0 & Rp & _).
rewrite HS in Rq, Rp. fold (l_ACEIL (lay Σ)) in Rq, Rp. unfold rtA_sp0 in Rq, Rp. fold (l_ACEIL (lay Σ)) in Rq, Rp.
pose proof (af_live_disj RTA rta_art_facts Σ1 m2 q n p n0 [] (live Σ) ART2 HL Hin) as DJ.
set (n' := Z.min n n0) in *.
assert (Hn' : 1 <= n' <= n /\ n' <= n0) by (unfold n'; lia).

assert (SRC : bytes_at bsegs m2 p (firstn (Z.to_nat n') bs)).
{ assert (B0 : bytes_at bsegs m p (firstn (Z.to_nat n') bs)) by (rewrite <- (firstn_skipn (Z.to_nat n') bs) in HBS; exact (proj1 (proj1 (bytes_at_app bsegs m p _ _) HBS))).
assert (LEN : Z.of_nat (length (firstn (Z.to_nat n') bs)) = n') by (rewrite firstn_length_le by lia; lia).
apply (X0ra.bytes_at_agree bsegs m1 m2); [apply (X0ra.bytes_at_agree bsegs m m1 _ _ B0)|]; rewrite LEN.
- intros x Hx. apply MU1. apply (RL_front.fn_client Σ m usp HA Hsp0). right; right; left. exists p, n0. split; [exact Hin | lia].
- intros x Hx. apply PR2. right; right; left. exists p, n0. split; [exact Hin | lia]. }
assert (LENs : length (firstn (Z.to_nat n') bs) = Z.to_nat (Z.min n n0)) by (fold n'; rewrite firstn_length_le by lia; reflexivity).
destruct (fl_CB_of_wr m2 q n q (Z.to_nat n') WR2 ltac:(lia) ltac:(lia)) as (uj & UJ).
pose proof (ART_consts Σ1 m2 ART2) as (_ & _ & _ & _ & _ & _ & _ & ICR).
destruct ICR as (_ & _ & _ & _ & G1 & G2 & _).
assert (SEP : M + 16 + n' <= q \/ q + n' <= M).
{ destruct (rbk_slot Σ1 m2 p n0 Hn0 ART2 Hin1) as (c1 & i1 & Hc1 & Hni1 & Ep1 & Y1 & Y2).
destruct (rbk_slot Σ1 m2 q n ltac:(lia) ART2 Hinq) as (c2 & i2 & Hc2 & Hni2 & Eq2 & Z1 & Z2).
assert (Hne : c1 <> c2 \/ i1 <> i2).
{ destruct (Z.eq_dec c1 c2) as [E1|X]; [|left; exact X]. destruct (Nat.eq_dec i1 i2) as [E2|Y]; [|right; exact Y].
exfalso. subst c2 i2. rewrite Hni1 in Hni2. injection Hni2 as E0. rewrite Ep1, Eq2, E0 in DJ. lia. }
pose proof (slot_apart Σ1 m2 ART2 c1 i1 c2 i2 _ _ Hc1 Hc2 Hni1 Hni2 Hne) as SA. lia. }
eapply evt_mono.
{ rewrite EpM in SRC |- *. replace (Z_to_bv 64 (M + 16)) with (Z_to_bv 64 (M + 16)) by reflexivity.
apply (realloc_B_spec (Z_to_bv 64 0x4676c) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 M q n n0 (bv_unsigned b1) (usp + -2136) ctx
(firstn (Z.to_nat n') bs) uj); try assumption; try (unfold USTACK_TOP in *; lia).
- pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1. exact Rb1.
- assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
pose proof (bv_unsigned_in_range 8 b1) as Rb1; unfold bv_modulus in Rb1; change (2 ^ Z.of_N 8) with 256 in Rb1; apply Z.mod_small; exact Rb1).
rewrite Eb. exact HD. }
intros ms3 (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
fold n' in MU3, DST3.

assert (MUC : munch (W_client Σ1 (usp + -2208)) m2 m3).
{ eapply (munch_weaken _ _ m2 m3); [|exact MU3]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
destruct Hx as (X1 & X2). split; [|exact I].
intros Hpx. destruct (outside_app_inv _ _ _ X2) as (_ & X3). destruct (outside_app_inv _ _ _ X3) as (X4 & _).
refine (not_outside _ q (q + n) x _ ltac:(lia) X4). rewrite HL. left. reflexivity. }
assert (Hsp' : rtA_sp0 Σ1 - STACK_WIN <= usp + -2208) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
assert (DSK : forall a j, l_ACEIL (lay Σ) <= a -> disjoint_from [(q, q + n')] a j) by (intros a j Ha; cbn [disjoint_from]; split; [lia | exact I]).
unfold rl_B_post. exists t0', t1', t2', a6', a7', t3', t4', t5', t6', m3.
assert (Ev : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; unfold USTACK_TOP in *; lia).
split.
{ unfold rl_dealloc_entry. rewrite Ev. replace (usp + -80 + -2128) with (usp + -2208) by lia. replace (usp + -80 + -2056) with (usp + -2136) by lia.
rewrite EpM. reflexivity. }
split; [exact (ART_transport _ Σ1 m2 m3 ART2 MUC WM3 (art_avoid_client Σ1 m2 (usp + -2208) ART2 Hsp'))|].
split; [exact MI3|]. split; [exact (stk_wmono m2 m3 _ _ ST2 WM3)|].
split.
{ intros a Ha. rewrite (MU3 a).
- rewrite (PR2 a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])). exact (MU1 a (RL_front.fn_client Σ m usp HA Hsp0 _ Ha)).
- cbn [outside]. split; [|exact I]. intros Hqa. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
+ lia.
+ destruct Ha as ((lo0 & hi0 & Hin0 & Hlh0) & _). unfold CLIENT_STATIC in Hin0.
pose proof (rta_live_range Σ1 m2 q n ART2 Hinq) as (_ & _ & Rq3). unfold SEGTOP_A in Rq3.
repeat (destruct Hin0 as [E|Hin0]; [injection E as <- <-; lia|]). destruct Hin0.
+ destruct Ha as (p2 & n2 & Hin2 & Hp2).
pose proof (af_live_disj RTA rta_art_facts Σ1 m2 q n p2 n2 [] (live Σ) ART2 HL Hin2) as D. lia.
+ destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
pose proof (af_frames_range RTA rta_art_facts Σ1 m2 f kf ART2 Hinf) as (_ & _ & _ & D). specialize (D q n Hinq). lia.
+ destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
pose proof (af_fshadow_apart RTA rta_art_facts Σ1 m2 f kf ART2 Hinf) as (D & _). specialize (D q n Hinq). lia. }
split; [destruct DST3 as [[_ DB] _]; cbn [cells_bytes cbytes] in DB; rewrite app_nil_r in DB; replace (Z.min n0 n) with n' by (unfold n'; lia); exact DB|].
assert (TR : forall a cs, rw_cells bsegs m1 a cs -> usp + -2208 <= a -> a + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells bsegs m3 a cs).
{ intros a cs C H1 H2. apply (rw_cells_transport bsegs _ m2 m3 _ _ (X0ra.rw_cells_agree bsegs m1 m2 _ _ C (AG a _ H1 H2) WM2) MU3 WM3). apply DSK. lia. }
split; [apply (TR _ _ IC1); cbn [cells_size csize Nat.add]; lia|].
split; [apply (TR _ _ IC2); cbn [cells_size csize Nat.add]; lia|].
split; [apply (TR _ _ IC3); cbn [cells_size csize Nat.add]; lia|].
assert (TB3 : u64arr bsegs m3 (usp + -2120) (wr_trace tr tb)).
{ assert (LW : length (wr_trace tr tb) = 255%nat) by (rewrite wr_trace_length; [exact HTB | rewrite HTB; destruct Htr as (_ & X); lia]).
apply (u64arr_transport bsegs _ m2 m3 _ _ (X0ra.u64arr_agree bsegs m1 m2 _ _ TB1 ltac:(apply AG; [lia | rewrite LW; cbn; lia]) WM2) MU3 WM3). apply DSK. lia. }
split.
{ replace (usp + -80 + -2128) with (usp + -2208) by lia.
split; [exists (Z_to_bv 64 1), (Z_to_bv 64 realloc_pc), (Z_to_bv 64 p), (Z_to_bv 64 n), (Z_to_bv 64 usp)|].
2: split; [exists jr|split; [exists jq|split; [exists (Z_to_bv 64 (Z.of_nat (length tr)))|exists (wr_trace tr tb)]]].
- replace (usp + -80 + -2128) with (usp + -2208) by lia. apply (TR _ _ IC7). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2080) with (usp + -2160) by lia. apply (TR _ _ IC6). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2064) with (usp + -2144) by lia. apply (TR _ _ IC5). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2056) with (usp + -2136) by lia. replace (usp + -80 + -2040) with (usp + -2120) by lia. apply (TR _ _ IC4). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2040) with (usp + -2120) by lia. split; [exact TB3|]. rewrite wr_trace_length; [exact HTB | rewrite HTB; destruct Htr as (_ & X); lia]. }
split; [apply (TR _ _ IC4); cbn [cells_size csize Nat.add]; lia | exact TB3].
Qed.

Theorem rl_back_cps :
cps bsegs (rcore_post F fc Σ PMc (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1)
(fun c => exists (Σ' : rts RTA) (q : Z),
ASTA RTA Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
/\ rt_after_f RTA Σ' usp lo m m'
/\ rt_pres (live_remove p (rt_live RTA Σ)) (rt_frames RTA Σ) usp m m'
/\ wr_at bsegs m' q n /\ acc bsegs m' q n
/\ bytes_at bsegs m' q (firstn (Z.to_nat (Z.min n0 n)) bs)) c
/\ rt_live RTA Σ' = (q, n) :: live_remove p (rt_live RTA Σ) /\ rt_frames RTA Σ' = rt_frames RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
/\ rt_credit RTA Σ' = rt_credit RTA Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q <> p /\ q + n < USTACK_TOP /\ rt_pois RTA Σ' = rt_pois RTA Σ).
Proof using DRAIN FC FDO MST HA Hin HBS HLB Hn Hn0 LOW LOR SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6 IC7 Htr.
intros TT c2 Hc2 Hk. destruct Hc2 as (Σ1 & q & HAST & HL & HF & HS & HCR & Hq0 & Hq16 & HqU & HPO).
apply (cps_realizes bsegs _ _ _ c2 (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST)
(rbk_B Σ1 q HL HF HS Hq0 HqU)) HAST).
intros c3 Hc3. unfold rl_B_post in Hc3.
apply AST_exI in Hc3 as (t0' & Hc3). apply AST_exI in Hc3 as (t1' & Hc3). apply AST_exI in Hc3 as (t2' & Hc3). apply AST_exI in Hc3 as (a6' & Hc3).
apply AST_exI in Hc3 as (a7' & Hc3). apply AST_exI in Hc3 as (t3' & Hc3). apply AST_exI in Hc3 as (t4' & Hc3). apply AST_exI in Hc3 as (t5' & Hc3).
apply AST_exI in Hc3 as (t6' & Hc3). apply AST_exI in Hc3 as (m3 & Hc3).
pose proof Hc3 as (_ & (_ & ART3 & MI3 & ST3 & RP3 & BY3 & J1 & J2 & J3 & ICF3 & BC3 & TB3) & _ & _).
assert (Hin1 : In (p, n0) (live Σ1)) by (rewrite HL; right; exact Hin).
assert (Hinq : In (q, n) (live Σ1)) by (rewrite HL; left; reflexivity).
destruct (rbk_old Σ1 m3 p n0 Hn0 ART3 Hin1) as (c & i & Hc & Hni & Ep).
assert (Hn01 : 1 <= n0).
{ pose proof (ART_wf Σ1 m3 ART3) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hni)) as X. cbv beta iota in X. clear - X; lia. }
assert (Hqp : q <> p) by (pose proof (af_live_disj RTA rta_art_facts Σ1 m3 q n p n0 [] (live Σ) ART3 HL Hin) as D; lia).
assert (HACE : l_ACEIL (lay Σ1) = l_ACEIL (lay Σ)) by (unfold l_ACEIL; unfold rtA_sp0 in HS; rewrite HS; reflexivity).
set (spv := Z_to_bv 64 (usp + -80)) in *.
assert (Ev : bv_unsigned spv = usp + -80) by (apply unsigned_lit; pose proof (rta_sp0_range Σ m HA) as HR0; clear - HR0 LOW LOR SPT; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
assert (Hc3' : ASTA RTA Σ1 PMc (eq (rl_dealloc_entry spv gp t0' t1' t2' (Z_to_bv 64 (usp + -2136)) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (p_ubeg (l_SB (lay Σ1)) c i n0) m3)) c3).
{ unfold ASTA. eapply AST_conseq; [exact Hc3 | intros ms (E & _); rewrite <- Ep; symmetry; exact E | intros mo H; exact H]. }
assert (ST3v : stk bsegs m3 lo (bv_unsigned spv + -2128)) by (rewrite Ev; replace (usp + -80 + -2128) with (usp + -2208) by lia; exact ST3).
assert (BC3v : rw_cells bsegs m3 (bv_unsigned spv + -2056) [C8 (Z_to_bv 64 (bv_unsigned spv + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))])
by (rewrite Ev; replace (usp + -80 + -2056) with (usp + -2136) by lia; replace (usp + -80 + -2040) with (usp + -2120) by lia; exact BC3).
assert (TB3v : u64arr bsegs m3 (bv_unsigned spv + -2040) (wr_trace tr tb)) by (rewrite Ev; replace (usp + -80 + -2040) with (usp + -2120) by lia; exact TB3).
assert (ICF3v : icpt_frame m3 (bv_unsigned spv) ra s0 s1 s2 s3 s4 s5) by (rewrite Ev; exact ICF3).
apply (rl_dealloc_prim DRAIN FC Σ1 PMc ra spv gp t0' t1' t2' (Z_to_bv 64 (usp + -2136)) s1 a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m3 lo c i n0 tr tb
FDO MST ART3 MI3 Hc Hni Hn01 ltac:(rewrite HACE; exact LOW) ltac:(rewrite Ev; clear - LOR; lia) ltac:(rewrite Ev; clear - SPT; lia)
ST3v BC3v TB3v HTB Htr ICF3v TT c3 Hc3').
intros c4 (Σ2 & HAST4 & EL & EF & ELY & EC & EP). rewrite <- Ep in *.
assert (EL2 : live Σ2 = (q, n) :: live_remove p (live Σ)) by (rewrite EL, HL; exact (live_remove_cons_ne p q n (live Σ) Hqp)).
assert (W4 : forall ms, (exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m4 : mem),
ms = rl_ret_st (bv_unsigned spv) gp (Z_to_bv 64 (usp + -2136)) w1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q) (Z_to_bv 64 (usp + -2136))
(Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m4
/\ ART_A Σ2 m4 /\ mem_inv bsegs m4 /\ stk bsegs m4 lo (bv_unsigned spv + -2128)
/\ rt_pres (live_remove p (live Σ1)) (frames Σ1) (bv_unsigned spv) m3 m4
/\ icpt_frame m4 (bv_unsigned spv) ra (Z_to_bv 64 (usp + -2136)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q) (Z_to_bv 64 (usp + -2136))) ->
evt bsegs (fun ms' => exists m5, ret_stF F fc ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m5 ms'
/\ ART_A Σ2 m5 /\ mem_inv bsegs m5 /\ stk bsegs m5 lo usp
/\ rt_pres (live_remove p (live Σ)) (frames Σ) usp m m5
/\ wr_at bsegs m5 q n /\ acc bsegs m5 q n /\ bytes_at bsegs m5 q (firstn (Z.to_nat (Z.min n0 n)) bs)) ms).
{ intros ms (w1 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & -> & ART4 & MI4 & ST4 & RP4 & ICF4).
unfold rl_ret_st. rewrite Ev in *. replace (usp + -80 + -2128) with (usp + -2208) in * by lia.
destruct ICF4 as ((s4r & s3r & s2r & s1r & s0r & R1) & (jr' & R2) & (jq' & R3) & (w' & R4) & (ws & R5 & R5l)).
replace (usp + -80 + -2128) with (usp + -2208) in R1 by lia. replace (usp + -80 + -2080) with (usp + -2160) in R2 by lia. replace (usp + -80 + -2064) with (usp + -2144) in R3 by lia.
replace (usp + -80 + -2056) with (usp + -2136) in R4 by lia. replace (usp + -80 + -2040) with (usp + -2120) in R4, R5 by lia.
assert (AG4 : forall a : word, usp + -80 <= bv_unsigned a < USTACK_TOP -> m4 a = m3 a) by (intros a Ha; apply RP4; left; exact Ha).
pose proof (X0ra.rw_cells_agree_nw bsegs m3 m4 _ _ J1 ltac:(intros a Ha; apply AG4; cbn [cells_size csize Nat.add] in Ha; lia)) as J1'.
pose proof (X0ra.rw_cells_agree_nw bsegs m3 m4 _ _ J2 ltac:(intros a Ha; apply AG4; cbn [cells_size csize Nat.add] in Ha; lia)) as J2'.
pose proof (X0ra.rw_cells_agree_nw bsegs m3 m4 _ _ J3 ltac:(intros a Ha; apply AG4; cbn [cells_size csize Nat.add] in Ha; lia)) as J3'.
pose proof (ART_wf Σ2 m4 ART4) as HW2. pose proof (geo_of_wf Σ2 HW2) as HG2.
assert (HA2 : l_ACEIL (lay Σ2) <= usp - 2208) by (rewrite ELY, HACE; clear - LOW LOR; lia).
assert (Hinq2 : In (q, n) (live Σ2)) by (rewrite EL2; left; reflexivity).
pose proof (rta_live_range Σ2 m4 q n ART4 Hinq2) as (_ & Rq & _). unfold rtA_sp0 in Rq. fold (l_ACEIL (lay Σ2)) in Rq.
eapply evt_mono.
{ apply (realloc_C_spec ra sp gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 (usp + -2136)) w1 y3 y4 y5 y6 y7 y8 y9 y10 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0))
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 y11 y12 y13 y14 (Z_to_bv 64 0x46800) s0 s1 s2 s3 s4 s5 s6
s0r s1r s2r s3r s4r F fc m4 q lo ws w' jp jq' jr'); try assumption.
all: try (pose proof (rta_sp0_range Σ m HA) as HR0; clear - HR0 LOW LOR SPT Hq0 HqU Hn; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia). }
intros ms5 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & -> & MU5 & WM5 & MI5 & ST5).
assert (ART5 : ART_A Σ2 m5).
{ apply c_ART; [exact HW2|]. apply (ARTc_stack Σ2 (usp - 2208) usp HG2 HA2 m4 m5 (ART_c _ _ ART4) MU5 WM5).
- destruct HW2 as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
- destruct HW2 as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK. }
exists m5. split; [exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13; reflexivity|].
split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|].
split.
{ intros a Ha.
assert (Ha2 : aclient (live Σ2) (frames Σ2) usp (bv_unsigned a)).
{ rewrite EL2, EF, HF. destruct Ha as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
right; right; left. destruct H as (p' & n' & Hi & Hx). exists p', n'. split; [right; exact Hi | exact Hx]. }
destruct (X155.aclient_split Σ2 m4 usp _ ART4 Ha2) as [X|X].
- rewrite (MU5 a) by (cbn [outside]; split; [lia | exact I]).
rewrite (RP4 a) by (rewrite HL, HF; exact (rbk_aclient_rm p (live Σ) q n (frames Σ) usp (usp + -80) _ ltac:(lia) Hqp Ha)).
exact (RP3 a (aclient_live_remove _ _ _ _ _ Ha)).
- rewrite (MU5 a) by (cbn [outside]; split; [lia | exact I]).
rewrite (RP4 a) by (rewrite HL, HF; exact (rbk_aclient_rm p (live Σ) q n (frames Σ) usp (usp + -80) _ ltac:(lia) Hqp Ha)).
exact (RP3 a (aclient_live_remove _ _ _ _ _ Ha)). }
destruct (af_acc_live RTA rta_art_facts Σ2 m5 q n ART5 Hinq2) as (WR5 & AC5).
split; [exact WR5|]. split; [exact AC5|].
assert (LEN : Z.of_nat (length (firstn (Z.to_nat (Z.min n0 n)) bs)) <= n) by (rewrite firstn_length; lia).
apply (bytes_at_transport bsegs _ m4 m5 _ _ (X0ra.bytes_at_agree bsegs m3 m4 _ _ BY3 ltac:(intros x Hx; apply RP4; right; right; left; exists q, n;
split; [rewrite HL; rewrite (live_remove_cons_ne p q n (live Σ) Hqp); left; reflexivity | lia])) MU5).
cbn [disjoint_from]. split; [lia | exact I]. }
apply (cps_realizes bsegs _ _ _ c4 (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W4) HAST4).
intros c5 Hc5. apply Hk. exists Σ2, q.
cbn [rt_live rt_frames rt_sp0 rt_credit rt_pois RTA]. unfold rtA_live, rtA_frames, rtA_credit.
split; [|split; [exact EL2 | split; [exact (eq_trans EF HF) | split; [unfold rtA_sp0; rewrite ELY; exact HS | split; [rewrite EC; exact HCR |
split; [exact Hq0 | split; [exact Hq16 | split; [exact Hqp | split; [exact HqU | exact (eq_trans EP HPO)]]]]]]]]].
unfold ASTA. eapply AST_conseq; [exact Hc5| |intros mo H; exact H].
intros ms (m5 & RS & A5 & MI5 & ST5 & RP5 & WR5 & AC5 & BY5).
exists m5. split; [exact RS|]. split; [split; [exact A5 | split; [exact MI5 | exact ST5]]|].
split; [exact RP5|]. split; [exact WR5|]. split; [exact AC5 | exact BY5].
Qed.

End Back.

Theorem rta_realloc_of : core_stmt_realloc -> drain_stmt -> fixed_commit_node -> realloc_contract RTA.
Proof.
intros CP DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo bs
FDO MST Hin Hn Hn0 Ha0 Ha1 Htp HBS HLB Hlen Hcr ART0 MI0 CALL LOR80 UWOK. subst a0 a1 tp.
intros TT cf Hc Hkk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0, Hin.
unfold rtA_live, rtA_credit in Hlen, Hcr, Hin.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & _ & _ & GT5).
pose proof (geo_grant Σ m ART0 (l_TCX (lay Σ)) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (GX1 & _ & _ & _ & GX5).
assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
destruct (site_trace_main m realloc_pc (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) ra s0 sp ltac:(right; right; right; left; reflexivity) UWOK ltac:(lia))
as (ch & tr & CHC & HTR & Htr & Htrl).
destruct (ART_ia Σ m ART0) as (b & IS).
pose proof (rta_live_range Σ m p n0 ART0 Hin) as (Rp0 & Rp & _). pose proof (rta_sp0_range Σ m ART0) as Rs0. unfold rtA_sp0 in Rp, Rs0.

pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & _ & _ & _ & ICR).
destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
& I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & _).
destruct (stk_two_words m (l_T (lay Σ) + 2856) ltac:(destruct (stk_split bsegs m (l_T (lay Σ) + 2768) (l_T (lay Σ) + 2856) (l_T (lay Σ) + 3168) I32 ltac:(lia)) as [_ X];
destruct (stk_split bsegs m (l_T (lay Σ) + 2856) (l_T (lay Σ) + 2872) (l_T (lay Σ) + 3168) X ltac:(lia)) as [X' _];
replace (l_T (lay Σ) + 2856 + 16) with (l_T (lay Σ) + 2872) by lia; exact X')) as (rc & rd & STATS).
assert (W1 : evt bsegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo rc rd tr m)
(entry_st ra sp gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_realloc m)).
{ unfold entry_st, e_realloc.
apply (realloc_A_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n
(l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b ch tr rc rd); try assumption.
all: try (unfold RT_STACK, USTACK_TOP, STACK_WIN, SEGTOP_A, kHighShadowEnd in *; lia). }
assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_realloc m) ms ->
evt bsegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo rc rd tr m) ms)
by (intros ms <-; exact W1).
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. unfold realloc_A_post in Hc1.
apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (jr & Hc1).
apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
destruct Hc1 as (HM & HPm & HPM & HZ).
destruct HPm as (Hms & MU1 & WM1 & MI1 & IS1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & IC6 & IC7 & AFr & J0 & UB1 & STATS1 & ST1).
assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
pose proof (RL_front.fn_ART Σ m (bv_unsigned sp) ART0 Hsp0 m1 MU1 WM1 IS1 UB1) as ART1.
set (usp := bv_unsigned sp) in *.
assert (Hc2 : ASTA RTA Σ PMc (eq (rcore_entry Σ (usp + -2136) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n m1)) c1).
{ split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold rcore_entry.
replace (usp + -2136 + -200) with (usp + -2336) by lia. reflexivity. }
assert (ST1' : stk bsegs m1 lo (usp + -2136 + -200)) by (replace (usp + -2136 + -200) with (usp + -2336) by lia; exact ST1).
assert (TRC : trc_cells (usp + -2136) tr m1 tb).
{ split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact IC4|]. split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact TB1 | exact HTB]. }
assert (AFC : raf_cells (usp + -2136) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
{ split; replace (usp + -2136 + -200) with (usp + -2336) by lia; [exact AFr | exact J0]. }
assert (LOR' : lo + 0x1000 <= usp + -2136 + -200) by (unfold RT_STACK in LOR; lia).
assert (SPT' : usp + -2136 + 2144 <= USTACK_TOP) by lia.
assert (SPA' : (usp + -2136) mod 16 = 8).
{ pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq].
replace (usp + -2136) with (8 + (q - 134) * 16) by lia. rewrite Z_mod_plus_full. reflexivity. }
assert (K : forall c2, rcore_post F fc Σ PMc (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1 c2 -> realizes bsegs c2 TT).
{ intros c2 Hc2'. exact (rl_back_cps Σ PMc F fc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 p n0 n lo bs tr tb jp jq jr
DRAIN FC FDO MST Hn Hn0 Hin HBS HLB ART0 LOW' ltac:(unfold RT_STACK in LOR80; exact LOR80) SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB
IC4 IC5 IC6 IC7 (conj Htr Htrl) TT c2 Hc2' Hkk). }
exact (CP Σ PMc m1 (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
FDO MST Hn Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.
End B_TWIN.

Lemma live_remove_cons_ne : forall p q n l, q <> p -> live_remove p ((q, n) :: l) = (q, n) :: live_remove p l.
Proof. intros p q n l H. unfold live_remove. cbn. replace (q =? p) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.

Lemma In_live_remove : forall p q n l, In (q, n) l -> q <> p -> In (q, n) (live_remove p l).
Proof.
intros p q n l He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
split; [| apply stdpp.base.list_elem_of_In; exact He]. cbn [fst]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

Lemma rbk_old : forall Σ' m' p n0, n0 <= 64512 -> ART_A Σ' m' -> In (p, n0) (live Σ') ->
exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ' c)) i = Some (CkAlloc n0) /\ p = p_ubeg (l_SB (lay Σ')) c i n0.
Proof.
intros Σ' m' p n0 Hn0 HA' Hin'. pose proof (ART_wf Σ' m' HA') as (_ & _ & (_ & _ & V3 & _) & HSW & _).
destruct (V3 p n0 Hin') as [X|(s & Hs & Hq & Hsn & E)]; [exact X|].
exfalso. destruct HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s Hs) as ((Tn1 & _) & _). lia.
Qed.

Lemma rbk_slot : forall Σ' m' p n0, n0 <= 64512 -> ART_A Σ' m' -> In (p, n0) (live Σ') ->
exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ' c)) i = Some (CkAlloc n0) /\ p = p_ubeg (l_SB (lay Σ')) c i n0
/\ p_abeg (l_SB (lay Σ')) c i + 16 <= p /\ p + n0 <= p_abeg (l_SB (lay Σ')) c i + ClassSize c.
Proof.
intros Σ' m' p n0 Hn0 HA' Hin'. destruct (geo_live Σ' m' HA' p n0 Hin') as [(c & i & Hc & Hni & E & Y1 & Y2 & _)|(s & Hs & _ & Hsn & _)].
- exists c, i. split; [exact Hc|]. split; [exact Hni|]. split; [exact E|]. split; [exact Y1 | exact Y2].
- exfalso. pose proof (ART_wf Σ' m' HA') as (_ & _ & _ & HSW & _). destruct HSW as (_ & _ & _ & SW4 & _).
pose proof (proj1 (Forall_forall _ _) SW4 s Hs) as ((Tn1 & _) & _). lia.
Qed.

Lemma rbk_aclient_rm : forall p (l : list (Z * Z)) q0 k0 fr u u' x, u' <= u -> q0 <> p ->
aclient (live_remove p l) fr u x -> aclient (live_remove p ((q0, k0) :: l)) fr u' x.
Proof.
intros p l q0 k0 fr u u' x Hu Hq [H|[H|[H|H]]]; [left; lia | right; left; exact H | | right; right; right; exact H].
right; right; left. destruct H as (p' & n' & Hi & Hx). exists p', n'. split; [|exact Hx]. rewrite (live_remove_cons_ne p q0 k0 l Hq). right. exact Hi.
Qed.

Section Back.
Variables (Σ : rtsA) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m m1 : mem)
(p n0 n lo : Z) (bs : list byte) (tr : list Z) (tb : list word) (jp jq jr : list byte).
Hypothesis DRAIN : drain_stmt.
Hypothesis FC : fixed_commit_node.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis Hn0 : n0 <= 64512.
Hypothesis Hin : In (p, n0) (live Σ).
Hypothesis HBS : bytes_at asegs m p bs.
Hypothesis HLB : Z.of_nat (length bs) = n0.
Hypothesis HA : ART_A Σ m.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x10000 + 80 <= bv_unsigned sp.
Hypothesis SPT : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis MU1 : munch (W_fn (l_T (lay Σ)) (bv_unsigned sp)) m m1.
Hypothesis WM1 : wmono asegs m m1.
Hypothesis IC1 : rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis IC2 : rw_cells asegs m1 (bv_unsigned sp + -72) [CB 8 jp].
Hypothesis IC3 : rw_cells asegs m1 (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))].
Hypothesis TB1 : u64arr asegs m1 (bv_unsigned sp + -2120) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis IC4 : rw_cells asegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis IC5 : rw_cells asegs m1 (bv_unsigned sp + -2144) [CB 8 jq].
Hypothesis IC6 : rw_cells asegs m1 (bv_unsigned sp + -2160) [CB 8 jr; C8 (Z_to_bv 64 0x68684)].
Hypothesis IC7 : rw_cells asegs m1 (bv_unsigned sp + -2208)
[C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 realloc_pc); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x46604)].
Hypothesis Htr : In tr T_MAIN /\ (1 <= length tr <= 5)%nat.
#[local] Notation usp := (bv_unsigned sp).

Lemma rbk_agree : forall (m' : mem) a j, rt_pres (live Σ) (frames Σ) (usp + -2208) m1 m' -> usp + -2208 <= a -> a + j <= USTACK_TOP ->
agree_on (fun x => a <= x < a + j) m1 m'.
Proof. intros m' a j P H1 H2 x Hx. apply P. left. lia. Qed.

Definition rl_B_post (Σ1 : rtsA) (q : Z) : machine_state -> Prop := fun ms =>
exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem),
ms = rl_dealloc_entry (Z_to_bv 64 (usp + -80)) gp t0' t1' t2' (Z_to_bv 64 (usp + -2136)) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc p m3
/\ ART_A Σ1 m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo (usp + -2208)
/\ rt_pres (live Σ) (frames Σ) usp m m3
/\ bytes_at asegs m3 q (firstn (Z.to_nat (Z.min n0 n)) bs)
/\ rw_cells asegs m3 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m3 (usp + -72) [CB 8 jp] /\ rw_cells asegs m3 (usp + -80) [C8 (Z_to_bv 64 usp)]
/\ icpt_frame m3 (usp + -80) ra s0 s1 s2 s3 s4 s5
/\ rw_cells asegs m3 (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
/\ u64arr asegs m3 (usp + -2120) (wr_trace tr tb).

Lemma rbk_B : forall (Σ1 : rtsA) (q : Z), live Σ1 = (q, n) :: live Σ -> frames Σ1 = frames Σ -> rtA_sp0 Σ1 = rtA_sp0 Σ -> 0 < q -> q + n < USTACK_TOP ->
forall ms, (exists m2, ret_stF F fc (Z_to_bv 64 0x46680) (Z_to_bv 64 (usp + -2136 + -72)) gp (Z_to_bv 64 tpA) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
(Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 (Z_to_bv 64 q) m2 ms
/\ ART_A Σ1 m2 /\ mem_inv asegs m2 /\ wmono asegs m1 m2 /\ stk asegs m2 lo (usp + -2136 + -72)
/\ rt_pres (live Σ) (frames Σ) (usp + -2136 + -72) m1 m2 /\ wr_at asegs m2 q n /\ acc asegs m2 q n) ->
evt asegs (rl_B_post Σ1 q) ms.
Proof using HA Hin HBS HLB Hn Hn0 LOW LOR SPT MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6 IC7 Htr.
intros Σ1 q HL HF HS Hq0 HqU ms (m2 & (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->) & ART2 & MI2 & WM2 & ST2 & PR2 & WR2 & AC2).
replace (usp + -2136 + -72) with (usp + -2208) in * by lia.
rewrite (ret_pc_even 0x46680) by (lia || reflexivity).
assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= usp) by lia.
assert (AG : forall a j, usp + -2208 <= a -> a + j <= USTACK_TOP -> agree_on (fun x => a <= x < a + j) m1 m2)
by (intros a j H1 H2; exact (rbk_agree m2 a j PR2 H1 H2)).

assert (Hin1 : In (p, n0) (live Σ1)) by (rewrite HL; right; exact Hin).
assert (Hinq : In (q, n) (live Σ1)) by (rewrite HL; left; reflexivity).
destruct (rbk_old Σ1 m2 p n0 Hn0 ART2 Hin1) as (c & i & Hc & Hni & Ep).
assert (Hn01 : 1 <= n0).
{ pose proof (ART_wf Σ1 m2 ART2) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hni)) as X. cbv beta iota in X. clear - X; lia. }
destruct (ART_chunk Σ1 m2 ART2) as [CP _]. destruct (CP c i (CkAlloc n0) Hc Hni) as (WrA & (b1 & ctx & Hb1 & HD) & _). clear CP.
pose proof (sa_geo Σ1 m2 c i n0 ART2 Hc Hni Hn01) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
& K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
set (M := p_abeg (l_SB (lay Σ1)) c i + rz_size n0 - 16) in *.
assert (EpM : p = M + 16) by (rewrite Ep; unfold p_ubeg, M; lia).
pose proof (rta_live_range Σ1 m2 q n ART2 Hinq) as (_ & Rq & _). pose proof (rta_live_range Σ1 m2 p n0 ART2 Hin1) as (Rp0 & Rp & _).
rewrite HS in Rq, Rp. fold (l_ACEIL (lay Σ)) in Rq, Rp. unfold rtA_sp0 in Rq, Rp. fold (l_ACEIL (lay Σ)) in Rq, Rp.
pose proof (af_live_disj RTA rta_art_facts Σ1 m2 q n p n0 [] (live Σ) ART2 HL Hin) as DJ.
set (n' := Z.min n n0) in *.
assert (Hn' : 1 <= n' <= n /\ n' <= n0) by (unfold n'; lia).

assert (SRC : bytes_at asegs m2 p (firstn (Z.to_nat n') bs)).
{ assert (B0 : bytes_at asegs m p (firstn (Z.to_nat n') bs)) by (rewrite <- (firstn_skipn (Z.to_nat n') bs) in HBS; exact (proj1 (proj1 (bytes_at_app asegs m p _ _) HBS))).
assert (LEN : Z.of_nat (length (firstn (Z.to_nat n') bs)) = n') by (rewrite firstn_length_le by lia; lia).
apply (X00b.bytes_at_agree asegs m1 m2); [apply (X00b.bytes_at_agree asegs m m1 _ _ B0)|]; rewrite LEN.
- intros x Hx. apply MU1. apply (RL_front.fn_client Σ m usp HA Hsp0). right; right; left. exists p, n0. split; [exact Hin | lia].
- intros x Hx. apply PR2. right; right; left. exists p, n0. split; [exact Hin | lia]. }
assert (LENs : length (firstn (Z.to_nat n') bs) = Z.to_nat (Z.min n n0)) by (fold n'; rewrite firstn_length_le by lia; reflexivity).
destruct (fl_CB_of_wr m2 q n q (Z.to_nat n') WR2 ltac:(lia) ltac:(lia)) as (uj & UJ).
pose proof (ART_consts Σ1 m2 ART2) as (_ & _ & _ & _ & _ & _ & _ & ICR).
destruct ICR as (_ & _ & _ & _ & G1 & G2 & _).
assert (SEP : M + 16 + n' <= q \/ q + n' <= M).
{ destruct (rbk_slot Σ1 m2 p n0 Hn0 ART2 Hin1) as (c1 & i1 & Hc1 & Hni1 & Ep1 & Y1 & Y2).
destruct (rbk_slot Σ1 m2 q n ltac:(lia) ART2 Hinq) as (c2 & i2 & Hc2 & Hni2 & Eq2 & Z1 & Z2).
assert (Hne : c1 <> c2 \/ i1 <> i2).
{ destruct (Z.eq_dec c1 c2) as [E1|X]; [|left; exact X]. destruct (Nat.eq_dec i1 i2) as [E2|Y]; [|right; exact Y].
exfalso. subst c2 i2. rewrite Hni1 in Hni2. injection Hni2 as E0. rewrite Ep1, Eq2, E0 in DJ. lia. }
pose proof (slot_apart Σ1 m2 ART2 c1 i1 c2 i2 _ _ Hc1 Hc2 Hni1 Hni2 Hne) as SA. lia. }
eapply evt_mono.
{ rewrite EpM in SRC |- *. replace (Z_to_bv 64 (M + 16)) with (Z_to_bv 64 (M + 16)) by reflexivity.
apply (realloc_B_spec (Z_to_bv 64 0x46680) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 M q n n0 (bv_unsigned b1) (usp + -2136) ctx
(firstn (Z.to_nat n') bs) uj); try assumption; try (unfold USTACK_TOP in *; lia).
- pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1. exact Rb1.
- assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
pose proof (bv_unsigned_in_range 8 b1) as Rb1; unfold bv_modulus in Rb1; change (2 ^ Z.of_N 8) with 256 in Rb1; apply Z.mod_small; exact Rb1).
rewrite Eb. exact HD. }
intros ms3 (t0' & t1' & t2' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
fold n' in MU3, DST3.

assert (MUC : munch (W_client Σ1 (usp + -2208)) m2 m3).
{ eapply (munch_weaken _ _ m2 m3); [|exact MU3]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
destruct Hx as (X1 & X2). split; [|exact I].
intros Hpx. destruct (outside_app_inv _ _ _ X2) as (_ & X3). destruct (outside_app_inv _ _ _ X3) as (X4 & _).
refine (not_outside _ q (q + n) x _ ltac:(lia) X4). rewrite HL. left. reflexivity. }
assert (Hsp' : rtA_sp0 Σ1 - STACK_WIN <= usp + -2208) by (rewrite HS; unfold l_ACEIL, rtA_sp0 in *; lia).
assert (DSK : forall a j, l_ACEIL (lay Σ) <= a -> disjoint_from [(q, q + n')] a j) by (intros a j Ha; cbn [disjoint_from]; split; [lia | exact I]).
unfold rl_B_post. exists t0', t1', t2', a6', a7', t3', t4', t5', t6', m3.
assert (Ev : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; unfold USTACK_TOP in *; lia).
split.
{ unfold rl_dealloc_entry. rewrite Ev. replace (usp + -80 + -2128) with (usp + -2208) by lia. replace (usp + -80 + -2056) with (usp + -2136) by lia.
rewrite EpM. reflexivity. }
split; [exact (ART_transport _ Σ1 m2 m3 ART2 MUC WM3 (art_avoid_client Σ1 m2 (usp + -2208) ART2 Hsp'))|].
split; [exact MI3|]. split; [exact (stk_wmono m2 m3 _ _ ST2 WM3)|].
split.
{ intros a Ha. rewrite (MU3 a).
- rewrite (PR2 a ltac:(destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha])). exact (MU1 a (RL_front.fn_client Σ m usp HA Hsp0 _ Ha)).
- cbn [outside]. split; [|exact I]. intros Hqa. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
+ lia.
+ destruct Ha as ((lo0 & hi0 & Hin0 & Hlh0) & _). unfold CLIENT_STATIC in Hin0.
pose proof (rta_live_range Σ1 m2 q n ART2 Hinq) as (_ & _ & Rq3). unfold SEGTOP_A in Rq3.
repeat (destruct Hin0 as [E|Hin0]; [injection E as <- <-; lia|]). destruct Hin0.
+ destruct Ha as (p2 & n2 & Hin2 & Hp2).
pose proof (af_live_disj RTA rta_art_facts Σ1 m2 q n p2 n2 [] (live Σ) ART2 HL Hin2) as D. lia.
+ destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
pose proof (af_frames_range RTA rta_art_facts Σ1 m2 f kf ART2 Hinf) as (_ & _ & _ & D). specialize (D q n Hinq). lia.
+ destruct Ha as (f & kf & Hinf & Hf). rewrite <- HF in Hinf.
pose proof (af_fshadow_apart RTA rta_art_facts Σ1 m2 f kf ART2 Hinf) as (D & _). specialize (D q n Hinq). lia. }
split; [destruct DST3 as [[_ DB] _]; cbn [cells_bytes cbytes] in DB; rewrite app_nil_r in DB; replace (Z.min n0 n) with n' by (unfold n'; lia); exact DB|].
assert (TR : forall a cs, rw_cells asegs m1 a cs -> usp + -2208 <= a -> a + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells asegs m3 a cs).
{ intros a cs C H1 H2. apply (rw_cells_transport asegs _ m2 m3 _ _ (X00b.rw_cells_agree asegs m1 m2 _ _ C (AG a _ H1 H2) WM2) MU3 WM3). apply DSK. lia. }
split; [apply (TR _ _ IC1); cbn [cells_size csize Nat.add]; lia|].
split; [apply (TR _ _ IC2); cbn [cells_size csize Nat.add]; lia|].
split; [apply (TR _ _ IC3); cbn [cells_size csize Nat.add]; lia|].
assert (TB3 : u64arr asegs m3 (usp + -2120) (wr_trace tr tb)).
{ assert (LW : length (wr_trace tr tb) = 255%nat) by (rewrite wr_trace_length; [exact HTB | rewrite HTB; destruct Htr as (_ & X); lia]).
apply (u64arr_transport asegs _ m2 m3 _ _ (X00b.u64arr_agree asegs m1 m2 _ _ TB1 ltac:(apply AG; [lia | rewrite LW; cbn; lia]) WM2) MU3 WM3). apply DSK. lia. }
split.
{ replace (usp + -80 + -2128) with (usp + -2208) by lia.
split; [exists (Z_to_bv 64 1), (Z_to_bv 64 realloc_pc), (Z_to_bv 64 p), (Z_to_bv 64 n), (Z_to_bv 64 usp)|].
2: split; [exists jr|split; [exists jq|split; [exists (Z_to_bv 64 (Z.of_nat (length tr)))|exists (wr_trace tr tb)]]].
- replace (usp + -80 + -2128) with (usp + -2208) by lia. apply (TR _ _ IC7). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2080) with (usp + -2160) by lia. apply (TR _ _ IC6). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2064) with (usp + -2144) by lia. apply (TR _ _ IC5). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2056) with (usp + -2136) by lia. replace (usp + -80 + -2040) with (usp + -2120) by lia. apply (TR _ _ IC4). all: cbn [cells_size csize Nat.add]; lia.
- replace (usp + -80 + -2040) with (usp + -2120) by lia. split; [exact TB3|]. rewrite wr_trace_length; [exact HTB | rewrite HTB; destruct Htr as (_ & X); lia]. }
split; [apply (TR _ _ IC4); cbn [cells_size csize Nat.add]; lia | exact TB3].
Qed.

Theorem rl_back_cps :
cps asegs (rcore_post F fc Σ PMc (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1)
(fun c => exists (Σ' : rts RTA) (q : Z),
ASTA RTA Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
/\ rt_after_f RTA Σ' usp lo m m'
/\ rt_pres (live_remove p (rt_live RTA Σ)) (rt_frames RTA Σ) usp m m'
/\ wr_at asegs m' q n /\ acc asegs m' q n
/\ bytes_at asegs m' q (firstn (Z.to_nat (Z.min n0 n)) bs)) c
/\ rt_live RTA Σ' = (q, n) :: live_remove p (rt_live RTA Σ) /\ rt_frames RTA Σ' = rt_frames RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ
/\ rt_credit RTA Σ' = rt_credit RTA Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q <> p /\ q + n < USTACK_TOP /\ rt_pois RTA Σ' = rt_pois RTA Σ).
Proof using DRAIN FC FDO MST HA Hin HBS HLB Hn Hn0 LOW LOR SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB IC4 IC5 IC6 IC7 Htr.
intros TT c2 Hc2 Hk. destruct Hc2 as (Σ1 & q & HAST & HL & HF & HS & HCR & Hq0 & Hq16 & HqU & HPO).
apply (cps_realizes asegs _ _ _ c2 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ1) _ _ _ (fl_ASTA_mat_stable Σ1 PMc MST)
(rbk_B Σ1 q HL HF HS Hq0 HqU)) HAST).
intros c3 Hc3. unfold rl_B_post in Hc3.
apply AST_exI in Hc3 as (t0' & Hc3). apply AST_exI in Hc3 as (t1' & Hc3). apply AST_exI in Hc3 as (t2' & Hc3). apply AST_exI in Hc3 as (a6' & Hc3).
apply AST_exI in Hc3 as (a7' & Hc3). apply AST_exI in Hc3 as (t3' & Hc3). apply AST_exI in Hc3 as (t4' & Hc3). apply AST_exI in Hc3 as (t5' & Hc3).
apply AST_exI in Hc3 as (t6' & Hc3). apply AST_exI in Hc3 as (m3 & Hc3).
pose proof Hc3 as (_ & (_ & ART3 & MI3 & ST3 & RP3 & BY3 & J1 & J2 & J3 & ICF3 & BC3 & TB3) & _ & _).
assert (Hin1 : In (p, n0) (live Σ1)) by (rewrite HL; right; exact Hin).
assert (Hinq : In (q, n) (live Σ1)) by (rewrite HL; left; reflexivity).
destruct (rbk_old Σ1 m3 p n0 Hn0 ART3 Hin1) as (c & i & Hc & Hni & Ep).
assert (Hn01 : 1 <= n0).
{ pose proof (ART_wf Σ1 m3 ART3) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hni)) as X. cbv beta iota in X. clear - X; lia. }
assert (Hqp : q <> p) by (pose proof (af_live_disj RTA rta_art_facts Σ1 m3 q n p n0 [] (live Σ) ART3 HL Hin) as D; lia).
assert (HACE : l_ACEIL (lay Σ1) = l_ACEIL (lay Σ)) by (unfold l_ACEIL; unfold rtA_sp0 in HS; rewrite HS; reflexivity).
set (spv := Z_to_bv 64 (usp + -80)) in *.
assert (Ev : bv_unsigned spv = usp + -80) by (apply unsigned_lit; pose proof (rta_sp0_range Σ m HA) as HR0; clear - HR0 LOW LOR SPT; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
assert (Hc3' : ASTA RTA Σ1 PMc (eq (rl_dealloc_entry spv gp t0' t1' t2' (Z_to_bv 64 (usp + -2136)) a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc (p_ubeg (l_SB (lay Σ1)) c i n0) m3)) c3).
{ unfold ASTA. eapply AST_conseq; [exact Hc3 | intros ms (E & _); rewrite <- Ep; symmetry; exact E | intros mo H; exact H]. }
assert (ST3v : stk asegs m3 lo (bv_unsigned spv + -2128)) by (rewrite Ev; replace (usp + -80 + -2128) with (usp + -2208) by lia; exact ST3).
assert (BC3v : rw_cells asegs m3 (bv_unsigned spv + -2056) [C8 (Z_to_bv 64 (bv_unsigned spv + -2040)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))])
by (rewrite Ev; replace (usp + -80 + -2056) with (usp + -2136) by lia; replace (usp + -80 + -2040) with (usp + -2120) by lia; exact BC3).
assert (TB3v : u64arr asegs m3 (bv_unsigned spv + -2040) (wr_trace tr tb)) by (rewrite Ev; replace (usp + -80 + -2040) with (usp + -2120) by lia; exact TB3).
assert (ICF3v : icpt_frame m3 (bv_unsigned spv) ra s0 s1 s2 s3 s4 s5) by (rewrite Ev; exact ICF3).
apply (rl_dealloc_prim DRAIN FC Σ1 PMc ra spv gp t0' t1' t2' (Z_to_bv 64 (usp + -2136)) s1 a6' a7' (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m3 lo c i n0 tr tb
FDO MST ART3 MI3 Hc Hni Hn01 ltac:(rewrite HACE; exact LOW) ltac:(rewrite Ev; clear - LOR; lia) ltac:(rewrite Ev; clear - SPT; lia)
ST3v BC3v TB3v HTB Htr ICF3v TT c3 Hc3').
intros c4 (Σ2 & HAST4 & EL & EF & ELY & EC & EP). rewrite <- Ep in *.
assert (EL2 : live Σ2 = (q, n) :: live_remove p (live Σ)) by (rewrite EL, HL; exact (live_remove_cons_ne p q n (live Σ) Hqp)).
assert (W4 : forall ms, (exists (w1 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word) (m4 : mem),
ms = rl_ret_st (bv_unsigned spv) gp (Z_to_bv 64 (usp + -2136)) w1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q) (Z_to_bv 64 (usp + -2136))
(Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F fc m4
/\ ART_A Σ2 m4 /\ mem_inv asegs m4 /\ stk asegs m4 lo (bv_unsigned spv + -2128)
/\ rt_pres (live_remove p (live Σ1)) (frames Σ1) (bv_unsigned spv) m3 m4
/\ icpt_frame m4 (bv_unsigned spv) ra (Z_to_bv 64 (usp + -2136)) s1 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0)) (Z_to_bv 64 q) (Z_to_bv 64 (usp + -2136))) ->
evt asegs (fun ms' => exists m5, ret_stF F fc ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m5 ms'
/\ ART_A Σ2 m5 /\ mem_inv asegs m5 /\ stk asegs m5 lo usp
/\ rt_pres (live_remove p (live Σ)) (frames Σ) usp m m5
/\ wr_at asegs m5 q n /\ acc asegs m5 q n /\ bytes_at asegs m5 q (firstn (Z.to_nat (Z.min n0 n)) bs)) ms).
{ intros ms (w1 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & -> & ART4 & MI4 & ST4 & RP4 & ICF4).
unfold rl_ret_st. rewrite Ev in *. replace (usp + -80 + -2128) with (usp + -2208) in * by lia.
destruct ICF4 as ((s4r & s3r & s2r & s1r & s0r & R1) & (jr' & R2) & (jq' & R3) & (w' & R4) & (ws & R5 & R5l)).
replace (usp + -80 + -2128) with (usp + -2208) in R1 by lia. replace (usp + -80 + -2080) with (usp + -2160) in R2 by lia. replace (usp + -80 + -2064) with (usp + -2144) in R3 by lia.
replace (usp + -80 + -2056) with (usp + -2136) in R4 by lia. replace (usp + -80 + -2040) with (usp + -2120) in R4, R5 by lia.
assert (AG4 : forall a : word, usp + -80 <= bv_unsigned a < USTACK_TOP -> m4 a = m3 a) by (intros a Ha; apply RP4; left; exact Ha).
pose proof (X00b.rw_cells_agree_nw asegs m3 m4 _ _ J1 ltac:(intros a Ha; apply AG4; cbn [cells_size csize Nat.add] in Ha; lia)) as J1'.
pose proof (X00b.rw_cells_agree_nw asegs m3 m4 _ _ J2 ltac:(intros a Ha; apply AG4; cbn [cells_size csize Nat.add] in Ha; lia)) as J2'.
pose proof (X00b.rw_cells_agree_nw asegs m3 m4 _ _ J3 ltac:(intros a Ha; apply AG4; cbn [cells_size csize Nat.add] in Ha; lia)) as J3'.
pose proof (ART_wf Σ2 m4 ART4) as HW2. pose proof (geo_of_wf Σ2 HW2) as HG2.
assert (HA2 : l_ACEIL (lay Σ2) <= usp - 2208) by (rewrite ELY, HACE; clear - LOW LOR; lia).
assert (Hinq2 : In (q, n) (live Σ2)) by (rewrite EL2; left; reflexivity).
pose proof (rta_live_range Σ2 m4 q n ART4 Hinq2) as (_ & Rq & _). unfold rtA_sp0 in Rq. fold (l_ACEIL (lay Σ2)) in Rq.
eapply evt_mono.
{ apply (realloc_C_spec ra sp gp (Z_to_bv 64 tpA) y0 y1 y2 (Z_to_bv 64 (usp + -2136)) w1 y3 y4 y5 y6 y7 y8 y9 y10 (Z_to_bv 64 INST) (Z_to_bv 64 (Z.min n n0))
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 y11 y12 y13 y14 (Z_to_bv 64 0x46714) s0 s1 s2 s3 s4 s5 s6
s0r s1r s2r s3r s4r F fc m4 q lo ws w' jp jq' jr'); try assumption.
all: try (pose proof (rta_sp0_range Σ m HA) as HR0; clear - HR0 LOW LOR SPT Hq0 HqU Hn; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia). }
intros ms5 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & -> & MU5 & WM5 & MI5 & ST5).
assert (ART5 : ART_A Σ2 m5).
{ apply c_ART; [exact HW2|]. apply (ARTc_stack Σ2 (usp - 2208) usp HG2 HA2 m4 m5 (ART_c _ _ ART4) MU5 WM5).
- destruct HW2 as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
- destruct HW2 as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK. }
exists m5. split; [exists u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13; reflexivity|].
split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|].
split.
{ intros a Ha.
assert (Ha2 : aclient (live Σ2) (frames Σ2) usp (bv_unsigned a)).
{ rewrite EL2, EF, HF. destruct Ha as [H|[H|[H|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
right; right; left. destruct H as (p' & n' & Hi & Hx). exists p', n'. split; [right; exact Hi | exact Hx]. }
destruct (X0ek.aclient_split Σ2 m4 usp _ ART4 Ha2) as [X|X].
- rewrite (MU5 a) by (cbn [outside]; split; [lia | exact I]).
rewrite (RP4 a) by (rewrite HL, HF; exact (rbk_aclient_rm p (live Σ) q n (frames Σ) usp (usp + -80) _ ltac:(lia) Hqp Ha)).
exact (RP3 a (aclient_live_remove _ _ _ _ _ Ha)).
- rewrite (MU5 a) by (cbn [outside]; split; [lia | exact I]).
rewrite (RP4 a) by (rewrite HL, HF; exact (rbk_aclient_rm p (live Σ) q n (frames Σ) usp (usp + -80) _ ltac:(lia) Hqp Ha)).
exact (RP3 a (aclient_live_remove _ _ _ _ _ Ha)). }
destruct (af_acc_live RTA rta_art_facts Σ2 m5 q n ART5 Hinq2) as (WR5 & AC5).
split; [exact WR5|]. split; [exact AC5|].
assert (LEN : Z.of_nat (length (firstn (Z.to_nat (Z.min n0 n)) bs)) <= n) by (rewrite firstn_length; lia).
apply (bytes_at_transport asegs _ m4 m5 _ _ (X00b.bytes_at_agree asegs m3 m4 _ _ BY3 ltac:(intros x Hx; apply RP4; right; right; left; exists q, n;
split; [rewrite HL; rewrite (live_remove_cons_ne p q n (live Σ) Hqp); left; reflexivity | lia])) MU5).
cbn [disjoint_from]. split; [lia | exact I]. }
apply (cps_realizes asegs _ _ _ c4 (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ2) _ _ _ (fl_ASTA_mat_stable Σ2 PMc MST) W4) HAST4).
intros c5 Hc5. apply Hk. exists Σ2, q.
cbn [rt_live rt_frames rt_sp0 rt_credit rt_pois RTA]. unfold rtA_live, rtA_frames, rtA_credit.
split; [|split; [exact EL2 | split; [exact (eq_trans EF HF) | split; [unfold rtA_sp0; rewrite ELY; exact HS | split; [rewrite EC; exact HCR |
split; [exact Hq0 | split; [exact Hq16 | split; [exact Hqp | split; [exact HqU | exact (eq_trans EP HPO)]]]]]]]]].
unfold ASTA. eapply AST_conseq; [exact Hc5| |intros mo H; exact H].
intros ms (m5 & RS & A5 & MI5 & ST5 & RP5 & WR5 & AC5 & BY5).
exists m5. split; [exact RS|]. split; [split; [exact A5 | split; [exact MI5 | exact ST5]]|].
split; [exact RP5|]. split; [exact WR5|]. split; [exact AC5 | exact BY5].
Qed.

End Back.

Theorem rta_realloc_of : core_stmt_realloc -> drain_stmt -> fixed_commit_node -> realloc_contract RTA.
Proof.
intros CP DRAIN FC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo bs
FDO MST Hin Hn Hn0 Ha0 Ha1 Htp HBS HLB Hlen Hcr ART0 MI0 CALL LOR80 UWOK. subst a0 a1 tp.
intros TT cf Hc Hkk. cbn [ART rt_live rt_frames rt_sp0 rt_credit RTA] in Hlen, Hcr, ART0, Hin.
unfold rtA_live, rtA_credit in Hlen, Hcr, Hin.
pose proof CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
pose proof (mp_cells Σ m ART0) as (G60 & GCF & MX & RZ & AI & MCS & RSS & PSC & FUM & TC & SC & UB).
pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
pose proof (geo_grant Σ m ART0 (l_T (lay Σ)) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & _ & _ & GT5).
pose proof (geo_grant Σ m ART0 (l_TCX (lay Σ)) 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (GX1 & _ & _ & _ & GX5).
assert (LOW' : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; lia).
destruct (site_trace_main m realloc_pc (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) ra s0 sp ltac:(right; right; right; left; reflexivity) UWOK ltac:(lia))
as (ch & tr & CHC & HTR & Htr & Htrl).
destruct (ART_ia Σ m ART0) as (b & IS).
pose proof (rta_live_range Σ m p n0 ART0 Hin) as (Rp0 & Rp & _). pose proof (rta_sp0_range Σ m ART0) as Rs0. unfold rtA_sp0 in Rp, Rs0.

pose proof (ART_consts Σ m ART0) as (_ & _ & _ & _ & _ & _ & _ & ICR).
destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
& I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & _).
destruct (stk_two_words m (l_T (lay Σ) + 2856) ltac:(destruct (stk_split asegs m (l_T (lay Σ) + 2768) (l_T (lay Σ) + 2856) (l_T (lay Σ) + 3168) I32 ltac:(lia)) as [_ X];
destruct (stk_split asegs m (l_T (lay Σ) + 2856) (l_T (lay Σ) + 2872) (l_T (lay Σ) + 3168) X ltac:(lia)) as [X' _];
replace (l_T (lay Σ) + 2856 + 16) with (l_T (lay Σ) + 2872) by lia; exact X')) as (rc & rd & STATS).
assert (W1 : evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo rc rd tr m)
(entry_st ra sp gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_realloc m)).
{ unfold entry_st, e_realloc.
apply (realloc_A_spec ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n
(l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b ch tr rc rd); try assumption.
all: try (unfold RT_STACK, USTACK_TOP, STACK_WIN, SEGTOP_A, kHighShadowEnd in *; lia). }
assert (W1' : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_realloc m) ms ->
evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n (l_T (lay Σ)) lo rc rd tr m) ms)
by (intros ms <-; exact W1).
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. unfold realloc_A_post in Hc1.
apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1).
apply AST_exI in Hc1 as (a4' & Hc1). apply AST_exI in Hc1 as (a5' & Hc1). apply AST_exI in Hc1 as (a6' & Hc1).
apply AST_exI in Hc1 as (a7' & Hc1). apply AST_exI in Hc1 as (t3' & Hc1). apply AST_exI in Hc1 as (t4' & Hc1).
apply AST_exI in Hc1 as (t5' & Hc1). apply AST_exI in Hc1 as (t6' & Hc1). apply AST_exI in Hc1 as (tb & Hc1).
apply AST_exI in Hc1 as (jp & Hc1). apply AST_exI in Hc1 as (jq & Hc1). apply AST_exI in Hc1 as (jr & Hc1).
apply AST_exI in Hc1 as (j0 & Hc1). apply AST_exI in Hc1 as (m1 & Hc1).
destruct Hc1 as (HM & HPm & HPM & HZ).
destruct HPm as (Hms & MU1 & WM1 & MI1 & IS1 & IC1 & IC2 & IC3 & TB1 & HTB & IC4 & IC5 & IC6 & IC7 & AFr & J0 & UB1 & STATS1 & ST1).
assert (Hsp0 : l_ACEIL (lay Σ) + 0xF000 <= bv_unsigned sp) by (unfold RT_STACK in LOR; lia).
pose proof (RL_front.fn_ART Σ m (bv_unsigned sp) ART0 Hsp0 m1 MU1 WM1 IS1 UB1) as ART1.
set (usp := bv_unsigned sp) in *.
assert (Hc2 : ASTA RTA Σ PMc (eq (rcore_entry Σ (usp + -2136) gp t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n m1)) c1).
{ split; [exact HM|]. split; [|split; [exact HPM | exact HZ]]. rewrite Hms. unfold rcore_entry.
replace (usp + -2136 + -200) with (usp + -2336) by lia. reflexivity. }
assert (ST1' : stk asegs m1 lo (usp + -2136 + -200)) by (replace (usp + -2136 + -200) with (usp + -2336) by lia; exact ST1).
assert (TRC : trc_cells (usp + -2136) tr m1 tb).
{ split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact IC4|]. split; [replace (usp + -2136 + 16) with (usp + -2120) by lia; exact TB1 | exact HTB]. }
assert (AFC : raf_cells (usp + -2136) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 m1 j0).
{ split; replace (usp + -2136 + -200) with (usp + -2336) by lia; [exact AFr | exact J0]. }
assert (LOR' : lo + 0x1000 <= usp + -2136 + -200) by (unfold RT_STACK in LOR; lia).
assert (SPT' : usp + -2136 + 2144 <= USTACK_TOP) by lia.
assert (SPA' : (usp + -2136) mod 16 = 8).
{ pose proof SPA as SPA0. apply Z.mod_divide in SPA0; [|lia]. destruct SPA0 as [q Hq].
replace (usp + -2136) with (8 + (q - 134) * 16) by lia. rewrite Z_mod_plus_full. reflexivity. }
assert (K : forall c2, rcore_post F fc Σ PMc (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 n lo m1 c2 -> realizes asegs c2 TT).
{ intros c2 Hc2'. exact (rl_back_cps Σ PMc F fc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m m1 p n0 n lo bs tr tb jp jq jr
DRAIN FC FDO MST Hn Hn0 Hin HBS HLB ART0 LOW' ltac:(unfold RT_STACK in LOR80; exact LOR80) SPT SPA MU1 WM1 IC1 IC2 IC3 TB1 HTB
IC4 IC5 IC6 IC7 (conj Htr Htrl) TT c2 Hc2' Hkk). }
exact (CP Σ PMc m1 (usp + -2136) gp (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST) (Z_to_bv 64 n) (Z_to_bv 64 1)
(Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F fc n lo tr tb j0
FDO MST Hn Hlen Hcr ART1 MI1 ST1' LOW' LOR' SPT' SPA' Htr Htrl TRC AFC TT c1 Hc2 K).
Qed.
