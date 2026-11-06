(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb
X0il X0gp X0h2 X0j4 X0hf X0j3 X0hi X0fy X0fg X0da X0g4 X0d8 X0fq X04b
X0d7 X0ff X0h3 X0hn X0j0 X0g6 X0g7 X0ej X0fv X0fr X0bt X05a.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X18c X17w X196 X17a X17n X19n X180 X19m X183 X16j X161 X13v X16p X13t X16b X0v9 X13s X160 X17o X188 X19k X16r X16s X154 X16g X16c X12e X0w7.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X160 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X154 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AllocasUnpoisonLo.
Variables (Σ : rtsA) (m m' : mem) (top bottom usp : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation P := (rtA_pois Σ).
Hypothesis Htb : 0 < top <= bottom.
Hypothesis Ht8 : top mod 8 = 0.
Hypothesis Hb8 : bottom mod 8 = 0.
Hypothesis Hlo : l_ACEIL L <= top.
Hypothesis Hbt : bottom <= USTACK_TOP - 16.
Hypothesis HST : forall e, In e P -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e.
Hypothesis Husp : l_ACEIL L + 128 <= usp.
Hypothesis MU : munch (au_W top bottom usp) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis P_zero : rw_cells bsegs m' (shad top) [CB (Z.to_nat ((bottom - top) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((bottom - top) / 8)))].

Lemma au_ssr_lo : stack_shadow_rep L (pois_drop bottom P) m'.
Proof using HA Htb Ht8 Hb8 Hlo Hbt HST Husp MU P_zero.
pose proof (au_geo top bottom Htb Ht8 Hb8) as (G1 & G2). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
split; [exact M8|]. split; [|split].
- intros a Ha Hnp.
destruct (Z_lt_le_dec a top) as [X|X]; [|destruct (Z_lt_le_dec a bottom) as [Y|Y]].
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport bsegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_lt_al a top Ht8 X). apply (au_dsj Σ m top bottom usp HA Htb Ht8 Hb8 Husp); lia.
+
destruct P_zero as [[_ PB] _]. cbn [cells_bytes cbytes] in PB. rewrite app_nil_r in PB.
assert (Hj : 0 <= shad a - shad top < (bottom - top) / 8).
{ pose proof (shad_mono top a X). pose proof (shad_lt_al a bottom Hb8 Y). lia. }
replace (shad a) with (shad top + Z.of_nat (Z.to_nat (shad a - shad top))) by (rewrite Z2Nat.id by lia; lia).
apply (bytes_at_nth1 bsegs m' _ _ _ _ PB). apply nth_error_repeat. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by lia. lia.
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport bsegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_mono bottom a Y). apply (au_dsj Σ m top bottom usp HA Htb Ht8 Hb8 Husp); lia.
- apply Forall_forall. intros [a0 n0] He. unfold pois_drop in He. apply filter_In in He as [He Hb]. apply Z.leb_le in Hb.
pose proof (proj1 (Forall_forall _ _) AC _ He) as X.
pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a0 n0) as (RB & _).
destruct (Z.eq_dec n0 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ X MU ltac:(lia)).
pose proof (shad_top (a0 + n0 - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply (au_dsj Σ m top bottom usp HA Htb Ht8 Hb8 Husp); [right; apply shad_mono; lia | lia].
- destruct WF as (WF1 & WF2). split.
+ apply Forall_forall. intros e He. unfold pois_drop in He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) WF1 e He).
+ exact (FOP_filter _ _ _ WF2).
Qed.

End AllocasUnpoisonLo.

Theorem rta_allocas_unpoison_lo : allocas_unpoison_lo_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo
FDO MST -> -> HTB HT8 HB8 HSP HBT HST ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
destruct (ss_pre Σ m sp lo ART0 CALL) as (M2S & SS & _ & _ & SHS & LOW & LOR & SPT & ST & A1 & A2 & A3 & A4).
set (usp := bv_unsigned sp) in *.
assert (HUS : l_ACEIL (lay Σ) + 128 <= usp) by (unfold RT_STACK in LOR; lia).
destruct (au_geo top bottom HTB HT8 HB8) as (G1 & G2).
assert (B1 : shad (l_ACEIL (lay Σ)) <= shad top) by (apply shad_mono; lia).
assert (B2 : shad bottom <= shad (2 ^ 47)) by (apply shad_mono; unfold USTACK_TOP in *; lia).
assert (B3 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
assert (SHT0 : stk bsegs m (shad top) (shad top + Z.of_nat (Z.to_nat ((bottom - top) / 8)))) by (rewrite Z2Nat.id by lia; apply (ss_stk_sub m _ _ _ _ SHS); lia).
destruct (ss_stk_cell m (shad top) _ SHT0) as (shj & SHC).
assert (W1 : evt bsegs (allocas_unpoison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top bottom lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) (Z_to_bv 64 bottom) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc e_allocas_unpoison m)).
{ unfold entry_st.
exact (allocas_unpoison_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo shj
eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)
ltac:(right; unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, SHB, RT_STACK in *; lia) M2S SS SHC ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(lia) MI0). }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold allocas_unpoison_post in Hc1.
assert (EP : rtA_pois (pois_set Σ (pois_drop bottom (pois Σ))) = pois_drop bottom (rtA_pois Σ)).
{ unfold rtA_pois. cbn [frames pois pois_set]. destruct (frames Σ); reflexivity. }
exists (pois_set Σ (pois_drop bottom (pois Σ))).
split; [|split; [exact EP | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. change (rt_allow RTA (pois_set Σ (pois_drop bottom (pois Σ)))) with (rtA_allow Σ).
eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PZ).
assert (MU' : munch (W_ss top bottom usp 32) m m') by exact (au_munch m m' top bottom usp HTB HT8 HB8 MU).
exists m', a0'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split.
{ split; [|split; [exact MI | split; [exact WM | exact ST']]].
apply (ss_art Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' WM).
rewrite EP. exact (au_ssr_lo Σ m m' top bottom usp ART0 HTB HT8 HB8 ltac:(lia) HBT HST HUS MU PZ). }
split; [exact (ss_pres Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' ltac:(lia))|].
intros o k Hacc HT Hoff. exact (au_acc_tr Σ m m' top bottom usp ART0 HTB HT8 HB8 HUS MU o k Hacc HT Hoff).
Qed.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AllocasUnpoisonLo.
Variables (Σ : rtsA) (m m' : mem) (top bottom usp : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation P := (rtA_pois Σ).
Hypothesis Htb : 0 < top <= bottom.
Hypothesis Ht8 : top mod 8 = 0.
Hypothesis Hb8 : bottom mod 8 = 0.
Hypothesis Hlo : l_ACEIL L <= top.
Hypothesis Hbt : bottom <= USTACK_TOP - 16.
Hypothesis HST : forall e, In e P -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e.
Hypothesis Husp : l_ACEIL L + 128 <= usp.
Hypothesis MU : munch (au_W top bottom usp) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis P_zero : rw_cells asegs m' (shad top) [CB (Z.to_nat ((bottom - top) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((bottom - top) / 8)))].

Lemma au_ssr_lo : stack_shadow_rep L (pois_drop bottom P) m'.
Proof using HA Htb Ht8 Hb8 Hlo Hbt HST Husp MU P_zero.
pose proof (au_geo top bottom Htb Ht8 Hb8) as (G1 & G2). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
split; [exact M8|]. split; [|split].
- intros a Ha Hnp.
destruct (Z_lt_le_dec a top) as [X|X]; [|destruct (Z_lt_le_dec a bottom) as [Y|Y]].
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport asegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_lt_al a top Ht8 X). apply (au_dsj Σ m top bottom usp HA Htb Ht8 Hb8 Husp); lia.
+
destruct P_zero as [[_ PB] _]. cbn [cells_bytes cbytes] in PB. rewrite app_nil_r in PB.
assert (Hj : 0 <= shad a - shad top < (bottom - top) / 8).
{ pose proof (shad_mono top a X). pose proof (shad_lt_al a bottom Hb8 Y). lia. }
replace (shad a) with (shad top + Z.of_nat (Z.to_nat (shad a - shad top))) by (rewrite Z2Nat.id by lia; lia).
apply (bytes_at_nth1 asegs m' _ _ _ _ PB). apply nth_error_repeat. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by lia. lia.
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport asegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_mono bottom a Y). apply (au_dsj Σ m top bottom usp HA Htb Ht8 Hb8 Husp); lia.
- apply Forall_forall. intros [a0 n0] He. unfold pois_drop in He. apply filter_In in He as [He Hb]. apply Z.leb_le in Hb.
pose proof (proj1 (Forall_forall _ _) AC _ He) as X.
pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a0 n0) as (RB & _).
destruct (Z.eq_dec n0 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ X MU ltac:(lia)).
pose proof (shad_top (a0 + n0 - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply (au_dsj Σ m top bottom usp HA Htb Ht8 Hb8 Husp); [right; apply shad_mono; lia | lia].
- destruct WF as (WF1 & WF2). split.
+ apply Forall_forall. intros e He. unfold pois_drop in He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) WF1 e He).
+ exact (FOP_filter _ _ _ WF2).
Qed.

End AllocasUnpoisonLo.

Theorem rta_allocas_unpoison_lo : allocas_unpoison_lo_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo
FDO MST -> -> HTB HT8 HB8 HSP HBT HST ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
destruct (ss_pre Σ m sp lo ART0 CALL) as (M2S & SS & _ & _ & SHS & LOW & LOR & SPT & ST & A1 & A2 & A3 & A4).
set (usp := bv_unsigned sp) in *.
assert (HUS : l_ACEIL (lay Σ) + 128 <= usp) by (unfold RT_STACK in LOR; lia).
destruct (au_geo top bottom HTB HT8 HB8) as (G1 & G2).
assert (B1 : shad (l_ACEIL (lay Σ)) <= shad top) by (apply shad_mono; lia).
assert (B2 : shad bottom <= shad (2 ^ 47)) by (apply shad_mono; unfold USTACK_TOP in *; lia).
assert (B3 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
assert (SHT0 : stk asegs m (shad top) (shad top + Z.of_nat (Z.to_nat ((bottom - top) / 8)))) by (rewrite Z2Nat.id by lia; apply (ss_stk_sub m _ _ _ _ SHS); lia).
destruct (ss_stk_cell m (shad top) _ SHT0) as (shj & SHC).
assert (W1 : evt asegs (allocas_unpoison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top bottom lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) (Z_to_bv 64 bottom) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc e_allocas_unpoison m)).
{ unfold entry_st.
exact (allocas_unpoison_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo shj
eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)
ltac:(right; unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, SHB, RT_STACK in *; lia) M2S SS SHC ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(lia) MI0). }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold allocas_unpoison_post in Hc1.
assert (EP : rtA_pois (pois_set Σ (pois_drop bottom (pois Σ))) = pois_drop bottom (rtA_pois Σ)).
{ unfold rtA_pois. cbn [frames pois pois_set]. destruct (frames Σ); reflexivity. }
exists (pois_set Σ (pois_drop bottom (pois Σ))).
split; [|split; [exact EP | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. change (rt_allow RTA (pois_set Σ (pois_drop bottom (pois Σ)))) with (rtA_allow Σ).
eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PZ).
assert (MU' : munch (W_ss top bottom usp 32) m m') by exact (au_munch m m' top bottom usp HTB HT8 HB8 MU).
exists m', a0'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split.
{ split; [|split; [exact MI | split; [exact WM | exact ST']]].
apply (ss_art Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' WM).
rewrite EP. exact (au_ssr_lo Σ m m' top bottom usp ART0 HTB HT8 HB8 ltac:(lia) HBT HST HUS MU PZ). }
split; [exact (ss_pres Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' ltac:(lia))|].
intros o k Hacc HT Hoff. exact (au_acc_tr Σ m m' top bottom usp ART0 HTB HT8 HB8 HUS MU o k Hacc HT Hoff).
Qed.
