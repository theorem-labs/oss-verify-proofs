(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx X1cq X1d0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb
X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv X0gj
X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5 X0df X0g3
X0ci X0cr X0cp X0cn X0ca X0ck X0ce X0cd
X0co X0cl X0cq X0cm.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X174 X16j X161 X13v X16p X16b X14p X14t X13u X14q X140 X16o X133 X13c X13a X138 X12v X135 X12z X12y X139 X136 X13b X137.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X174 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X140 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X138 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X135 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X139 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X136 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X137.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma stk_of_bytes_wr : forall (m : mem) a bs, bytes_at bsegs m a bs -> wr_at bsegs m a (Z.of_nat (length bs)) ->
stk bsegs m a (a + Z.of_nat (length bs)).
Proof.
intros m a bs (B0 & B1 & Hb) (W0 & W1 & Hw). split; [exact B0|]. split; [lia|]. intros x Hx.
split; [replace x with (a + (x - a)) by lia; apply Hw; lia|].
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite Hb by lia.
destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma qbatch_stk : forall (m : mem) b nxt ents, qbatch m b nxt ents -> stk bsegs m b (b + 8192).
Proof.
intros m b nxt ents (H & (ws & U & Hl & _) & _).
destruct H as ((_ & Hb) & Hw). cbn [cells_bytes cbytes] in Hb. rewrite !app_nil_r in Hb.
pose proof (stk_of_bytes_wr m b _ Hb ltac:(rewrite !length_app, !length_le8; exact Hw)) as S1.
rewrite !length_app, !length_le8 in S1. change (Z.of_nat (8 + (8 + 8))) with 24 in S1.
destruct U as (Ub & Uw). pose proof (stk_of_bytes_wr m (b + 0x18) _ Ub ltac:(rewrite u64s_length, Nat2Z.inj_mul; exact Uw)) as S2.
rewrite u64s_length, Hl in S2. change (Z.of_nat (8 * 1021)) with 8168 in S2.
destruct S1 as (A0 & A1 & Aw). destruct S2 as (C0 & C1 & Cw). split; [lia|]. split; [lia|]. intros x Hx.
destruct (Z_lt_ge_dec x (b + 24)) as [X|X]; [apply Aw; lia | apply Cw; lia].
Qed.

Lemma artc_unbatch : forall (Σ : rtsA) (m : mem) ib, ARTc Σ m -> nth_error (r_st (pr Σ 24)) ib = Some CkBatch ->
stk bsegs m (p_abeg (l_SB (lay Σ)) 24 ib) (p_abeg (l_SB (lay Σ)) 24 ib + 8192) -> ARTc (set_st Σ 24 ib CkIdle) m.
Proof.
intros Σ m ib HA Hib ST. destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
apply ARTc_intro.
- exact A1.
- intros c' Hc'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same'. apply reg_rep_ureg'. exact (A2 24 Hc').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne). exact (A2 c' Hc').
- exact A3.
- destruct A4 as [P Sc]. split; [|exact Sc].
intros c' i' st Hc' Hn'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same' in Hn'. unfold ureg in Hn'. cbn [r_st] in Hn'. rewrite nth_upd_ck in Hn'.
destruct (Nat.eqb_spec ib i') as [<-|Hii].
* destruct (Nat.ltb_spec ib (length (r_st (pr Σ 24)))); [|discriminate]. injection Hn' as <-.
pose proof (P 24 ib CkBatch Hc' Hib) as X. cbn [pchunk] in X |- *. split; [exact ST | exact X].
* exact (P 24 i' st Hc' Hn').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne) in Hn'. exact (P c' i' st Hc' Hn').
- exact A5.
- exact A6.
- exact A7.
- exact A8.
- exact A9.
- exact A10.
- exact A11.
Qed.

Lemma bt_batch_av : forall (Σ : rtsA) j' C lo, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j' = Some CkBatch ->
l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) (p_abeg (l_SB (lay Σ)) 24 j') 8192.
Proof.
intros Σ j' C lo HG Hj HL1 HL2 HL3.
pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
assert (HTT : l_T (lay Σ) + 4096 <= l_SB (lay Σ) \/ l_SB (lay Σ) + 2 ^ 37 + 4096 <= l_T (lay Σ)) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
repeat split; lia.
Qed.

Lemma bt_stack_av : forall (Σ : rtsA) C lo a k, geo_ok Σ -> l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
C - 112 <= a -> 0 <= k -> disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) a k.
Proof.
intros Σ C lo a k HG HL1 HL2 HL3 Ha Hk.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
repeat split; lia.
Qed.

Section Batch.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem batch_ok : batch_stmt p.
Proof using FC HOK.
intros j Σk b ib ents rest HWP HS Hib Eb.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
pose proof (proj1 (proj2 (proj2 HR)) 24 ltac:(lia)) as (Hcnt & _ & Hcl0).
assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk 24)))) (ca Σk 24)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
pose proof (proj1 HR 24 ltac:(lia)) as HRW.
assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
assert (HEg : rt_eager (recp Σk 24 ib) <= 2 ^ 38)
by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk 24 ib CkBatch HB HR HSW ltac:(lia) Hib ltac:(discriminate) Einit)))))).
pose proof (rt_wfP_batch Σk b rest ib HWP Hib Eb Einit) as HWP'.
apply cps_pointwise.
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof FR as (FR1 & FR2 & FR3).
assert (HA' : ARTc (set_st Σk 24 ib CkIdle) m).
{ apply (artc_unbatch Σk m ib HA Hib). rewrite <- Eb. exact (qbatch_stk m b _ ents QB). }
assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply (cps_conseq bsegs).
- exact (cd_lift Σk PMc m 24 ib CkBatch lo (Z_to_bv 64 0x47fa0) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C)
(Z_to_bv 64 INST) a4 a5 a6 a7 (Z_to_bv 64 1057944) (Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p)
FDO MST FC HG HA' ltac:(lia) Hib Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
MI Hlive Hdep HQB HL HAw HEg).
- intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms E. rewrite <- E. unfold cd_msD. rewrite <- Eb, El. reflexivity.
- intros cf Hcf. exists (recp Σk 24 ib). split.
+ unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
rewrite Esp in MU2, ST2, RP2.
rewrite (ret_pc_even 0x47fa0); [| lia | reflexivity].
exists (Z_to_bv 64 0x47fa0), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', (Z_to_bv 64 b), s6, s7, s8, s9,
t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2) by (rewrite <- Elv, <- Efr; exact RP2).
pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WM2) | exact HGo]|].
split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
split.
* split; [|split].
-- apply (rw_cells_transport bsegs _ m m2 _ _ FR1 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport bsegs _ m m2 _ _ FR2 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport bsegs _ m m2 _ _ FR3 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
* apply (qcache_rep_frame _ m m2 C rest QR MU2 WM2).
-- exact (bt_stack_av Σk C lo C 32 HG HLk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
-- apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'.
exact (bt_batch_av Σk j' C lo HG Hj' HLk ltac:(lia) ltac:(lia)).
+ split; [exact HWP'|].
pose proof (recp_fields Σk 24 ib) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | split; [rewrite X2; exact Einit | exact Epo]].
Qed.

End Batch.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma stk_of_bytes_wr : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) ->
stk asegs m a (a + Z.of_nat (length bs)).
Proof.
intros m a bs (B0 & B1 & Hb) (W0 & W1 & Hw). split; [exact B0|]. split; [lia|]. intros x Hx.
split; [replace x with (a + (x - a)) by lia; apply Hw; lia|].
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite Hb by lia.
destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma qbatch_stk : forall (m : mem) b nxt ents, qbatch m b nxt ents -> stk asegs m b (b + 8192).
Proof.
intros m b nxt ents (H & (ws & U & Hl & _) & _).
destruct H as ((_ & Hb) & Hw). cbn [cells_bytes cbytes] in Hb. rewrite !app_nil_r in Hb.
pose proof (stk_of_bytes_wr m b _ Hb ltac:(rewrite !length_app, !length_le8; exact Hw)) as S1.
rewrite !length_app, !length_le8 in S1. change (Z.of_nat (8 + (8 + 8))) with 24 in S1.
destruct U as (Ub & Uw). pose proof (stk_of_bytes_wr m (b + 0x18) _ Ub ltac:(rewrite u64s_length, Nat2Z.inj_mul; exact Uw)) as S2.
rewrite u64s_length, Hl in S2. change (Z.of_nat (8 * 1021)) with 8168 in S2.
destruct S1 as (A0 & A1 & Aw). destruct S2 as (C0 & C1 & Cw). split; [lia|]. split; [lia|]. intros x Hx.
destruct (Z_lt_ge_dec x (b + 24)) as [X|X]; [apply Aw; lia | apply Cw; lia].
Qed.

Lemma artc_unbatch : forall (Σ : rtsA) (m : mem) ib, ARTc Σ m -> nth_error (r_st (pr Σ 24)) ib = Some CkBatch ->
stk asegs m (p_abeg (l_SB (lay Σ)) 24 ib) (p_abeg (l_SB (lay Σ)) 24 ib + 8192) -> ARTc (set_st Σ 24 ib CkIdle) m.
Proof.
intros Σ m ib HA Hib ST. destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
apply ARTc_intro.
- exact A1.
- intros c' Hc'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same'. apply reg_rep_ureg'. exact (A2 24 Hc').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne). exact (A2 c' Hc').
- exact A3.
- destruct A4 as [P Sc]. split; [|exact Sc].
intros c' i' st Hc' Hn'. destruct (Z.eq_dec c' 24) as [->|Hne].
+ rewrite set_st_pr_same' in Hn'. unfold ureg in Hn'. cbn [r_st] in Hn'. rewrite nth_upd_ck in Hn'.
destruct (Nat.eqb_spec ib i') as [<-|Hii].
* destruct (Nat.ltb_spec ib (length (r_st (pr Σ 24)))); [|discriminate]. injection Hn' as <-.
pose proof (P 24 ib CkBatch Hc' Hib) as X. cbn [pchunk] in X |- *. split; [exact ST | exact X].
* exact (P 24 i' st Hc' Hn').
+ rewrite (set_st_pr_other' Σ 24 ib CkIdle c' Hne) in Hn'. exact (P c' i' st Hc' Hn').
- exact A5.
- exact A6.
- exact A7.
- exact A8.
- exact A9.
- exact A10.
- exact A11.
Qed.

Lemma bt_batch_av : forall (Σ : rtsA) j' C lo, geo_ok Σ -> nth_error (r_st (pr Σ 24)) j' = Some CkBatch ->
l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) (p_abeg (l_SB (lay Σ)) 24 j') 8192.
Proof.
intros Σ j' C lo HG Hj HL1 HL2 HL3.
pose proof (dk_slot_in Σ HG 24 j' _ ltac:(lia) Hj) as (U1 & U2 & U3 & U4 & U5 & U6). change (ClassSize 24) with 8192 in *.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5). pose proof HSB as (Y1 & Y2 & Y3 & Y4).
assert (HTT : l_T (lay Σ) + 4096 <= l_SB (lay Σ) \/ l_SB (lay Σ) + 2 ^ 37 + 4096 <= l_T (lay Σ)) by (destruct TSEP as (_ & _ & _ & _ & X & _); exact X).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB, kHighShadowEnd in *.
repeat split; lia.
Qed.

Lemma bt_stack_av : forall (Σ : rtsA) C lo a k, geo_ok Σ -> l_ACEIL (lay Σ) <= lo -> lo <= C - 1136 -> C <= 2 ^ 47 ->
C - 112 <= a -> 0 <= k -> disjoint_from (W_CD (l_T (lay Σ)) (l_SB (lay Σ)) 24 (C - 112)) a k.
Proof.
intros Σ C lo a k HG HL1 HL2 HL3 Ha Hk.
pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (dk_rb Σ HG 24 ltac:(lia)) as (B1 & B2 & B3 & B4).
pose proof (dg_ok Σ HG) as (HT & HSB & TSEP). pose proof HT as (T1 & T2 & T3 & T4 & T5).
pose proof (fk_shad_mono (rb (l_SB (lay Σ)) 24 + 2 ^ 32) (2 ^ 47) ltac:(unfold rb in *; lia)) as SL4.
assert (SL5 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
unfold W_CD. cbn [disjoint_from]. unfold pc_addr, rinfo, RIS_of, fa, rb, kFaCap, kUserCap, SHB in *.
repeat split; lia.
Qed.

Section Batch.
Variable p : dlp.
Hypothesis FC : fixed_commit_node.
Hypothesis HOK : dl_ok p.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).

Theorem batch_ok : batch_stmt p.
Proof using FC HOK.
intros j Σk b ib ents rest HWP HS Hib Eb.
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof HWP as (HL & HR & Hlive & HSW & HQW & HFW & HB & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
pose proof (proj1 (proj2 (proj2 HR)) 24 ltac:(lia)) as (Hcnt & _ & Hcl0).
assert (Hcl : Forall (fun x => 0 <= x < Z.of_nat (length (r_st (pr Σk 24)))) (ca Σk 24)) by (eapply Forall_impl; [|exact Hcl0]; intros x (X & _); exact X).
pose proof (proj1 HR 24 ltac:(lia)) as HRW.
assert (HAw : A_bytes (aw Σk) <= CREDIT0) by (destruct HB as (X1 & _ & X3 & _); lia).
assert (HEg : rt_eager (recp Σk 24 ib) <= 2 ^ 38)
by (exact (proj1 (proj2 (proj2 (proj2 (budget_wf_recp Σk 24 ib CkBatch HB HR HSW ltac:(lia) Hib ltac:(discriminate) Einit)))))).
pose proof (rt_wfP_batch Σk b rest ib HWP Hib Eb Einit) as HWP'.
apply cps_pointwise.
intros ms (t0 & t1 & t2 & a4 & a5 & a6 & a7 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
pose proof DM as (HA & MI & ST & WM0 & RP & FR & QR).
pose proof FR as (FR1 & FR2 & FR3).
assert (HA' : ARTc (set_st Σk 24 ib CkIdle) m).
{ apply (artc_unbatch Σk m ib HA Hib). rewrite <- Eb. exact (qbatch_stk m b _ ents QB). }
assert (Esp : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; lia).
eapply (cps_conseq asegs).
- exact (cd_lift Σk PMc m 24 ib CkBatch lo (Z_to_bv 64 0x47eb4) (Z_to_bv 64 (C - 112)) (dl_gp p) t0 t1 t2 (Z_to_bv 64 C)
(Z_to_bv 64 INST) a4 a5 a6 a7 (Z_to_bv 64 1023064) (Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2 ^ 37))
s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p)
FDO MST FC HG HA' ltac:(lia) Hib Einit HRW Hcl Hcnt ltac:(rewrite Esp; exact ST) HLk ltac:(rewrite Esp; lia) ltac:(rewrite Esp; lia)
MI Hlive Hdep HQB HL HAw HEg).
- intros cf Hcf. unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms E. rewrite <- E. unfold cd_msD. rewrite <- Eb, El. reflexivity.
- intros cf Hcf. exists (recp Σk 24 ib). split.
+ unfold ASTA in *. eapply AST_conseq; [exact Hcf | | intros mo X; exact X].
intros ms2 (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & HA2 & MU2 & WM2 & MI2 & ST2 & RP2).
rewrite Esp in MU2, ST2, RP2.
rewrite (ret_pc_even 0x47eb4); [| lia | reflexivity].
exists (Z_to_bv 64 0x47eb4), t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', (Z_to_bv 64 b), s6, s7, s8, s9,
t3'', t4'', t5'', t6'', m2. split; [reflexivity|].
assert (RPa : rt_pres (live Σ0) (frames Σ0) (C - 112) m m2) by (rewrite <- Elv, <- Efr; exact RP2).
pose proof (pres_munch _ _ _ m m2 RPa) as MUa.
split; [exact HA2|]. split; [exact MI2|]. split; [exact ST2|].
split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m2 WG WM2) | exact HGo]|].
split; [exact (rt_pres_trans _ _ _ _ m m2 RP (rt_pres_mono _ _ (C - 112) (C + 32) m m2 RPa ltac:(lia)))|].
split.
* split; [|split].
-- apply (rw_cells_transport asegs _ m m2 _ _ FR1 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport asegs _ m m2 _ _ FR2 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
-- apply (rw_cells_transport asegs _ m m2 _ _ FR3 MUa WM2). cbn [disjoint_from cells_size csize Nat.add Z.of_nat]. unfold USTACK_TOP. lia.
* apply (qcache_rep_frame _ m m2 C rest QR MU2 WM2).
-- exact (bt_stack_av Σk C lo C 32 HG HLk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
-- apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'.
exact (bt_batch_av Σk j' C lo HG Hj' HLk ltac:(lia) ltac:(lia)).
+ split; [exact HWP'|].
pose proof (recp_fields Σk 24 ib) as (X1 & X2 & _ & _ & _ & X6 & _ & _ & _ & _ & _ & X12 & X13 & X14).
split; [rewrite X1; exact El|]. split; [rewrite X13; exact Elv|]. split; [rewrite X14; exact Efr|].
split; [rewrite X12; exact Ecr|]. split; [rewrite X6; exact Eql | split; [rewrite X2; exact Einit | exact Epo]].
Qed.

End Batch.
