(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cy X1cp X1cj X1dd X1cg X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X02b X0j0 X0hn X0ec X001 X0fy X0fg X0da
X0d8 X0fq X0d7 X0bw X04b.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X0ta X19k X188 X14x X0r0 X16j X161 X13v X13t X16b X13s X12h X0v9.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9.
Import ListNotations.
Open Scope Z_scope.

Ltac ss_proof := unfold set_shadow_stmt;
let jk := fresh "jk" in
intros ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6 ?F ?fc ?m ?sa ?n jk;
intros -> -> ?H0 ?Hn ?Hsn ?DST [?GOT ?RM] ?MI;
unfold g_got_real_memset, g_real_memset, musl_memset_entry in *;
do 6 zstep; eapply memset_callZ with (junk := jk); [eassumption | eassumption | lia | lia | lia | lia].

Lemma set_shadow_01_spec : set_shadow_stmt 0x6a1c4 1. Proof. ss_proof. Qed.
Lemma set_shadow_02_spec : set_shadow_stmt 0x6a1dc 2. Proof. ss_proof. Qed.
Lemma set_shadow_03_spec : set_shadow_stmt 0x6a1f4 3. Proof. ss_proof. Qed.
Lemma set_shadow_04_spec : set_shadow_stmt 0x6a20c 4. Proof. ss_proof. Qed.
Lemma set_shadow_05_spec : set_shadow_stmt 0x6a224 5. Proof. ss_proof. Qed.
Lemma set_shadow_06_spec : set_shadow_stmt 0x6a23c 6. Proof. ss_proof. Qed.
Lemma set_shadow_07_spec : set_shadow_stmt 0x6a254 7. Proof. ss_proof. Qed.
Lemma set_shadow_f1_spec : set_shadow_stmt 0x6a26c 241. Proof. ss_proof. Qed.
Lemma set_shadow_f2_spec : set_shadow_stmt 0x6a284 242. Proof. ss_proof. Qed.
Lemma set_shadow_f3_spec : set_shadow_stmt 0x6a29c 243. Proof. ss_proof. Qed.

Lemma set_shadow_all : forall v, In v set_shadow_vals -> set_shadow_stmt (e_set_shadow v) v /\ 0 <= v < 256.
Proof.
intros v Hv. unfold set_shadow_vals in Hv.
repeat (destruct Hv as [<-|Hv]; [split; [first [exact set_shadow_00_spec | exact set_shadow_01_spec | exact set_shadow_02_spec
| exact set_shadow_03_spec | exact set_shadow_04_spec | exact set_shadow_05_spec | exact set_shadow_06_spec | exact set_shadow_07_spec
| exact set_shadow_f1_spec | exact set_shadow_f2_spec | exact set_shadow_f3_spec | exact set_shadow_f5_spec | exact set_shadow_f8_spec] | lia]|]).
destruct Hv.
Qed.

Lemma rta_setshadow_cells : forall Σ m, ART_A Σ m -> setshadow_cells m.
Proof. intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (_ & _ & SC & _) & _). exact SC. Qed.

Lemma rta_ASTA_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Theorem rta_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract RTA v.
Proof.
intros v Hv. destruct (set_shadow_all v Hv) as (SPEC & Hv8).
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n lo
FDO MST _ -> -> Hn HFS WR ART0 MI0 CALL.
intros T cf Hc Hk. cbn [ART rt_frames rt_live rt_sp0 RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0 in *.
destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (wr_at_rw_CB m d n WR ltac:(lia)) as (junk & DST).
pose proof (rta_setshadow_cells Σ m ART0) as SC.
destruct WR as (D0 & D1 & _).

assert (Hd : exists d', Z_to_bv 64 d = Z_to_bv 64 d' /\ 0 <= d' /\ d' + n < 2 ^ 64 /\ (n = 0 \/ d' = d)
/\ rw_cells bsegs m d' [CB (Z.to_nat n) junk]).
{ destruct (Z_lt_le_dec (d + n) (2 ^ 64)) as [L|L].
{ exists d. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; reflexivity | exact DST]. }
assert (Hn0 : n = 0).
{ destruct (Z.eq_dec n 0) as [E|NE]; [exact E|]. destruct (HFS (n - 1) ltac:(lia)) as (f & k & Hin & Hx1 & Hx2).
destruct (sep_fshad Σ m ART0 f k Hin) as (_ & X). unfold K_HIGH_SHADOW_hi in X. lia. }
subst n. assert (d = 2 ^ 64) as -> by lia. exists 0. split; [apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
split; [lia|]. split; [lia|]. split; [left; reflexivity|]. destruct DST as [[Hw _] _]. cbn in Hw. destruct Hw as [Hw _]. destruct junk; [|discriminate].
exact (rw_cells_CB0 m 0 ltac:(lia)). }
destruct Hd as (d' & Ed & D0' & D1' & Hdd & DST').
assert (W1 : evt bsegs (memset_postZ ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d' v n m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (e_set_shadow v) m)).
{ unfold entry_st. rewrite ESP, Ed. apply (SPEC ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d') (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d' n junk); [reflexivity | reflexivity | lia | lia | lia | exact DST' | exact SC | exact MI0]. }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (rta_ASTA_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hk. exists (Z_to_bv 64 d').
unfold icpt_post, ASTA in *. eapply AST_conseq; [exact Hc1| |auto]. intros ms PO.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & DC).
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].

assert (HCL : forall a : word, ~ aclient (live Σ) (frames Σ) usp (bv_unsigned a) -> m' a = m a).
{ intros a Ha. apply MU. cbn. split; [|exact I]. intros Hx. apply Ha. destruct Hdd as [ -> | -> ]; [lia|].
right; right; right; right. replace (bv_unsigned a) with (d + (bv_unsigned a - d)) by lia. apply HFS. lia. }
split.
{ split; [exact (ART_client_frame Σ m m' usp ART0 ltac:(unfold rtA_sp0, RT_STACK in *; lia) HCL WM)|]. split; [exact MI|]. split; [exact WM|].
exact (stk_wmono m m' _ _ ST WM). }
split.
{ intros a Ha Hout. apply MU. cbn. split; [|exact I]. intros Hx. apply Hout. destruct Hdd as [ -> | -> ]; lia. }
destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r, Z.mod_small in DB by lia.
destruct Hdd as [ -> | -> ]; [apply bytes_at_nil; lia | exact DB].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Ltac ss_proof := unfold set_shadow_stmt;
let jk := fresh "jk" in
intros ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6 ?F ?fc ?m ?sa ?n jk;
intros -> -> ?H0 ?Hn ?Hsn ?DST [?GOT ?RM] ?MI;
unfold g_got_real_memset, g_real_memset, musl_memset_entry in *;
do 6 zstep; eapply memset_callZ with (junk := jk); [eassumption | eassumption | lia | lia | lia | lia].

Lemma set_shadow_01_spec : set_shadow_stmt 0x6a0d8 1. Proof. ss_proof. Qed.
Lemma set_shadow_02_spec : set_shadow_stmt 0x6a0f0 2. Proof. ss_proof. Qed.
Lemma set_shadow_03_spec : set_shadow_stmt 0x6a108 3. Proof. ss_proof. Qed.
Lemma set_shadow_04_spec : set_shadow_stmt 0x6a120 4. Proof. ss_proof. Qed.
Lemma set_shadow_05_spec : set_shadow_stmt 0x6a138 5. Proof. ss_proof. Qed.
Lemma set_shadow_06_spec : set_shadow_stmt 0x6a150 6. Proof. ss_proof. Qed.
Lemma set_shadow_07_spec : set_shadow_stmt 0x6a168 7. Proof. ss_proof. Qed.
Lemma set_shadow_f1_spec : set_shadow_stmt 0x6a180 241. Proof. ss_proof. Qed.
Lemma set_shadow_f2_spec : set_shadow_stmt 0x6a198 242. Proof. ss_proof. Qed.
Lemma set_shadow_f3_spec : set_shadow_stmt 0x6a1b0 243. Proof. ss_proof. Qed.

Lemma set_shadow_all : forall v, In v set_shadow_vals -> set_shadow_stmt (e_set_shadow v) v /\ 0 <= v < 256.
Proof.
intros v Hv. unfold set_shadow_vals in Hv.
repeat (destruct Hv as [<-|Hv]; [split; [first [exact set_shadow_00_spec | exact set_shadow_01_spec | exact set_shadow_02_spec
| exact set_shadow_03_spec | exact set_shadow_04_spec | exact set_shadow_05_spec | exact set_shadow_06_spec | exact set_shadow_07_spec
| exact set_shadow_f1_spec | exact set_shadow_f2_spec | exact set_shadow_f3_spec | exact set_shadow_f5_spec | exact set_shadow_f8_spec] | lia]|]).
destruct Hv.
Qed.

Lemma rta_setshadow_cells : forall Σ m, ART_A Σ m -> setshadow_cells m.
Proof. intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (_ & _ & SC & _) & _). exact SC. Qed.

Lemma rta_ASTA_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Theorem rta_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract RTA v.
Proof.
intros v Hv. destruct (set_shadow_all v Hv) as (SPEC & Hv8).
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n lo
FDO MST _ -> -> Hn HFS WR ART0 MI0 CALL.
intros T cf Hc Hk. cbn [ART rt_frames rt_live rt_sp0 RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0 in *.
destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
destruct (wr_at_rw_CB m d n WR ltac:(lia)) as (junk & DST).
pose proof (rta_setshadow_cells Σ m ART0) as SC.
destruct WR as (D0 & D1 & _).

assert (Hd : exists d', Z_to_bv 64 d = Z_to_bv 64 d' /\ 0 <= d' /\ d' + n < 2 ^ 64 /\ (n = 0 \/ d' = d)
/\ rw_cells asegs m d' [CB (Z.to_nat n) junk]).
{ destruct (Z_lt_le_dec (d + n) (2 ^ 64)) as [L|L].
{ exists d. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; reflexivity | exact DST]. }
assert (Hn0 : n = 0).
{ destruct (Z.eq_dec n 0) as [E|NE]; [exact E|]. destruct (HFS (n - 1) ltac:(lia)) as (f & k & Hin & Hx1 & Hx2).
destruct (sep_fshad Σ m ART0 f k Hin) as (_ & X). unfold K_HIGH_SHADOW_hi in X. lia. }
subst n. assert (d = 2 ^ 64) as -> by lia. exists 0. split; [apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
split; [lia|]. split; [lia|]. split; [left; reflexivity|]. destruct DST as [[Hw _] _]. cbn in Hw. destruct Hw as [Hw _]. destruct junk; [|discriminate].
exact (rw_cells_CB0 m 0 ltac:(lia)). }
destruct Hd as (d' & Ed & D0' & D1' & Hdd & DST').
assert (W1 : evt asegs (memset_postZ ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d' v n m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (e_set_shadow v) m)).
{ unfold entry_st. rewrite ESP, Ed. apply (SPEC ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d') (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d' n junk); [reflexivity | reflexivity | lia | lia | lia | exact DST' | exact SC | exact MI0]. }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (rta_ASTA_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hk. exists (Z_to_bv 64 d').
unfold icpt_post, ASTA in *. eapply AST_conseq; [exact Hc1| |auto]. intros ms PO.
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI & DC).
exists m'. split; [rewrite ESP; do 14 eexists; reflexivity|].

assert (HCL : forall a : word, ~ aclient (live Σ) (frames Σ) usp (bv_unsigned a) -> m' a = m a).
{ intros a Ha. apply MU. cbn. split; [|exact I]. intros Hx. apply Ha. destruct Hdd as [ -> | -> ]; [lia|].
right; right; right; right. replace (bv_unsigned a) with (d + (bv_unsigned a - d)) by lia. apply HFS. lia. }
split.
{ split; [exact (ART_client_frame Σ m m' usp ART0 ltac:(unfold rtA_sp0, RT_STACK in *; lia) HCL WM)|]. split; [exact MI|]. split; [exact WM|].
exact (stk_wmono m m' _ _ ST WM). }
split.
{ intros a Ha Hout. apply MU. cbn. split; [|exact I]. intros Hx. apply Hout. destruct Hdd as [ -> | -> ]; lia. }
destruct DC as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r, Z.mod_small in DB by lia.
destruct Hdd as [ -> | -> ]; [apply bytes_at_nil; lia | exact DB].
Qed.
