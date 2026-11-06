(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf
X0id X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5 X0db X0dd
X0fd X0fc X0fe X0fi.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13w X13y X15y X15x X15z X163.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X163.
Import ListNotations.
Open Scope Z_scope.

Section RfArt.
Variables (Σ : rtsA) (c usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x400 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) usp).

Let HG : geo_ok Σ := geo_of_wf0 Σ HW0.

Theorem refill_ART : forall (m m' : mem), ARTc Σ m -> munch W m m' -> wmono bsegs m m' ->
reg_rep SB c (refill_reg (pr Σ c) c) m' ->
pclass_rep T c true (refill_ca (pr Σ c) c) m' ->
(forall c', 1 <= c' <= 31 -> c' <> c -> pclass_rep T c' true (ca Σ c') m') ->
(forall i, (length (r_st (pr Σ c)) <= i)%nat -> nth_error (r_st (refill_reg (pr Σ c) c)) i = Some CkIdle -> pchunk SB c i CkIdle m') ->
ARTc (refillΣ Σ c) m'.
Proof.
intros m m' ART MW WM REG PCc PCo NEW.
pose proof (rz_img Σ c usp HG Hc Hsp) as HWi. pose proof (rz_T Σ c usp HG Hc Hsp) as HWt.
pose proof (rz_grant Σ c usp HG Hc Hsp) as HWg. pose proof (rz_grant67 Σ c usp HG Hc Hsp) as HWg67.
pose proof (rz_ris Σ c usp HG Hc Hsp) as HWr. pose proof (rz_fa Σ c usp HG Hc Hsp) as HWf.
pose proof (rz_slot Σ c usp HG Hc Hsp) as HWs. pose proof (rz_shad_slot Σ c usp HG Hc Hsp) as HWss.
pose proof (rz_shad_reg Σ c usp HG Hc Hsp) as HWsr. pose proof (rz_shad_app Σ c usp HG Hc Hsp) as HWsa.
pose proof (rz_secmap Σ c usp HG Hc Hsp) as HWm.
pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
destruct ART as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
apply ARTc_intro; cbn [refillΣ lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames fsc].
-
apply (consts_rep_frame L m m' CR); [|exact WM]. intros a Ha. apply MW.
destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
+ rewrite E. unfold W_R. cbn [outside]. pose proof (rz_geo Σ c HG Hc) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
pose proof (se_disj Σ HG) as (_ & T4 & ATP). pose proof (rz_shad Σ c HG Hc) as (Q1 & Q2).
clear - K4 K5 K6 K8 K11 ATP T4 Q1 Q2 K3 Hsp Hc. unfold rb, kUserCap, rinfo, RIS_of, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SHB in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (kv_consts Σ W (TZ_R T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_R; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
-
intros c' Hc'. cbn [refillΣ pr lay]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact REG|].
exact (reg_rep_transport W _ c' _ m m' (PR c' Hc') MW WM (kv_reg Σ W [c] HG HWr HWf HWsr c' Hc' ltac:(intros [E|[]]; exact (Hcc (eq_sym E))))).
-
intros c' Hc'. cbn [refillΣ ca ca_init lay]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact PCc | exact (PCo c' Hc' Hcc)].
-
destruct CH as [P Sc]. split.
+ intros c' i' st Hc' Hn'. destruct (rfs_st Σ c Hc HW0 c' i' st Hn') as [Hn0|(-> & -> & Hi)].
* apply (pchunk_transport W _ c' i' _ m m' (P c' i' st Hc' Hn0) MW WM). exact (kv_pchunk Σ W [] HG HWs HWss c' i' st Hc' Hn0 ltac:(intros [])).
* apply NEW; [exact Hi|]. cbn [refillΣ pr] in Hn'. rewrite Z.eqb_refl in Hn'. exact Hn'.
+ intros k s Hk. apply (schunk_transport W k s m m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
-
exact (sec_rep_transport W _ m m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
-
apply (quar_rep_transport W _ m m' QR MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & _) & _).
eapply kv_quar; try eassumption.
+ unfold TZ_R, qcacheT. cbn [disjoint_from]. split; [lia | exact I].
+ apply Forall_forall. intros; exact I.
+ intros i _ [].
-
pose proof HW0 as (_ & _ & _ & _ & _ & _ & _ & DOK & _).
exact (dep_rep_transport W L (dep Σ) m m' DR DOK MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I) HWg67)).
-
exact (fs_rep_transport W _ m m' FR MW WM (kv_fs Σ W [] (TZ_R T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
ltac:(unfold TZ_R; cbn; repeat split; try exact I; lia))).
- exact (ia_rep_transport W _ m m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
- exact (shadow_rep_transport W _ _ m m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
- exact (vis_rep_wmono _ m m' VIS WM).
Qed.

End RfArt.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section RfArt.
Variables (Σ : rtsA) (c usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x400 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) usp).

Let HG : geo_ok Σ := geo_of_wf0 Σ HW0.

Theorem refill_ART : forall (m m' : mem), ARTc Σ m -> munch W m m' -> wmono asegs m m' ->
reg_rep SB c (refill_reg (pr Σ c) c) m' ->
pclass_rep T c true (refill_ca (pr Σ c) c) m' ->
(forall c', 1 <= c' <= 31 -> c' <> c -> pclass_rep T c' true (ca Σ c') m') ->
(forall i, (length (r_st (pr Σ c)) <= i)%nat -> nth_error (r_st (refill_reg (pr Σ c) c)) i = Some CkIdle -> pchunk SB c i CkIdle m') ->
ARTc (refillΣ Σ c) m'.
Proof.
intros m m' ART MW WM REG PCc PCo NEW.
pose proof (rz_img Σ c usp HG Hc Hsp) as HWi. pose proof (rz_T Σ c usp HG Hc Hsp) as HWt.
pose proof (rz_grant Σ c usp HG Hc Hsp) as HWg. pose proof (rz_grant67 Σ c usp HG Hc Hsp) as HWg67.
pose proof (rz_ris Σ c usp HG Hc Hsp) as HWr. pose proof (rz_fa Σ c usp HG Hc Hsp) as HWf.
pose proof (rz_slot Σ c usp HG Hc Hsp) as HWs. pose proof (rz_shad_slot Σ c usp HG Hc Hsp) as HWss.
pose proof (rz_shad_reg Σ c usp HG Hc Hsp) as HWsr. pose proof (rz_shad_app Σ c usp HG Hc Hsp) as HWsa.
pose proof (rz_secmap Σ c usp HG Hc Hsp) as HWm.
pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & _ & GT3 & _).
destruct ART as (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS).
apply ARTc_intro; cbn [refillΣ lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames fsc].
-
apply (consts_rep_frame L m m' CR); [|exact WM]. intros a Ha. apply MW.
destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
+ rewrite E. unfold W_R. cbn [outside]. pose proof (rz_geo Σ c HG Hc) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
pose proof (se_disj Σ HG) as (_ & T4 & ATP). pose proof (rz_shad Σ c HG Hc) as (Q1 & Q2).
clear - K4 K5 K6 K8 K11 ATP T4 Q1 Q2 K3 Hsp Hc. unfold rb, kUserCap, rinfo, RIS_of, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SHB in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
+ apply (kv_consts Σ W (TZ_R T) [] HWi HWt HWg); [apply Forall_forall; intros; exact I | unfold TZ_R; cbn; repeat split; try exact I; lia | exact Ha | exact NE].
-
intros c' Hc'. cbn [refillΣ pr lay]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact REG|].
exact (reg_rep_transport W _ c' _ m m' (PR c' Hc') MW WM (kv_reg Σ W [c] HG HWr HWf HWsr c' Hc' ltac:(intros [E|[]]; exact (Hcc (eq_sym E))))).
-
intros c' Hc'. cbn [refillΣ ca ca_init lay]. destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact PCc | exact (PCo c' Hc' Hcc)].
-
destruct CH as [P Sc]. split.
+ intros c' i' st Hc' Hn'. destruct (rfs_st Σ c Hc HW0 c' i' st Hn') as [Hn0|(-> & -> & Hi)].
* apply (pchunk_transport W _ c' i' _ m m' (P c' i' st Hc' Hn0) MW WM). exact (kv_pchunk Σ W [] HG HWs HWss c' i' st Hc' Hn0 ltac:(intros [])).
* apply NEW; [exact Hi|]. cbn [refillΣ pr] in Hn'. rewrite Z.eqb_refl in Hn'. exact Hn'.
+ intros k s Hk. apply (schunk_transport W k s m m' (Sc k s Hk) MW WM). exact (kv_schunk Σ W [] HG HWsa HWm k s Hk ltac:(intros [])).
-
exact (sec_rep_transport W _ m m' SR MW WM (kv_sec Σ W [] HG HWi HWg ltac:(apply Forall_forall; intros; exact I))).
-
apply (quar_rep_transport W _ m m' QR MW WM). pose proof HW0 as (_ & _ & _ & _ & (_ & _ & QB & _) & _).
eapply kv_quar; try eassumption.
+ unfold TZ_R, qcacheT. cbn [disjoint_from]. split; [lia | exact I].
+ apply Forall_forall. intros; exact I.
+ intros i _ [].
-
pose proof HW0 as (_ & _ & _ & _ & _ & _ & _ & DOK & _).
exact (dep_rep_transport W L (dep Σ) m m' DR DOK MW WM (kv_dep Σ W [] HWi ltac:(apply Forall_forall; intros; exact I) HWg67)).
-
exact (fs_rep_transport W _ m m' FR MW WM (kv_fs Σ W [] (TZ_R T) [] HG HWi HWt HWg HWsa ltac:(apply Forall_forall; intros; exact I)
ltac:(unfold TZ_R; cbn; repeat split; try exact I; lia))).
- exact (ia_rep_transport W _ m m' IR MW WM (kv_ia W [] HWi ltac:(apply Forall_forall; intros; exact I))).
- exact (shadow_rep_transport W _ _ m m' SHR MW WM (kv_shadow Σ W [] HG HWsa)).
- exact (vis_rep_wmono _ m m' VIS WM).
Qed.

End RfArt.
