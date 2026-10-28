(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Mem Frame Cells Step Arr Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import F_memset R_setshadow R_poison RT_iface D_defs RT_state RT_rep RT_frame RT_facts0 RT_sep RT_facts RT_artfacts I_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac ss_proof := unfold set_shadow_stmt;
  let jk := fresh "jk" in
  intros ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6 ?F ?fc ?m ?sa ?n jk;
  intros -> -> ?H0 ?Hn ?Hsn ?DST [?GOT ?RM] ?MI;
  unfold g_got_real_memset, g_real_memset, musl_memset_entry in *;
  do 6 zstep; eapply memset_callZ with (junk := jk); [eassumption | eassumption | lia | lia | lia | lia].

Lemma set_shadow_01_spec : set_shadow_stmt 0x1c0550 1. Proof. ss_proof. Qed.
Lemma set_shadow_02_spec : set_shadow_stmt 0x1c0568 2. Proof. ss_proof. Qed.
Lemma set_shadow_03_spec : set_shadow_stmt 0x1c0580 3. Proof. ss_proof. Qed.
Lemma set_shadow_04_spec : set_shadow_stmt 0x1c0598 4. Proof. ss_proof. Qed.
Lemma set_shadow_05_spec : set_shadow_stmt 0x1c05b0 5. Proof. ss_proof. Qed.
Lemma set_shadow_06_spec : set_shadow_stmt 0x1c05c8 6. Proof. ss_proof. Qed.
Lemma set_shadow_07_spec : set_shadow_stmt 0x1c05e0 7. Proof. ss_proof. Qed.
Lemma set_shadow_f1_spec : set_shadow_stmt 0x1c05f8 241. Proof. ss_proof. Qed.
Lemma set_shadow_f2_spec : set_shadow_stmt 0x1c0610 242. Proof. ss_proof. Qed.
Lemma set_shadow_f3_spec : set_shadow_stmt 0x1c0628 243. Proof. ss_proof. Qed.

Lemma set_shadow_all : forall v, In v set_shadow_vals -> set_shadow_stmt (e_set_shadow v) v /\ 0 <= v < 256.
Proof.
  intros v Hv. unfold set_shadow_vals in Hv.
  repeat (destruct Hv as [<-|Hv]; [split; [first [exact set_shadow_00_spec | exact set_shadow_01_spec | exact set_shadow_02_spec
    | exact set_shadow_03_spec | exact set_shadow_04_spec | exact set_shadow_05_spec | exact set_shadow_06_spec | exact set_shadow_07_spec
    | exact set_shadow_f1_spec | exact set_shadow_f2_spec | exact set_shadow_f3_spec | exact set_shadow_f5_spec | exact set_shadow_f8_spec] | lia]|]).
  destruct Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  (* [comment removed for export] *)
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
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  (* [comment removed for export] *)
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
