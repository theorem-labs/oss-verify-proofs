(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeD RT_freeI RT_freeS RT_freeSA RT_drain_defs RT_drain_pure RT_drain_led RT_drain_kit RT_dsec_geo RT_dsec_kit RT_dsec_fkit RT_dsec_nw RT_dsec_art.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Definition pass_d (Σ : rtsA) (k : nat) (s : secst) (D' : depot) : rtsA := set_sec (free_s Σ k s D') (sec Σ).
Definition pass_s (Σ : rtsA) (k : nat) (s : secst) (D' : depot) : rtsA := recs (pass_d Σ k s D') k.

Lemma pass_d_fields : forall Σ k s D', lay (pass_d Σ k s D') = lay Σ /\ pr (pass_d Σ k s D') = pr Σ /\ ca (pass_d Σ k s D') = ca Σ
  /\ ca_init (pass_d Σ k s D') = ca_init Σ /\ sec (pass_d Σ k s D') = sec Σ /\ sec_nres (pass_d Σ k s D') = sec_nres Σ
  /\ aw (pass_d Σ k s D') = aw Σ /\ ql (pass_d Σ k s D') = ql Σ /\ qg (pass_d Σ k s D') = qg Σ /\ dep (pass_d Σ k s D') = D'
  /\ credit (pass_d Σ k s D') = credit Σ /\ live (pass_d Σ k s D') = live_remove (s_ubeg s) (live Σ)
  /\ frames (pass_d Σ k s D') = frames Σ.
Proof. intros. repeat split; reflexivity. Qed.

Lemma pass_s_fields : forall Σ k s D', lay (pass_s Σ k s D') = lay Σ /\ pr (pass_s Σ k s D') = pr Σ /\ ca (pass_s Σ k s D') = ca Σ
  /\ ca_init (pass_s Σ k s D') = ca_init Σ /\ sec (pass_s Σ k s D') = swap_remove k (sec Σ) /\ sec_nres (pass_s Σ k s D') = sec_nres Σ
  /\ aw (pass_s Σ k s D') = aw Σ /\ ql (pass_s Σ k s D') = ql Σ /\ qg (pass_s Σ k s D') = qg Σ /\ dep (pass_s Σ k s D') = D'
  /\ credit (pass_s Σ k s D') = credit Σ /\ live (pass_s Σ k s D') = live_remove (s_ubeg s) (live Σ)
  /\ frames (pass_s Σ k s D') = frames Σ.
Proof. intros. repeat split; reflexivity. Qed.

Lemma pass_d_geo : forall Σ k s D', geo_ok Σ -> geo_ok (pass_d Σ k s D').
Proof. intros Σ k s D' H. exact H. Qed.

Lemma pass_d_allow : forall Σ k s D', rtA_allow (pass_d Σ k s D') = rtA_allow Σ.
Proof. intros. reflexivity. Qed.

Section PassWf.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (D' : depot).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = false.
Hypothesis HDok : depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HDinv : dep_step (dep Σ) D'.
#[local] Notation Σ2 := (pass_s Σ k s D').

Theorem pass_wf : rt_wf Σ2.
Proof using HA Hk Hq HDok HDinv.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & (RC1 & RC2)).
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  assert (LRI : In (s_ubeg s, s_n s) (live Σ)) by (destruct W3 as (_ & _ & _ & _ & V5); exact (V5 s (nth_error_In _ _ Hk) Hq)).
  pose proof (live_remove_length_in _ _ (live Σ) LRI) as LRL.
  assert (POT' : dep_pot (d_n D') (Z.of_nat (length (live_remove (s_ubeg s) (live Σ)))) (credit Σ))
    by (apply (dep_pot_free (dep Σ) D' (Z.of_nat (length (live Σ))) _ _ HDinv W9); lia).
  pose proof (dep_inv_bounds D' _ _ (proj1 HDinv) POT' ltac:(lia) ltac:(destruct W7 as (C0 & _); exact C0)) as (B1 & B2).

  assert (Hsk : forall s', In s' (sec Σ) -> s_mb s' <> s_mb s -> In s' (swap_remove k (sec Σ))).
  { intros s' Hs' Hne. destruct (In_nth_error _ _ Hs') as (j & Hj). apply (swap_remove_keep k _ j s' Hkl); [|exact Hj].
    intros ->. rewrite Hk in Hj. injection Hj as <-. exact (Hne eq_refl). }
  assert (Hsk' : forall s', In s' (swap_remove k (sec Σ)) -> In s' (sec Σ) /\ s_mb s' <> s_mb s).
  { intros s' Hs'. destruct (swap_remove_other k _ s' Hkl Hs') as (j & Hj & Ej). split; [exact (nth_error_In _ _ Ej)|].
    intros E. exact (Hj (sec_pos_inj Σ j k s' s W4 Ej Hk E)). }
  assert (SWR : sec_wf (recs Σ k)) by exact (sec_wf_recs Σ k s W4 Hk).
  pose proof (pass_s_fields Σ k s D') as (El & Epr & Eca & Eci & Es & En & Ea & Eql & Eqg & Ed & Ec & Elv & Efr).
  unfold rt_wf. rewrite El, Ed, Elv, Ec.
  split; [exact W1|]. split; [exact W2|]. split.
  {
    unfold live_wf. rewrite Elv, Epr, El, Es. destruct W3 as (V1 & V2 & V3 & V4 & V5).
    split; [pose proof (live_remove_length (s_ubeg s) (live Σ)); lia|]. split; [apply NoDup_ListNoDup; apply nodup_live_remove; apply NoDup_ListNoDup; exact V2|].
    split; [|split].
    - intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
      destruct (V3 p' n' Hin) as [X|(t & Ht & Htq & Htn & Ep)]; [left; exact X|right].
      exists t. split; [|split; [exact Htq | split; [exact Htn | exact Ep]]]. apply Hsk; [exact Ht|].
      intros E. apply Hne. rewrite Ep. unfold s_ubeg. rewrite E. reflexivity.
    - intros c' i' n' Hc' Hn'. apply live_remove_In. cbn [fst]. split; [exact (V4 c' i' n' Hc' Hn')|].
      intros E. exact (fp_sec_ne Σ m c' i' n' HA Hc' Hn' s (nth_error_In _ _ Hk) (eq_sym E)).
    - intros t Ht Htq. destruct (Hsk' t Ht) as (Ht0 & Hne). apply live_remove_In. cbn [fst]. split; [exact (V5 t Ht0 Htq)|].
      intros E. apply Hne. unfold s_ubeg in E. lia. }
  split; [exact SWR|].
  split.
  {
    unfold quar_wf. rewrite Eql, Eqg, Epr, El. destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [|split; [exact Q7 | exact Q8]].
    unfold qents in *. rewrite Eql, Eqg. apply Forall_forall. intros e He.
    destruct (proj1 (Forall_forall _ _) Q6 e He) as [X|(t & Ht & Htq & Htn & Ee)]; [left; exact X|right].
    exists t. rewrite Es. split; [|split; [exact Htq | split; [exact Htn | exact Ee]]]. apply Hsk; [exact Ht|].
    intros E. destruct (In_nth_error _ _ Ht) as (j & Hj). pose proof (sec_pos_inj Σ j k t s W4 Hj Hk E) as ->.
    rewrite Hk in Hj. injection Hj as <-. rewrite Hq in Htq. discriminate Htq. }
  split; [exact W6|]. split.
  {
    destruct W7 as (G1 & G2 & G3 & G4 & G5). unfold budget_wf. rewrite Ea, Ec.
    pose proof (secsum_recs Σ k s Hk) as Ess.
    assert (ESS : secsum Σ2 = secsum (recs Σ k)) by reflexivity.
    assert (Hsn : 64513 <= s_n s) by (destruct W4 as (_ & _ & _ & HF & _); destruct (proj1 (Forall_forall _ _) HF s (nth_error_In _ _ Hk)) as ((X & _) & _); exact X).
    pose proof (smsz_pos (s_n s) Hsn).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    split; [apply rt_eager_bound; [exact W2 | exact SWR | rewrite ESS; unfold CREDIT0 in *; lia] | rewrite ESS; lia]. }
  split; [exact HDok|]. split; [exact POT'|]. split; [lia|]. split; [exact (proj1 HDinv)|].

  unfold rt_count, qents. rewrite Eql, Eqg, Epr, El, Es. split.
  - exact RC1.
  - intros s' Hs' Hq'. exact (RC2 s' (proj1 (Hsk' s' Hs')) Hq').
Qed.

End PassWf.

Definition ARTcK (Σ : rtsA) (k : nat) (m : mem) : Prop :=
  consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m
  /\ ((forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk (ann Σ) (l_SB (lay Σ)) c i st m)
      /\ (forall j t, nth_error (sec Σ) j = Some t -> j <> k -> schunk (ann Σ) j t m))
  /\ sec_rep Σ m /\ quar_rep Σ m
  /\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

Section SegPK.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = false.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp).
#[local] Notation TZ := [(l_T (lay Σ) + 2824, l_T (lay Σ) + 2840)].
#[local] Notation ss_img' := (ss_img Σ m k s usp HA Hk Hsp).
#[local] Notation ss_Tz' := (ss_Tz Σ m k s usp HA Hk Hsp).
#[local] Notation ss_grant' := (ss_grant Σ m k s usp HA Hk Hsp).
#[local] Notation ss_ris' := (ss_ris Σ m k s usp HA Hk Hsp).
#[local] Notation ss_fa' := (ss_fa Σ m k s usp HA Hk Hsp).
#[local] Notation ss_slot' := (ss_slot Σ m k s usp HA Hk Hsp).
#[local] Notation ss_shad_slot' := (ss_shad_slot Σ m k s usp HA Hk Hsp).
#[local] Notation ss_shad_reg' := (ss_shad_reg Σ m k s usp HA Hk Hsp).
#[local] Notation ss_shad_app' := (ss_shad_app Σ m k s usp HA Hk Hsp).
#[local] Notation ss_secmap' := (ss_secmap Σ m k s usp HA Hk Hsp).

Theorem segP_ARTK : forall (m' : mem) (D' : depot), munch W m m' -> wmono bsegs m m' ->
  depot_rep D' (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB m' -> hash_of (d_hs D') 1 = hash_of (d_hs (dep Σ)) 1 ->
  ARTcK (pass_d Σ k s D') k m'.
Proof using HA Hk Hq Hsp.
  intros m' D' MU WM DR Dh.
  pose proof (geo_of_ART Σ m HA) as HG.
  pose proof (kv_reg Σ W [] HG (ris_of_whole SB W [] ss_ris') (fun c0 a k' Hc0 _ => ss_fa' c0 a k' Hc0)
                (fun c0 a k' Hc0 _ => ss_shad_reg' c0 a k' Hc0)) as KR.
  pose proof (kv_pchunk Σ W [] HG ss_slot' ss_shad_slot') as KP.
  pose proof (kv_schunk Σ W [k] HG ss_shad_app' ss_secmap') as KS.
  unfold ARTcK. change (lay (pass_d Σ k s D')) with (lay Σ). change (rtA_allow (pass_d Σ k s D')) with (rtA_allow Σ).
  split; [exact (ss_consts Σ m k s usp HA Hk Hsp m' MU WM)|].
  split; [intros c' Hc'; exact (reg_rep_transport W _ c' _ m m' (ART_prim Σ m HA c' Hc') MU WM (KR c' Hc' ltac:(intros [])))|].
  split; [intros c' Hc'; exact (pclass_rep_transport W _ c' _ _ m m' (ART_cache Σ m HA c' Hc') MU WM
                                  (kv_pclass Σ W TZ ss_Tz' c' Hc' ltac:(cbn; split; [unfold pc_addr; lia | exact I])))|].
  split.
  { destruct (ART_chunk Σ m HA) as [P Sc]. split.
    + intros c' i' st Hc' Hn'. exact (pchunk_transport W _ c' i' st m m' (P c' i' st Hc' Hn') MU WM (KP c' i' st Hc' Hn' (fun X => X))).
    + intros k' t Hk' Hne. change (sec (pass_d Σ k s D')) with (sec Σ) in Hk'.
      exact (schunk_transport W k' t m m' (Sc k' t Hk') MU WM (KS k' t Hk' ltac:(intros [E|[]]; exact (Hne (eq_sym E))))). }
  split; [exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM
                   (kv_sec Σ W IZ_A HG ss_img' ss_grant' ltac:(apply dsjb_all'; vm_compute; reflexivity)))|].
  split; [exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM
             (kv_quar Σ W [] TZ IZ_A HG ss_img' ss_Tz' ss_slot' ltac:(cbn; split; [unfold qcacheT; lia | exact I])
                ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(intros i' Hi' [])
                ltac:(pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & (_ & _ & HBt & _) & _); exact HBt)))|].
  split; [unfold dep_rep; change (dep (pass_d Σ k s D')) with D'; rewrite Dh; exact DR|].
  split; [exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM (kv_fs Σ W [k] TZ IZ_A HG ss_img' ss_Tz' ss_grant' ss_shad_app'
             ltac:(apply dsjb_all'; vm_compute; reflexivity) ltac:(cbn; split; [lia | exact I])))|].
  split; [exact (ia_rep_transport W Σ m m' (ART_ia Σ m HA) MU WM (kv_ia W IZ_A ss_img' ltac:(apply dsjb_all'; vm_compute; reflexivity)))|].
  split; [exact (shadow_rep_transport W _ m m' (ART_shadow Σ m HA) MU WM (kv_shadow Σ W [k] HG ss_shad_app'))|].
  exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

End SegPK.

Section DsArtK.
Variables (Σ : rtsA) (m m' : mem) (W : list ivl) (k : nat) (s lst : secst) (TZ : list ivl) (zlo zhi : Z) (ws : list word).
Hypothesis HG : geo_ok Σ.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hlst : nth_error (sec Σ) (length (sec Σ) - 1) = Some lst.
Hypothesis HTZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) TZ.
Hypothesis HTZd : disjoint_from TZ (l_T (lay Σ)) 0x50 /\ disjoint_from TZ (l_T (lay Σ) + 48) 16 /\ disjoint_from TZ (l_T (lay Σ) + 0xc60) 1
                  /\ (forall c', 1 <= c' <= 31 -> disjoint_from TZ (pc_addr (l_T (lay Σ)) c') 80) /\ disjoint_from TZ (qcacheT (l_T (lay Σ))) 32.
Hypothesis Hzlo : l_ACEIL (lay Σ) <= zlo.
Hypothesis Hzlh : zlo <= zhi.
Hypothesis HW : Forall (dzoneP Σ [] [] [k; (length (sec Σ) - 1)%nat] TZ IZ_S [] zlo zhi) W.
Hypothesis HA : ARTcK Σ k m.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation NS := (length (sec Σ)).
#[local] Notation da_img' := (da_img Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_Tz' := (da_Tz Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_grant' := (da_grant Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_grant67' := (da_grant67 Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_ris' := (da_ris Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_fa' := (da_fa Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_slot' := (da_slot Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_shad_slot' := (da_shad_slot Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_shad_reg' := (da_shad_reg Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_shad_app' := (da_shad_app Σ W k TZ zlo zhi HG HTZ Hzlo HW).
#[local] Notation da_secmap' := (da_secmap Σ W k TZ zlo zhi HG HTZ Hzlo HW).

Lemma da_constsK : consts_rep L m'.
Proof using HG HTZ HTZd Hzlo HW HA MU WM.
  destruct HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  apply (consts_rep_frame L m m' (proj1 HA)); [|exact WM].
  intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
  + apply (disjoint_outside W (T + 0xc60) 1); [|lia]. apply da_Tz'; [lia | lia | exact Z3].
  + apply (kw_consts Σ W TZ IZ_S da_img' da_Tz' da_grant'); [apply dsjb_all; vm_compute; reflexivity | exact Z1 | exact Ha | exact NE].
Qed.

Theorem ds_artcK :
  sec_core m' (l_PAB L) (sec_nres Σ) (Z.of_nat NS - 1) -> sec_pad m' -> sec_junk m' ->
  u64arr bsegs m' (l_PAB L) (upd ws k (Z_to_bv 64 (s_mb lst))) -> Z.of_nat (length ws) = sec_nres Σ ->
  firstn NS ws = map (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σ) ->
  ((k < NS - 1)%nat -> schunk_avoid_nh W lst /\ rw_cells bsegs m' (s_mb lst + 24) [C8 (Z_to_bv 64 (Z.of_nat k))]) ->
  ARTc (recs Σ k) m'.
Proof using HG Hk Hlst HTZ HTZd Hzlo HW HA Hdep HQB MU WM.
  intros HSC HSP HSJ HWS HWl HWf HLST. pose proof HTZd as (Z1 & Z2 & Z3 & Z4 & Z5).
  pose proof da_constsK as HC'.
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kw_reg Σ W [] HG da_ris' da_fa' da_shad_reg') as KR.
  pose proof (kw_pchunk Σ W [] HG da_slot' da_shad_slot') as KP.
  pose proof (kw_schunk Σ W [k; (NS - 1)%nat] HG da_shad_app' da_secmap') as KS.
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  pose proof HG as (_ & _ & HSW & _). pose proof HSW as (SW1 & SW2 & SW3 & _).
  assert (Hnres : sec_nres Σ = 0x4000) by (apply SW3; intros E; rewrite E in Hk; destruct k; discriminate).
  apply ARTc_intro.
  - exact HC'.
  - intros c' Hc'. exact (reg_rep_transport W _ c' _ m m' (A2 c' Hc') MU WM (KR c' Hc' (fun X => X))).
  - intros c' Hc'. exact (pclass_rep_transport W _ c' _ _ m m' (A3 c' Hc') MU WM (kw_pclass Σ W TZ da_Tz' c' Hc' (Z4 c' Hc'))).
  - destruct A4 as [P Sc]. split.
    + intros c' i' st0 Hc' Hn'. exact (pchunk_transport W _ c' i' st0 m m' (P c' i' st0 Hc' Hn') MU WM (KP c' i' st0 Hc' Hn' (fun X => X))).
    + intros j' t Hj'. cbn [recs set_sec sec] in Hj'. destruct (swap_remove_nth k (sec Σ) j' t Hkl Hj') as (Nt & Hlt).
      destruct (Nat.eqb_spec j' k) as [->|Hne].
      * rewrite Hlst in Nt. injection Nt as <-. destruct (HLST Hlt) as (AV & HI).
        exact (schunk_transport_nh W _ k lst m m' (Sc _ lst Hlst ltac:(clear - Hlt; lia)) MU WM AV HI).
      * exact (schunk_transport W j' t m m' (Sc j' t Nt Hne) MU WM (KS j' t Nt ltac:(intros [E|[E|[]]]; [exact (Hne (eq_sym E)) | lia]))).
  - pose proof A5 as (_ & _ & _ & SPG & SRG & _ & NMC).
    unfold sec_rep. cbn [recs set_sec sec sec_nres lay].
    rewrite (swap_remove_length k (sec Σ) Hkl).
    split; [rewrite Nat2Z.inj_sub by lia; exact HSC|]. split; [exact HSP|].
    split.
    { exists (upd ws k (Z_to_bv 64 (s_mb lst))). split; [exact HWS|]. split; [rewrite upd_length; exact HWl|].
      apply (ds_upd_prefix (fun s0 => Z_to_bv 64 (s_mb s0)) (sec Σ) ws k lst HWf); [|exact Hkl | exact Hlst].
      rewrite Hnres in HWl. clear - HWl SW1. unfold SEC_MAX in *. lia. }
    unfold sec_page, sec_range, name_cells in *. destruct NMC as (NM1 & NM2).
    split; [apply (rw_cells_transport bsegs W m m' _ _ SPG MU WM); cbn [cells_size csize Nat.add Z.of_nat];
            apply da_img'; [unfold i_sec_page, INST, g_instance; lia | unfold i_sec_page, INST, g_instance, SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity]|].
    split; [apply (rw_cells_transport bsegs W m m' _ _ SRG MU WM); cbn [cells_size csize Nat.add Z.of_nat];
            apply da_img'; [unfold i_sec_range, INST, g_instance; lia | unfold i_sec_range, INST, g_instance, SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity]|].
    split; [exact HSJ|].
    split; [apply (rw_cells_transport bsegs W m m' _ _ NM1 MU WM); cbn [cells_size csize Nat.add Z.of_nat];
            apply da_img'; [lia | unfold SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity]|].
    apply (rw_cells_transport bsegs W m m' _ _ NM2 MU WM); cbn [cells_size csize Nat.add Z.of_nat];
      apply da_img'; [lia | unfold SEGTOP_A; lia | apply dsj1; vm_compute; reflexivity].
  - exact (quar_rep_transport W Σ m m' A6 MU WM
             (kw_quar Σ W [] TZ IZ_S HG da_img' da_Tz' da_slot' Z5 ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' Hi' []) HQB)).
  - exact (dep_rep_transport W _ _ m m' A7 Hdep MU WM (kw_dep Σ W IZ_S da_img' ltac:(apply dsjb_all'; vm_compute; reflexivity) da_grant67')).
  - exact (fs_rep_transport W Σ m m' A8 MU WM (kw_fs Σ W [k; (NS - 1)%nat] TZ IZ_S HG da_img' da_Tz' da_grant' da_shad_app'
             ltac:(apply dsjb_all'; vm_compute; reflexivity) Z2)).
  - exact (ia_rep_transport W Σ m m' A9 MU WM (kw_ia W IZ_S da_img' ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (shadow_rep_transport W _ m m' A10 MU WM (kw_shadow Σ W [k; (NS - 1)%nat] HG da_shad_app')).
  - exact (vis_rep_wmono _ m m' A11 WM).
Qed.

End DsArtK.

Definition schunkP (k : nat) (s : secst) (m : mem) : Prop :=
  let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
  shdr m mb msz (needed n + rz_size n) (Z.of_nat k) /\ wr_at bsegs m mb msz /\ lch m AB M /\ qhdr3 m M n
  /\ stk bsegs m (shad mb) (shad (mb + msz)).

Section SegPC.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp).

Lemma segP_chunk : forall (m' : mem), munch W m m' -> wmono bsegs m m' -> qhdr3 m' (s_mb s + 6128) (s_n s) -> schunkP k s m'.
Proof using HA Hk Hsp.
  intros m' MU WM HQ.
  destruct (ART_chunk Σ m HA) as [_ Sc]. pose proof (Sc k s Hk) as X. unfold schunk in X.
  destruct X as (X1 & X2 & X3 & _ & X5 & _).
  pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  unfold schunkP. replace (s_mb s + 4096 + 2032) with (s_mb s + 6128) by lia.
  split; [apply (rw_cells_transport bsegs W m m' _ _ X1 MU WM); cbn [cells_size csize Nat.add Z.of_nat]; apply (ss_map_lo Σ m k s usp HA Hk Hsp); lia|].
  split; [exact (wr_at_wmono m m' _ _ X2 WM)|].
  split; [replace (s_mb s + 4096 + 2032) with (s_mb s + 6128) in X3 by lia; apply (lch_transport W m m' _ _ X3 MU WM); apply (ss_map_lo Σ m k s usp HA Hk Hsp); lia|].
  split; [exact HQ|].
  apply (ss_stk_wmono m m' _ _ X5 WM); unfold img_hull_hi, SHB in *; lia.
Qed.

End SegPC.

End GWIN.
