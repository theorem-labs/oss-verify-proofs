(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc BnModel BnTree BgState ApBase ApState ApLogic ApErr ApParse
  CtSizes CtWire CtTime CtModel CtLogic CtInv CtTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S1.
Context {ptr : Type}.
Variables rcrit rcritS rcritI : Z -> Z -> Prop.
Variable spre : sysop -> Prop.
Local Notation ST := (ap_st ptr) (only parsing).
Local Notation BL := (list (ptr * Z)) (only parsing).
Local Notation awp := (awp (@okC ptr) rcrit rcritS rcritI spre) (only parsing).
Implicit Types (s : ap_st ptr) (R X F : list (ptr * Z)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition octb (o : octet ptr) : BL := optb (os_data o) ++ [(os_blk o, SZ_ASN1_STRING)].
Definition bufb (b : bufm ptr) : BL := optb (bm_data b).
Definition sctb (x : sctr ptr) : BL :=
  optb (option_map (fun p => (p, CT_V1_HASHLEN)) (sc_logid x)) ++ optb (sc_ext x) ++ optb (sc_sig x) ++ optb (sc_blob x) ++ [(sc_blk x, SZ_SCT)].
Fixpoint sctsb (l : list (sctr ptr)) : BL := match l with [] => [] | x :: t => sctb x ++ sctsb t end.
Definition arrb (k : skr ptr) : BL := optb (option_map (fun qn => (fst qn, 8 * snd qn)) (sk_data k)).
Definition skb (k : skr ptr) : BL := sctsb (sk_items k) ++ arrb k ++ [(sk_blk k, SZ_STACK)].

Lemma sctsb_app l1 l2 : sctsb (l1 ++ l2) = sctsb l1 ++ sctsb l2.
Proof. induction l1 as [|x l IH]; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma st_blocks_small s : sinv s -> Forall (fun xb => 0 <= snd xb <= 128) (st_blocks s).
Proof.
  intros Hs. pose proof Hs as (L1 & L2 & _ & _ & _ & L6 & _ & _ & _ & S1 & S2 & S3 & _).
  assert (FM : forall B l, sizes_le B l -> B <= 128 -> Forall (fun xb : ptr * Z => 0 <= snd xb <= 128) (fm l)).
  { intros B l H HB. induction H as [|o l Ho H IH]; [constructor|]. rewrite fm_cons. apply Forall_app. split; [|exact IH].
    destruct o as [[p n]|]; cbn; [constructor; [cbn; lia| constructor]| constructor]. }
  unfold st_blocks. repeat (apply Forall_app; split); [eapply FM; [exact S1| lia]| eapply FM; [exact S2| lia]| eapply FM; [exact S3| lia]|].
  destruct (as_cnf s) as [[[a b] c]|]; cbn; repeat constructor; cbn; lia.
Qed.

Lemma measure_small X B : Forall (fun xb : ptr * Z => 0 <= snd xb <= B) X -> B < ASAN_SEC_MIN ->
  m_sm (measure X) <= bsum X /\ m_n63 (measure X) = 0 /\ m_r63 (measure X) = 0 /\ m_nsec (measure X) = 0.
Proof.
  intros HF HB. induction HF as [|[p n] X Hx HF IH].
  - rewrite (@measure_nil ptr), (@bsum_nil ptr). cbn. lia.
  - rewrite measure_cons, bsum_cons. cbn [snd] in *. destruct IH as (I1 & I2 & I3 & I4).
    pose proof (mblk_small n B Hx HB) as (M1 & M2 & M3 & M4 & M5 & M6).
    pose proof (smsz_le n ltac:(lia)). pose proof (bigb_nonneg n ltac:(lia)). pose proof (isbig_01 n). pose proof (issec_01 n). unfold madd; cbn in *. lia.
Qed.

Lemma st_measure s : sinv s ->
  m_cnt (measure (st_blocks s)) <= 51 /\ m_sm (measure (st_blocks s)) <= 1744 /\ m_n63 (measure (st_blocks s)) = 0
  /\ m_r63 (measure (st_blocks s)) = 0 /\ m_nsec (measure (st_blocks s)) = 0 /\ bnonneg (st_blocks s).
Proof.
  intros Hs. destruct (st_blocks_bound s Hs) as (B1 & B2 & B3).
  destruct (measure_small _ 128 (st_blocks_small s Hs) ltac:(unfold ASAN_SEC_MIN; lia)) as (M1 & M2 & M3 & M4).
  unfold ST_NB, ST_TOT in *. unfold measure in *; cbn in *. repeat split; try lia. exact B3.
Qed.

(* [comment removed for export] *)
Lemma ok_frame s R X n : sinv s -> Permutation X (st_blocks s ++ R) -> bnonneg R -> 0 <= n <= 100663296 ->
  m_cnt (measure R) + 52 <= CT_NBT ->
  m_sm (measure R) + 1744 + smsz n <= CT_SMB ->
  m_n63 (measure R) + isbig n <= CT_NB63 ->
  m_r63 (measure R) + bigb n <= CT_BIGB ->
  m_nsec (measure R) + issec n <= CT_NSEC ->
  okC X n.
Proof.
  intros Hs HP HR Hn C1 C2 C3 C4 C5. destruct (st_measure s Hs) as (S1 & S2 & S3 & S4 & S5 & S6).
  apply (okC_perm (st_blocks s ++ R)); [apply Permutation_sym; exact HP|].
  apply (okC_of_meas _ _ (measure (st_blocks s ++ R))); [apply bnonneg_app; assumption| exact Hn| apply mle_refl| | | | |];
    rewrite measure_app; cbn [madd m_cnt m_sum m_sm m_n63 m_r63 m_nsec]; lia.
Qed.

(* [comment removed for export] *)
Definition RFc (R : BL) : Prop :=
  bnonneg R /\ m_cnt (measure R) + 52 <= CT_NBT /\ m_sm (measure R) + 1767 <= CT_SMB
  /\ m_n63 (measure R) <= CT_NB63 /\ m_r63 (measure R) <= CT_BIGB /\ m_nsec (measure R) <= CT_NSEC.

Lemma okR_ct : forall s R X n, rel s R X -> RFc R -> 0 <= n <= 23 -> okC X n.
Proof.
  intros s R X n [Hs HP] (F0 & F1 & F2 & F3 & F4 & F5) Hn.
  apply (ok_frame s R X n Hs HP F0 ltac:(lia) F1).
  - rewrite smsz_small by (unfold MMAP_THRESHOLD; lia). lia.
  - rewrite isbig_small by (unfold MMAP_THRESHOLD; lia). lia.
  - rewrite bigb_small by (unfold MMAP_THRESHOLD; lia). lia.
  - rewrite issec_small by (unfold ASAN_SEC_MIN; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma RFc_of_mle R M : bnonneg R -> mle (measure R) M ->
  m_cnt M + 52 <= CT_NBT -> m_sm M + 1767 <= CT_SMB -> m_n63 M <= CT_NB63 -> m_r63 M <= CT_BIGB -> m_nsec M <= CT_NSEC -> RFc R.
Proof. intros HB (L1 & L2 & L3 & L4 & L5 & L6) C1 C2 C3 C4 C5. unfold RFc. repeat split; try assumption; lia. Qed.

Lemma RFc_perm R R' : Permutation R R' -> RFc R -> RFc R'.
Proof. intros HP (F0 & F). unfold RFc. rewrite <- (measure_perm _ _ HP). split; [eapply bnonneg_perm; eassumption| exact F]. Qed.

(* [comment removed for export] *)
Definition err_raise_spec' := err_raise_spec (@okC ptr) rcrit rcritS rcritI spre RFc okR_ct.
Definition err_clear_error_spec' := err_clear_error_spec (@okC ptr) rcrit rcritS rcritI spre.

(* [comment removed for export] *)
Lemma rs_ct_sizes : forall rs, In rs [RS_td_small; RS_prim_nested; RS_coll_unexp_eoc; RS_coll_nested; RS_coll_nest_str; RS_coll_miss_eoc; RS_tlen_bad_hdr; RS_tlen_wrong_tag;
    RS_hdr_too_long; RS_too_long; RS_list_len; RS_list_mismatch; RS_list_lt2; RS_list_sctlen; RS_sct_len; RS_sct_43; RS_sct_ext; RS_sct_sig; RS_sig_version; RS_sig_len4;
    RS_sig_nid; RS_sig_overrun; RS_i2o_notset; RS_i2o_list; RS_i2o_siginc] -> 0 <= rs_flen rs <= 23 /\ 0 <= rs_fnlen rs <= 23.
Proof. intros rs H. cbn in H. repeat (destruct H as [<-|H]; [cbn; lia|]). destruct H. Qed.

(* [comment removed for export] *)
Lemma raise_spec rs s R X : rel s R X -> RFc R -> 0 <= rs_flen rs <= 23 -> 0 <= rs_fnlen rs <= 23 ->
  awp (err_raise rs s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s).
Proof.
  intros HR HF H1 H2. eapply awp_mono; [apply (err_raise_spec' rs s R X HR HF H1 H2)|]. intros [u s'] X' (HA & HB & _). split; assumption.
Qed.

Ltac rs_sizes := cbn [rs_flen rs_fnlen RS_td_small RS_prim_nested RS_coll_unexp_eoc RS_coll_nested RS_coll_nest_str RS_coll_miss_eoc RS_tlen_bad_hdr RS_tlen_wrong_tag
    RS_hdr_too_long RS_too_long RS_list_len RS_list_mismatch RS_list_lt2 RS_list_sctlen RS_sct_len RS_sct_43 RS_sct_ext RS_sct_sig RS_sig_version RS_sig_len4
    RS_sig_nid RS_sig_overrun RS_i2o_notset RS_i2o_list RS_i2o_siginc]; lia.

(* [comment removed for export] *)
Lemma raise_then {A} rs (k : unit -> @AM ptr A) s R X (Q : A * ST -> BL -> Prop) :
  rel s R X -> RFc R -> 0 <= rs_flen rs <= 23 -> 0 <= rs_fnlen rs <= 23 ->
  (forall s' X', rel s' R X' -> as_cnf s' = as_cnf s -> awp (k tt s') X' Q) ->
  awp (abind (err_raise rs) k s) X Q.
Proof.
  intros HR HF H1 H2 HK. apply awp_abind. eapply awp_mono; [apply (raise_spec rs s R X HR HF H1 H2)|]. intros [[] s'] X' [HA HB]. apply HK; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afree_opt_spec (o : option (ptr * Z)) s R X : rel s (optb o ++ R) X ->
  awp (afree_opt (option_map fst o) s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros [Hs HP]. destruct o as [[p n]|]; cbn -[st_blocks] in *.
  - exists n, (st_blocks s ++ R). split; [perm_via HP|]. split; [| reflexivity]. split; [exact Hs| apply Permutation_refl].
  - split; [| reflexivity]. split; [exact Hs| exact HP].
Qed.

(* [comment removed for export] *)
Lemma afree_optp_spec (o : option ptr) (n : Z) s R X : rel s (optb (option_map (fun p => (p, n)) o) ++ R) X ->
  awp (afree_opt o s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof. intros H. destruct o as [p|]; [apply (afree_opt_spec (Some (p, n)) s R X H)| apply (afree_opt_spec None s R X H)]. Qed.

Lemma afree_spec p n s R X : rel s ((p, n) :: R) X ->
  awp (afree p s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof. intros H. apply (afree_opt_spec (Some (p, n)) s R X H). Qed.

(* [comment removed for export] *)
Lemma seq_unit {A} (m : @AM ptr unit) (k : unit -> @AM ptr A) s X R' (Q : A * ST -> BL -> Prop) :
  awp (m s) X (fun r X' => rel (snd r) R' X' /\ snd r = s) ->
  (forall X', rel s R' X' -> awp (k tt s) X' Q) ->
  awp (abind m k s) X Q.
Proof. intros H HK. apply awp_abind. eapply awp_mono; [exact H|]. intros [[] s'] X' [HA E]. cbn [fst snd] in *. subst s'. apply HK. exact HA. Qed.

Lemma sct_free_spec x s R X : rel s (sctb x ++ R) X ->
  awp (sct_free x s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros HR. unfold sct_free, sctb in *. rewrite <- !app_assoc in HR.
  eapply seq_unit; [apply (afree_optp_spec (sc_logid x) CT_V1_HASHLEN); exact HR|]. intros X1 HR1.
  eapply seq_unit; [apply afree_opt_spec; exact HR1|]. intros X2 HR2.
  eapply seq_unit; [apply afree_opt_spec; exact HR2|]. intros X3 HR3.
  eapply seq_unit; [apply afree_opt_spec; exact HR3|]. intros X4 HR4.
  apply (afree_spec _ SZ_SCT). exact HR4.
Qed.

Lemma scts_free_spec l : forall s R X, rel s (sctsb l ++ R) X ->
  awp (scts_free l s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  induction l as [|x l IH]; intros s R X HR.
  - cbn in *. split; [exact HR| reflexivity].
  - change (sctsb (x :: l)) with (sctb x ++ sctsb l) in HR. rewrite <- app_assoc in HR.
    change (scts_free (x :: l) s) with (abind (sct_free x) (fun _ => scts_free l) s).
    eapply seq_unit; [apply sct_free_spec; exact HR|]. intros X1 HR1. apply IH. exact HR1.
Qed.

Lemma sk_free_all_spec k s R X : rel s (skb k ++ R) X ->
  awp (sk_free_all k s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros HR. unfold sk_free_all, skb in *. rewrite <- !app_assoc in HR.
  eapply seq_unit; [apply scts_free_spec; exact HR|]. intros X1 HR1.
  eapply seq_unit; [unfold arrb in HR1; destruct (sk_data k) as [[q na]|]; [apply (afree_opt_spec (Some (q, 8 * na))); exact HR1| apply (afree_opt_spec None); exact HR1]|]. intros X2 HR2.
  apply (afree_spec _ SZ_STACK). exact HR2.
Qed.

Lemma octet_free_spec o s R X : rel s (octb o ++ R) X ->
  awp (octet_free o s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros HR. unfold octet_free, octb in *. rewrite <- app_assoc in HR.
  eapply seq_unit; [apply afree_opt_spec; exact HR|]. intros X1 HR1. apply (afree_spec _ SZ_ASN1_STRING). exact HR1.
Qed.

End S1.
