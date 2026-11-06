(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc BnModel BnTree BgState ApBase ApState ApLogic ApErr ApParse
  CtSizes CtWire CtTime CtModel CtLogic CtInv CtTac CtSpecs1 CtSpecs2 CtSpecs3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
Definition CT_MAX_INPUT : Z := 67108864.

Lemma der_hl_range n : 0 <= n < 65536 -> 2 <= der_hl n <= 4.
Proof.
  intros Hn. destruct (Z_lt_le_dec n 128) as [A|A]; [rewrite der_hl_small by lia; lia|].
  destruct (Z_lt_le_dec n 256) as [B|B]; [rewrite der_hl_mid by lia; lia| rewrite der_hl_big by lia; lia].
Qed.

Section S4.
Context {ptr : Type}.
Variables rcrit rcritS rcritI : Z -> Z -> Prop.
Variable spre : sysop -> Prop.
Local Notation ST := (ap_st ptr) (only parsing).
Local Notation BL := (list (ptr * Z)) (only parsing).
Local Notation awp := (awp (@okC ptr) rcrit rcritS rcritI spre) (only parsing).
Local Notation raise_then := (raise_then rcrit rcritS rcritI spre) (only parsing).
Implicit Types (s : ap_st ptr) (R X F : list (ptr * Z)).
Hypothesis Hgrow : forall na, In na GROWTH -> na <= 21844 -> rcrit (8 * na) (8 * (na * 8 / 5)).
Hypothesis HinI : rcritI SZ_GEN_DATA SZ_GENSTR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RFt R : Prop :=
  bnonneg R /\ m_cnt (measure R) + 54 <= CT_NBT /\ m_sm (measure R) + 1807 <= CT_SMB
  /\ m_n63 (measure R) <= CT_NB63 /\ m_r63 (measure R) <= CT_BIGB /\ m_nsec (measure R) <= CT_NSEC.

Ltac small24 := unfold SZ_ASN1_STRING, SZ_GEN_DATA, SZ_GENSTR, SZ_BIO;
  rewrite ?(smsz_small 24), ?(isbig_small 24), ?(bigb_small 24), ?(issec_small 24),
          ?(smsz_small 20), ?(isbig_small 20), ?(bigb_small 20), ?(issec_small 20),
          ?(smsz_small 19), ?(isbig_small 19), ?(bigb_small 19), ?(issec_small 19),
          ?(smsz_small 128), ?(isbig_small 128), ?(bigb_small 128), ?(issec_small 128) by (unfold MMAP_THRESHOLD, ASAN_SEC_MIN; lia).
Ltac meas_simpl := repeat (rewrite measure_app || rewrite measure_cons); rewrite ?(@measure_nil ptr); cbn [madd mblk m0 m_cnt m_sum m_sm m_n63 m_r63 m_nsec snd fst].

Lemma timestamp_print_spec ts s R X : rel s R X -> RFt R ->
  awp (timestamp_print ts s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  intros [Hs HP] (F0 & F1 & F2 & F3 & F4 & F5). unfold timestamp_print.
  apply awp_abind. apply awp_amalloc; [apply lt62; unfold SZ_ASN1_STRING; lia| |].
  { apply (ok_frame s R X SZ_ASN1_STRING Hs ltac:(exact HP) F0); small24; lia. }
  intros gen Hgen. cbn [fst snd].
  destruct (printable ts).
  - apply awp_abind. apply awp_amalloc; [apply lt62; unfold SZ_GEN_DATA; lia| |].
    { apply (ok_frame s ((gen, SZ_ASN1_STRING) :: R) _ SZ_GEN_DATA Hs ltac:(perm_via (perm_skip (gen, SZ_ASN1_STRING) HP)));
        [constructor; [cbn; unfold SZ_ASN1_STRING; lia| exact F0]| unfold SZ_GEN_DATA; lia| | | | |]; meas_simpl; small24; lia. }
    intros dp Hdp. cbn [fst snd]. apply awp_abind.
    eapply (awp_areallocI _ _ _ _ _ dp SZ_GEN_DATA SZ_GENSTR s _ ((gen, SZ_ASN1_STRING) :: X)).
    + apply Permutation_refl.
    + apply lt62. unfold SZ_GENSTR. lia.
    + exact HinI.
    + apply (ok_frame s ((dp, SZ_GEN_DATA) :: (gen, SZ_ASN1_STRING) :: R) _ SZ_GENSTR Hs ltac:(perm_via (perm_skip (dp, SZ_GEN_DATA) (perm_skip (gen, SZ_ASN1_STRING) HP))));
        [constructor; [cbn; unfold SZ_GEN_DATA; lia| constructor; [cbn; unfold SZ_ASN1_STRING; lia| exact F0]]| unfold SZ_GENSTR; lia| | | | |]; meas_simpl; small24; lia.
    + intros dp' _. cbn [fst snd].
      eapply seq_unit; [apply (afree_spec _ _ _ _ dp' SZ_GENSTR s ((gen, SZ_ASN1_STRING) :: R)); split; [exact Hs| perm_via (perm_skip (dp', SZ_GENSTR) (perm_skip (gen, SZ_ASN1_STRING) HP))]|].
      intros X1 HR1. apply (afree_spec _ _ _ _ gen SZ_ASN1_STRING s R). destruct HR1 as [Hs1 HP1]. split; [exact Hs1| perm_via HP1].
  - apply (afree_spec _ _ _ _ gen SZ_ASN1_STRING s R). split; [exact Hs| perm_via (perm_skip (gen, SZ_ASN1_STRING) HP)].
Qed.

Lemma scts_print_spec l : forall s R X, rel s R X -> RFt R ->
  awp (scts_print l s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof.
  induction l as [|x l IH]; intros s R X HR HF.
  - apply awp_aret. split; [exact HR| reflexivity].
  - change (scts_print (x :: l) s) with (abind (sct_print x) (fun _ => scts_print l) s).
    eapply seq_unit; [| intros X1 HR1; apply (IH s R X1 HR1 HF)].
    unfold sct_print. destruct (sc_version x =? 0); [apply timestamp_print_spec; assumption| apply awp_aret; split; [exact HR| reflexivity]].
Qed.

Lemma sct_list_print_spec k s R X : rel s R X -> RFt R ->
  awp (sct_list_print k s) X (fun r X' => rel (snd r) R X' /\ snd r = s).
Proof. intros. unfold sct_list_print. apply scts_print_spec; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RFe R : Prop :=
  bnonneg R /\ m_cnt (measure R) + 55 <= CT_NBT /\ m_sm (measure R) + 1744 + 65535 + 24 + 65539 <= CT_SMB
  /\ m_n63 (measure R) <= CT_NB63 /\ m_r63 (measure R) <= CT_BIGB /\ m_nsec (measure R) + 2 <= CT_NSEC.

Lemma RFc_of_RFe R : RFe R -> RFc R.
Proof. intros (F0 & F1 & F2 & F3 & F4 & F5). unfold RFc. split; [exact F0| lia]. Qed.

Lemma i2o_len_pass_spec l : forall acc s R X, rel s R X -> RFe R ->
  awp (i2o_len_pass l acc s) X (fun r X' => rel (snd r) R X' /\ match fst r with Some n => n = acc + i2o_tot l | None => True end).
Proof.
  induction l as [|x l IH]; intros acc s R X HR HF.
  - apply awp_aret. cbn [fst snd]. split; [exact HR| unfold i2o_tot; cbn -[Z.add]; lia].
  - change (i2o_len_pass (x :: l) acc s) with
      ((if sct_complete x then i2o_len_pass l (acc + 2 + i2o_sct_len x) else err_raise RS_i2o_notset ;;; err_raise RS_i2o_list ;;; aret None) s).
    destruct (sct_complete x).
    + eapply awp_mono; [apply (IH _ s R X HR HF)|]. intros [[n|] s1] X1; cbn [fst snd]; [| tauto].
      intros [A B]. split; [exact A|]. unfold i2o_tot in *. cbn -[Z.add i2o_sct_len] in *. lia.
    + pose proof (RFc_of_RFe R HF) as HFc.
      eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s1 X1 HR1 _.
      eapply raise_then; [exact HR1| exact HFc| cbn; lia| cbn; lia|]. intros s2 X2 HR2 _. apply awp_aret. split; [exact HR2| exact I].
Qed.

Lemma i2d_sct_list_spec k s R X : rel s R X -> RFe R -> 0 <= i2o_tot (sk_items k) ->
  awp (i2d_sct_list k s) X (fun r X' => rel (snd r) R X').
Proof.
  intros HR HF Ht. pose proof HF as (F0 & F1 & F2 & F3 & F4 & F5). pose proof (RFc_of_RFe R HF) as HFc. unfold i2d_sct_list.
  apply awp_abind. eapply awp_mono; [apply (i2o_len_pass_spec (sk_items k) 2 s R X HR HF)|].
  intros [[len2|] s1] X1; cbn [fst snd]; [| intros [A _]; apply awp_aret; exact A]. intros [HR1 E1].
  destruct (Z.ltb_spec MAX_SCT_LIST_SIZE len2) as [LM|LM].
  { eapply raise_then; [exact HR1| exact HFc| cbn; lia| cbn; lia|]. intros s2 X2 HR2 _. apply awp_aret. exact HR2. }
  unfold MAX_SCT_LIST_SIZE in LM. pose proof (der_hl_range len2 ltac:(lia)) as Hhl. destruct HR1 as [Hs HP].
  pose proof (mblk1 len2 ltac:(unfold MMAP_THRESHOLD; lia)) as (Q1 & Q2 & Q3 & Q4 & _).
  pose proof (mblk1 (der_hl len2 + len2) ltac:(unfold MMAP_THRESHOLD; lia)) as (P1 & P2 & P3 & P4 & _).
  (* [comment removed for export] *)
  apply awp_abind. apply awp_amalloc; [apply lt62c; assert (E40 : 2^40 = 1099511627776) by reflexivity; lia| |].
  { apply (ok_frame s1 R X1 len2 Hs ltac:(exact HP) F0 ltac:(lia)); rewrite ?Q1, ?Q2, ?Q3; lia. }
  intros data Hdata. cbn [fst snd].
  (* [comment removed for export] *)
  apply awp_abind. apply awp_amalloc; [apply lt62; unfold SZ_ASN1_STRING; lia| |].
  { apply (ok_frame s1 ((data, len2) :: R) _ SZ_ASN1_STRING Hs ltac:(perm_via (perm_skip (data, len2) HP)));
      [constructor; [cbn; lia| exact F0]| unfold SZ_ASN1_STRING; lia| | | | |]; meas_simpl; small24; rewrite ?Q1, ?Q2, ?Q3; lia. }
  intros oct Hoct. cbn [fst snd].
  (* [comment removed for export] *)
  apply awp_abind. apply awp_amalloc; [apply lt62c; assert (E40 : 2^40 = 1099511627776) by reflexivity; lia| |].
  { apply (ok_frame s1 ((oct, SZ_ASN1_STRING) :: (data, len2) :: R) _ (der_hl len2 + len2) Hs ltac:(perm_via (perm_skip (oct, SZ_ASN1_STRING) (perm_skip (data, len2) HP))));
      [constructor; [cbn; unfold SZ_ASN1_STRING; lia| constructor; [cbn; lia| exact F0]]| lia| | | | |]; meas_simpl; small24; rewrite ?Q1, ?Q2, ?Q3, ?P1, ?P2, ?P3; lia. }
  intros der Hder. cbn [fst snd].
  eapply seq_unit; [apply (afree_spec _ _ _ _ data len2 s1 ((der, der_hl len2 + len2) :: (oct, SZ_ASN1_STRING) :: R));
    split; [exact Hs| perm_via (perm_skip (der, der_hl len2 + len2) (perm_skip (oct, SZ_ASN1_STRING) (perm_skip (data, len2) HP)))]|].
  intros X2 [Hs2 HP2].
  eapply seq_unit; [apply (afree_spec _ _ _ _ oct SZ_ASN1_STRING s1 ((der, der_hl len2 + len2) :: R)); split; [exact Hs2| perm_via HP2]|].
  intros X3 [Hs3 HP3].
  eapply awp_mono; [apply (afree_spec _ _ _ _ der (der_hl len2 + len2) s1 R); split; [exact Hs3| perm_via HP3]|].
  intros [[] s4] X4 [A B]. exact A.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RFtop F : Prop :=
  bnonneg F /\ m_cnt (measure F) <= 1000 /\ m_sm (measure F) <= 400000 /\ m_n63 (measure F) <= 1 /\ m_r63 (measure F) <= 10000000 /\ m_nsec (measure F) <= 1.

Lemma RFtop_nil : RFtop [].
Proof. unfold RFtop. rewrite (@measure_nil ptr). cbn. split; [apply Forall_nil| lia]. Qed.

Lemma BMAX_max T : 0 <= T <= CT_MAX_INPUT -> BMAX T <= 89478488.
Proof. intros HT. eapply Z.le_trans; [apply (BMAX_mono T CT_MAX_INPUT); lia|]. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma RFd_top T F : RFtop F -> 0 <= T <= CT_MAX_INPUT -> RFd T F.
Proof.
  intros (F0 & F1 & F2 & F3 & F4 & F5) HT. pose proof (BMAX_max T HT). unfold RFd. unfold CT_MAX_INPUT, CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *.
  split; [exact F0| lia].
Qed.

Lemma octb_meas T (o : octet ptr) : oinv T o -> 0 <= T <= CT_MAX_INPUT ->
  bnonneg (octb o) /\ m_cnt (measure (octb o)) <= 2 /\ m_sm (measure (octb o)) <= 131075 /\ m_n63 (measure (octb o)) <= 1
  /\ m_r63 (measure (octb o)) <= 89486607 /\ m_nsec (measure (octb o)) <= 1.
Proof.
  intros [HL HD] HT. pose proof (BMAX_max T HT). unfold octb. destruct (os_data o) as [[q n]|]; cbn [optb].
  - destruct HD as (D1 & D2 & D3 & D4). meas_simpl. small24.
    pose proof (smsz_bound n ltac:(lia)). pose proof (isbig_01 n). pose proof (issec_01 n). pose proof (bigb_le n ltac:(lia)).
    split; [repeat constructor; cbn; unfold SZ_ASN1_STRING; lia| lia].
  - meas_simpl. small24. split; [repeat constructor; cbn; lia| lia].
Qed.

Lemma RFo_top T (o : octet ptr) F : RFtop F -> oinv T o -> 0 <= T <= CT_MAX_INPUT -> RFo (octb o ++ F).
Proof.
  intros (F0 & F1 & F2 & F3 & F4 & F5) HO HT. pose proof (octb_meas T o HO HT) as (B0 & B1 & B2 & B3 & B4 & B5).
  unfold RFo. meas_simpl. unfold CT_BIGB. split; [apply bnonneg_app; assumption| lia].
Qed.

Lemma RFt_top (k : skr ptr) F bio : RFtop F -> linv k 65533 -> RFt ((bio, SZ_BIO) :: skb k ++ F).
Proof.
  intros (F0 & F1 & F2 & F3 & F4 & F5) HL. pose proof (skb_meas k 65533 HL ltac:(lia)) as (B0 & B1 & B2 & B3 & B4 & B5).
  unfold RFt. meas_simpl. small24. unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *.
  split; [constructor; [cbn; lia| apply bnonneg_app; assumption]| lia].
Qed.

Lemma RFe_top (k : skr ptr) F : RFtop F -> linv k 65533 -> RFe (skb k ++ F).
Proof.
  intros (F0 & F1 & F2 & F3 & F4 & F5) HL. pose proof (skb_meas k 65533 HL ltac:(lia)) as (B0 & B1 & B2 & B3 & B4 & B5).
  unfold RFe. meas_simpl. unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC in *.
  split; [apply bnonneg_app; assumption| lia].
Qed.

Lemma RFtop_bio F : RFtop F -> bnonneg F /\ m_cnt (measure F) + 53 <= CT_NBT /\ m_sm (measure F) + 1744 + 128 <= CT_SMB
  /\ m_n63 (measure F) <= CT_NB63 /\ m_r63 (measure F) <= CT_BIGB /\ m_nsec (measure F) <= CT_NSEC.
Proof. intros (F0 & F1 & F2 & F3 & F4 & F5). unfold CT_NBT, CT_SMB, CT_NB63, CT_BIGB, CT_NSEC. split; [exact F0| lia]. Qed.

Theorem ct_call_spec d s F X : Forall (fun x => 0 <= x) d -> zlength d <= CT_MAX_INPUT -> rel s F X -> RFtop F ->
  awp (ct_call d s) X (fun r X' =>
    rel (snd r) F X' /\ fst r = 0 /\ (forall j, (j < ERR_NUM)%nat -> get_file j (snd r) = None /\ get_func j (snd r) = None)).
Proof.
  intros Hd HT HR HF. assert (HT0 : 0 <= zlength d) by (unfold zlength; lia).
  (* [comment removed for export] *)
  assert (TAIL : forall s1 X1, rel s1 F X1 -> awp ((err_clear_error ;;; aret 0) s1) X1 (fun r X' =>
            rel (snd r) F X' /\ fst r = 0 /\ (forall j, (j < ERR_NUM)%nat -> get_file j (snd r) = None /\ get_func j (snd r) = None))).
  { intros s1 X1 HR1. apply awp_abind. eapply awp_mono; [apply (err_clear_error_spec' rcrit rcritS rcritI spre s1 F X1 HR1)|].
    intros [[] s2] X2 (HR2 & HC2 & HN2). cbn [fst snd]. apply awp_aret. cbn [fst snd].
    split; [exact HR2|]. split; [reflexivity| exact HN2]. }
  unfold ct_call. apply awp_abind.
  eapply awp_mono; [apply (d2i_octet_spec rcrit rcritS rcritI spre d s F X Hd ltac:(unfold CT_MAX_INPUT in HT; assert (E30 : 2^30 = 1073741824) by reflexivity; lia) HR (RFd_top (zlength d) F HF ltac:(lia)))|].
  intros [[os|] s1] X1; cbn [fst snd].
  2:{ intros HR1. apply awp_abind. apply awp_aret. cbn [fst snd]. apply TAIL. exact HR1. }
  intros [HR1 HO]. pose proof (proj1 HO) as HOL.
  apply awp_abind. apply awp_abind.
  eapply awp_mono; [apply (o2i_sct_list_spec rcrit rcritS rcritI spre Hgrow (os_bytes os) (os_len os) s1 (octb os ++ F) X1 HR1 (RFo_top (zlength d) os F HF HO ltac:(lia)) ltac:(lia))|].
  intros [[k|] s2] X2; cbn [fst snd].
  - intros [HR2 HL2].
    assert (HR2' : rel s2 (octb os ++ skb k ++ F) X2) by (destruct HR2 as [Hs2 HP2]; split; [exact Hs2| perm_via HP2]).
    eapply seq_unit; [apply (octet_free_spec _ _ _ _ os s2 (skb k ++ F) X2 HR2')|]. intros X3 [Hs3 HP3]. cbn [fst snd].
    (* [comment removed for export] *)
    apply awp_abind. pose proof (RFe_top k F HF HL2) as HFe. pose proof HFe as (E0 & E1 & E2 & E3 & E4 & E5).
    apply awp_amalloc; [apply lt62; unfold SZ_BIO; lia| |].
    { apply (ok_frame s2 (skb k ++ F) X3 SZ_BIO Hs3 HP3 E0); small24; lia. }
    intros bio Hbio. cbn [fst snd].
    assert (HR4 : rel s2 ((bio, SZ_BIO) :: skb k ++ F) ((bio, SZ_BIO) :: X3)) by (split; [exact Hs3| perm_via (perm_skip (bio, SZ_BIO) HP3)]).
    eapply seq_unit; [apply (sct_list_print_spec k s2 _ _ HR4 (RFt_top k F bio HF HL2))|]. intros X5 HR5.
    eapply seq_unit; [apply (afree_spec _ _ _ _ bio SZ_BIO s2 (skb k ++ F) X5 HR5)|]. intros X6 HR6.
    apply awp_abind. eapply awp_mono; [apply (i2d_sct_list_spec k s2 (skb k ++ F) X6 HR6 HFe); destruct HL2 as (_ & _ & _ & _ & K5); lia|].
    intros [[] s7] X7 HR7. cbn [fst snd].
    eapply awp_mono; [apply (sk_free_all_spec _ _ _ _ k s7 F X7 HR7)|]. intros [[] s8] X8 [HR8 E8]. cbn [fst snd]. apply TAIL. exact HR8.
  - intros HR2. eapply seq_unit; [apply (octet_free_spec _ _ _ _ os s2 F X2 HR2)|]. intros X3 HR3. apply awp_aret. cbn [fst snd]. apply TAIL. exact HR3.
Qed.

End S4.
