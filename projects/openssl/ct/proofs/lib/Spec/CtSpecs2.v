(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc BnModel BnTree BgState ApBase ApState ApLogic ApErr ApParse
  CtSizes CtWire CtTime CtModel CtLogic CtInv CtTac CtSpecs1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Section S2.
Context {ptr : Type}.
Variables rcrit rcritS rcritI : Z -> Z -> Prop.
Variable spre : sysop -> Prop.
Local Notation ST := (ap_st ptr) (only parsing).
Local Notation BL := (list (ptr * Z)) (only parsing).
Local Notation awp := (awp (@okC ptr) rcrit rcritS rcritI spre) (only parsing).
Local Notation raise_then := (raise_then rcrit rcritS rcritI spre) (only parsing).
Implicit Types (s : ap_st ptr) (R X F : list (ptr * Z)).

Definition BMAX (T : Z) : Z := (T + 3) / 3 * 4.
Lemma BMAX_ge T : 0 <= T -> T + 1 <= BMAX T /\ 4 <= BMAX T.
Proof. intros. unfold BMAX. pose proof (Z.div_mod (T + 3) 3 ltac:(lia)). pose proof (Z.mod_pos_bound (T + 3) 3 ltac:(lia)). lia. Qed.
Lemma BMAX_mono a b : 0 <= a <= b -> BMAX a <= BMAX b.
Proof. intros. unfold BMAX. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma BMAX_le T : 0 <= T -> BMAX T <= 2 * T + 4.
Proof. intros. unfold BMAX. pose proof (Z.mul_div_le (T + 3) 3 ltac:(lia)). lia. Qed.
Lemma BMAX_max' T : 0 <= T <= 67108864 -> BMAX T <= 89478488.
Proof. intros HT. eapply Z.le_trans; [apply (BMAX_mono T 67108864); lia|]. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition binv (T : Z) (b : bufm ptr) : Prop :=
  0 <= bm_len b <= T /\
  match bm_data b with
  | None => bm_len b = 0
  | Some (_, m) => bm_len b <= m /\ 4 <= m <= BMAX (bm_len b)
  end.

Lemma binv_buf0 T : 0 <= T -> binv T buf0.
Proof. intros. unfold binv, buf0. cbn. lia. Qed.

(* [comment removed for export] *)
Definition RFd (T : Z) F : Prop :=
  bnonneg F /\ m_cnt (measure F) + 56 <= CT_NBT /\ m_sm (measure F) + 1767 + 262102 + 24 <= CT_SMB
  /\ m_n63 (measure F) + 2 <= CT_NB63 /\ m_r63 (measure F) + (T + 4115) + (BMAX T + 4115) <= CT_BIGB /\ m_nsec (measure F) + 2 <= CT_NSEC.

Lemma bigb_bound n B : 0 <= n <= B -> bigb n <= B + 4115.
Proof. intros. pose proof (bigb_le n ltac:(lia)). lia. Qed.
Lemma smsz_bound n : 0 <= n -> smsz n <= 131051.
Proof. intros. unfold smsz. destruct (Z.ltb_spec n MMAP_THRESHOLD); unfold MMAP_THRESHOLD in *; lia. Qed.

(* [comment removed for export] *)
Lemma bufb_measure T b : binv T b ->
  bnonneg (bufb b) /\ m_cnt (measure (bufb b)) <= 1 /\ m_sm (measure (bufb b)) <= 131051 /\ m_n63 (measure (bufb b)) <= 1
  /\ m_r63 (measure (bufb b)) <= BMAX T + 4115 /\ m_nsec (measure (bufb b)) <= 1.
Proof.
  intros [HL HD]. unfold bufb. destruct (bm_data b) as [[q m]|]; cbn -[measure smsz bigb isbig issec BMAX].
  - destruct HD as [H1 [H2 H3]]. pose proof (BMAX_mono (bm_len b) T ltac:(lia)).
    rewrite measure_cons, (@measure_nil ptr). unfold madd, mblk, m0; cbn [m_cnt m_sum m_sm m_n63 m_r63 m_nsec snd].
    pose proof (smsz_bound m ltac:(lia)). pose proof (isbig_01 m). pose proof (issec_01 m). pose proof (bigb_bound m (BMAX T) ltac:(lia)).
    split; [apply Forall_cons; [cbn; lia| apply Forall_nil]|]. lia.
  - rewrite (@measure_nil ptr). pose proof (BMAX_ge T ltac:(lia)). cbn -[BMAX]. split; [apply Forall_nil| lia].
Qed.

Lemma RFc_buf T b F : binv T b -> RFd T F -> RFc (bufb b ++ F).
Proof.
  intros HB (F0 & F1 & F2 & F3 & F4 & F5). destruct (bufb_measure T b HB) as (B0 & B1 & B2 & B3 & B4 & B5).
  pose proof (BMAX_ge T ltac:(destruct HB; lia)). pose proof (proj1 HB).
  unfold RFc. rewrite measure_app. cbn [madd m_cnt m_sum m_sm m_n63 m_r63 m_nsec]. split; [apply bnonneg_app; assumption| lia].
Qed.

Lemma lt62c n : 0 <= n <= 2^40 -> 0 <= n < 2^62.
Proof. intros H. assert (E : 2^62 = 4611686018427387904) by reflexivity. assert (E2 : 2^40 = 1099511627776) by reflexivity. rewrite E. rewrite E2 in H. lia. Qed.
Lemma lt62 n : 0 <= n <= 2640 -> 0 <= n < 2^62.
Proof. intros H. apply lt62c. assert (E2 : 2^40 = 1099511627776) by reflexivity. lia. Qed.

(* [comment removed for export] *)
Lemma tlen_fail_spec e s R X : rel s R X -> RFc R -> e <> GeTooSmall ->
  awp (tlen_fail e s) X (fun r X' => rel (snd r) R X' /\ as_cnf (snd r) = as_cnf s).
Proof.
  intros HR HF He. unfold tlen_fail. destruct e; [| | congruence]; cbn iota;
    (eapply raise_then; [exact HR| exact HF| cbn; lia| cbn; lia|]; intros s1 X1 HR1 E1;
     eapply awp_mono; [apply (raise_spec _ _ _ _ _ s1 _ X1 HR1 HF); cbn; lia|]; intros [[] s2] X2 [HR2 E2]; split; [exact HR2| cbn [snd] in *; congruence]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma buf_grow_clean_spec T b len s F X : rel s (bufb b ++ F) X -> RFd T F -> binv T b -> T <= 67108864 ->
  bm_len b <= len <= T ->
  awp (buf_grow_clean b len s) X (fun r X' =>
    rel (snd r) (bufb (fst r) ++ F) X' /\ snd r = s /\ binv T (fst r) /\ bm_len (fst r) = len /\ bm_bytes (fst r) = bm_bytes b).
Proof.
  intros HR HF HB HT Hlen. pose proof HB as [HL HD]. unfold buf_grow_clean.
  destruct (Z.leb_spec len (bm_len b)) as [L1|L1].
  { cbn. split; [exact HR|]. split; [reflexivity|]. split; [| split; reflexivity].
    unfold binv; cbn. assert (len = bm_len b) by lia. subst len. exact HB. }
  destruct (Z.leb_spec len (bm_max b)) as [L2|L2].
  { cbn. split; [exact HR|]. split; [reflexivity|]. split; [| split; reflexivity].
    unfold binv, bm_max in *; cbn. destruct (bm_data b) as [[q m]|]; [| lia]. destruct HD as [H1 [H2 H3]].
    pose proof (BMAX_mono (bm_len b) len ltac:(lia)). lia. }
  destruct (Z.ltb_spec LIMIT_BEFORE_EXPANSION len) as [L3|L3].
  { exfalso. unfold LIMIT_BEFORE_EXPANSION in L3. assert (E2 : 2^30 = 1073741824) by reflexivity. lia. }
  cbn -[st_blocks Z.div Z.mul Z.add bufb].
  pose proof (BMAX_ge len ltac:(lia)) as [G1 G2]. pose proof (BMAX_mono len T ltac:(lia)) as G3. fold (BMAX len).
  assert (E40 : 2^30 = 1073741824) by reflexivity. assert (E41 : 2^40 = 1099511627776) by reflexivity.
  pose proof (BMAX_le T ltac:(lia)) as G4. pose proof (BMAX_max' T ltac:(lia)) as G5.
  split; [apply lt62c; lia|].
  split.
  { (* [comment removed for export] *)
    destruct HR as [Hs HP]. destruct HF as (F0 & F1 & F2 & F3 & F4 & F5). destruct (bufb_measure T b HB) as (B0 & B1 & B2 & B3 & B4 & B5).
    apply (ok_frame s (bufb b ++ F) X (BMAX len) Hs HP); [apply bnonneg_app; assumption| lia| | | | |];
      rewrite measure_app; cbn [madd m_cnt m_sum m_sm m_n63 m_r63 m_nsec].
    - lia.
    - pose proof (smsz_bound (BMAX len) ltac:(lia)). lia.
    - pose proof (isbig_01 (BMAX len)). lia.
    - (* [comment removed for export] *)
      assert (BO : m_r63 (measure (bufb b)) <= T + 4115).
      { unfold bufb, bm_max in *. destruct (bm_data b) as [[q m]|]; cbn [optb].
        - rewrite measure_cons, (@measure_nil ptr). cbn [madd m_r63 mblk m0 snd]. pose proof (bigb_bound m T ltac:(lia)). lia.
        - rewrite (@measure_nil ptr). cbn. lia. }
      pose proof (bigb_bound (BMAX len) (BMAX T) ltac:(lia)). lia.
    - pose proof (issec_01 (BMAX len)). lia. }
  split; [reflexivity|]. intros q Hq.
  (* [comment removed for export] *)
  apply awp_abind.
  assert (HR1 : rel s (bufb b ++ (q, BMAX len) :: F) ((q, BMAX len) :: X)).
  { destruct HR as [Hs HP]. split; [exact Hs|]. perm_via (perm_skip (q, BMAX len) HP). }
  eapply awp_mono; [apply (afree_opt_spec _ _ _ _ (bm_data b) s ((q, BMAX len) :: F)); unfold bufb in HR1; exact HR1|].
  intros [[] s1] X1 [HR2 E1]. cbn [fst snd] in *. subst s1. cbn -[st_blocks BMAX].
  split; [unfold bufb; cbn; exact HR2|]. split; [reflexivity|]. split; [| split; reflexivity].
  unfold binv. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma collect_data_spec d T b p plen s F X : rel s (bufb b ++ F) X -> RFd T F -> binv T b -> T <= 67108864 ->
  0 <= plen -> bm_len b + plen <= T ->
  awp (collect_data d b p plen s) X (fun r X' =>
    rel (snd r) (bufb (fst (fst r)) ++ F) X' /\ snd r = s /\ binv T (fst (fst r)) /\ bm_len (fst (fst r)) = bm_len b + plen /\ snd (fst r) = p + plen).
Proof.
  intros HR HF HB HT Hp Hl. unfold collect_data. apply awp_abind.
  eapply awp_mono; [apply (buf_grow_clean_spec T); try eassumption; destruct HB; lia|].
  intros [b1 s1] X1 (HR1 & E1 & HB1 & HL1 & _). cbn [fst snd] in *. subst s1. cbn -[st_blocks bufb Z.add].
  split; [unfold bufb in *; cbn; exact HR1|]. split; [reflexivity|]. split; [| split; [exact HL1| reflexivity]].
  unfold binv in *. cbn. exact HB1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition coll_post T (b : bufm ptr) (p lenb : Z) F s (r : (bufm ptr * option Z) * ST) X' : Prop :=
  let b' := fst (fst r) in
  rel (snd r) (bufb b' ++ F) X' /\ binv T b' /\ bm_len b <= bm_len b' /\
  match snd (fst r) with None => True | Some p' => p <= p' /\ bm_len b' - bm_len b <= p' - p /\ p' - p <= lenb end.

(* [comment removed for export] *)
Lemma collect_S d fuel (b : bufm ptr) p len inf depth :
  collect (ptr:=ptr) (S fuel) d b p len inf depth =
  (if len <=? 0 then
      (if inf then err_raise RS_coll_miss_eoc ;;; aret (b, None) else aret (b, Some p))
    else if (2 <=? len) && (znth d p =? 0) && (znth d (p + 1) =? 0) then
      (if inf then aret (b, Some (p + 2)) else err_raise RS_coll_unexp_eoc ;;; aret (b, None))
    else
      let g := get_object d p len in
      match go_err g with
      | Some e => tlen_fail e ;;; err_raise RS_coll_nested ;;; aret (b, None)
      | None =>
          let p1 := go_p g in
          let ininf := Z.testbit (go_ret g) 0 in
          let cst := negb (Z.land (go_ret g) 32 =? 0) in
          let plen := if ininf then len - (p1 - p) else go_len g in
          if cst then
            if 5 <=? depth then err_raise RS_coll_nest_str ;;; aret (b, None)
            else
              ' (b1, r) <- collect fuel d b p1 plen ininf (depth + 1) ;;
              match r with
              | None => aret (b1, None)
              | Some p2 => collect fuel d b1 p2 (len - (p2 - p)) inf depth
              end
          else
            ' (b1, p2) <- (if plen =? 0 then aret (b, p1) else collect_data d b p1 plen) ;;
            collect fuel d b1 p2 (len - (p2 - p)) inf depth
      end).
Proof. reflexivity. Qed.

Lemma collect_spec d T : Forall (fun x => 0 <= x) d -> T <= 67108864 ->
  forall fuel b p len inf depth s F X,
  rel s (bufb b ++ F) X -> RFd T F -> binv T b -> 0 <= len -> bm_len b + len <= T -> 2 * len + 2 <= Z.of_nat fuel ->
  awp (collect fuel d b p len inf depth s) X (coll_post T b p len F s).
Proof.
  intros Hd HT. induction fuel as [|fuel IH]; intros b p len inf depth s F X HR HF HB Hlen Hbud Hfuel; [cbn in Hfuel; lia|].
  rewrite Nat2Z.inj_succ in Hfuel. rewrite collect_S. cbn zeta.
  pose proof (RFc_buf T b F HB HF) as HFc.
  destruct (Z.leb_spec len 0) as [L0|L0].
  { destruct inf.
    - eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s' X' HR' _. cbn. unfold coll_post; cbn. split; [exact HR'|]. split; [exact HB|]. split; [lia| exact I].
    - cbn. unfold coll_post; cbn. split; [exact HR|]. split; [exact HB|]. lia. }
  destruct ((2 <=? len) && (znth d p =? 0) && (znth d (p + 1) =? 0)) eqn:EE.
  { assert (L2 : 2 <= len) by (apply andb_prop in EE as [EE _]; apply andb_prop in EE as [EE _]; apply Z.leb_le in EE; exact EE).
    destruct inf.
    - cbn. unfold coll_post; cbn. split; [exact HR|]. split; [exact HB|]. lia.
    - eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s' X' HR' _. cbn. unfold coll_post; cbn. split; [exact HR'|]. split; [exact HB|]. split; [lia| exact I]. }
  pose proof (get_object_bounds d p len Hd ltac:(lia)) as GB. cbn zeta in GB.
  destruct (go_err (get_object d p len)) as [e|] eqn:Eg.
  { (* [comment removed for export] *)
    apply awp_abind. eapply awp_mono; [apply (tlen_fail_spec e s _ X HR HFc); destruct e; [discriminate| discriminate| destruct GB]|].
    intros [[] s1] X1 [HR1 _]. cbn [fst snd] in *.
    eapply raise_then; [exact HR1| exact HFc| cbn; lia| cbn; lia|]. intros s3 X3 HR3 _. cbn. unfold coll_post; cbn.
    split; [exact HR3|]. split; [exact HB|]. split; [lia| exact I]. }
  destruct GB as (G1 & G2 & G3).
  set (g := get_object d p len) in *.
  set (ininf := Z.testbit (go_ret g) 0). set (cst := negb (Z.land (go_ret g) 32 =? 0)).
  set (plen := if ininf then len - (go_p g - p) else go_len g).
  assert (Hplen : 0 <= plen /\ go_p g - p + plen <= len) by (subst plen; destruct ininf; lia).
  destruct cst.
  - destruct (Z.leb_spec 5 depth) as [D5|D5].
    + eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s' X' HR' _. cbn. unfold coll_post; cbn.
      split; [exact HR'|]. split; [exact HB|]. split; [lia| exact I].
    + apply awp_abind. eapply awp_mono; [apply (IH b (go_p g) plen ininf (depth + 1) s F X HR HF HB ltac:(lia) ltac:(lia) ltac:(lia))|].
      intros [[b1 r1] s1] X1 (HR1 & HB1 & HL1 & HP1). cbn [fst snd] in *.
      destruct r1 as [p2|].
      * destruct HP1 as (HP1a & HP1b & HP1c). eapply awp_mono; [apply (IH b1 p2 (len - (p2 - p)) inf depth s1 F X1 HR1 HF HB1 ltac:(lia) ltac:(lia) ltac:(lia))|].
        intros [[b3 r3] s3] X3 (HR3 & HB3 & HL3 & HP3). cbn [fst snd] in *. unfold coll_post; cbn.
        split; [exact HR3|]. split; [exact HB3|]. split; [lia|]. destruct r3 as [p4|]; [| exact I]. repeat split; lia.
      * cbn. unfold coll_post; cbn. split; [exact HR1|]. split; [exact HB1|]. split; [lia| exact I].
  - apply awp_abind.
    destruct (Z.eqb_spec plen 0) as [P0|P0].
    + cbn -[st_blocks bufb collect Z.add Z.sub].
      eapply awp_mono; [apply (IH b (go_p g) (len - (go_p g - p)) inf depth s F X HR HF HB ltac:(lia) ltac:(lia) ltac:(lia))|].
      intros [[b3 r3] s3] X3 (HR3 & HB3 & HL3 & HP3). cbn [fst snd] in *. unfold coll_post; cbn.
      split; [exact HR3|]. split; [exact HB3|]. split; [lia|]. destruct r3 as [p4|]; [| exact I]. repeat split; lia.
    + eapply awp_mono; [apply (collect_data_spec d T b (go_p g) plen s F X HR HF HB HT ltac:(lia) ltac:(lia))|].
      intros [[b1 p2] s1] X1 (HR1 & E1 & HB1 & HL1 & HP2). cbn [fst snd] in *. subst s1. subst p2. cbn -[st_blocks bufb collect Z.add Z.sub].
      eapply awp_mono; [apply (IH b1 (go_p g + plen) (len - (go_p g + plen - p)) inf depth s F X1 HR1 HF HB1 ltac:(lia) ltac:(lia) ltac:(lia))|].
      intros [[b3 r3] s3] X3 (HR3 & HB3 & HL3 & HP3). cbn [fst snd] in *. unfold coll_post; cbn.
      split; [exact HR3|]. split; [exact HB3|]. split; [lia|]. destruct r3 as [p4|]; [| exact I]. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition oinv (T : Z) (o : octet ptr) : Prop :=
  0 <= os_len o <= T /\
  match os_data o with
  | None => True
  | Some (_, n) => 1 <= n /\ os_len o <= n /\ n <= (os_len o + 4) / 3 * 4 /\ n <= BMAX T + 4
  end.

Lemma d2i_octet_spec d s F X : Forall (fun x => 0 <= x) d -> zlength d <= 67108864 ->
  rel s F X -> RFd (zlength d) F ->
  awp (d2i_octet d (zlength d) s) X (fun r X' =>
    match fst r with
    | None => rel (snd r) F X'
    | Some o => rel (snd r) (octb o ++ F) X' /\ oinv (zlength d) o
    end).
Proof.
  intros Hd HT HR HF. set (len := zlength d) in *.
  assert (Hlen : 0 <= len) by (subst len; unfold zlength; lia).
  assert (HFc : RFc F).
  { destruct HF as (F0 & F1 & F2 & F3 & F4 & F5). pose proof (BMAX_ge len Hlen). unfold RFc. repeat split; try assumption; lia. }
  unfold d2i_octet.
  destruct (Z.leb_spec len 0) as [L0|L0].
  { eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s' X' HR' _. cbn. exact HR'. }
  pose proof (get_object_bounds d 0 len Hd ltac:(lia)) as GB. cbn zeta in GB.
  destruct (go_err (get_object d 0 len)) as [e|] eqn:Eg.
  { apply awp_abind. eapply awp_mono; [apply (tlen_fail_spec e s _ X HR HFc); destruct e; [discriminate| discriminate| destruct GB]|].
    intros [[] s1] X1 [HR1 _]. cbn [fst snd] in *.
    eapply raise_then; [exact HR1| exact HFc| cbn; lia| cbn; lia|]. intros s3 X3 HR3 _. cbn. exact HR3. }
  destruct GB as (G1 & G2 & G3).
  set (g := get_object d 0 len) in *.
  destruct (negb (go_tag g =? V_ASN1_OCTET_STRING) || negb (go_cls g =? 0)).
  { eapply raise_then; [exact HR| exact HFc| cbn; lia| cbn; lia|]. intros s1 X1 HR1 _.
    eapply raise_then; [exact HR1| exact HFc| cbn; lia| cbn; lia|]. intros s2 X2 HR2 _. cbn. exact HR2. }
  set (inf := Z.testbit (go_ret g) 0). set (cst := negb (Z.land (go_ret g) 32 =? 0)).
  set (plen := if inf then len - go_p g else go_len g).
  assert (Hplen : 0 <= plen /\ go_p g + plen <= len) by (subst plen; destruct inf; lia).
  destruct cst.
  - (* [comment removed for export] *)
    apply awp_abind.
    assert (HR0 : rel s (bufb buf0 ++ F) X) by (unfold bufb, buf0; cbn; exact HR).
    eapply awp_mono; [apply (collect_spec d len Hd HT (ct_fuel d) buf0 (go_p g) plen inf 0 s F X HR0 HF (binv_buf0 len Hlen) ltac:(lia)); [cbn; lia| unfold ct_fuel; subst len; unfold zlength in *; lia]|].
    intros [[b r] s1] X1 (HR1 & HB1 & HL1 & HP1). cbn [fst snd] in *. cbn [buf0 bm_len] in HL1, HP1.
    destruct r as [p'|].
    + (* [comment removed for export] *)
      apply awp_abind. destruct HB1 as [HBL HBD]. destruct HP1 as (HP1a & HP1b & HP1c).
      assert (C : bm_len b + 1 <= len) by lia.
      eapply awp_mono; [apply (buf_grow_clean_spec len b (bm_len b + 1) s1 F X1 HR1 HF (conj HBL HBD) HT ltac:(lia))|].
        intros [b2 s2] X2 (HR2 & E2 & HB2 & HL2 & _). cbn [fst snd] in *. subst s2.
        cbn -[st_blocks bufb octb Z.add Z.div Z.mul firstn Z.to_nat].
        split; [apply lt62; unfold SZ_ASN1_STRING; lia|].
        split.
        { destruct HR2 as [Hs HP]. destruct HF as (F0 & F1 & F2 & F3 & F4 & F5). destruct (bufb_measure len b2 HB2) as (B0 & B1 & B2 & B3 & B4 & B5).
          apply (ok_frame s1 (bufb b2 ++ F) X2 SZ_ASN1_STRING Hs HP); [apply bnonneg_app; assumption| unfold SZ_ASN1_STRING; lia| | | | |];
            rewrite measure_app; cbn [madd m_cnt m_sum m_sm m_n63 m_r63 m_nsec]; unfold SZ_ASN1_STRING;
            rewrite ?smsz_small, ?isbig_small, ?bigb_small, ?issec_small by (unfold MMAP_THRESHOLD, ASAN_SEC_MIN; lia); pose proof (BMAX_ge len Hlen); lia. }
        split; [reflexivity|]. intros blk Hblk. cbn -[st_blocks bufb octb Z.add Z.div Z.mul firstn Z.to_nat BMAX].
        split.
        { destruct HR2 as [Hs HP]. split; [exact Hs|]. unfold octb, bufb in *. cbn [os_data os_blk]. perm_via (perm_skip (blk, SZ_ASN1_STRING) HP). }
        unfold oinv. cbn [os_len os_data]. destruct HB2 as [HB2a HB2b]. split; [lia|].
        destruct (bm_data b2) as [[q m]|]; [| exact I]. rewrite HL2 in HB2b. destruct HB2b as [M1 [M2 M3]].
        pose proof (BMAX_mono (bm_len b + 1) len ltac:(lia)). unfold BMAX in *.
        replace (bm_len b + 1 + 3) with (bm_len b + 4) in * by lia. lia.
    + (* [comment removed for export] *)
      eapply seq_unit; [apply (afree_opt_spec _ _ _ _ (bm_data b) s1 F X1); unfold bufb in HR1; exact HR1|].
      intros X2 HR2. cbn. exact HR2.
  - (* [comment removed for export] *)
    cbn -[st_blocks octb Z.add slice amalloc_crypto].
    split; [apply lt62; unfold SZ_ASN1_STRING; lia|].
    split.
    { destruct HR as [Hs HP]. destruct HF as (F0 & F1 & F2 & F3 & F4 & F5).
      apply (ok_frame s F X SZ_ASN1_STRING Hs ltac:(rewrite <- (app_nil_l F) in HP; exact HP) F0); unfold SZ_ASN1_STRING;
        rewrite ?smsz_small, ?isbig_small, ?bigb_small, ?issec_small by (unfold MMAP_THRESHOLD, ASAN_SEC_MIN; lia); pose proof (BMAX_ge len Hlen); lia. }
    split; [reflexivity|]. intros blk Hblk.
    unfold amalloc_crypto. destruct (Z.eqb_spec plen 0) as [P0|P0].
    + cbn -[st_blocks octb slice]. split.
      { destruct HR as [Hs HP]. split; [exact Hs|]. unfold octb. cbn. perm_via (perm_skip (blk, SZ_ASN1_STRING) HP). }
      unfold oinv. cbn. lia.
    + cbn -[st_blocks octb slice Z.add].
      split; [apply lt62c; lia|].
      split.
      { destruct HR as [Hs HP]. destruct HF as (F0 & F1 & F2 & F3 & F4 & F5).
        apply (ok_frame s ((blk, SZ_ASN1_STRING) :: F) ((blk, SZ_ASN1_STRING) :: X) plen Hs); [perm_via (perm_skip (blk, SZ_ASN1_STRING) HP)| constructor; [cbn; unfold SZ_ASN1_STRING; lia| exact F0]| lia| | | | |];
          rewrite measure_cons; cbn [madd m_cnt m_sum m_sm m_n63 m_r63 m_nsec mblk snd]; unfold SZ_ASN1_STRING;
          rewrite ?(smsz_small 24), ?(isbig_small 24), ?(bigb_small 24), ?(issec_small 24) by (unfold MMAP_THRESHOLD, ASAN_SEC_MIN; lia).
        - lia.
        - pose proof (smsz_bound plen ltac:(lia)). lia.
        - pose proof (isbig_01 plen). lia.
        - pose proof (bigb_bound plen len ltac:(lia)). pose proof (BMAX_ge len Hlen). lia.
        - pose proof (issec_01 plen). lia. }
      split; [reflexivity|]. intros dp Hdp. cbn -[st_blocks octb slice].
      split.
      { destruct HR as [Hs HP]. split; [exact Hs|]. unfold octb. cbn. perm_via (perm_skip (dp, plen) (perm_skip (blk, SZ_ASN1_STRING) HP)). }
      unfold oinv. cbn. pose proof (BMAX_ge plen ltac:(lia)). pose proof (BMAX_mono plen len ltac:(lia)). unfold BMAX in *.
      assert (plen <= (plen + 4) / 3 * 4) by (pose proof (Z.div_mod (plen + 4) 3 ltac:(lia)); pose proof (Z.mod_pos_bound (plen + 4) 3 ltac:(lia)); lia).
      lia.
Qed.

End S2.
