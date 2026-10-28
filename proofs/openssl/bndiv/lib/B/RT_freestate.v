(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_sizeclass R_cache_defs R_prim_defs R_depot_defs R_fs_defs RT_state RT_rep RT_facts0 RT_sep RT_facts RT_malstate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_remove_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.

Lemma live_remove_In : forall p l x, In x (live_remove p l) <-> In x l /\ fst x <> p.
Proof.
  intros p l x. induction l as [|e l IH]; [cbn; tauto|]. rewrite live_remove_cons.
  destruct (Z.eqb_spec (fst e) p) as [E|E].
  - rewrite IH. cbn [In]. split; [intros (H1 & H2); split; [right; exact H1 | exact H2]|].
    intros ([<-|H1] & H2); [exfalso; exact (H2 E) | split; [exact H1 | exact H2]].
  - cbn [In]. rewrite IH. split; [intros [<-|(H1 & H2)]; [split; [left; reflexivity | exact E] | split; [right; exact H1 | exact H2]]|].
    intros ([<-|H1] & H2); [left; reflexivity | right; split; [exact H1 | exact H2]].
Qed.

Lemma live_remove_length : forall p l, (length (live_remove p l) <= length l)%nat.
Proof. intros p l. induction l as [|e l IH]; [cbn; lia|]. rewrite live_remove_cons. destruct (fst e =? p); cbn [length]; lia. Qed.

Lemma nodup_live_remove : forall p l, List.NoDup (map fst l) -> List.NoDup (map fst (live_remove p l)).
Proof.
  intros p l. induction l as [|e l IH]; intros H; [cbn; constructor|]. rewrite live_remove_cons. inversion H as [|a b Hx Hl]; subst.
  destruct (fst e =? p); [exact (IH Hl)|]. cbn [map]. constructor; [|exact (IH Hl)].
  intros Hin. apply Hx. apply in_map_iff in Hin as (y & Ey & Hy). apply live_remove_In in Hy as (Hy & _). apply in_map_iff. exists y. split; [exact Ey | exact Hy].
Qed.

(* [comment removed for export] *)
Lemma dep_inv_put : forall D tr, dep_inv D -> In tr T_MAIN -> (length tr <= TR_MAX)%nat -> dep_inv (fst (depot_put D tr)).
Proof.
  intros D tr (Hnd & Hin & H1 & H2) HT Hl. destruct (Z.eqb_spec (find_of (d_hs D) (depot_hash tr)) 0) as [E|E].
  - pose proof (depot_put_nodup D tr Hnd) as ND'. rewrite (depot_put_miss D tr E) in ND' |- *. cbn [fst d_hs d_tot] in *.
    unfold dep_inv, d_n in *. cbn [d_hs d_tot]. rewrite length_app. cbn [length].
    split; [exact ND'|].
    split.
    + intros h Hh. apply in_app_or in Hh as [Hh|[<-|[]]].
      * destruct (Hin h Hh) as [X|X]; [left | right; exact X]. rewrite hash_of_snoc_old by lia. exact X.
      * right. apply in_map. exact HT.
    + split; lia.
  - rewrite (depot_put_hit D tr E). cbn [fst]. exact (conj Hnd (conj Hin (conj H1 H2))).
Qed.

Lemma depot_ok_mono : forall D DNB SSB lo lo', depot_ok D DNB SSB lo -> lo <= lo' -> depot_ok D DNB SSB lo'.
Proof. intros D DNB SSB lo lo' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) H. unfold depot_ok. repeat split; try assumption; lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition free_p (Σ : rtsA) (c : Z) (i : nat) (n p : Z) (D' : depot) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? c then upd_reg (pr Σ c) i (CkQuar n) else pr Σ c') (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ)
    (aw Σ) (ql Σ) (qg Σ) D' (fs0 Σ) (fs2 Σ) (fs4 Σ) (ia_init Σ) (credit Σ) (live_remove p (live Σ)) (frames Σ).

Section FreeP.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n : Z) (D' : depot).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HDok : depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HDinv : dep_inv D'.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation p := (p_ubeg (l_SB (lay Σ)) c i n).

Lemma fp_reg_wf : reg_wf c (upd_reg (pr Σ c) i (CkQuar n)).
Proof.
  pose proof (ART_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  unfold upd_reg, reg_wf. cbn [r_muser r_mfa r_st r_fl]. rewrite upd_length.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|]. split; [exact W6|].
  split; [exact W7|]. split; [exact W8|]. split; [|split; [|exact W11]].
  - apply Forall_forall. intros j Hj. destruct (proj1 (Forall_forall _ _) W9 j Hj) as (J1 & J2). split; [exact J1|].
    rewrite nth_error_upd_ck. destruct (Nat.eqb_spec i (Z.to_nat j)) as [E|E]; [|exact J2].
    rewrite <- E, Hn in J2. discriminate.
  - apply Forall_forall. intros st Hst. apply (In_nth_error _ _) in Hst as (k & Hk). rewrite nth_error_upd_ck in Hk.
    destruct (Nat.eqb_spec i k) as [E|E].
    + destruct (Nat.ltb_spec k (length (r_st (pr Σ c)))); [injection Hk as <-|discriminate].
      exact (proj1 (Forall_forall _ _) W10 (CkAlloc n) (nth_error_In _ _ Hn)).
    + exact (proj1 (Forall_forall _ _) W10 st (nth_error_In _ _ Hk)).
Qed.

(* [comment removed for export] *)
Lemma fp_ubeg_ne : forall c' i' n', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some (CkAlloc n') -> (c' <> c \/ i' <> i) ->
  p_ubeg SB c' i' n' <> p.
Proof.
  intros c' i' n' Hc' Hn' Hne E.
  destruct (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hn' ltac:(destruct Hne; [left | right]; congruence)) as [Y|Y];
    unfold p_ubeg in *; pose proof (rz_facts n) as (_ & R); pose proof (rz_facts n') as (_ & R');
    pose proof (live_in_slot Σ m HA c i n Hc Hn) as (_ & _ & F & F0); pose proof (live_in_slot Σ m HA c' i' n' Hc' Hn') as (_ & _ & F' & F0'); lia.
Qed.

Lemma fp_sec_ne : forall s, In s (sec Σ) -> s_ubeg s <> p.
Proof.
  intros s Hs E. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & _ & Ha & _).
  pose proof (slot_geo Σ m HA c i _ Hc Hn) as (S1 & S2 & S3 & _). pose proof (geo_prb Σ m HA) as (P1 & P2 & _).
  pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. pose proof (rz_facts n) as (_ & R).
  pose proof (live_in_slot Σ m HA c i n Hc Hn) as (_ & _ & F & F0).
  unfold apart, s_ubeg, p_ubeg, rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma fp_st : forall c' i' st, nth_error (r_st (if c' =? c then upd_reg (pr Σ c) i (CkQuar n) else pr Σ c')) i' = Some st ->
  (c' = c /\ i' = i /\ st = CkQuar n) \/ ((c' <> c \/ i' <> i) /\ nth_error (r_st (pr Σ c')) i' = Some st).
Proof.
  intros c' i' st H. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|right; split; [left; exact Hcc | exact H]].
  unfold upd_reg in H. cbn [r_st] in H. rewrite nth_error_upd_ck in H. destruct (Nat.eqb_spec i i') as [<-|Hii].
  - destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [injection H as <-; left; tauto | discriminate].
  - right. split; [right; intros E; exact (Hii (eq_sym E)) | exact H].
Qed.

Theorem free_p_wf : rt_wf0 (free_p Σ c i n p D').
Proof.
  pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & _).
  pose proof (dep_inv_bounds D' HDinv) as (B1 & B2).
  unfold rt_wf0, free_p. cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fs2 fs4 ia_init credit live frames].
  split; [exact W1|]. split.
  { (* [comment removed for export] *)
    unfold regs_wf. cbn [pr ca ca_init]. destruct W2 as (R1 & R2 & R3 & R4 & R5 & R6).
    split; [intros c' Hc'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [exact fp_reg_wf | exact (R1 c' Hc')]|].
    split; [intros c' Hc'; destruct (Z.eqb_spec c' c) as [->|Hcc]; [lia | exact (R2 c' Hc')]|].
    split; [|split; [exact R4|split]].
    - intros c' Hc'. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact (R3 c' Hc')].
      destruct (R3 c Hc) as (C1 & C2 & C3). unfold upd_reg. cbn [r_st r_fl]. rewrite upd_length.
      split; [exact C1|]. split; [exact C2|].
      apply Forall_forall. intros j Hj. destruct (proj1 (Forall_forall _ _) C3 j Hj) as (J1 & J2).
      split; [exact J1|]. rewrite nth_error_upd_ck. destruct (Nat.eqb_spec i (Z.to_nat j)) as [E|E]; [|exact J2].
      rewrite <- E, Hn in J2. discriminate.
    - (* [comment removed for export] *)
      intros c' i' Hc' Hi'. destruct (fp_st c' i' CkIdle Hi') as [(_ & _ & E)|(_ & Hi0)]; [discriminate E|].
      destruct (Z.eqb_spec c' c) as [->|Hcc]; [unfold upd_reg; cbn [r_fl]|]; exact (R5 _ i' Hc' Hi0).
    - (* [comment removed for export] *)
      intros Hci c'. destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact (R6 Hci c')]. unfold upd_reg. cbn [r_st]. rewrite (R6 Hci c). reflexivity. }
  split.
  { (* [comment removed for export] *)
    unfold live_wf. cbn [pr live lay sec]. destruct W3 as (V1 & V2 & V3 & V4 & V5).
    split; [pose proof (live_remove_length p (live Σ)); lia|]. split; [apply NoDup_ListNoDup; apply nodup_live_remove; apply NoDup_ListNoDup; exact V2|].
    split; [|split].
    - intros p' n' Hin. apply live_remove_In in Hin as (Hin & Hne). cbn [fst] in Hne.
      destruct (V3 p' n' Hin) as [(c' & i' & Hc' & Hn' & Ep)|X]; [left|right; exact X]. exists c', i'. split; [exact Hc'|]. split; [|exact Ep].
      destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact Hn']. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
      destruct (Nat.eqb_spec i i') as [<-|Hii]; [|exact Hn']. rewrite Hn in Hn'. injection Hn' as <-. exfalso. exact (Hne Ep).
    - intros c' i' n' Hc' Hn'. apply live_remove_In. cbn [fst].
      assert (Hn0 : nth_error (r_st (pr Σ c')) i' = Some (CkAlloc n') /\ (c' <> c \/ i' <> i)).
      { destruct (Z.eqb_spec c' c) as [->|Hcc]; [|split; [exact Hn' | left; exact Hcc]].
        unfold upd_reg in Hn'. cbn [r_st] in Hn'. rewrite nth_error_upd_ck in Hn'. destruct (Nat.eqb_spec i i') as [<-|Hii].
        - destruct (Nat.ltb_spec i (length (r_st (pr Σ c)))); [injection Hn' as E; discriminate E | discriminate].
        - split; [exact Hn' | right; intros E; exact (Hii (eq_sym E))]. }
      destruct Hn0 as (Hn0 & Hne). split; [exact (V4 c' i' n' Hc' Hn0)|]. exact (fp_ubeg_ne c' i' n' Hc' Hn0 Hne).
    - intros s Hs Hq. apply live_remove_In. split; [exact (V5 s Hs Hq)|]. cbn [fst]. exact (fp_sec_ne s Hs). }
  split; [exact W4|]. split.
  { (* [comment removed for export] *)
    unfold quar_wf. cbn [ql qg pr lay sec]. destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [exact Q1|]. split; [exact Q2|]. split; [|split; [exact Q4|split; [exact Q5|split; [|split; [exact Q7|]]]]].
    - apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) Q3 b Hb) as (i' & Hi' & Eb). exists i'. split; [|exact Eb].
      destruct (Z.eqb_spec 24 c) as [Ec|Hcc]; [|exact Hi']. rewrite Ec in Hi'. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
      destruct (Nat.eqb_spec i i') as [Ei|Hii]; [rewrite <- Ei, Hn in Hi'; discriminate | exact Hi'].
    - unfold qents in *. cbn [ql qg] in *. apply Forall_forall. intros e He.
      destruct (proj1 (Forall_forall _ _) Q6 e He) as [(c' & i' & Hc' & Hi' & Ee)|X]; [left|right; exact X].
      exists c', i'. split; [exact Hc'|]. split; [|exact Ee]. cbn [pr free_p].
      destruct (Z.eqb_spec c' c) as [->|Hcc]; [|exact Hi']. unfold upd_reg. cbn [r_st]. rewrite nth_error_upd_ck.
      destruct (Nat.eqb_spec i i') as [Ei|Hii]; [rewrite <- Ei, Hn in Hi'; discriminate | exact Hi'].
    - intros c' i' Hc' Hi'. destruct (fp_st c' i' CkBatch Hi') as [(_ & _ & E)|(_ & Hi0)]; [discriminate E|]. exact (Q8 c' i' Hc' Hi0). }
  split.
  { (* [comment removed for export] *)
    destruct W6 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|].
    split; [exact F7|]. intros k Hk. pose proof (F8 k Hk) as X. destruct Hk as [ -> | [ -> | -> ] ]; exact X. }
  split.
  { (* [comment removed for export] *)
    unfold budget_wf. cbn [credit aw]. destruct W7 as (G1 & G2 & G3 & G4 & G5).
    split; [lia|]. split; [exact G2|]. split; [lia|]. split; [|unfold secsum in *; cbn [sec]; exact G5].
    assert (E : rt_eager (free_p Σ c i n p D') = rt_eager Σ).
    { unfold rt_eager, free_p. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
      destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; reflexivity | reflexivity]. }
    unfold free_p in E. cbn [pr sec sec_nres] in E. rewrite E. exact G4. }
  split; [exact HDok|]. split; [lia|]. split; [lia|]. exact HDinv.
Qed.

End FreeP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ARTc (Σ : rtsA) (m : mem) : Prop :=
  consts_rep (lay Σ) m /\ prim_rep Σ m /\ cache_rep Σ m /\ chunk_rep Σ m /\ sec_rep Σ m /\ quar_rep Σ m
  /\ dep_rep (lay Σ) (dep Σ) m /\ fs_rep Σ m /\ ia_rep Σ m /\ shadow_rep (lay Σ) m /\ vis_rep (lay Σ) (rtA_allow Σ) m.

Lemma ART_c : forall Σ m, ART_A Σ m -> ARTc Σ m.
Proof. intros Σ m H. exact (proj2 H). Qed.

Lemma c_ART : forall Σ m, rt_wf Σ -> ARTc Σ m -> ART_A Σ m.
Proof. intros Σ m H1 H2. exact (conj H1 H2). Qed.

Lemma ARTc_intro : forall Σ m, consts_rep (lay Σ) m -> prim_rep Σ m -> cache_rep Σ m -> chunk_rep Σ m ->
  sec_rep Σ m -> quar_rep Σ m -> dep_rep (lay Σ) (dep Σ) m -> fs_rep Σ m -> ia_rep Σ m -> shadow_rep (lay Σ) m ->
  vis_rep (lay Σ) (rtA_allow Σ) m -> ARTc Σ m.
Proof. intros. unfold ARTc. repeat (split; [assumption|]). assumption. Qed.
