(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import Rtauto.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMallocH AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ptauto := first [ solve [unfold iff, not in *; rtauto] | tauto ].
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hit_cache (cache : Z -> pcache) (c : Z) : Z -> pcache :=
  fun c' => if Z.eqb c' c then PCc (removelast (pk_chunks (cache c))) else cache c'.
Definition hit_user (A : AState) (n kidx : Z) : Z := user_of (a_sb A) (ChP (CP (class_of n) kidx)) n.
Definition hitA (A : AState) (n kidx : Z) (key : list Z) : AState :=
  mkA (a_pl A) (a_reg A) (a_cache_inited A) (hit_cache (a_cache A) (class_of n))
      (<[ hit_user A n kidx := LI (ChP (CP (class_of n) kidx)) n ]> (a_livemap A))
      (a_qthread A) (a_qglobal A) (a_sec A) (fst (depot_putC (a_depot A) key))
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A - is_tiny n)
      (a_qlimbo A) (a_scred A) (a_deadsh A)   (* [comment removed for export] *)
      (a_pcred A - class_size (class_of n)) (paid_add (a_paid A) (class_of n) kidx).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma removelast_incl : forall {X} (l : list X) x, In x (removelast l) -> In x l.
Proof.
  intros X l. induction l as [|a l IH]; intros x H; [destruct H|]. cbn in H. destruct l as [|b l'].
  - destruct H.
  - destruct H as [<-|H]; [left; reflexivity| right; exact (IH x H)].
Qed.
Lemma last_nth : forall {X} (l : list X) d, last l d = nth (length l - 1) l d.
Proof.
  intros X l d. induction l as [|a l IH]; [reflexivity|]. cbn [last length]. destruct l as [|b l']; [reflexivity|].
  rewrite IH. cbn [length]. replace (S (length l') - 1)%nat with (length l') by lia.
  replace (S (S (length l')) - 1)%nat with (S (length l')) by lia. reflexivity.
Qed.
Lemma removelast_app_last : forall {X} (l : list X) d, l <> [] -> l = removelast l ++ [nth (length l - 1) l d].
Proof. intros X l d NE. rewrite <- last_nth. apply app_removelast_last. exact NE. Qed.
Lemma removelast_nodup : forall (l : list Z), NoDup l -> NoDup (removelast l) /\ (l <> [] -> ~ In (nth (length l - 1) l 0) (removelast l)).
Proof.
  intros l ND. destruct l as [|x l'] eqn:E; [split; [constructor| tauto]|]. rewrite <- E in *.
  assert (NE : l <> []) by (subst l; discriminate).
  pose proof (removelast_app_last l 0 NE) as EQ. rewrite EQ in ND. apply NoDup_List in ND. split.
  - apply NoDup_List. apply (List.NoDup_app_remove_r _ _ ND).
  - intros _ Hin. apply (List.NoDup_remove_2 _ [] _ ND). rewrite app_nil_r. exact Hin.
Qed.
Lemma removelast_length' : forall {X} (l : list X), length (removelast l) = (length l - 1)%nat.
Proof. intros X l. rewrite removelast_firstn_len, firstn_length. lia. Qed.

Lemma as_nlive_insert : forall lm u (li : liveinfo), lm !! u = None -> as_nlive_ (<[u := li]> lm) = as_nlive_ lm + 1.
Proof. intros lm u li Hu. unfold as_nlive_. rewrite map_size_insert_None by exact Hu. lia. Qed.
Lemma tiny_live_insert : forall lm u li, lm !! u = None -> tiny_live_ (<[u := li]> lm) = is_tiny (li_n li) + tiny_live_ lm.
Proof.
  intros lm u li Hu. unfold tiny_live_. rewrite map_fold_insert_L; [reflexivity| | exact Hu].
  intros j1 j2 z1 z2 y _ _ _. lia.
Qed.
Lemma is_tiny_range : forall n, 0 <= is_tiny n <= 1.
Proof. intros n. unfold is_tiny. destruct (Z.ltb n 16); lia. Qed.
Lemma as_livebytes_insert : forall lm u li, lm !! u = None -> as_livebytes_ (<[u := li]> lm) = li_n li + as_livebytes_ lm.
Proof.
  intros lm u li Hu. unfold as_livebytes_. rewrite map_fold_insert_L; [reflexivity| | exact Hu].
  intros j1 j2 z1 z2 y _ _ _. lia.
Qed.

Section WFpost.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (n kidx : Z) (key : list Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation ks' := (pk_chunks (a_cache A (class_of n))).
  Hypothesis NE : ks' <> [].
  Hypothesis KID : kidx = nth (length ks' - 1) ks' 0.
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis LIM : as_livebytes A + n <= LIVE_MAX.
  Hypothesis NLV : as_nlive A + 1 <= NLIVE_MAX.
  Hypothesis TINY : n < 16 -> 1 <= as_tinycred A.
  Hypothesis PCRED : prim_cost n <= as_primcred A.   (* [comment removed for export] *)
  Local Notation u := (hit_user A n kidx).
  Local Notation lm := (a_livemap A).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  Lemma hit_CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  Lemma hit_KIN : In kidx ks'. Proof. rewrite KID. exact (proj1 (proj2 (hit_kidx A m md n AI NR NE))). Qed.
  Lemma hit_KB : 0 <= kidx < carved_count A c.
  Proof. destruct (wfC A W) as (C1 & _). destruct (C1 c ltac:(pose proof hit_CR; lia)) as (_ & _ & B & _). exact (B kidx hit_KIN). Qed.

  (* [comment removed for export] *)
  Lemma hit_partition :
    ~ p_free_ (a_reg A) c kidx /\ ~ p_live_ lm c kidx /\ ~ p_quar_ (a_qthread A) (a_qglobal A) c kidx /\ ~ p_batch_ (a_qthread A) (a_qglobal A) c kidx.
  Proof.
    pose proof (wfX A W c kidx hit_CR hit_KB) as X. cbv zeta in X.
    destruct X as (_ & NFC & _ & _ & _ & NCV & NCQ & NCB & _).
    assert (C : p_cached_ (a_cache A) c kidx) by exact hit_KIN.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros H; [apply NFC | apply NCV | apply NCQ | apply NCB]; split; assumption.
  Qed.
  Lemma hit_not_live : forall u' li, lm !! u' = Some li -> li_chunk li <> ChP (CP c kidx).
  Proof.
    intros u' li Hl E. destruct hit_partition as (_ & NV & _). apply NV. exists u', (li_n li). rewrite <- E. destruct li; exact Hl.
  Qed.
  Lemma hit_u_range : chunk_addr (a_sb A) c kidx + 16 <= u /\ u + n <= chunk_addr (a_sb A) c kidx + class_size c /\ u = chunk_addr (a_sb A) c kidx + rz_size n.
  Proof.
    pose proof (primary_layout (a_sb A) c kidx n hit_CR ltac:(lia) eq_refl) as (L1 & L2 & _). cbv zeta in L1, L2. unfold hit_user.
    split; [exact L1|]. split; [exact L2| reflexivity].
  Qed.
  Lemma hit_u_fresh : lm !! u = None.
  Proof.
    destruct (lm !! u) as [li|] eqn:E; [| reflexivity]. exfalso.
    destruct (wfV A W) as (V1 & _). pose proof (V1 _ _ E) as (N1 & _). cbv zeta in N1. destruct hit_u_range as (R1 & R2 & _).
    pose proof (primary_chunk_no_other_user A c kidx u W hit_CR hit_KB ltac:(lia) u li E ltac:(lia)) as EQ.
    exact (hit_not_live _ _ E EQ).
  Qed.
  Lemma hit_not_quar : ~ In (ChP (CP c kidx)) (quarantined_chunks_ (a_qthread A) (a_qglobal A)).
  Proof.
    intros Hin. destruct hit_partition as (_ & _ & NQ & _). apply NQ. unfold p_quar_.
    unfold quarantined_chunks_ in Hin. apply in_map_iff in Hin as (e & E & He). exists (qe_n e). destruct e as [ch k]; cbn in E; subst ch. exact He.
  Qed.

  Lemma hit_cached_other : forall k, k <> kidx -> In k (removelast ks') <-> In k ks'.
  Proof.
    intros k Hk. split; [apply removelast_incl|]. intros Hin. rewrite (removelast_app_last ks' 0 NE) in Hin.
    apply in_app_iff in Hin as [Hin|[Hin|[]]]; [exact Hin|]. exfalso. apply Hk. rewrite KID. symmetry. exact Hin.
  Qed.

  Theorem hit_WF : WF (hitA A n kidx key).
  Proof.
    pose proof hit_CR as CR. pose proof hit_KB as KB. pose proof hit_KIN as KIN. pose proof hit_u_fresh as FR.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    constructor; cbn [hitA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - exact (wf_regions_paid_add _ _ _ _ _ hit_CR wR).
    - (* [comment removed for export] *) destruct wC as (C1 & C31 & C0). split; [| split; [unfold hit_cache; destruct (Z.eqb_spec 31 c); [lia| exact C31] | unfold hit_cache; destruct (Z.eqb_spec 0 c); [lia| exact C0]]].
      intros c' Hc'. unfold hit_cache. destruct (Z.eqb_spec c' c) as [->|NEQ]; [| exact (C1 c' Hc')].
      destruct (C1 c ltac:(lia)) as (L1 & ND & B & CI). cbv zeta in *. cbn [pk_chunks].
      destruct (removelast_nodup ks' ND) as [ND' NL]. rewrite removelast_length'.
      split; [lia|]. split; [exact ND'|]. split; [intros k Hk; apply B; apply removelast_incl; exact Hk|].
      intros Hci. rewrite (CI Hci). reflexivity.
    - (* [comment removed for export] *) intros c' k Hc' Hk. cbv zeta. unfold hit_cache, p_cached_. cbn [pk_chunks].
      pose proof (wX c' k Hc' Hk) as X. cbv zeta in X. unfold p_cached_ in X.
      (* [comment removed for export] *)
      assert (LV : p_live_ (<[u:=LI (ChP (CP c kidx)) n]> lm) c' k <-> p_live_ lm c' k \/ (c' = c /\ k = kidx)).
      { unfold p_live_. split.
        - intros (u0 & n0 & H). destruct (decide (u0 = u)) as [->|NEu].
          + rewrite lookup_insert_eq in H. injection H as <- <- <-. right. split; reflexivity.
          + rewrite lookup_insert_ne in H by (intros E; apply NEu; symmetry; exact E). left. exists u0, n0. exact H.
        - intros [(u0 & n0 & H)|[-> ->]].
          + exists u0, n0. rewrite lookup_insert_ne; [exact H|]. intros E. rewrite <- E in H. rewrite FR in H. discriminate.
          + exists u, n. rewrite lookup_insert_eq. reflexivity. }
      destruct (Z.eqb_spec c' c) as [->|NEQ].
      + destruct (Z.eq_dec k kidx) as [->|NK].
        * (* [comment removed for export] *)
          destruct hit_partition as (NF & NV & NQ & NB). destruct (removelast_nodup ks' ltac:(destruct (wC) as (C1 & _); destruct (C1 c ltac:(lia)) as (_ & ND & _); exact ND)) as [_ NL].
          assert (NC : ~ In kidx (removelast ks')) by (rewrite KID at 1; apply NL; exact NE).
          assert (V : p_live_ (<[u:=LI (ChP (CP c kidx)) n]> lm) c kidx) by (apply LV; right; split; reflexivity).
          clear - NF NV NQ NB NC V.
          split; [ptauto|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros [H1 H2]; ptauto.
        * (* [comment removed for export] *)
          assert (CC : In k (removelast ks') <-> In k ks') by (apply hit_cached_other; exact NK).
          assert (VV : p_live_ (<[u:=LI (ChP (CP c kidx)) n]> lm) c k <-> p_live_ lm c k) by (rewrite LV; split; [intros [H|[_ H]]; [exact H| congruence]| tauto]).
          rewrite CC, VV. exact X.
      + assert (VV : p_live_ (<[u:=LI (ChP (CP c kidx)) n]> lm) c' k <-> p_live_ lm c' k) by (rewrite LV; split; [intros [H|[H _]]; [exact H| congruence]| tauto]).
        rewrite VV. exact X.
    - (* [comment removed for export] *) destruct wV as (V1 & V2 & V3). split; [| split].
      + intros u0 li Hl. destruct (decide (u0 = u)) as [->|NEu].
        * rewrite lookup_insert_eq in Hl. injection Hl as <-. cbv zeta. cbn [li_n li_chunk].
          split; [unfold REQ_MAX, kMaxPrimaryUser in *; lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact KB].
        * rewrite lookup_insert_ne in Hl by congruence. exact (V1 u0 li Hl).
      + intros u1 u2 li1 li2 H1 H2 NEQ.
        destruct (decide (u1 = u)) as [->|N1]; destruct (decide (u2 = u)) as [->|N2]; try congruence.
        * rewrite lookup_insert_eq in H1. injection H1 as <-. rewrite lookup_insert_ne in H2 by congruence. cbn [li_chunk].
          intros E. exact (hit_not_live _ _ H2 (eq_sym E)).
        * rewrite lookup_insert_eq in H2. injection H2 as <-. rewrite lookup_insert_ne in H1 by congruence. cbn [li_chunk].
          exact (hit_not_live _ _ H1).
        * rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (V2 _ _ _ _ H1 H2 NEQ).
      + rewrite as_livebytes_insert by exact FR. cbn [li_n]. unfold as_livebytes, as_livebytes_ in LIM. unfold as_livebytes_. lia.
    - (* [comment removed for export] *) destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). repeat (split; [assumption|]).
      intros u0 li Hl. destruct (decide (u0 = u)) as [->|NEu].
      + rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_chunk]. exact hit_not_quar.
      + rewrite lookup_insert_ne in Hl by congruence. exact (Q8 _ _ Hl).
    - (* [comment removed for export] *) destruct wS as (S1 & S2 & S3 & S4 & S5). repeat (split; [assumption|]).
      intros s Hs. destruct (S5 s Hs) as [(u0 & Hu0)|Hq]; [left| right; exact Hq]. exists u0.
      rewrite lookup_insert_ne; [exact Hu0|]. intros E. rewrite <- E in Hu0. rewrite FR in Hu0. discriminate.
    - (* [comment removed for export] *) destruct wD as (INC & ND & NN). split; [| split; [apply depot_putC_nodup; exact ND| apply depot_putC_nonnil; exact NN]].
      apply Forall_forall. intros k Hk. assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros x Hx; exact (proj1 (Forall_forall _ _) INC x Hx)).
      exact (depot_putC_incl _ _ _ INC' KEYU k Hk).
    - exact wF.
    - (* [comment removed for export] *) destruct wB as (B1 & B2 & B3 & B4 & B5). unfold as_nlive, as_tinycred in NLV, TINY. pose proof (is_tiny_range n) as IT.
      assert (ITv : n < 16 -> is_tiny n = 1) by (intros Hn; unfold is_tiny; destruct (Z.ltb_spec n 16); lia).
      assert (ITn : ~ n < 16 -> is_tiny n = 0) by (intros Hn; unfold is_tiny; destruct (Z.ltb_spec n 16); lia).
      unfold wf_budget_. rewrite as_livebytes_insert, as_nlive_insert, tiny_live_insert by exact FR. cbn [li_n].
      destruct (Z_lt_dec n 16) as [Hn|Hn]; [rewrite (ITv Hn) in *; specialize (TINY Hn)| rewrite (ITn Hn) in *]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - exact wI.
    - exact wE.
    - exact wJ.
    - (* [comment removed for export] *)
      apply (wf_prim_hit lm (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) u c kidx n hit_CR wN); [| exact FR].
      unfold as_primcred in PCRED. rewrite prim_cost_primary in PCRED by lia. exact PCRED.
  Qed.
End WFpost.
