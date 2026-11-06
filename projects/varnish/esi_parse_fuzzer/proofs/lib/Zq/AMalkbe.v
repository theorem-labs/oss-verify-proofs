(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMallocH AMalmys AMal9l1 AMaldga.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ptauto := first [ solve [unfold iff, not in *; rtauto] | tauto ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@H; @KR; @NR; @A1; @A5; @ENOUGH; @CR; @B1; @Hk; @A7; @RL; @A10; @A11; @H0; @e; @Hn; @B2; @NLV; @B4; @B5; @E; @R1; @R2; @N1; @Hc'; @FL; @LIM; @TINY])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pboth).

(* [comment removed for export] *)
Definition ref_fetched (fr : list Z) (k : Z) : list Z := skipn (length fr - Z.to_nat k) fr.
Definition ref_rest (fr : list Z) (k : Z) : list Z := firstn (length fr - Z.to_nat k) fr.
Definition ref_reg (reg : Z -> region) (c k : Z) : Z -> region :=
  fun c' => if Z.eqb c' c then let R := reg c in RG (rg_mapped_user R) (rg_allocated_user R) (rg_mapped_fa R) (ref_rest (rg_free R) k) else reg c'.
Definition ref_cache (cache : Z -> pcache) (c : Z) (fetched : list Z) : Z -> pcache :=
  fun c' => if Z.eqb c' c then PCc (removelast fetched) else cache c'.
Definition refK (A : AState) (n : Z) : Z :=
  let fr := rg_free (a_reg A (class_of n)) in nth (length fr - 1) fr 0.
Definition refA (A : AState) (n : Z) (key : list Z) : AState :=
  let c := class_of n in let fr := rg_free (a_reg A c) in let k := refill_count c in let kidx := refK A n in
  mkA (a_pl A) (ref_reg (a_reg A) c k) (a_cache_inited A) (ref_cache (a_cache A) c (ref_fetched fr k))
      (<[ hit_user A n kidx := LI (ChP (CP c kidx)) n ]> (a_livemap A))
      (a_qthread A) (a_qglobal A) (a_sec A) (fst (depot_putC (a_depot A) key))
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A - is_tiny n)
      (a_qlimbo A) (a_scred A) (a_deadsh A)
      (a_pcred A - class_size c) (paid_add (a_paid A) c kidx).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ref_split : forall fr k, fr = ref_rest fr k ++ ref_fetched fr k.
Proof. intros. unfold ref_rest, ref_fetched. symmetry. apply firstn_skipn. Qed.
Lemma ref_fetched_length : forall fr k, 0 <= k <= Z.of_nat (length fr) -> length (ref_fetched fr k) = Z.to_nat k.
Proof. intros. unfold ref_fetched. rewrite length_skipn. lia. Qed.
Lemma ref_rest_length : forall fr k, 0 <= k <= Z.of_nat (length fr) -> Z.of_nat (length (ref_rest fr k)) = Z.of_nat (length fr) - k.
Proof. intros. unfold ref_rest. rewrite firstn_length. lia. Qed.
Lemma ref_in_rest : forall fr k x, In x (ref_rest fr k) -> In x fr.
Proof. intros fr k x H. rewrite (ref_split fr k). apply in_or_app. left. exact H. Qed.
Lemma ref_in_fetched : forall fr k x, In x (ref_fetched fr k) -> In x fr.
Proof. intros fr k x H. rewrite (ref_split fr k). apply in_or_app. right. exact H. Qed.
Lemma NoDup_app_parts : forall (l1 l2 : list Z), NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> In x l2 -> False).
Proof.
  intros l1 l2 ND. apply (proj1 (list.NoDup_app _ _)) in ND. (first [ dand3 ND as N1 DJ N2 | destruct ND as (N1 & DJ & N2) ]).
  split; [exact N1|]. split; [exact N2|]. intros x H1 H2. apply (DJ x); apply list_elem_of_In; assumption.
Qed.
Lemma ref_nodup : forall fr k, NoDup fr -> NoDup (ref_rest fr k) /\ NoDup (ref_fetched fr k) /\
  (forall x, In x (ref_rest fr k) -> In x (ref_fetched fr k) -> False).
Proof. intros fr k ND. rewrite (ref_split fr k) in ND. exact (NoDup_app_parts _ _ ND). Qed.
Lemma ref_last_fetched : forall fr k, 1 <= k <= Z.of_nat (length fr) ->
  nth (length (ref_fetched fr k) - 1) (ref_fetched fr k) 0 = nth (length fr - 1) fr 0 /\ ref_fetched fr k <> [].
Proof.
  intros fr k Hk. unfold ref_fetched. rewrite length_skipn. split.
  - rewrite nth_skipn. f_equal. lia.
  - intros E. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
Qed.

Section WFref.
Context {Clg : Ceiling}.
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (n : Z) (key : list Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation fr := (rg_free (a_reg A (class_of n))).
  Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).
  Local Notation k := (refill_count (class_of n)).
  Local Notation kidx := (refK A n).
  Local Notation fetched := (ref_fetched (rg_free (a_reg A (class_of n))) (refill_count (class_of n))).
  Hypothesis CI : a_cache_inited A = true.
  Hypothesis EMP : pk_chunks (a_cache A (class_of n)) = [].
  Hypothesis ENOUGH : refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))).
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis LIM : as_livebytes A + n <= LIVE_MAX.
  Hypothesis NLV : as_nlive A + 1 <= NLIVE_MAX.
  Hypothesis TINY : n < 16 -> 1 <= as_tinycred A.
  Hypothesis PCRED : prim_cost n <= as_primcred A.   (* [comment removed for export] *)
  Local Notation u := (hit_user A n (refK A n)).
  Local Notation lm := (a_livemap A).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  Lemma rf_CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.
  Lemma rf_k : 1 <= k <= 8 /\ max_count c = 2 * k. Proof. pose proof (max_count_range _ rf_CR); lia. Qed.
  Lemma rf_KIN : In kidx fr. Proof. exact (proj1 (ref_kidx A m md n AI NR ENOUGH)). Qed.
  Lemma rf_KB : 0 <= kidx < carved_count A c. Proof. exact (proj1 (proj2 (ref_kidx A m md n AI NR ENOUGH))). Qed.
  Lemma rf_kidx_fetched : In kidx fetched /\ kidx = nth (length fetched - 1) fetched 0 /\ fetched <> [].
  Proof.
    pose proof rf_k as [KR _]. destruct (ref_last_fetched fr k ltac:(lia)) as [E NE]. unfold refK. rewrite <- E.
    split; [| split; [reflexivity| exact NE]].
    apply (nth_error_In _ (length fetched - 1)). apply nth_error_nth'. destruct fetched; [congruence| cbn; lia].
  Qed.
  Lemma rf_ND : NoDup fr.
  Proof. (first [ pose proof ((wfR A W)) as dR_2; dand3 dR_2 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c rf_CR)) as dR_3; dand9 dR_3 as _ _ _ _ _ _ _ ND _ | destruct (WR c rf_CR) as (_ & _ & _ & _ & _ & _ & _ & ND & _) ]). exact ND. Qed.

  (* [comment removed for export] *)
  Lemma rf_free_iff : forall c' j, p_free_ (ref_reg (a_reg A) c k) c' j <-> (c' <> c /\ p_free_ (a_reg A) c' j) \/ (c' = c /\ In j (ref_rest fr k)).
  Proof.
    intros c' j. unfold p_free_, ref_reg. destruct (Z.eqb_spec c' c) as [->|NE]; cbn [rg_free]; split; intros H; try tauto.
    all: destruct H as [[X1 X2]|[X1 X2]]; first [congruence | assumption].
  Qed.
  Lemma rf_cached_iff : forall c' j, p_cached_ (ref_cache (a_cache A) c fetched) c' j <-> (c' <> c /\ p_cached_ (a_cache A) c' j) \/ (c' = c /\ In j (removelast fetched)).
  Proof.
    intros c' j. unfold p_cached_, ref_cache. destruct (Z.eqb_spec c' c) as [->|NE]; cbn [pk_chunks]; split; intros H; try tauto.
    all: destruct H as [[X1 X2]|[X1 X2]]; first [congruence | assumption].
  Qed.
  Lemma rf_u_fresh : lm !! u = None.
  Proof.
    destruct (lm !! u) as [li|] eqn:E; [| reflexivity]. exfalso.
    destruct (wfV A W) as (V1 & _). pose proof (V1 _ _ E) as (N1 & _). cbv zeta in N1.
    (first [ pose proof ((hit_u_range A n kidx NR)) as dR_4; dand3 dR_4 as R1 R2 _ | destruct (hit_u_range A n kidx NR) as (R1 & R2 & _) ]).
    pose proof (primary_chunk_no_other_user A c kidx u W rf_CR rf_KB ltac:(lia) u li E ltac:(lia)) as EQ.
    (* [comment removed for export] *)
    pose proof (wfX A W c kidx rf_CR rf_KB) as X. cbv zeta in X. (first [ dand4 X as _ _ NFV _ | destruct X as (_ & _ & NFV & _) ]).
    apply NFV. split; [exact rf_KIN|]. exists u, (li_n li). rewrite <- EQ. destruct li; exact E.
  Qed.
  Lemma rf_live_iff : forall c' j, p_live_ (<[u:=LI (ChP (CP c kidx)) n]> lm) c' j <-> p_live_ lm c' j \/ (c' = c /\ j = kidx).
  Proof.
    intros c' j. unfold p_live_. split.
    - ((first [ intro dR_24; dex2 dR_24 as u0 n0; rename dR_24 into H | intro dR_24; dand3 dR_24 as u0 n0 H | intros (u0 & n0 & H) ])). destruct (decide (u0 = u)) as [->|NEu].
      + rewrite lookup_insert_eq in H. injection H as <- <- <-. right. split; reflexivity.
      + rewrite lookup_insert_ne in H by (intros E; apply NEu; symmetry; exact E). left. exists u0, n0. exact H.
    - intros [(u0 & n0 & H)|[-> ->]].
      + exists u0, n0. rewrite lookup_insert_ne; [exact H|]. intros E. rewrite <- E in H. rewrite rf_u_fresh in H. discriminate.
      + exists u, n. rewrite lookup_insert_eq. reflexivity.
  Qed.
  Lemma rf_cc : carved_count_ (ref_reg (a_reg A) c k) = carved_count_ (a_reg A).
  Proof.
    apply functional_extensionality. intros c'. unfold carved_count_, ref_reg. destruct (Z.eqb_spec c' c) as [->|NE]; reflexivity.
  Qed.
  Lemma rf_not_quar : ~ In (ChP (CP c kidx)) (quarantined_chunks_ (a_qthread A) (a_qglobal A)).
  Proof.
    intros Hin. pose proof (wfX A W c kidx rf_CR rf_KB) as X. cbv zeta in X. (first [ dand5 X as _ _ _ NFQ _ | destruct X as (_ & _ & _ & NFQ & _) ]).
    apply NFQ. split; [exact rf_KIN|]. unfold p_quar_. unfold quarantined_chunks_ in Hin. apply in_map_iff in Hin as (e & E & He).
    exists (qe_n e). destruct e as [ch j]; cbn in E; subst ch. exact He.
  Qed.
  Lemma rf_not_live : forall u' li, lm !! u' = Some li -> li_chunk li <> ChP (CP c kidx).
  Proof.
    intros u' li Hl E. pose proof (wfX A W c kidx rf_CR rf_KB) as X. cbv zeta in X. (first [ dand4 X as _ _ NFV _ | destruct X as (_ & _ & NFV & _) ]).
    apply NFV. split; [exact rf_KIN|]. exists u', (li_n li). rewrite <- E. destruct li; exact Hl.
  Qed.

  (* [comment removed for export] *)
  Lemma ref_partition :
    ~ p_cached_ (a_cache A) c kidx /\ ~ p_live_ lm c kidx /\ ~ p_quar_ (a_qthread A) (a_qglobal A) c kidx /\ ~ p_batch_ (a_qthread A) (a_qglobal A) c kidx.
  Proof.
    pose proof (wfX A W c kidx rf_CR rf_KB) as X. cbv zeta in X.
    (first [ dand6 X as _ NFC' NFV NFQ NFB _ | destruct X as (_ & NFC' & NFV & NFQ & NFB & _) ]).
    pose proof rf_KIN as F. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros H; [apply NFC' | apply NFV | apply NFQ | apply NFB]; split; assumption.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem ref_WF : WF (refA A n key).
  Proof.
    pose proof rf_CR as CR. pose proof rf_KB as KB. pose proof rf_KIN as KIN. pose proof rf_u_fresh as FR. pose proof rf_k as [KR MK].
    pose proof rf_ND as ND. (first [ pose proof ((ref_nodup fr k ND)) as dR_11; dand3 dR_11 as NDr NDf DISJ | destruct (ref_nodup fr k ND) as (NDr & NDf & DISJ) ]). (first [ dand3 rf_kidx_fetched as KF KL FNE | destruct rf_kidx_fetched as (KF & KL & FNE) ]).
    destruct (removelast_nodup fetched NDf) as [NDrl NLast]. specialize (NLast FNE). rewrite <- KL in NLast.
    pose proof rf_cc as CC.
    destruct W as [wP wM wR0 wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    pose proof (wf_regions_paid_add _ _ _ c kidx CR wR0) as wR.   (* [comment removed for export] *)
    unfold refA. cbv zeta.
    constructor; cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - (* [comment removed for export] *) (first [ dand3 wR as R1 R2 R3 | destruct wR as (R1 & R2 & R3) ]). split; [| split].
      + intros c' Hc'. unfold ref_reg. destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (R1 c' Hc')].
        (first [ pose proof ((R1 c CR)) as dR_14; dand11 dR_14 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 | destruct (R1 c CR) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) ]). unfold wf_region. cbn [rg_mapped_user rg_allocated_user rg_mapped_fa rg_free].
        pose proof (ref_rest_length fr k ltac:(lia)) as RL.
        clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 RL KR MK NDr.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
        all: try exact NDr.
        all: try (match goal with H : In ?j (ref_rest _ _) |- _ => pose proof (A9 _ (ref_in_rest _ _ _ H)); lia end).
        all: try (intros H0; destruct (A10 H0) as [_ E]; generalize E; clear; intros E; unfold ref_rest; rewrite E; cbn; destruct (length (@nil Z) - Z.to_nat k)%nat; reflexivity).
        all: match goal with |- ?g => idtac "REGLEFT" g end.
      + intros c' Hc'. unfold ref_reg. destruct (Z.eqb_spec c' c) as [->|NE]; [lia| exact (R2 c' Hc')].
      + intros _. exact CI.
    - (* [comment removed for export] *) (first [ dand3 wC as C1 C31 C0 | destruct wC as (C1 & C31 & C0) ]). split; [| split; [unfold ref_cache; destruct (Z.eqb_spec 31 c); [lia| exact C31] | unfold ref_cache; destruct (Z.eqb_spec 0 c); [lia| exact C0]]].
      intros c' Hc'. rewrite CC. unfold ref_cache. destruct (Z.eqb_spec c' c) as [->|NEQ]; [| exact (C1 c' Hc')].
      cbv zeta. cbn [pk_chunks]. rewrite removelast_length'. pose proof (ref_fetched_length fr k ltac:(lia)) as FL.
      split; [rewrite MK; lia|]. split; [exact NDrl|]. split; [| intros F; rewrite CI in F; discriminate].
      intros j Hj. (first [ pose proof ((wfR A (ai_wf _ _ _ _ _ _ _ AI))) as dR_16; dand3 dR_16 as WR _ _ | destruct (wfR A (ai_wf _ _ _ _ _ _ _ AI)) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_17; dand10 dR_17 as _ _ _ _ _ _ _ _ B9 _ | destruct (WR c CR) as (_ & _ & _ & _ & _ & _ & _ & _ & B9 & _) ]).
      unfold carved_count_. apply B9. apply (ref_in_fetched _ k). apply removelast_incl. exact Hj.
    - (* [comment removed for export] *) intros c' j Hc' Hj. rewrite CC in Hj. cbv zeta.
      pose proof (wX c' j Hc' Hj) as X. cbv zeta in X.
      rewrite (rf_free_iff c' j), (rf_cached_iff c' j), (rf_live_iff c' j).
      assert (Cold : p_cached_ (a_cache A) c j <-> False) by (unfold p_cached_; rewrite EMP; cbn; tauto).
      destruct (Z.eq_dec c' c) as [->|NEQ].
      + (* [comment removed for export] *)
        assert (FRold : In j fr <-> p_free_ (a_reg A) c j) by (unfold p_free_; tauto).
        (first [ dand11 X as COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB | destruct X as (COV & NFC' & NFV & NFQ & NFB & NCV & NCQ & NCB & NVQ & NVB & NQB) ]).
        destruct (in_dec Z.eq_dec j (ref_rest fr k)) as [JR|JR];
        [| destruct (in_dec Z.eq_dec j (removelast fetched)) as [JC|JC];
           [| destruct (Z.eq_dec j kidx) as [->|JK]]].
        * (* [comment removed for export] *) assert (JF : In j fr) by (apply (ref_in_rest _ k); exact JR).
          assert (NJf : ~ In j fetched) by (intros H; exact (DISJ _ JR H)).
          assert (JNK : j <> kidx) by (intros ->; exact (NJf KF)).
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JF NJf JNK.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? ?]]); try (destruct H2 as [[? ?]|[? ?]]); try ptauto.
          all: try (apply NJf; apply removelast_incl; assumption). all: try (destruct H2 as [H2|[_ H2]]; [apply NFV; ptauto| congruence]).
        * (* [comment removed for export] *) assert (JF : In j fr) by (apply (ref_in_fetched _ k); apply removelast_incl; exact JC).
          assert (JNK : j <> kidx) by (intros ->; exact (NLast JC)).
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JC JF JNK DISJ.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? ?]]); try (destruct H2 as [[? ?]|[? ?]]); try ptauto.
          all: try (eapply DISJ; [eassumption| apply removelast_incl; eassumption]).
          all: try (destruct H2 as [H2|[_ H2]]; [apply NFV; ptauto| congruence]).
          all: try (apply NFQ; ptauto). all: try (apply NFB; ptauto).
        * (* [comment removed for export] *)
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JC DISJ KF NLast KIN KL FNE.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? H1']]); try ptauto; try (exact (DISJ _ H1' KF)); try (exact (NLast H1')).
          all: try (destruct H2 as [[? ?]|[? H2']]); try ptauto; try (exact (NLast H2')).
          all: try (apply NFQ; ptauto). all: try (apply NFB; ptauto).
        * (* [comment removed for export] *)
          assert (NJF : ~ In j fr).
          { intros H. rewrite (ref_split fr k) in H. apply in_app_iff in H as [H|H]; [exact (JR H)|].
            rewrite (removelast_app_last fetched 0 FNE) in H. apply in_app_iff in H as [H|[H|[]]]; [exact (JC H)|]. apply JK. rewrite KL. symmetry. exact H. }
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JC JK NJF.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? ?]]); try (destruct H2 as [[? ?]|[? ?]]); try ptauto.
      + (* [comment removed for export] *)
        assert (VV : (p_live_ lm c' j \/ c' = c /\ j = kidx) <-> p_live_ lm c' j) by (split; [intros [H|[H _]]; [exact H| congruence]| tauto]).
        rewrite VV. assert (FF : (c' <> c /\ p_free_ (a_reg A) c' j \/ c' = c /\ In j (ref_rest fr k)) <-> p_free_ (a_reg A) c' j) by tauto.
        assert (CC' : (c' <> c /\ p_cached_ (a_cache A) c' j \/ c' = c /\ In j (removelast fetched)) <-> p_cached_ (a_cache A) c' j) by tauto.
        rewrite FF, CC'. exact X.
    - (* [comment removed for export] *) unfold wf_live_. rewrite !CC. (first [ dand3 wV as V1 V2 V3 | destruct wV as (V1 & V2 & V3) ]). split; [| split].
      + intros u0 li Hl. destruct (decide (u0 = u)) as [->|NEu].
        * rewrite lookup_insert_eq in Hl. injection Hl as <-. cbv zeta. cbn [li_n li_chunk].
          split; [unfold REQ_MAX, kMaxPrimaryUser in *; lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact KB].
        * rewrite lookup_insert_ne in Hl by congruence. exact (V1 u0 li Hl).
      + intros u1 u2 li1 li2 H1 H2 NEQ.
        destruct (decide (u1 = u)) as [->|N1]; destruct (decide (u2 = u)) as [->|N2]; try congruence.
        * rewrite lookup_insert_eq in H1. injection H1 as <-. rewrite lookup_insert_ne in H2 by congruence. cbn [li_chunk].
          intros E. exact (rf_not_live _ _ H2 (eq_sym E)).
        * rewrite lookup_insert_eq in H2. injection H2 as <-. rewrite lookup_insert_ne in H1 by congruence. cbn [li_chunk].
          exact (rf_not_live _ _ H1).
        * rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (V2 _ _ _ _ H1 H2 NEQ).
      + rewrite as_livebytes_insert by exact FR. cbn [li_n]. unfold as_livebytes, as_livebytes_ in LIM. unfold as_livebytes_. lia.
    - (* [comment removed for export] *) unfold wf_quarantine_, wf_batch_, wf_qentry_. rewrite !CC. fold (wf_qentry_ (a_reg A) (a_sec A)). fold (wf_batch_ (a_reg A) (a_sec A)).
      (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]). repeat (split; [assumption|]).
      intros u0 li Hl. destruct (decide (u0 = u)) as [->|NEu].
      + rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_chunk]. exact rf_not_quar.
      + rewrite lookup_insert_ne in Hl by congruence. exact (Q8 _ _ Hl).
    - (* [comment removed for export] *) (first [ dand5 wS as S1 S2 S3 S4 S5 | destruct wS as (S1 & S2 & S3 & S4 & S5) ]). repeat (split; [assumption|]).
      intros s Hs. destruct (S5 s Hs) as [(u0 & Hu0)|Hq]; [left| right; exact Hq]. exists u0.
      rewrite lookup_insert_ne; [exact Hu0|]. intros E. rewrite <- E in Hu0. rewrite FR in Hu0. discriminate.
    - (* [comment removed for export] *) (first [ dand3 wD as INC NDD NN | destruct wD as (INC & NDD & NN) ]). split; [| split; [apply depot_putC_nodup; exact NDD| apply depot_putC_nonnil; exact NN]].
      apply Forall_forall. intros k0 Hk. assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros x Hx; exact (proj1 (Forall_forall _ _) INC x Hx)).
      exact (depot_putC_incl _ _ _ INC' KEYU k0 Hk).
    - exact wF.
    - (* [comment removed for export] *) (first [ dand5 wB as B1 B2 B3 B4 B5 | destruct wB as (B1 & B2 & B3 & B4 & B5) ]). unfold as_nlive, as_tinycred in NLV, TINY. pose proof (is_tiny_range n) as IT.
      assert (ITv : n < 16 -> is_tiny n = 1) by (intros Hn; unfold is_tiny; destruct (Z.ltb_spec n 16); lia).
      assert (ITn : ~ n < 16 -> is_tiny n = 0) by (intros Hn; unfold is_tiny; destruct (Z.ltb_spec n 16); lia).
      unfold wf_budget_. rewrite as_livebytes_insert, as_nlive_insert, tiny_live_insert by exact FR. cbn [li_n].
      destruct (Z_lt_dec n 16) as [Hn|Hn]; [rewrite (ITv Hn) in *; specialize (TINY Hn)| rewrite (ITn Hn) in *]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    - exact wI.
    - exact wE.
    - exact wJ.
    - (* [comment removed for export] *)
      apply (wf_prim_hit lm (a_qthread A) (a_qglobal A) (a_paid A) (a_pcred A) u c kidx n CR wN); [| exact FR].
      unfold as_primcred in PCRED. rewrite prim_cost_primary in PCRED by lia. exact PCRED.
  Qed.
End WFref.
