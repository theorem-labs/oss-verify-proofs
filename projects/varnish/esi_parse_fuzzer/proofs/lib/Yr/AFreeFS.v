(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMallocH AMalmys AMal9l1 AMaldga AMalkbe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
#[local] Notation WF := (WF AL_pasan).
#[local] Notation QB := kQuarantineBatchClass.

(* [comment removed for export] *)
Definition reff_cache (cache : Z -> pcache) (fetched : list Z) : Z -> pcache :=
  fun c' => if Z.eqb c' QB then PCc fetched else cache c'.

Definition refF (A : AState) : AState :=
  let fr := rg_free (a_reg A QB) in
  mkA (a_pl A) (ref_reg (a_reg A) QB 1) true (reff_cache (a_cache A) (ref_fetched fr 1))
      (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_depot A)
      (a_fhint A) (a_fframes A) (a_ia_inited A) (a_oom A) (a_tiny A) (a_qlimbo A) (a_scred A) (a_deadsh A) (a_pcred A) (a_paid A).

(* [comment removed for export] *)
Lemma max_count_QB : max_count QB = 2. Proof. reflexivity. Qed.

Section WFrefF.
Context {Clg : Ceiling}.
  Variables (A : AState).
  Hypothesis W : WF A.
  Local Notation fr := (rg_free (a_reg A QB)).
  Local Notation fetched := (ref_fetched (rg_free (a_reg A QB)) 1).
  Hypothesis CI : a_cache_inited A = true.
  Hypothesis EMP : pk_chunks (a_cache A QB) = [].
  Hypothesis ENOUGH : 1 <= Z.of_nat (length (rg_free (a_reg A QB))).

  Lemma rff_CR : 1 <= QB <= 30. Proof. unfold QB. lia. Qed.
  Lemma rff_ND : NoDup fr.
  Proof. (first [ pose proof ((wfR A W)) as dR_1; dand3 dR_1 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR QB rff_CR)) as dR_2; dand9 dR_2 as _ _ _ _ _ _ _ ND _ | destruct (WR QB rff_CR) as (_ & _ & _ & _ & _ & _ & _ & ND & _) ]). exact ND. Qed.
  (* [comment removed for export] *)
  Lemma rff_fetched : exists kb, fetched = [kb] /\ In kb fr /\ fr = ref_rest fr 1 ++ [kb].
  Proof.
    pose proof (ref_fetched_length fr 1 ltac:(lia)) as L. pose proof (ref_split fr 1) as SP.
    destruct fetched as [|kb [|x l]] eqn:EF; cbn in L; try lia.
    exists kb. split; [reflexivity|]. split; [| exact SP].
    assert (X : In kb (ref_rest fr 1 ++ [kb])) by (apply in_app_iff; right; left; reflexivity). rewrite <- SP in X. exact X.
  Qed.

  Lemma rff_free_iff : forall c' j, p_free_ (ref_reg (a_reg A) QB 1) c' j <-> (c' <> QB /\ p_free_ (a_reg A) c' j) \/ (c' = QB /\ In j (ref_rest fr 1)).
  Proof.
    intros c' j. unfold p_free_, ref_reg. destruct (Z.eqb_spec c' QB) as [->|NE]; cbn [rg_free]; split; intros H; try tauto.
    all: destruct H as [[X1 X2]|[X1 X2]]; first [congruence | assumption].
  Qed.
  Lemma rff_cached_iff : forall c' j, p_cached_ (reff_cache (a_cache A) fetched) c' j <-> (c' <> QB /\ p_cached_ (a_cache A) c' j) \/ (c' = QB /\ In j fetched).
  Proof.
    intros c' j. unfold p_cached_, reff_cache. destruct (Z.eqb_spec c' QB) as [->|NE]; cbn [pk_chunks]; split; intros H; try tauto.
    all: destruct H as [[X1 X2]|[X1 X2]]; first [congruence | assumption].
  Qed.
  Lemma rff_cc : carved_count_ (ref_reg (a_reg A) QB 1) = carved_count_ (a_reg A).
  Proof.
    apply functional_extensionality. intros c'. unfold carved_count_, ref_reg. destruct (Z.eqb_spec c' QB) as [->|NE]; reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem refF_WF : WF (refF A).
  Proof.
    pose proof rff_CR as CR. pose proof rff_ND as ND. (first [ pose proof ((ref_nodup fr 1 ND)) as dR_5; dand3 dR_5 as NDr NDf DISJ | destruct (ref_nodup fr 1 ND) as (NDr & NDf & DISJ) ]).
    (first [ dex1 rff_fetched as kb; dand3 rff_fetched as EF KIN SP | dand4 rff_fetched as kb EF KIN SP | destruct rff_fetched as (kb & EF & KIN & SP) ]).
    pose proof rff_cc as CC.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN] eqn:EW. clear EW.
    unfold refF. cbv zeta.
    constructor; cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs].
    - exact wP.
    - exact wM.
    - (* [comment removed for export] *) (first [ dand3 wR as R1 R2 R3 | destruct wR as (R1 & R2 & R3) ]). split; [| split].
      + intros c' Hc'. unfold ref_reg. destruct (Z.eqb_spec c' QB) as [->|NE]; [| exact (R1 c' Hc')].
        (first [ pose proof ((R1 QB CR)) as dR_8; dand11 dR_8 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 | destruct (R1 QB CR) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) ]). unfold wf_region. cbn [rg_mapped_user rg_allocated_user rg_mapped_fa rg_free].
        pose proof (ref_rest_length fr 1 ltac:(lia)) as RL.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia.
        all: try exact NDr.
        all: try (match goal with H : In ?j (ref_rest _ _) |- _ => pose proof (A9 _ (ref_in_rest _ _ _ H)); lia end).
        all: try (intros H0; destruct (A10 H0) as [_ E]; generalize E; clear; intros E; unfold ref_rest; rewrite E; cbn; reflexivity).
        all: match goal with |- ?g => idtac "REGLEFT" g end.
      + intros c' Hc'. unfold ref_reg. destruct (Z.eqb_spec c' QB) as [->|NE]; [lia| exact (R2 c' Hc')].
      + intros _. reflexivity.
    - (* [comment removed for export] *) (first [ dand3 wC as C1 C31 C0 | destruct wC as (C1 & C31 & C0) ]).
      split; [| split; [unfold reff_cache; destruct (Z.eqb_spec 31 QB); [unfold QB in *; lia| exact C31]
                     | unfold reff_cache; destruct (Z.eqb_spec 0 QB); [unfold QB in *; lia| exact C0]]].
      intros c' Hc'. rewrite CC. unfold reff_cache. destruct (Z.eqb_spec c' QB) as [->|NEQ].
      2:{ (first [ pose proof ((C1 c' Hc')) as dR_10; dand4 dR_10 as X1 X2 X3 X4 | destruct (C1 c' Hc') as (X1 & X2 & X3 & X4) ]). split; [exact X1|]. split; [exact X2|]. split; [exact X3| intros F; discriminate F]. }
      cbv zeta. cbn [pk_chunks]. rewrite EF. cbn [length Z.of_nat Pos.of_succ_nat].
      split; [rewrite max_count_QB; lia|]. split; [exact NDf' || (rewrite <- EF; exact NDf)|]. split; [| intros F; discriminate F].
      intros j Hj. unfold carved_count_. (first [ dand3 wR as WR _ _ | destruct wR as (WR & _ & _) ]).
      (first [ pose proof ((WR QB CR)) as dR_12; dand10 dR_12 as _ _ _ _ _ _ _ _ B9 _ | destruct (WR QB CR) as (_ & _ & _ & _ & _ & _ & _ & _ & B9 & _) ]). apply B9. rewrite <- EF in Hj. apply (ref_in_fetched _ 1). exact Hj.
    - (* [comment removed for export] *) intros c' j Hc' Hj. rewrite CC in Hj. cbv zeta.
      pose proof (wX c' j Hc' Hj) as X. cbv zeta in X.
      rewrite (rff_free_iff c' j), (rff_cached_iff c' j).
      assert (Cold : p_cached_ (a_cache A) QB j <-> False) by (unfold p_cached_; rewrite EMP; cbn; tauto).
      destruct (Z.eq_dec c' QB) as [->|NEQ].
      + (* [comment removed for export] *)
        assert (FRold : In j fr <-> p_free_ (a_reg A) QB j) by (unfold p_free_; tauto).
        (first [ dand11 X as COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB | destruct X as (COV & NFC' & NFV & NFQ & NFB & NCV & NCQ & NCB & NVQ & NVB & NQB) ]).
        destruct (in_dec Z.eq_dec j (ref_rest fr 1)) as [JR|JR]; [| destruct (in_dec Z.eq_dec j fetched) as [JC|JC]].
        * (* [comment removed for export] *) assert (JF : In j fr) by (apply (ref_in_rest _ 1); exact JR).
          assert (NJf : ~ In j fetched) by (intros H; exact (DISJ _ JR H)).
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JF NJf.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? ?]]); try (destruct H2 as [[? ?]|[? ?]]); try ptauto.
        * (* [comment removed for export] *) assert (JF : In j fr) by (apply (ref_in_fetched _ 1); exact JC).
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JC JF DISJ.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? ?]]); try (destruct H2 as [[? ?]|[? ?]]); try ptauto.
          all: try (eapply DISJ; eassumption).
          all: try (apply NFV; tauto). all: try (apply NFQ; tauto). all: try (apply NFB; tauto).
        * (* [comment removed for export] *)
          assert (NJF : ~ In j fr).
          { intros H. rewrite SP in H. apply in_app_iff in H as [H|H]; [exact (JR H)|]. apply JC. rewrite EF. exact H. }
          clear - COV NFC' NFV NFQ NFB NCV NCQ NCB NVQ NVB NQB Cold FRold JR JC NJF.
          OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try ptauto. all: intros [H1 H2]; try ptauto.
          all: try (destruct H1 as [[? ?]|[? ?]]); try (destruct H2 as [[? ?]|[? ?]]); try ptauto.
      + assert (FF : (c' <> QB /\ p_free_ (a_reg A) c' j \/ c' = QB /\ In j (ref_rest fr 1)) <-> p_free_ (a_reg A) c' j) by tauto.
        assert (CC' : (c' <> QB /\ p_cached_ (a_cache A) c' j \/ c' = QB /\ In j fetched) <-> p_cached_ (a_cache A) c' j) by tauto.
        rewrite FF, CC'. exact X.
    - (* [comment removed for export] *) unfold wf_live_. rewrite !CC. exact wV.
    - (* [comment removed for export] *) unfold wf_quarantine_, wf_batch_, wf_qentry_. rewrite !CC. exact wQ.
    - exact wS.
    - exact wD.
    - exact wF.
    - exact wB.
    - exact wI.
    - exact wE.
    - exact wJ.
    - exact wN.
  Qed.

  (* [comment removed for export] *)
  Lemma refF_line : pk_chunks (a_cache (refF A) QB) = fetched.
  Proof. unfold refF. cbn [a_cache]. unfold reff_cache. rewrite Z.eqb_refl. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma refF_reg_other : forall c', c' <> QB -> a_reg (refF A) c' = a_reg A c'.
  Proof. intros c' NE. unfold refF. cbn [a_reg]. unfold ref_reg. destruct (Z.eqb_spec c' QB); [congruence| reflexivity]. Qed.
  Lemma refF_reg_QB : a_reg (refF A) QB = let Rg := a_reg A QB in RG (rg_mapped_user Rg) (rg_allocated_user Rg) (rg_mapped_fa Rg) (ref_rest fr 1).
  Proof. unfold refF. cbn [a_reg]. unfold ref_reg. rewrite Z.eqb_refl. reflexivity. Qed.
End WFrefF.
