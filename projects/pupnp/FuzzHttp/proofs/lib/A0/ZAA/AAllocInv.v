(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix F_prim_calloc2.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section INV.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).

  #[using="Type"] Lemma dr_inv_calloc : forall (X : pstate) (H H1 : word -> bool) (m m1 : mem) WB WC hrest lo q c,
    let P := fst X in let P' := fst (cache_alloc P c) in let v := snd (cache_alloc P c) in
    alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q -> 1 <= c <= 31 ->
    dr_inv AL E X H m WB WC hrest ->
    munch (prim_W AL lo q c (get_cls P c) (get_cls P' c)) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    poison_env E m1 -> thread_env L m1 -> shvis H1 m1 -> RPRIM AL P' m1 -> prim_ok P' ->
    held_ok P' ((c, v) :: map bpair WB ++ flat_map prim_of WC ++ hrest) ->
    dr_inv AL E (P', snd X) H1 m1 WB WC ((c, v) :: hrest).
  Proof.
    intros X H H1 m m1 WB WC hrest lo q c P P' v AO LOH CLO LQ Hc INV MU WM MI1 PE1 TE1 SV1 RPN POKN HOKN.
    destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP). fold P in WF0.
    pose proof RPN as (_ & _ & CLSN & _). assert (WFN : forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls P' c0)) by (intros c0 Hc0; exact (proj1 (CLSN c0 Hc0))).
    pose proof (WF0 c Hc) as (K1 & _ & _ & _ & K5 & _ & K7 & K8 & _).
    pose proof (WFN c Hc) as (D1 & _ & _ & _ & D5 & _ & D7 & D8 & _).
    assert (FW : Forall (atouch AL lo q (fst X) (snd X) [] []) (prim_W AL lo q c (get_cls P c) (get_cls P' c))).
    { apply atouch_prim_W; [exact Hc| fold P; lia| lia| lia| lia| lia| lia| fold P; lia]. }
    destruct HOK as [ND FH]. destruct HOKN as [NDN FHN].
    assert (PM : Permutation ((c, v) :: map bpair WB ++ flat_map prim_of WC ++ hrest) (map bpair WB ++ flat_map prim_of WC ++ (c, v) :: hrest)).
    { rewrite !app_assoc. apply Permutation_middle. }
    unfold dr_inv. cbn [fst snd].
    split; [exact RPN|]. split; [exact POKN|].
    split.
    { eapply (RSEC_frame_pzone AL (snd X) _ m m1 lo AO LOH CLO RS MU WM). apply pzone_prim_W; [exact AO| exact Hc| lia| lia| lia| lia| lia| lia]. }
    split; [exact MI1|]. split; [exact PE1|]. split; [exact TE1|]. split; [exact SV1|]. split; [exact WFS|].
    split.
    { apply Forall_forall. intros ch' Hin.
      eapply (qchunk_rep_other AL X m m1 lo q _ [] [] ch' AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU FW).
      - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
      - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
      - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
      - intros cv _ [].
      - intros sc _ []. }
    split.
    { apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'.
      destruct ch' as [[c' v'|sc] rz n]; unfold held_kind in *; cbn [qc_kind fst snd] in *; [| exact HK'].
      apply (proj1 (Forall_forall _ _) FHN). right. apply in_or_app. right. apply in_or_app. left.
      apply in_flat_map. eexists. split; [exact Hin|]. cbn [prim_of qc_kind]. left. reflexivity. }
    split.
    { split; [eapply Permutation_NoDup; [exact PM| exact NDN]| eapply Permutation_Forall; [exact PM| exact FHN]]. }
    split; [exact NDS|]. split; [exact BWF|].
    apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx BR]. exists nx.
    eapply (qbatch_rep_other AL X m m1 lo q _ [] [] b nx AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU FW BR).
    - apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb.
    - intros [].
  Qed.

  #[using="Type"] Lemma calloc_held_ok : forall (P : prim) (hs : list (Z * Z)) (c : Z),
    held_ok P hs -> 1 <= c <= 31 -> length (pr_cls P) = 32%nat ->
    (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls P c0)) -> refill_budget c (get_cls P c) ->
    held_ok (fst (cache_alloc P c)) ((c, snd (cache_alloc P c)) :: hs).
  Proof.
    intros P hs c HOK Hc LEN WF RB. pose proof (WF c Hc) as WFc.
    pose proof (max_count_range c Hc) as (MR & ME).
    assert (N0 : 0 < max_count c / 2) by (clear - MR; Z.div_mod_to_equations; lia).
    destruct (Z.eq_dec (p_cnt (get_cls P c)) 0) as [C0|CN].
    - rewrite (cache_alloc_refill P c LEN ltac:(clear - Hc; lia) C0 N0).
      assert (EK : get_cls (refill_prim P c) c = refill (get_cls P c) c) by (unfold refill_prim; apply get_cls_set_same; [exact LEN| clear - Hc; lia]).
      assert (AU : 0 <= p_au (get_cls P c) <= p_mu (get_cls P c) /\ p_au (get_cls P c) mod 16 = 0).
      { destruct WFc as (_ & _ & _ & _ & _ & _ & AU & _ & _ & AUM & _). split; [exact AU|].
        pose proof (class_size_mod16 c Hc) as CM. clear - AUM CM. Z.div_mod_to_equations. lia. }
      apply cache_alloc_held_ok.
      + apply (held_ok_mono P _ hs HOK). intros c1 v0 Hin.
        destruct HOK as [_ HF]. pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hc1 & _). cbn [fst] in Hc1.
        destruct (Z.eq_dec c1 c) as [->|NE].
        * rewrite EK. split; [apply refill_au; [exact Hc| exact (proj2 (proj1 AU))]|].
          intros X. apply (refill_free (get_cls P c) c v0 Hc (proj2 AU) X).
        * assert (EO : get_cls (refill_prim P c) c1 = get_cls P c1).
          { unfold refill_prim, get_cls. cbn [pr_cls]. apply nth_set_nth_other. clear - NE Hc Hc1. lia. }
          rewrite EO. split; [lia| intros X; left; exact X].
      + exact Hc.
      + unfold refill_prim. cbn [pr_cls]. rewrite set_nth_length. exact LEN.
      + rewrite EK. exact (APrimRefill.refill_wf c (get_cls P c) Hc WFc (proj1 RB) (proj2 RB) C0).
      + rewrite EK. unfold refill, get_from_allocator. cbn [p_cnt]. exact N0.
    - apply cache_alloc_held_ok; [exact HOK| exact Hc| exact LEN| exact WFc|].
      destruct WFc as (_ & CR & _). clear - CR CN. lia.
  Qed.
End INV.
