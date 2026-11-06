(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_ameta_iface MallocInv_vmfree
  MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_nttop MallocInv_freetop MallocIfaceX
  MallocInv_ametax_iface MallocSureLedger MallocSureInv MallocSureGrow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeFastX.
  Variables (A : astate) (s : mstate).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis HWIN : WIN s.
  Hypothesis HRO : rodata_clear (ms_mem s).
  Hypothesis HNL : rdn ml_segs (ms_mem s) A_NEED_LOCKS 1 = Some [Z_to_bv 8 0].
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i off n : Z) (p : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some (SLive off n).
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hp : p = slot_start mt i + 16 * off.

  Let S := mt_stride mt.
  Let Mb := mt_mem mt.
  Let p0 := Mb + 16 + i * S.
  Let e := p0 + S - 4.
  Let rsv := e - p - n.

  (* [comment removed for export] *)
  Let fr' := mt_freed mt + 2 ^ i.
  Let slots' := list_set slots (Z.to_nat i) SIdle.
  Let L' := lupd (a_live A) p None.
  Let A' := set_live (ameta_upd A ma (MT (gu_f mt (mt_avail mt) fr') (RGroup aib slots'))) L'.

  Let Wh3 := FCT (p - 3) 1 (2^64 - 1).
  Let Wh2 := FCT (p - 2) 2 0.
  Let Wfr := FCT (ma + 28) 4 (sx32 fr').

  (* [comment removed for export] *)
  Variable pw : word.
  Hypothesis Hpw : bv_unsigned pw = p.

  Hypothesis Hxm0 : a_xmaps A = [].

  Lemma free_fast_postX : forall m3,
    VMok A (ms_vm s) -> (forall j, 0 <= j < 8 -> ms_mem s (Z_to_bv 64 (LOCKA + j)) = None) ->
    Coh A (ms_mem s) (ms_vm s) -> ACT48 A ->
    RepW A (ms_mem s) [Wfr; Wh2; Wh3] m3 ->
    mt_freed mt <> 0 ->
    free_postX A pw s tt (upd s m3 (ms_vm s)).
  Proof using A' HR HW Hi Hi0 Hma Hp Hpw Hr Hxm0 MLok rsv. pu_keep (A', HR, HW, Hi, Hi0, Hma, Hp, Hpw, Hr, Hxm0, MLok, rsv).
    intros m3 HV HL HKc HA48 RW3 Eb1.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16. fold S in HS16.
    fold S in Hfit, Hce. fold Mb in Hal16, Hmem, Hfit, Hce, Hpg.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    assert (HiS : 0 <= i * S /\ i * S + S <= mt_cnt mt * S) by (subst S; lnia).
    pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hofit & _). fold S in Hofit.
    assert (Ep : p = p0 + 16 * off) by (rewrite Hp; reflexivity).
    pose proof (grp_heap A ma mt aib slots HW Hma Hr) as (G1 & G2 & G3). unfold gext_lo, gext_hi in G1, G2, G3. fold Mb S in G1, G2, G3.
    ceil.
    destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg & kk & Hpga & Hkk & Ema).
    destruct (wf_areas_al A HW pg Hpga) as [Hpgal Hpgh]. unfold heap_range in Hpgh. ceil.
    assert (Hbit : Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = false).
    { destruct (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i) eqn:E; [| reflexivity].
      exfalso. pose proof (proj1 (Hidle i (SLive off n) Hi Hi0) E). discriminate. }
    pose proof (free_fast_wf A HW ma mt aib slots i off n p Hma Hr Hi Hi0 Hp Hbit Eb1) as HW'. pose proof (free_fast_rep A s HW ma mt aib slots i off n p Hma Hr Hi Hi0 Hp m3 Hbit RW3) as HR'.
    fold fr' in HW', HR'. fold slots' in HW', HR'. fold L' in HW', HR'. fold A' in HW', HR'.
    (* [comment removed for export] *)
    assert (CLS : forall x, (ma + 28 <= x < ma + 32) \/ (p - 3 <= x < p) \/ wfree [Wfr; Wh2; Wh3] x).
    { intros x.
      assert (DQrng : (ma + 28) <= x < (ma + 32) \/ (p - 3) <= x < p \/
                     (~ ((ma + 28) <= x < (ma + 32)) /\ ~ ((p - 3) <= x < p))) by lia.
      destruct DQrng as [DQrng | [DQrng | DQrng]];
        [ left; llia
        | right; left; llia |].
       
      right; right; repeat apply wfree_cons; try apply wfree_nil; cbn; llia. }
    assert (OWN1 : forall a : word, ma + 28 <= bv_unsigned a < ma + 32 -> mowned A a).
    { intros a Ha. right. left. exists pg. split; [exact Hpga|]. rewrite Ema in Ha. unfold meta_addr in Ha. llia. }
    assert (OWN2 : forall a : word, p - 3 <= bv_unsigned a < p -> mowned A a).
    { intros a Ha. right. apply (grp_dom A ma mt aib slots _ HW Hma Hr). unfold gext_lo, gext_hi. fold Mb S. rewrite Ep in Ha. unfold p0 in Ha. llia. }
    (* [comment removed for export] *)
    destruct (slot_hdr_facts A HW ma mt aib slots i (SLive off n) off p Hma Hr Hi Hi0 ltac:(left; exists n; reflexivity) Hp) as (c & Hc & F4 & F3 & F2).
    assert (Ffr : has A (FCT (ma + 28) 4 (mt_freed mt))) by (right; right; left; exists ma, mt, FFreed; auto).
    assert (CL : forall (q : word) k x, mlive A q = Some k -> bv_unsigned q <= x < bv_unsigned q + k -> wfree [Wfr; Wh2; Wh3] x).
    { intros q k x Hq Hx. unfold mlive in Hq. apply (proj1 (wf_live_map A HW _ _)) in Hq.
      destruct Hq as (y & mty & aiby & sly & j & o & Hy & Hry & Hj0 & Hj & Eq).
      pose proof (live_clear A HW y mty aiby sly j o k Hy Hry Hj0 Hj) as LC. cbn in LC. rewrite <- Eq in LC.
      pose proof (LC _ Ffr) as X1. pose proof (LC _ F3) as X2. pose proof (LC _ F2) as X3. cbn in X1, X2, X3.
      repeat apply wfree_cons; try apply wfree_nil; cbn; llia. }
    exists A'. split; [cbn; exact Hxm0|]. split.
    { constructor; [exact HW' | exact HR' | apply (VMok_grp_upd A ma mt aib slots Hma Hr); exact HV | | | exact HA48].
      - intros j Hj. cbn. rewrite (rw_frame A _ _ m3 RW3); [apply HL; exact Hj|].
        destruct (CLS (bv_unsigned (Z_to_bv 64 (LOCKA + j)))) as [X | [X | X]]; [| | exact X]; exfalso; unfold LOCKA in X; rewrite uZ in X by llia; rewrite ?Ema in X; unfold meta_addr in X; rewrite ?Ep in X; unfold p0 in X; llia.
      - (* [comment removed for export] *)
        cbn. apply (coh_restate A A' m3 (ms_vm s)).
        + apply (coh_mem A (ms_mem s) m3 (ms_vm s) HW HV HKc). intros a Ha Hr' Hi'.
          destruct (CLS (bv_unsigned a)) as [X | [X | X]].
          * right. destruct (OWN1 a X) as [G | D]; [exfalso; unfold LOCKA, CTX_END in G; llia | exact D].
          * right. destruct (OWN2 a X) as [G | D]; [exfalso; unfold LOCKA, CTX_END in G; llia | exact D].
          * left. rewrite <- (rw_frame A _ _ m3 RW3 a X). exact Ha.
        + reflexivity.
        + reflexivity.
        + intros sc Hsc2. reflexivity.
        + intros x mt' Hx. unfold A' in Hx. cbn in Hx. unfold aupd in Hx.
          destruct (Z.eq_dec x ma) as [-> | Hne].
          * injection Hx as <-. exists mt. split; [exact Hma|]. cbn. split; intros HH; discriminate HH.
          * exists mt'. split; [exact Hx|]. split; intros HH; exact HH.
        + intros sc x Hsc2. unfold meta_usage, A'. cbn. unfold aupd.
          destruct (Z.eq_dec x ma) as [-> | Hne]; [| reflexivity].
          rewrite Hma, Hr. cbn. reflexivity. }
    split; [reflexivity|]. split; [reflexivity|].
    assert (Elive : forall q, mlive A' q = if Z.eq_dec (bv_unsigned q) p then None else mlive A q).
    { intros q. reflexivity. }
    split. { rewrite Elive, Hpw. destruct (Z.eq_dec p p); [reflexivity | contradiction]. }
    split. { intros q Hq. rewrite Elive. destruct (Z.eq_dec (bv_unsigned q) p) as [E|NE]; [| reflexivity].
             exfalso. apply Hq. apply bv_eq. rewrite E, Hpw. reflexivity. }
    split.
    { intros a Hown Hown' Herr. cbn. apply (rw_frame A _ _ m3 RW3).
      destruct (CLS (bv_unsigned a)) as [X | [X | X]]; [exfalso; exact (Hown (OWN1 a X)) | exfalso; exact (Hown (OWN2 a X)) | exact X]. }
    split.
    { intros q k j Hq Hj. cbn. apply (rw_frame A _ _ m3 RW3).
      rewrite Elive in Hq. destruct (Z.eq_dec (bv_unsigned q) p); [discriminate|].
      pose proof (m_live_hull A (ms_mem s) (ms_vm s) q k ltac:(constructor; assumption) Hq) as (Hk & _ & Hce' & _).
      pose proof (round16_ge k). ceil. pose proof (u64_range q).
      apply (CL q k); [exact Hq|]. unfold at_. rewrite uZ by llia. llia. }
    split. { intros a Hm. right. cbn. apply (rw_mapped A _ _ m3 RW3). exact Hm. }
    split; [repeat split; reflexivity |]. split; [cbn; llia |].
    (* [comment removed for export] *)
    apply sgrow_same; reflexivity.
  Qed.
End FreeFastX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeSlowX.
  Variables (A : astate) (s : mstate) (sp0 : word) (argv envp : list (list byte)).
  Hypothesis HE : call_env A s sp0 argv envp.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i off n : Z) (pw : word).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some (SLive off n).
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hp : u pw = slot_start mt i + 16 * off.
  Hypothesis Hxm0 : a_xmaps A = [].

  Let p := u pw.
  Let slotsT := list_set slots (Z.to_nat i) STaken.
  Let L' := lupd (a_live A) p None.
  Let A1 := slot_set A ma i STaken L'.
  Let mt1 := MT (mt_f mt) (RGroup aib slotsT).
  Let Wh3 := FCT (p - 3) 1 (2^64 - 1).
  Let Wh2 := FCT (p - 2) 2 0.

  Lemma EW : WF A. Proof using HE. pu_keep (HE). exact (mi_wf _ _ _ (ce_inv _ _ _ _ _ HE)). Qed.
  Lemma ER : Rep A (ms_mem s). Proof using HE. pu_keep (HE). exact (mi_rep _ _ _ (ce_inv _ _ _ _ _ HE)). Qed.
  Lemma EV : VMok A (ms_vm s). Proof using HE. pu_keep (HE). exact (mi_vm _ _ _ (ce_inv _ _ _ _ _ HE)). Qed.
  Lemma EC : Coh A (ms_mem s) (ms_vm s). Proof using HE. pu_keep (HE). exact (mi_coh _ _ _ (ce_inv _ _ _ _ _ HE)). Qed.
  Lemma E48 : ACT48 A. Proof using HE. pu_keep (HE). exact (mi_act _ _ _ (ce_inv _ _ _ _ _ HE)). Qed.
  Lemma EWIN : WIN s. Proof using HE. pu_keep (HE). exact (ce_win _ _ _ _ _ HE). Qed.
  Lemma EENV : EnvOK sp0 argv envp s. Proof using HE. pu_keep (HE). exact (ce_env _ _ _ _ _ HE). Qed.

  Lemma Hilt : (Z.to_nat i < length slots)%nat.
  Proof using Hi. pu_keep (Hi). apply (proj1 (nth_error_Some slots (Z.to_nat i))). rewrite Hi. discriminate. Qed.

  Lemma Hi1 : nth_error slotsT (Z.to_nat i) = Some STaken.
  Proof using Hi. pu_keep (Hi). unfold slotsT. apply list_set_nth_same. exact Hilt. Qed.

  Lemma A1_ma : a_meta A1 ma = Some mt1.
  Proof using Hma Hr L' slotsT. pu_keep (Hma, Hr, L', slotsT). unfold A1. exact (MallocInv_wf.A'_meta_same A ma mt aib slots i STaken Hma Hr L'). Qed.
  Lemma A1_other : forall x, x <> ma -> a_meta A1 x = a_meta A x.
  Proof using Hma Hr L' i. pu_keep (Hma, Hr, L', i). intros x Hx. unfold A1. exact (MallocInv_wf.A'_meta_other A ma mt aib slots i STaken Hma Hr L' x Hx). Qed.
  Lemma A1_live : a_live A1 = L'.
  Proof using Hma Hr i p. pu_keep (Hma, Hr, i, p). unfold A1. exact (MallocInv_wf.A'_live A ma mt aib slots i STaken Hma Hr L'). Qed.
  Lemma A1_eq : A1 = set_live (ameta_upd A ma mt1) L'.
  Proof using Hma Hr p slotsT. pu_keep (Hma, Hr, p, slotsT). unfold A1. exact (MallocInv_wf.A'_eq A ma mt aib slots i STaken Hma Hr L'). Qed.

  Lemma WF1 : WF A1.
  Proof using HE Hi Hi0 Hma Hp Hr L'. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr, L').
    unfold A1. apply (WF_slot_set A EW ma mt aib slots i (SLive off n) STaken Hma Hr Hi Hi0).
    - right. exists off, n. reflexivity.
    - left. reflexivity.
    - intros o k H. discriminate H.
    - intros q k. unfold L', lupd. split.
      + destruct (Z.eq_dec q p) as [-> | Hne]; [discriminate|]. intros Hq. right. split; [exact Hq|].
        intros o k' E. injection E as <- <-. rewrite <- Hp. exact Hne.
      + intros [(o & E & _) | (Hq & Hne)]; [discriminate E|].
        destruct (Z.eq_dec q p) as [-> | Hne']; [| exact Hq]. exfalso. apply (Hne off n eq_refl). unfold p. rewrite Hp. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma AVOID : forall f x, has A1 f -> f_a f <= x < f_a f + f_n f -> ~ (p - 3 <= x < p).
  Proof using HE Hi Hi0 Hma Hp Hr L' MLok mt1. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr, L', MLok, mt1).
    intros f x Hf Hx Hpx.
    pose proof (wf_live A EW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hfit & _).
    pose proof (span_clear A1 WF1 ma mt1 aib slotsT i STaken A1_ma eq_refl Hi1 Hi0 (or_intror eq_refl) f Hf) as SC.
    change (slot_start mt1 i) with (slot_start mt i) in SC. change (slot_end mt1 i) with (slot_end mt i) in SC.
    unfold slot_end, slot_end_g in SC. unfold slot_start, slot_start_g in Hp, SC. unfold p in *. lia.
  Qed.

  Section AfterHdr.
    Variable m2 : word -> option byte.
    Hypothesis RW2 : RepW A (ms_mem s) [Wh2; Wh3] m2.
    Let s2 := upd s m2 (ms_vm s).

    Lemma HR1 : Rep A1 m2.
    Proof using HE Hi Hi0 Hma Hp Hr L' MLok RW2 mt1. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr, L', MLok, RW2, mt1).
      apply (repw_commit2 A A1 (ms_mem s) [Wh2; Wh3] m2 WF1 RW2).
      - intros f Hf. left. unfold A1 in Hf.
        destruct (MallocInv_wf.has_slot_set A ma mt aib slots i STaken Hma Hr Hi0 L' f Hf) as [H | H]; [exact H|].
        right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right. exists (Z.to_nat i), (SLive off n).
        split; [exact Hi|]. rewrite Z2Nat.id by exact Hi0. unfold slot_fields, slot_fields_g in H |- *. apply in_app_iff. left.
        apply in_app_iff in H. destruct H as [H | H]; [exact H | destruct H].
      - intros x b Hw. right; right. intros f Hf Hfx.
        destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw).
        apply (AVOID f x Hf Hfx). destruct Hin as [<- | [<- | []]]; unfold Wh2, Wh3 in Hxw; cbn [f_a f_n] in Hxw; lia.
      - intros x Hx. unfold A1 in Hx. exact (MallocInv_wf.dom_slot_set A ma mt aib slots i STaken Hma Hr L' x Hx).
    Qed.

    (* [comment removed for export] *)
    Lemma hdr_facts : exists c, has A (FCT (p - 3) 1 (i + 32 * c)) /\ has A (FCT (p - 2) 2 ((p - mt_mem mt - 16) / 16)).
    Proof using HE Hi Hi0 Hma Hp Hr. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr).
      destruct (slot_hdr_facts A EW ma mt aib slots i (SLive off n) off p Hma Hr Hi Hi0 ltac:(left; exists n; reflexivity) Hp) as (c & _ & _ & F3 & F2).
      exists c. split; [exact F3 | exact F2].
    Qed.

    (* [comment removed for export] *)
    Lemma live_avoid : forall q k x, a_live A q = Some k -> q <= x < q + k -> ~ (p - 3 <= x < p).
    Proof using HE Hi Hi0 Hma Hp Hr MLok. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr, MLok).
      intros q k x Hq Hx. apply (proj1 (wf_live_map A EW _ _)) in Hq.
      destruct Hq as (y & mty & aiby & sly & j & o & Hy & Hry & Hj0 & Hj & ->).
      pose proof (live_clear A EW y mty aiby sly j o k Hy Hry Hj0 Hj) as LC. cbn in LC.
      destruct hdr_facts as (c & F3 & F2). pose proof (LC _ F3) as X3. pose proof (LC _ F2) as X2. cbn [f_a f_n] in X3, X2. lia.
    Qed.

    Lemma WO : writes_ok A [Wh2; Wh3].
    Proof using HE Hi Hi0 Hma Hp Hr MLok p. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr, MLok, p).
      intros w x Hin Hx.
      assert (Hpx : p - 3 <= x < p) by (destruct Hin as [<- | [<- | []]]; unfold Wh2, Wh3 in Hx; cbn [f_a f_n] in Hx; lia).
      destruct (live_geom A EW ma mt aib slots i off n Hma Hr Hi0 Hi) as (q & _ & Hn & Ho & _ & _ & _ & G1 & G2 & G3 & G4 & _).
      split.
      - left. apply (grp_dom A ma mt aib slots x EW Hma Hr). pose proof (round16_ge n). unfold p in *. rewrite Hp in Hpx. lia.
      - intros q' k Hq Hqx. exact (live_avoid q' k x Hq Hqx Hpx).
    Qed.

    Variable cb : list byte.
    Hypothesis Hcb : GRD cb (ms_mem s).

    Lemma IS0 : IS sp0 argv envp cb A s.
    Proof using HE Hcb. pu_keep (HE, Hcb). constructor; [exact EW | exact ER | exact (covm_of_coh _ _ _ EC) | exact EWIN | exact EENV | exact Hcb]. Qed.

    Lemma IS1 : IS sp0 argv envp cb A1 s2.
    Proof using HE Hcb Hi Hi0 Hma Hp Hr L' MLok RW2 mt1. pu_keep (HE, Hcb, Hi, Hi0, Hma, Hp, Hr, L', MLok, RW2, mt1). exact (IS_commit sp0 argv envp cb A A1 s [Wh2; Wh3] m2 IS0 RW2 WO WF1 HR1). Qed.

    Lemma A1_meta_inv : forall x mtx, a_meta A1 x = Some mtx -> (x = ma /\ mtx = mt1) \/ (x <> ma /\ a_meta A x = Some mtx).
    Proof using Hma Hr L' slotsT. pu_keep (Hma, Hr, L', slotsT).
      intros x mtx Hx. destruct (Z.eq_dec x ma) as [-> | Hne].
      - left. rewrite A1_ma in Hx. injection Hx as <-. auto.
      - right. rewrite (A1_other x Hne) in Hx. auto.
    Qed.

    Lemma V1 : VMok A1 (ms_vm s).
    Proof using HE Hma Hr L' mt1. pu_keep (HE, Hma, Hr, L', mt1).
      apply (VMok_transfer A A1 (ms_vm s) EV); try (rewrite A1_eq; reflexivity).
      - intros x mtx aibx slx Hx Hrx Hml. destruct (A1_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')].
        + exists mt, aib, slots. cbn in Hrx. auto.
        + exists mtx, aibx, slx. auto.
      - intros x mt0 aib0 sl0 Hx0 Hr0 Hml. destruct (Z.eq_dec x ma) as [-> | Hne].
        + rewrite Hma in Hx0. injection Hx0 as <-. exists mt1, aib, slotsT. split; [exact A1_ma|]. split; [reflexivity|]. split; reflexivity.
        + exists mt0, aib0, sl0. rewrite (A1_other x Hne). auto.
    Qed.

    Lemma II1 : II sp0 argv envp cb [] A1 s2.
    Proof using HE Hcb Hi Hi0 Hma Hp Hr L' MLok RW2 mt1. pu_keep (HE, Hcb, Hi, Hi0, Hma, Hp, Hr, L', MLok, RW2, mt1).
      pose proof EC as [_ Cnd Cus Cav].
      apply II_intro; [exact IS1 | exact V1 | | |].
      - apply (AvOK_transfer A A1 Cav); try (rewrite A1_eq; reflexivity).
        intros x mt' Hx Hrl. destruct (A1_meta_inv x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
      - apply (UsOK_transfer A A1 Cus); [rewrite A1_eq; reflexivity | intros; rewrite A1_eq; reflexivity |].
        intros sc x. unfold meta_usage. destruct (Z.eq_dec x ma) as [-> | Hne]; [rewrite A1_ma, Hma, Hr; reflexivity | rewrite (A1_other x Hne); reflexivity].
      - intros x. split; [| intros []]. intros (mt' & Hx & Hrl).
        destruct (A1_meta_inv x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exact (Cnd x mt' Hx' Hrl)].
    Qed.

    (* [comment removed for export] *)
    Theorem free_slow_body :
      tsafe ((mi <- m_nontrivial_free FREE_FUEL (Z_to_bv 64 ma) (Z_to_bv 64 i) ;;
              (let '(base, len) := mi in
               m_unlock ;;
               (if is0 len then mret tt
                else e0 <- m_lw A_ERRNO ;; r <- sys_munmap base len ;; m_sw A_ERRNO e0))) s2) (free_postX A pw s).
    Proof using HE Hcb Hi Hi0 Hma Hp Hr Hxm0 MLok RW2 mt1. pu_keep (HE, Hcb, Hi, Hi0, Hma, Hp, Hr, Hxm0, MLok, RW2, mt1).
      pose proof EW as HW. pose proof layout_nums as LN.
      assert (H48 : ACT48 A1) by (intros c Hc; rewrite A1_eq; cbn; exact (E48 c Hc)).
      eapply ts_bind_split.
      { apply (ntfree_ok sp0 argv envp cb FREE_FUEL [] A1 s2 ma mt1 aib slotsT i II1 H48 A1_ma eq_refl Hi1 Hi0).
        pose proof (nfuel_le A1 WF1 ma mt1 aib slotsT A1_ma eq_refl). unfold FREE_FUEL. lia. }
      intros [base len] s3 (A3 & HII3 & HF3 & HR3 & HRes3). cbv beta iota.
      pose proof (ii_is HII3) as HIS3. pose proof (is_wf _ _ _ _ _ _ HIS3) as HW3. pose proof (is_rep _ _ _ _ _ _ HIS3) as HRp3.
      pose proof (is_win _ _ _ _ _ _ HIS3) as HWIN3. pose proof (is_env _ _ _ _ _ _ HIS3) as HE3. pose proof (ii_vm HII3) as HV3.
      pose proof (nf_vm _ _ _ HF3) as Hvm3. unfold s2 in Hvm3. cbn [ms_vm upd] in Hvm3. rewrite Hvm3 in HV3.
      pose proof (nf_lo _ _ _ HF3) as Hlo3. pose proof (nf_hi _ _ _ HF3) as Hhi3. unfold s2 in Hlo3, Hhi3. cbn [ms_lo ms_hi upd] in Hlo3, Hhi3.
      (* [comment removed for export] *)
      assert (SP3 : spare A <= spare A3).
      { destruct (nr_fl _ _ _ _ _ HR3) as [l3 Fl3]. unfold spare. rewrite (nr_ctx _ _ _ _ _ HR3 KAmc I), Fl3, length_app, A1_eq.
        cbn [a_ctx a_freelist set_live ameta_upd set_meta]. lia. }
      destruct HR3 as [L3 Ar3 P3 B3 C3 Q3 G3 D3]. rewrite A1_live in L3.
      (* [comment removed for export] *)
      assert (OWN1A : forall x, owned_of A1 x -> owned_of A x).
      { intros x [Hx | Hx]; [left; exact Hx | right; unfold A1 in Hx; exact (MallocInv_wf.dom_slot_set A ma mt aib slots i STaken Hma Hr L' x Hx)]. }
      assert (OWN31 : forall x, owned_of A3 x -> owned_of A1 x) by (intros x [Hx | Hx]; [left; exact Hx | right; exact (D3 x Hx)]).
      assert (MEM23 : forall a : word, ~ owned_of A1 (u a) -> ms_mem s3 a = m2 a).
      { intros a Ha. rewrite (nf_mem _ _ _ HF3 a Ha). reflexivity. }
      assert (MEM12 : forall a : word, ~ (p - 3 <= u a < p) -> m2 a = ms_mem s a).
      { intros a Ha. apply (rw_frame A _ _ m2 RW2). unfold Wh2, Wh3. repeat apply wfree_cons; try apply wfree_nil; cbn [f_a f_n]; lia. }
      destruct (live_geom A HW ma mt aib slots i off n Hma Hr Hi0 Hi) as (q16 & _ & Hn & Ho & _ & _ & _ & Gg1 & Gg2 & Gg3 & Gg4 & _).
      assert (OWNp : forall a : word, p - 3 <= u a < p -> owned_of A (u a)).
      { intros a Ha. right. apply (grp_dom A ma mt aib slots _ HW Hma Hr). pose proof (round16_ge n). unfold p in *. rewrite Hp in Ha. lia. }
      assert (LIVE3 : forall (q : word) k j, a_live A3 (u q) = Some k -> 0 <= j < k -> ms_mem s3 (at_ q j) = ms_mem s (at_ q j) /\ dom A3 (u q + j)).
      { intros q k j Hq Hj. rewrite L3 in Hq. unfold L', lupd in Hq. destruct (Z.eq_dec (u q) p) as [E | NE]; [discriminate|].
        pose proof (live_dom A3 (u q) k (u q + j) HW3 ltac:(rewrite L3; unfold L', lupd; destruct (Z.eq_dec (u q) p); [contradiction | exact Hq]) ltac:(lia)) as Hd.
        pose proof (dom_mzone A3 _ HW3 Hd) as Hz. unfold mzone in Hz. ceil.
        assert (Ea : u (at_ q j) = u q + j) by (unfold at_; rewrite uZ by lia; reflexivity).
        split; [| exact Hd].
        rewrite (nf_live _ _ _ HF3 (u q) k (at_ q j) ltac:(rewrite A1_live; unfold L', lupd; destruct (Z.eq_dec (u q) p); [contradiction | exact Hq]) ltac:(rewrite Ea; lia)).
        unfold s2. cbn [ms_mem upd]. apply MEM12. rewrite Ea. exact (live_avoid (u q) k (u q + j) Hq ltac:(lia)). }
      assert (MAP3 : forall a : word, ms_mem s a <> None -> ms_mem s3 a <> None).
      { intros a Ha. apply (nf_mapped _ _ _ HF3). unfold s2. cbn [ms_mem upd]. exact (rw_mapped A _ _ m2 RW2 a Ha). }
      assert (ELIVE : forall q : word, mlive A3 q = if Z.eq_dec (u q) p then None else mlive A q).
      { intros q. unfold mlive. rewrite L3. reflexivity. }
      assert (H48' : ACT48 A3) by (intros c Hc; rewrite (Q3 c Hc); exact (H48 c Hc)).
      apply ts_unlock; [exact (eo_statics _ _ _ _ HE3) | exact HWIN3 |].
      destruct HRes3 as [(E & X3 & Dk3) | (B & L & E & HL & HBal & HLm & Hhr & X3 & Hin & Diff & Nod & Hav & WFx & VMx)].
      - (* [comment removed for export] *)
        injection E as -> ->. change (is0 w0) with true. cbn iota. apply ts_ret.
        exists A3. split.
        { rewrite X3, A1_eq. cbn [a_xmaps set_live ameta_upd set_meta]. exact Hxm0. }
        split.
        { constructor; [exact HW3 | exact HRp3 | rewrite Hvm3; exact HV3 | exact (eo_lock _ _ _ _ HE3) | | exact H48'].
          constructor; [exact (is_cov _ _ _ _ _ _ HIS3) | | exact (ii_us HII3) | exact (ii_av HII3)].
          intros x mtx Hx Hrl. exact (proj1 (ii_dd HII3 x) (ex_intro _ mtx (conj Hx Hrl))). }
        split; [exact Hlo3|]. split; [exact Hhi3|].
        split. { rewrite ELIVE. destruct (Z.eq_dec (u pw) p); [reflexivity | contradiction]. }
        split. { intros q Hq. rewrite ELIVE. destruct (Z.eq_dec (u q) p) as [E | NE]; [| reflexivity]. exfalso. apply Hq. apply bv_eq. exact E. }
        split. { intros a Ho1 Ho3 Herr. rewrite (MEM23 a ltac:(intros HoA; exact (Ho1 (OWN1A _ HoA)))). apply MEM12. intros Ha. exact (Ho1 (OWNp a Ha)). }
        split. { intros q k j Hq Hj. exact (proj1 (LIVE3 q k j Hq Hj)). }
        split. { intros a Ha. right. exact (MAP3 a Ha). }
        rewrite Hvm3. split; [repeat split; reflexivity |]. split; [lia |].
        (* [comment removed for export] *)
        apply sgrow_same; [reflexivity | rewrite Ar3, A1_eq; reflexivity | exact SP3].
      - (* [comment removed for export] *)
        injection E as -> ->. unfold heap_range in Hhr. ceil.
        rewrite is0_Z by lia. replace (L =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite A_ERRNO_eq.
        destruct (rdn_img (ms_mem s3) 4%nat ERRNO) as (bs & Hbs & Hbl); [lia | cbn; lia |].
        eapply ts_lw; [apply acc_ok_heap; [exact HWIN3 | lia | lia | lia] | exact Hbs |].
        assert (HuB : u (Z_to_bv 64 B) = B) by (apply uZ; lia). assert (HuL : u (Z_to_bv 64 L) = L) by (apply uZ; lia).
        assert (Hpr : page_round_up (Z_to_bv 64 L) = Z_to_bv 64 L).
        { unfold page_round_up. rewrite HuL, page_round_up_Z_aligned by (unfold page_size; lia). reflexivity. }
        eapply ts_sys_munmap; [rewrite HuB; exact HBal | rewrite HuL; lia | | |].
        { rewrite HuB, HuL, page_round_up_Z_aligned by (unfold page_size; lia). rewrite (vm_top A3 _ (ltac:(rewrite <- Hvm3 in HV3; exact HV3))). lia. }
        { rewrite Hpr. apply in_map_has. rewrite (nf_vm _ _ _ HF3). exact Hin. }
        rewrite Hpr. cbn [ms_mem ms_vm upd].
        (* [comment removed for export] *)
        unfold m_sw, m_st. change (Z.of_nat 4) with 4.
        lazymatch goal with |- tsafe (if acc_ok ?s4 _ _ && _ && _ then _ else _) _ =>
          rewrite (acc_ok_heap s4 ERRNO 4); [| exact HWIN3 | lia | lia | lia] end.
        rewrite <- A_ERRNO_eq at 1. rewrite st_zone_errno. rewrite store_ok_rwseg by (cbn; lia). cbn [andb tsafe ms_mem ms_vm upd].
        set (m4 := unfill (Z_to_bv 64 B) (Z_to_bv 64 L) (ms_mem s3)).
        set (m5 := wbytes m4 (Z_to_bv 64 ERRNO) (word_to_le_bytes 4 (v_lw (le_val bs)))).
        set (h5 := vm_munmap (Z_to_bv 64 B) (Z_to_bv 64 L) (ms_vm s3)).
        set (A5 := set_xmaps A3 (a_xmaps A1)).
        assert (Hlen4 : length (word_to_le_bytes 4 (v_lw (le_val bs))) = 4%nat) by (unfold word_to_le_bytes; apply length_Z_to_le_bytes).
        assert (M5out : forall a : word, ~ (ERRNO <= u a < ERRNO + 4) -> m5 a = m4 a).
        { intros a Ha. unfold m5. apply wbytes_other_Z; rewrite ?Hlen4; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        assert (M4out : forall a : word, ~ (B <= u a < B + L) -> m4 a = ms_mem s3 a).
        { intros a Ha. unfold m4, unfill. rewrite HuB, HuL.
          destruct (Z.leb_spec B (u a)), (Z.ltb_spec (u a) (B + L)); cbn [andb]; try reflexivity. exfalso. lia. }
        assert (M4in : forall a : word, B <= u a < B + L -> m4 a = None).
        { intros a Ha. unfold m4, unfill. rewrite HuB, HuL. destruct (Z.leb_spec B (u a)), (Z.ltb_spec (u a) (B + L)); cbn [andb]; try reflexivity; exfalso; lia. }
        assert (DOMB : forall x, B <= x < B + L -> owned_of A x).
        { intros x Hx. apply OWN1A. right. apply (proj2 (Diff x)). right. exact Hx. }
        exists A5. split.
        { unfold A5. cbn [a_xmaps set_xmaps]. rewrite A1_eq. cbn [a_xmaps set_live ameta_upd set_meta]. exact Hxm0. }
        split.
        { constructor.
          - exact WFx.
          - (* [comment removed for export] *)
            assert (HR4 : Rep A5 m4).
            { unfold m4. apply (rep_unfill A3 A5 (ms_mem s3) B L HRp3); [lia | lia | lia | | | |].
              - intros x b Hf. split; [| exact Hf]. destruct Hf as (f & Hf & [Hfx _]).
                pose proof (Hav f x Hf Hfx). lia.
              - intros x Hd. split; [| exact Hd]. pose proof (Nod x). tauto || (destruct (Z.lt_ge_cases x B); [lia|]; destruct (Z.lt_ge_cases x (B + L)); [exfalso; exact (Nod x ltac:(lia) Hd) | lia]).
              - intros x b Hf. exact (facts_addr64 A3 HW3 x b Hf).
              - intros x Hd. pose proof (dom_mzone A3 x HW3 Hd) as Hz. unfold mzone in Hz. lia. }
            unfold m5. apply (rep_write_clear A5 m4 ERRNO _ HR4); [lia | rewrite Hlen4; cbn; lia | | intros x b Hf; exact (facts_addr64 A3 HW3 x b Hf)].
            intros f Hf. rewrite Hlen4. change (Z.of_nat 4) with 4.
            destruct (has_addr A3 HW3 f Hf) as (Hfn & Hf1 & Hf2 & [(C1 & C2 & _) | [(Hh & _) | Hh]]); [lia | unfold heap_range in Hh; lia | unfold heap_range in Hh; lia].
          - (* [comment removed for export] *) unfold A5, h5. rewrite (nf_vm _ _ _ HF3). exact VMx.
          - (* [comment removed for export] *) intros j Hj. rewrite M5out by (rewrite uZ by lia; lia).
            destruct (Z.lt_ge_cases (LOCKA + j) B) as [Hb | Hb]; [rewrite M4out by (rewrite uZ by lia; lia); exact (eo_lock _ _ _ _ HE3 j Hj)|].
            destruct (Z.lt_ge_cases (LOCKA + j) (B + L)) as [Hb' | Hb']; [rewrite M4in by (rewrite uZ by lia; lia); reflexivity|].
            rewrite M4out by (rewrite uZ by lia; lia). exact (eo_lock _ _ _ _ HE3 j Hj).
          - (* [comment removed for export] *) constructor.
            3:{ exact (UsOK_transfer A3 A5 (ii_us HII3) eq_refl (fun _ _ => eq_refl) (fun _ _ => eq_refl)). }
            3:{ exact (AvOK_transfer A3 A5 (ii_av HII3) eq_refl eq_refl (fun x mt' Hx Hr' => ex_intro _ mt' (conj Hx Hr'))). }
            + intros a Ha Hra Hia. unfold h5. cbn [vm_maps vm_munmap].
              rewrite M5out in Ha by lia.
              assert (HaB : ~ (B <= u a < B + L)) by (intros HaB; rewrite (M4in a HaB) in Ha; exact (Ha eq_refl)).
              rewrite (M4out a HaB) in Ha.
              pose proof (is_cov _ _ _ _ _ _ HIS3 a Ha Hra Hia) as Hc.
              pose proof HV3 as [_ _ _ _ _ Vpw Vmw _ _ _ _ _ _]. rewrite <- Hvm3 in Vpw, Vmw.
              apply (mcov_remove (vm_maps (ms_vm s3)) (Z_to_bv 64 B) (Z_to_bv 64 L) (u a) 1 Vpw ltac:(rewrite (nf_vm _ _ _ HF3); exact Hin));
                [rewrite HuL; lia | intros b sz Hb; exact (proj1 (Vmw b sz Hb)) | exact Hc | lia | rewrite HuB, HuL; lia | rewrite HuB, HuL; intros y Hy; lia].
            + intros x mtx Hx Hrl. exact (proj1 (ii_dd HII3 x) (ex_intro _ mtx (conj Hx Hrl))).
          - intros c Hc. exact (H48' c Hc). }
        cbn [ms_lo ms_hi ms_mem ms_vm upd].
        split; [exact Hlo3|]. split; [exact Hhi3|].
        split. { unfold A5, mlive. cbn. fold (mlive A3 pw). rewrite ELIVE. destruct (Z.eq_dec (u pw) p); [reflexivity | contradiction]. }
        split. { intros q Hq. unfold A5, mlive. cbn. fold (mlive A3 q). rewrite ELIVE. destruct (Z.eq_dec (u q) p) as [E | NE]; [| reflexivity]. exfalso. apply Hq. apply bv_eq. exact E. }
        split. { intros a Ho1 Ho3 Herr. unfold errno_slot in Herr. rewrite (M5out a Herr).
                 rewrite M4out by (intros Ha; exact (Ho1 (DOMB _ Ha))).
                 rewrite (MEM23 a ltac:(intros HoA; exact (Ho1 (OWN1A _ HoA)))). apply MEM12. intros Ha. exact (Ho1 (OWNp a Ha)). }
        split. { intros q k j Hq Hj. change (a_live A5) with (a_live A3) in Hq || idtac.
                 destruct (LIVE3 q k j Hq Hj) as [E Hd].
                 destruct (dom_heap A3 _ HW3 Hd) as (lo & hi & Hhr' & Hx'). unfold heap_range in Hhr'. ceil.
                 assert (Ea : u (at_ q j) = u q + j) by (unfold at_; rewrite uZ by lia; reflexivity).
                 rewrite M5out by (rewrite Ea; lia). rewrite M4out by (rewrite Ea; intros HB; exact (Nod _ HB Hd)). exact E. }
        split. { intros a Ha. destruct (Z.lt_ge_cases (u a) B) as [Hb | Hb]; [| destruct (Z.lt_ge_cases (u a) (B + L)) as [Hb' | Hb']; [left; exact (DOMB _ (conj Hb Hb'))|]];
                 right; apply wbytes_keeps; rewrite ?Hlen4, ?uZ by lia; try (cbn; lia); rewrite M4out by lia; exact (MAP3 a Ha). }
        (* [comment removed for export] *)
        assert (SG : sgrow 0 0 0 A A5 (ms_vm s) h5).
        { unfold h5. rewrite (nf_vm _ _ _ HF3). unfold s2. cbn [ms_vm upd].
          apply (sgrow_weaken (-1) 0 0); [| clear; lia | clear; lia | clear; lia | clear; lia].
          apply (grow_munmap A A5 (ms_vm s) _ _ EV); [unfold s2 in Hin; cbn [ms_vm upd] in Hin; exact Hin| |].
          - unfold A5. cbn [a_areas set_xmaps]. rewrite Ar3, A1_eq. reflexivity.
          - exact SP3. }
        refine ((fun X => conj (proj1 X) (conj (proj2 X) SG)) _).
        unfold h5, vm_fixed, alloc_top, vm_live_bytes. cbn. rewrite (nf_vm _ _ _ HF3). cbn [ms_vm upd].
        split; [repeat split; reflexivity|].
        unfold s2. cbn [ms_vm upd]. unfold s2 in Hin. cbn [ms_vm upd] in Hin.
        pose proof (live_bytes_remove_entry (vm_maps (ms_vm s)) (Z_to_bv 64 B) (Z_to_bv 64 L) Hin) as X. rewrite HuL in X. lia.
    Qed.
  End AfterHdr.

  Theorem free_slow_ok : free_slow A s ma mt i p (free_postX A pw s).
  Proof using HE Hi Hi0 Hma Hp Hr Hxm0 MLok mt1. pu_keep (HE, Hi, Hi0, Hma, Hp, Hr, Hxm0, MLok, mt1).
    intros m2 RW2 _. destruct (guard_read (ms_mem s)) as (cb & Hcb & _).
    exact (free_slow_body m2 RW2 cb Hcb).
  Qed.
End FreeSlowX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem free_okX : forall A s (p sp0 : word) argv envp,
  call_env A s sp0 argv envp -> a_xmaps A = [] ->
  (p = Z_to_bv 64 0 \/ exists n, mlive A p = Some n) ->
  tsafe (m_free p s) (free_postX A p s).
Proof using MLok. pu_keep (MLok).
  intros A s p sp0 argv envp HE Hxm0 Hp. pose proof HE as [HM HWIN Henv]. pose proof HM as [HW HR HV HL HKc H48].
  destruct Hp as [-> | [n Hlive]].
  - (* [comment removed for export] *)
    unfold m_free. change (is0 (Z_to_bv 64 0)) with true. cbn.
    exists A. split; [exact Hxm0|]. split; [exact HM|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { unfold mlive. change (bv_unsigned (Z_to_bv 64 0)) with 0. destruct (a_live A 0) as [k|] eqn:E; [| reflexivity]. exfalso.
      apply (proj1 (wf_live_map A HW 0 k)) in E. destruct E as (ma & mt & aib & slots & j & off & Hma & Hr & Hj0 & Hj & Eq).
      destruct (live_geom A HW ma mt aib slots j off k Hma Hr Hj0 Hj) as (q & _ & _ & _ & _ & _ & _ & G1 & G2 & _).
      pose proof (grp_heap A ma mt aib slots HW Hma Hr) as (G0 & _). unfold gext_lo in *. lia. }
    split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros a Hm; right; exact Hm|]. split; [repeat split; reflexivity |]. split; [lia | apply sgrow_refl].
  - (* [comment removed for export] *)
    pose proof Hlive as Hlive0. unfold mlive in Hlive. apply (proj1 (wf_live_map A HW _ _)) in Hlive.
    destruct Hlive as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Ep).
    rewrite <- (Z_to_bv_bv_unsigned 64 p).
    apply (free_live_ok A s HW HR HWIN (eo_rodata _ _ _ _ Henv) (envok_needlocks _ _ _ _ Henv)
             ma mt aib slots i off n (bv_unsigned p) Hma Hr Hi Hi0 Ep).
    + intros m3 RW3 Eb1 Eb2. rewrite Z_to_bv_bv_unsigned.
      exact (free_fast_postX A s HW HR ma mt aib slots i off n (bv_unsigned p) Hma Hr Hi Hi0 Ep p eq_refl Hxm0 m3 HV HL HKc H48 RW3 Eb1).
    + rewrite Z_to_bv_bv_unsigned. exact (free_slow_ok A s sp0 argv envp HE ma mt aib slots i off n p Hma Hr Hi Hi0 Ep Hxm0).
Qed.

End WithLayout.
