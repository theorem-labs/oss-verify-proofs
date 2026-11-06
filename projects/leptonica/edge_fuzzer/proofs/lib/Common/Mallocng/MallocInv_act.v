(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_coh MallocInv_free MallocInv_actw.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Activate.
  Variable B : astate.
  Hypothesis HW : WF B.
  Variables (sc m : Z) (rest : list Z) (mt : meta_rec) (aib : Z) (sl : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active B sc = m :: rest.
  Hypothesis Hm : a_meta B m = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib sl.
  Hypothesis Hav0 : mt_avail mt = 0.

  Let k := aib mod 32.
  Definition ac_av : Z := mt_freed mt mod 2 ^ (k + 1).
  Definition ac_fr : Z := mt_freed mt - ac_av.
  Definition ac_mt : meta_rec := MT (gu_f mt ac_av ac_fr) (RGroup aib sl).
  Definition acA : astate := set_live (ameta_upd B m ac_mt) (a_live B).

  Lemma ac_grp : 0 <= mt_w32 mt < 2^64 /\ Z.of_nat (length sl) = mt_cnt mt /\
    0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\ 0 <= aib < 256 /\ aib mod 32 <= mt_last mt /\ mt_cnt mt <= 32 /\ mt_sc mt = sc /\
    (forall j st, nth_error sl (Z.to_nat j) = Some st -> 0 <= j -> (Z.testbit (mt_freed mt) j = true <-> st = SIdle)).
  Proof.
    destruct (wf_grp B HW m mt aib sl Hm Hr) as (H1 & _ & _ & H4 & _ & H6 & _ & H8 & _ & H10 & H11 & _).
    destruct (wf_act_mem B HW sc m ltac:(rewrite Hact; left; reflexivity)) as (mt' & aib' & sl' & Hm' & _ & Hs). rewrite Hm in Hm'. injection Hm' as <-.
    pose proof (w_last_range (mt_w32 mt)) as Hl.
    assert (Hc : mt_cnt mt <= 32) by (unfold mt_cnt, mt_last in *; llia).
    split; [exact H1|]. split; [exact H4|]. split; [exact H6|]. split; [exact H8|]. split; [exact H10|]. split; [exact Hc|]. split; [exact Hs|].
    intros j st Hj Hj0. rewrite <- (H11 j st Hj Hj0), Hav0, Z.lor_0_l. tauto.
  Qed.

  Lemma ac_fr32 : 0 <= mt_freed mt < 2^32 /\ 0 <= k < 32.
  Proof.
    pose proof ac_grp as (_ & _ & Hfr & _ & _ & Hc & _). pose proof (Z.mod_pos_bound aib 32 ltac:(lia)).
    assert (2 ^ mt_cnt mt <= 2 ^ 32) by (apply Z.pow_le_mono_r; llia). subst k. llia.
  Qed.

  Lemma ac_masks : 0 <= ac_av <= mt_freed mt /\ ac_av < 2 ^ (k + 1) /\ 0 <= ac_fr <= mt_freed mt /\
    Z.land ac_av ac_fr = 0 /\ Z.lor ac_av ac_fr = mt_freed mt /\
    (forall j, 0 <= j -> Z.testbit ac_fr j = (Z.testbit (mt_freed mt) j && (k + 1 <=? j))%bool).
  Proof.
    pose proof ac_fr32 as [Hfr Hk]. destruct (mask_split (mt_freed mt) k Hfr Hk) as (_ & R1 & R2 & D & L & TH & _).
    unfold ac_fr, ac_av. repeat split; try llia; auto.
  Qed.

  Theorem WF_acA : WF acA.
  Proof.
    pose proof ac_grp as (Hw & Hlen & Hfr & Haib & Haibl & Hc & Hs & Hidle).
    pose proof ac_masks as (A1 & A2 & A3 & A4 & A5 & A6).
    apply (WF_grp_upd B HW m mt aib sl Hm Hr ac_av ac_fr aib sl (a_live B)).
    - reflexivity.
    - intros j st st' Hj Hj'. rewrite Hj in Hj'. injection Hj' as <-. left. reflexivity.
    - llia.
    - llia.
    - exact A4.
    - exact Haib.
    - exact A2.
    - exact Haibl.
    - intros j st Hj Hj0. rewrite A5. apply Hidle; assumption.
    - intros j off n Hj Hj0. exact (wf_live B HW m mt aib sl j off n Hm Hr Hj Hj0).
    - intros j Hj. rewrite A6 by llia. rewrite (wf_inactive B HW m mt aib sl j Hm Hr Hj). rewrite (proj2 (Z.leb_le _ _)) by (unfold k; llia). reflexivity.
    - rewrite Hs, Hact. cbn [hd]. intros _ Hne. exfalso. exact (Hne eq_refl).
    - intros H. exact H.
    - intros _ Hnz. left. rewrite Hav0, Z.lor_0_l. rewrite A5 in Hnz. exact Hnz.
    - intros q n. rewrite (wf_live_map B HW q n). unfold is_live. split.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & E).
        destruct (Z.eq_dec x m) as [-> | Hne].
        * left. rewrite Hm in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-. exists j, off. auto.
        * right. exists x, mtx, aibx, slx, j, off. auto 10.
      + intros [(j & off & Hj0 & Hj & E) | (x & mtx & aibx & slx & j & off & Hne & Hx & Hrx & Hj0 & Hj & E)].
        * exists m, mt, aib, sl, j, off. auto 10.
        * exists x, mtx, aibx, slx, j, off. auto 10.
  Qed.

  Lemma acA_meta_same : a_meta acA m = Some ac_mt.
  Proof. unfold acA, set_live, ameta_upd, set_meta. cbn. apply aupd_same. Qed.
  Lemma acA_meta_other : forall x, x <> m -> a_meta acA x = a_meta B x.
  Proof. intros x Hne. unfold acA, set_live, ameta_upd, set_meta. cbn. apply aupd_other. exact Hne. Qed.
  Lemma acA_meta_inv : forall x mtx, a_meta acA x = Some mtx -> (x = m /\ mtx = ac_mt) \/ (x <> m /\ a_meta B x = Some mtx).
  Proof.
    intros x mtx Hx. destruct (Z.eq_dec x m) as [-> | Hne].
    - left. rewrite acA_meta_same in Hx. injection Hx as <-. auto.
    - right. rewrite (acA_meta_other x Hne) in Hx. auto.
  Qed.
  Lemma ac_mt_f : forall fl, mt_f ac_mt fl = match fl with FAvail => ac_av | FFreed => ac_fr | _ => mt_f mt fl end.
  Proof. intros fl. unfold ac_mt. rewrite mt_f_MT. unfold gu_f. destruct fl; reflexivity. Qed.
  Lemma ac_mt_role : mt_role ac_mt = RGroup aib sl. Proof. reflexivity. Qed.
  Lemma ac_mt_w32 : mt_w32 ac_mt = mt_w32 mt. Proof. unfold mt_w32. apply ac_mt_f. Qed.
  Lemma ac_mt_mem : mt_mem ac_mt = mt_mem mt. Proof. unfold mt_mem. apply ac_mt_f. Qed.
  Lemma ac_mt_prev : mt_prev ac_mt = mt_prev mt. Proof. unfold mt_prev. apply ac_mt_f. Qed.
  Lemma ac_mt_next : mt_next ac_mt = mt_next mt. Proof. unfold mt_next. apply ac_mt_f. Qed.
  Lemma ac_mt_sc : mt_sc ac_mt = mt_sc mt. Proof. unfold mt_sc. rewrite ac_mt_w32. reflexivity. Qed.
  Lemma ac_mt_cnt : mt_cnt ac_mt = mt_cnt mt. Proof. unfold mt_cnt, mt_last. rewrite ac_mt_w32. reflexivity. Qed.

  Lemma acA_ctx : a_ctx acA = a_ctx B. Proof. reflexivity. Qed.
  Lemma acA_active : a_active acA = a_active B. Proof. reflexivity. Qed.
  Lemma acA_areas : a_areas acA = a_areas B. Proof. reflexivity. Qed.
  Lemma acA_freelist : a_freelist acA = a_freelist B. Proof. reflexivity. Qed.
  Lemma acA_live : a_live acA = a_live B. Proof. reflexivity. Qed.
  Lemma acA_xmaps : a_xmaps acA = a_xmaps B. Proof. reflexivity. Qed.
  Lemma acA_pages : a_pages acA = a_pages B. Proof. reflexivity. Qed.
  Lemma acA_mblocks : a_mblocks acA = a_mblocks B. Proof. reflexivity. Qed.

  Lemma dom_acA : forall x, dom acA x <-> dom B x.
  Proof. exact (dom_grp_upd B m mt aib sl Hm Hr ac_av ac_fr aib sl (a_live B)). Qed.
  Lemma VMok_acA : forall h, VMok B h -> VMok acA h.
  Proof. exact (VMok_grp_upd B m mt aib sl Hm Hr ac_av ac_fr aib sl (a_live B)). Qed.

  Lemma meta_usage_acA : forall c x, meta_usage acA c x = meta_usage B c x.
  Proof.
    intros c x. unfold meta_usage. destruct (Z.eq_dec x m) as [-> | Hne].
    - rewrite acA_meta_same, Hm, Hr. cbn [mt_role ac_mt MT]. rewrite ac_mt_sc, ac_mt_cnt. reflexivity.
    - rewrite (acA_meta_other x Hne). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma has_acA : forall f, has acA f -> has B f \/ f = FCT (m + 24) 4 ac_av \/ f = FCT (m + 28) 4 ac_fr.
  Proof.
    intros f Hf.
    destruct (has_grp_upd B m mt ac_av ac_fr aib sl (a_live B) f Hf) as [[HfB _] | [[fl ->] | [Hhdr | (j & st & Hj & Hin)]]].
    - left. exact HfB.
    - destruct fl; cbn [gu_f moff mlen]; [left | left | left | right; left; reflexivity | right; right; reflexivity | left];
        right; right; left.
      + exists m, mt, FPrev. auto.
      + exists m, mt, FNext. auto.
      + exists m, mt, FMem. auto.
      + exists m, mt, FW32. auto.
    - left. right; right; right. exists m, mt, aib, sl. split; [exact Hm|]. split; [exact Hr|]. left. exact Hhdr.
    - left. right; right; right. exists m, mt, aib, sl. split; [exact Hm|]. split; [exact Hr|]. right. exists j, st. auto.
  Qed.
End Activate.

End WithLayout.
