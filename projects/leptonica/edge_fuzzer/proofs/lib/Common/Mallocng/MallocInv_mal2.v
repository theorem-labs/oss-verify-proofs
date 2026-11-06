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
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf6 MallocInv_wf7 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_vmops MallocInv_vmfree
  MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_hints MallocInv_sc
  MallocInv_enframe MallocInv_ameta_iface MallocInv_ameta5 MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_freetop MallocInv_free
  MallocInv_sc3 MallocInv_aslot_iface MallocInv_ametax_iface MallocInv_malloc_iface MallocInv_agm2 MallocInv_agm3 MallocInv_agtail MallocInv_agroot MallocInv_mal1 MallocInv_efII MallocInv_mal3
  MallocSureLedger MallocSureInv MallocSureGrow MallocSureCap MallocSureCredit MallocSurePot.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iav_1_0 : iav 1 0 = 0. Proof. reflexivity. Qed.
Lemma ifr_1_0 : ifr 1 0 = 0. Proof. reflexivity. Qed.
Lemma ir_aib_0_0 : ir_aib 0 0 = 0. Proof. reflexivity. Qed.
Lemma iw32_63_1 : forall L, iw32 L 63 1 = L + 4064. Proof. intros L. unfold iw32. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BigTail.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A1 : astate) (s1 : mstate).
  Variables (m : Z) (md : meta_rec) (p L nn : Z).
  Hypothesis HII : II sp0 argv envp cb [m] A1 s1.
  Hypothesis Hm : a_meta A1 m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis Hz : forall fl, mt_f md fl = 0.
  Hypothesis Hxm : a_xmaps A1 = [(p, L)].
  Hypothesis Hpal : page_aligned p.
  Hypothesis Hhr : heap_range p (p + L).
  Hypothesis HLm : L mod 4096 = 0.
  Hypothesis Hin : In (Z_to_bv 64 p, Z_to_bv 64 L) (vm_maps (ms_vm s1)).
  Hypothesis Hrf : region_free (vm_noaccess (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true.
  Hypothesis Hnodom : forall x, p <= x < p + L -> ~ dom A1 x.
  Hypothesis Hzero : forall a : word, p <= u a < p + L -> ms_mem s1 a = Some (Z_to_bv 8 0).
  Hypothesis Hnn : 0 <= nn /\ nn + 20 <= L /\ L <= nn + 20 + 4095.

  Let HW1 : WF A1 := is_wf _ _ _ _ _ _ (ii_is HII).

  Lemma HL : 0 < L. Proof. clear - Hnn. lia. Qed.
  Lemma L47 : L < 2^47. Proof. unfold heap_range in Hhr. pose proof layout_small. clear - Hhr H Hnn. lia. Qed.
  Lemma Hsc63 : 0 <= 63 < 48 \/ (63 = 63 /\ 1 = 1). Proof. right. split; reflexivity. Qed.
  Lemma Hcnt1 : 1 <= 1 <= 32. Proof. lia. Qed.
  Lemma Haidx0 : 0 <= 0 <= 1 - 1. Proof. lia. Qed.
  Lemma Hab0 : 0 <= 0 < 256. Proof. lia. Qed.

  Lemma p_m_apart : p + L <= m \/ m + 40 <= p.
  Proof.
    pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom). pose proof HL.
    destruct (Z.lt_ge_cases m (p + L)) as [H1 | H1]; [| left; lia]. destruct (Z.lt_ge_cases p (m + 40)) as [H2|H2]; [| right; lia]. exfalso.
    destruct (Z.lt_ge_cases m p) as [H3 | H3].
    - apply (Hnodom p ltac:(lia)). replace p with (m + (p - m)) by lia. apply Mdom. lia.
    - apply (Hnodom m ltac:(lia)). replace m with (m + 0) by lia. apply Mdom. lia.
  Qed.

  (* [comment removed for export] *)
  Definition bc2 (cv : Z) : ctx_rec := cupd (a_ctx A1) KCtr cv.
  Definition bA2 (cv : Z) : astate := set_ctx A1 (bc2 cv).
  Definition bmd3 : meta_rec := MT (ir_f p L 1 0 63) RDead.
  Definition bA3 (cv : Z) : astate := ameta_upd (bA2 cv) m bmd3.
  Definition bigA (cv : Z) : astate := instR (bA3 cv) m p L 1 0 63 0 [].
  Definition bmt : meta_rec := ir_mt p L 1 0 63 0.

  (* [comment removed for export] *)
  Definition BW (cv : Z) : list fct :=
    [FCT (caddr KCtr) 4 cv; FCT (m + 24) 4 0; FCT (m + 28) 4 0; FCT (m + 32) 8 (iw32 L 63 1); FCT p 8 m; FCT (m + 16) 8 p].

  Section Cv.
    Variable cv : Z.
    Hypothesis Hcv : 0 <= cv.

    Lemma bc2_heur : forall k, ctx_heur k \/ bc2 cv k = a_ctx A1 k.
    Proof. intros k. unfold bc2, cupd. destruct (cslot_eq_dec k KCtr) as [-> | Hne]; [left; exact I | right; reflexivity]. Qed.
    Lemma bc2_nn : forall k, 0 <= bc2 cv k.
    Proof. intros k. unfold bc2, cupd. pose proof (wf_ctx_nonneg A1 HW1 k). destruct (cslot_eq_dec k KCtr); lia. Qed.
    Lemma bc2_other : forall k, k <> KCtr -> bc2 cv k = a_ctx A1 k.
    Proof. intros k Hk. unfold bc2, cupd. destruct (cslot_eq_dec k KCtr); [contradiction | reflexivity]. Qed.
    Lemma bc2_ctr : bc2 cv KCtr = cv.
    Proof. unfold bc2, cupd. destruct (cslot_eq_dec KCtr KCtr); [reflexivity | contradiction]. Qed.
    Lemma WF2 : WF (bA2 cv). Proof. exact (WF_ctx_heur A1 HW1 (bc2 cv) bc2_heur bc2_nn). Qed.
    Lemma VMok2 : forall h, VMok A1 h -> VMok (bA2 cv) h. Proof. intros h Hv. exact (VMok_ctx_heur A1 (bc2 cv) bc2_heur h Hv). Qed.
    Lemma bA2_meta : a_meta (bA2 cv) = a_meta A1. Proof. reflexivity. Qed.

    Lemma bA3_meta : forall x, a_meta (bA3 cv) x = if Z.eq_dec x m then Some bmd3 else a_meta A1 x.
    Proof. intros x. reflexivity. Qed.
    Lemma bA3_m : a_meta (bA3 cv) m = Some bmd3.
    Proof. rewrite bA3_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.
    Lemma bA3_other : forall x, x <> m -> a_meta (bA3 cv) x = a_meta (bA2 cv) x.
    Proof. intros x Hx. rewrite bA3_meta, bA2_meta. destruct (Z.eq_dec x m); [contradiction | reflexivity]. Qed.
    Lemma bmd3_f : forall fl, mt_f bmd3 fl = ir_f p L 1 0 63 fl. Proof. intros fl. unfold bmd3. apply mt_f_MT. Qed.
    Lemma WF3 : WF (bA3 cv).
    Proof. apply (WF_dead_local (bA2 cv) (bA3 cv) m md bmd3 WF2); try reflexivity; [exact Hm | exact Hr | exact bA3_m | exact bA3_other]. Qed.
    Lemma VMok3 : forall h, VMok A1 h -> VMok (bA3 cv) h.
    Proof. intros h Hv. apply (VMok_dead_local (bA2 cv) (bA3 cv) m md bmd3); try reflexivity; [exact Hm | exact Hr | exact bA3_m | exact bA3_other | exact (VMok2 h Hv)]. Qed.
    Lemma dom_bA3 : forall x, dom (bA3 cv) x <-> dom A1 x.
    Proof.
      intros x. rewrite (dom_dead_local (bA2 cv) (bA3 cv) m md bmd3 Hm Hr bA3_m eq_refl bA3_other eq_refl eq_refl x). apply (dom_set_ctx A1 (bc2 cv) x).
    Qed.
    Lemma Hnodom3 : forall x, p <= x < p + L -> ~ dom (bA3 cv) x.
    Proof. intros x Hx Hd. apply (Hnodom x Hx). apply (proj1 (dom_bA3 x)). exact Hd. Qed.
    Lemma bA3_meta_inv : forall x mtx, a_meta (bA3 cv) x = Some mtx -> (x = m /\ mtx = bmd3) \/ (x <> m /\ a_meta A1 x = Some mtx).
    Proof.
      intros x mtx Hx. rewrite bA3_meta in Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; injection Hx as <-; auto | right; auto].
    Qed.

    Lemma WF4 : WF (bigA cv).
    Proof.
      unfold bigA. apply (WF_instR (bA3 cv) m bmd3 p L 1 0 63 0 [] WF3 bA3_m eq_refl).
      all: first [reflexivity | assumption | exact Hsc63 | exact Hcnt1 | exact Haidx0 | exact Hab0 | exact HL | exact L47 | exact Hnodom3 | (intros; lia)].
    Qed.
    Lemma bigA_m : a_meta (bigA cv) m = Some bmt.
    Proof. unfold bigA, bmt. apply ir_meta_m. Qed.
    Lemma bigA_other : forall x, x <> m -> a_meta (bigA cv) x = a_meta A1 x.
    Proof. intros x Hx. unfold bigA. rewrite (ir_meta_other (bA3 cv) m p L 1 0 63 0 [] x Hx). rewrite (bA3_other x Hx). reflexivity. Qed.
    Lemma bigA_meta_inv : forall x mtx, a_meta (bigA cv) x = Some mtx -> (x = m /\ mtx = bmt) \/ (x <> m /\ a_meta A1 x = Some mtx).
    Proof.
      intros x mtx Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; rewrite bigA_m in Hx; injection Hx as <-; auto | right].
      rewrite (bigA_other x Hne) in Hx. auto.
    Qed.
    Lemma bigA_active : a_active (bigA cv) = a_active A1. Proof. reflexivity. Qed.
    Lemma bigA_ctx : a_ctx (bigA cv) = bc2 cv. Proof. reflexivity. Qed.
    Lemma bigA_areas : a_areas (bigA cv) = a_areas A1. Proof. reflexivity. Qed.
    Lemma bigA_freelist : a_freelist (bigA cv) = a_freelist A1. Proof. reflexivity. Qed.
    Lemma bigA_live : a_live (bigA cv) = a_live A1. Proof. reflexivity. Qed.
    Lemma bigA_xmaps : a_xmaps (bigA cv) = []. Proof. reflexivity. Qed.
    Lemma bigA_pages : a_pages (bigA cv) = a_pages A1. Proof. reflexivity. Qed.
    Lemma bigA_mblocks : a_mblocks (bigA cv) = a_mblocks A1. Proof. reflexivity. Qed.
    Lemma bigA_brk_lo : a_brk_lo (bigA cv) = a_brk_lo A1. Proof. reflexivity. Qed.
    Lemma bmt_role : mt_role bmt = RGroup (ir_aib 0 0) (ir_slots 1). Proof. reflexivity. Qed.
    Lemma bmt_f : forall fl, mt_f bmt fl = ir_f p L 1 0 63 fl. Proof. intros fl. unfold bmt, ir_mt. apply mt_f_MT. Qed.
    Lemma bmt_w32 : mt_w32 bmt = iw32 L 63 1. Proof. reflexivity. Qed.
    Lemma bmt_mem : mt_mem bmt = p. Proof. reflexivity. Qed.
    Lemma bmt_sc : mt_sc bmt = 63. Proof. unfold bmt. apply ir_sc; [exact Hsc63 | exact Hcnt1 | exact Hab0 | exact HL | exact HLm]. Qed.
    Lemma bmt_last : mt_last bmt = 0. Proof. unfold bmt. rewrite (ir_last p L 1 0 63 0 Hsc63 Hcnt1 Hab0 HL HLm). reflexivity. Qed.
    Lemma bmt_maplen : mt_maplen bmt = L / 4096. Proof. unfold bmt. apply ir_maplen; [exact Hsc63 | exact Hcnt1 | exact Hab0 | exact HL | exact HLm]. Qed.
    Lemma bmt_maplen_pos : 0 < mt_maplen bmt. Proof. rewrite bmt_maplen. exact (proj1 (maplen_pages L HL HLm)). Qed.
    Lemma bmt_stride : mt_stride bmt = L - 16.
    Proof.
      unfold bmt. rewrite (ir_stride p L 1 0 63 0 Hsc63 Hcnt1 Hab0 HL HLm ltac:(intros _ H48; exfalso; clear - H48; lia) ltac:(intros _ H48; exfalso; clear - H48; lia)). rewrite Z.eqb_refl. reflexivity.
    Qed.
    Lemma slot0 : slot_start bmt 0 = p + 16 /\ slot_end bmt 0 = p + L - 4.
    Proof. unfold slot_start, slot_end, slot_start_g, slot_end_g. rewrite bmt_mem, bmt_stride. split; lia. Qed.

    Lemma dom_bigA : forall x, dom (bigA cv) x <-> dom A1 x \/ p <= x < p + L.
    Proof.
      intros x. unfold bigA. rewrite (dom_instR (bA3 cv) m bmd3 p L 1 0 63 0 [] bA3_m eq_refl Hsc63 Hcnt1 Hab0 HL HLm x).
      rewrite (dom_bA3 x). tauto.
    Qed.
    Lemma VMok4 : VMok (bigA cv) (ms_vm s1).
    Proof.
      unfold bigA. apply (VMok_instR (bA3 cv) m bmd3 p L 1 0 63 0 [] bA3_m eq_refl ltac:(rewrite <- Hxm; reflexivity) Hsc63 Hcnt1 Hab0 Hhr HL HLm L47); [| exact Hin | exact Hrf].
      apply VMok3. exact (ii_vm HII).
    Qed.
    Lemma meta_usage_bA3 : forall c x, meta_usage (bA3 cv) c x = meta_usage A1 c x.
    Proof.
      intros c x. unfold meta_usage. rewrite bA3_meta. destruct (Z.eq_dec x m) as [-> | Hne]; [| reflexivity].
      rewrite Hm, Hr. unfold bmd3. rewrite mt_role_MT. reflexivity.
    Qed.
    Lemma UsOK4 : UsOK (bigA cv).
    Proof.
      intros c Hc. rewrite bigA_ctx, (bc2_other (KUsage c)) by discriminate. unfold bigA.
      rewrite (usage_of_instR (bA3 cv) m bmd3 p L 1 0 63 0 [] WF3 bA3_m eq_refl Hsc63 Hcnt1 Hab0 HL HLm c Hc).
      replace (63 =? c) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r.
      rewrite (usage_of_ext A1 (bA3 cv) c eq_refl (meta_usage_bA3 c)). exact (ii_us HII c Hc).
    Qed.
    Lemma AvOK4 : AvOK (bigA cv).
    Proof.
      apply (AvOK_transfer A1 (bigA cv) (ii_av HII)); [reflexivity | |].
      - rewrite bigA_ctx. apply bc2_other. discriminate.
      - intros x mt' Hx Hrx. destruct (bigA_meta_inv x mt' Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    Qed.
    Lemma deads4 : deads (bigA cv) [].
    Proof.
      intros x. split.
      - intros (mtx & Hx & Hrx). destruct (bigA_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx|].
        destruct (proj1 (ii_dd HII x) (ex_intro _ mtx (conj H Hrx))) as [-> | Hin']; [contradiction | exact Hin'].
      - intros [].
    Qed.

    (* [comment removed for export] *)
    Lemma big_commit : forall m', RepW A1 (ms_mem s1) (BW cv) m' -> Rep (bigA cv) m'.
    Proof.
      intros m' RW.
      pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS.
      pose proof (ctx_slot_range KCtr I) as (C1 & C2 & C3). cbn [clen] in C2, C3. unfold CTX_END in C2.
      pose proof Hhr as HR'. unfold heap_range in HR'. pose proof p_m_apart as Hpm. pose proof HL as HL0. pose proof slot0 as [S0 E0].
      assert (INW : forall w, In w (BW cv) ->
        w = FCT (caddr KCtr) 4 cv \/ w = FCT (m + 24) 4 0 \/ w = FCT (m + 28) 4 0 \/ w = FCT (m + 32) 8 (iw32 L 63 1) \/ w = FCT p 8 m \/ w = FCT (m + 16) 8 p).
      { intros w Hw. unfold BW in Hw. cbn [In] in Hw. intuition auto. }
      apply (repw_commit3 A1 (bigA cv) (ms_mem s1) (BW cv) m' WF4 RW).
      - (* [comment removed for export] *)
        intros f Hf. unfold bigA in Hf.
        destruct (has_instR (bA3 cv) m bmd3 p L 1 0 63 0 [] bA3_m Hsc63 Hcnt1 Haidx0 Hab0 HL bmd3_f f Hf) as [Hf3 | [-> | [-> | (i & Hi & Hfi)]]].
        + destruct (has_dead_local (bA2 cv) (bA3 cv) m md bmd3 bA3_m eq_refl bA3_other eq_refl eq_refl f Hf3) as [[Hf2 Hnot] | [(fl & ->) | Hf2]].
          * destruct (has_set_ctx A1 (bc2 cv) f Hf2) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hmf | Hg]]]].
            -- unfold bc2, cupd. destruct (cslot_eq_dec k KCtr) as [-> | Hkc].
               ++ right; left. cbn [f_a f_n clen]. intros x Hx. unfold BW. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
               ++ left. left. exists k. auto.
            -- left. right; left. exact Har.
            -- left. right; left. exists pg. auto.
            -- destruct Hmf as (x & mtx & fl & Hx0 & ->). assert (Hx : a_meta A1 x = Some mtx) by exact Hx0. clear Hx0.
               destruct (Z.eq_dec x m) as [-> | Hne]; [exfalso; rewrite Hm in Hx; injection Hx as <-; exact (Hnot fl eq_refl)|].
               left. right; right; left. exists x, mtx, fl. auto.
            -- left. right; right; right. exact Hg.
          * (* [comment removed for export] *)
            rewrite bmd3_f. pose proof (mfield_range fl) as Hflr. cbn [f_a f_n].
            destruct fl; cbn [moff mlen ir_f].
            -- (* [comment removed for export] *) left. right; right; left. exists m, md, FPrev. rewrite (Hz FPrev). auto.
            -- (* [comment removed for export] *) left. right; right; left. exists m, md, FNext. rewrite (Hz FNext). auto.
            -- right; left. intros x Hx. unfold BW. do 5 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
            -- right; left. intros x Hx. unfold BW. do 1 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
            -- right; left. intros x Hx. unfold BW. do 2 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
            -- right; left. intros x Hx. unfold BW. do 3 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
          * destruct (has_set_ctx A1 (bc2 cv) f Hf2) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | [Hmf | Hg]]]].
            -- unfold bc2, cupd. destruct (cslot_eq_dec k KCtr) as [-> | Hkc].
               ++ right; left. cbn [f_a f_n clen]. intros x Hx. unfold BW. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
               ++ left. left. exists k. auto.
            -- left. right; left. exact Har.
            -- left. right; left. exists pg. auto.
            -- destruct Hmf as (x & mtx & fl & Hx0 & ->). assert (Hx : a_meta A1 x = Some mtx) by exact Hx0. clear Hx0.
               destruct (Z.eq_dec x m) as [-> | Hne].
               ++ rewrite Hm in Hx. injection Hx as <-. pose proof (mfield_range fl) as Hflr. cbn [f_a f_n]. rewrite (Hz fl).
                  destruct fl; cbn [moff mlen].
                  ** left. right; right; left. exists m, md, FPrev. rewrite (Hz FPrev). auto.
                  ** left. right; right; left. exists m, md, FNext. rewrite (Hz FNext). auto.
                  ** right; left. intros y Hy. unfold BW. do 5 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** right; left. intros y Hy. unfold BW. do 1 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** right; left. intros y Hy. unfold BW. do 2 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
                  ** right; left. intros y Hy. unfold BW. do 3 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
               ++ left. right; right; left. exists x, mtx, fl. auto.
            -- left. right; right; right. exact Hg.
        + (* [comment removed for export] *) right; left. cbn [f_a f_n]. intros x Hx. unfold BW.
          do 4 (rewrite wlook_skip by (cbn [f_a f_n]; lia)). rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
        + (* [comment removed for export] *)
          right; right. rewrite ir_aib_0_0. cbn [f_a f_n f_v]. intros x Hx. split.
          * unfold BW. repeat (rewrite wlook_skip by (cbn [f_a f_n]; lia)). reflexivity.
          * rewrite byte_of_zero. apply (mbyte_overlay (ms_mem s1) x (Z_to_bv 8 0)); [lia|]. apply Hzero. rewrite uZ by lia. lia.
        + (* [comment removed for export] *)
          right; right. assert (i = 0%nat) by lia. subst i. change (Z.of_nat 0) with 0 in Hfi. fold bmt in Hfi. rewrite S0, E0 in Hfi.
          assert (Hfz : f_v f = 0 /\ f_n f = 1 /\ p + 12 <= f_a f /\ f_a f + 1 <= p + L).
          { destruct Hfi as [-> | ->]; cbn [f_a f_n f_v]; (split; [reflexivity | split; [reflexivity | lia]]). }
          destruct Hfz as (Ev & En & Z3 & Z4). rewrite Ev, En. intros x Hx. split.
          * unfold BW. repeat (rewrite wlook_skip by (cbn [f_a f_n]; lia)). reflexivity.
          * rewrite byte_of_zero. apply (mbyte_overlay (ms_mem s1) x (Z_to_bv 8 0)); [lia|]. apply Hzero. rewrite uZ by lia. lia.
      - (* [comment removed for export] *)
        intros x b Hw. destruct (wlook_some_cov (BW cv) x b Hw) as (w & Hwin & Hwx).
        destruct (INW w Hwin) as [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn [f_a f_n] in Hwx; unfold BW in Hw;
          repeat (first [rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia) | rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia)]); cbn [f_a f_v] in Hw; injection Hw as <-.
        + right; left. exists KCtr. split; [exact I|]. cbn [clen]. split; [lia|]. rewrite bigA_ctx, bc2_ctr. reflexivity.
        + left. exists m, bmt, FAvail. split; [exact bigA_m|]. cbn [moff mlen]. split; [lia|]. rewrite bmt_f. cbn [ir_f]. rewrite iav_1_0. reflexivity.
        + left. exists m, bmt, FFreed. split; [exact bigA_m|]. cbn [moff mlen]. split; [lia|]. rewrite bmt_f. cbn [ir_f]. rewrite ifr_1_0. reflexivity.
        + left. exists m, bmt, FW32. split; [exact bigA_m|]. cbn [moff mlen]. split; [lia|]. rewrite bmt_f. reflexivity.
        + right; right; left. exists m, bmt, (ir_aib 0 0), (ir_slots 1), (FCT p 8 m).
          split; [exact bigA_m|]. split; [reflexivity|]. split; [cbn; left; reflexivity|]. cbn [f_a f_n f_v]. split; [lia | reflexivity].
        + left. exists m, bmt, FMem. split; [exact bigA_m|]. cbn [moff mlen]. split; [lia|]. rewrite bmt_f. reflexivity.
      - intros x Hx. apply dom_bigA in Hx. destruct Hx as [Hx | Hx]; [left; exact Hx | right]. split; [lia|].
        rewrite (Hzero (Z_to_bv 64 x)); [discriminate | rewrite uZ by lia; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma big_handover : forall m', RepW A1 (ms_mem s1) (BW cv) m' ->
      let s' := upd s1 m' (ms_vm s1) in
      II sp0 argv envp cb [] (bigA cv) s' /\ FR A1 s1 (bigA cv) s' /\
      (forall a : word, m' a = ms_mem s1 a \/ (LOCKA + 8 <= u a < LOCKA + 936) \/ (m <= u a < m + 40) \/ (p <= u a < p + 8)) /\
      (forall a : word, p + 8 <= u a < p + L -> m' a = Some (Z_to_bv 8 0)).
    Proof.
      intros m' RW. cbv zeta. pose proof (ii_is HII) as HIS. pose proof HIS as [HW HRp HC HWIN HE HG].
      pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS.
      pose proof Hhr as HR'. unfold heap_range in HR'. pose proof p_m_apart as Hpm. pose proof HL as HL0.
      pose proof (big_commit m' RW) as HR5.
      pose proof (ctx_slot_range KCtr I) as (C1 & C2 & C3). cbn [clen] in C2, C3. unfold CTX_END in C2.
      assert (WCASE : forall w x, In w (BW cv) -> f_a w <= x < f_a w + f_n w ->
        (LOCKA + 8 <= x < LOCKA + 936) \/ (m <= x < m + 40) \/ (p <= x < p + 8)).
      { intros w x Hw Hx. unfold BW in Hw. cbn [In] in Hw.
        destruct Hw as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [f_a f_n] in Hx; lia. }
      assert (ZONE : forall a : word, m' a = ms_mem s1 a \/ mzone (u a)).
      { intros a. destruct (wfree_dec (BW cv) (u a)) as [Hf | (w & Hw & Hx)]; [left; exact (rw_frame A1 _ _ m' RW a Hf) | right].
        unfold mzone, CTX, CTX_END. destruct (WCASE w (u a) Hw Hx) as [H | [H | H]]; lia. }
      assert (MAPPED : forall a : word, m' a <> None -> ms_mem s1 a <> None \/ (IMG_LO <= u a < IMG_HI) \/ mcov (vm_maps (ms_vm s1)) (u a) 1).
      { intros a Ha. destruct (wfree_dec (BW cv) (u a)) as [Hf | (w & Hw & Hx)]; [left; rewrite <- (rw_frame A1 _ _ m' RW a Hf); exact Ha|].
        destruct (WCASE w (u a) Hw Hx) as [H | [H | H]].
        - right; left. lia.
        - left. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom A1 (ms_mem s1) HRp). replace (u a) with (m + (u a - m)) by lia. apply Mdom. lia.
        - left. rewrite (Hzero a); [discriminate | lia]. }
      split; [| split; [| split]].
      - apply II_intro.
        + apply (IS_mem sp0 argv envp cb A1 (bigA cv) s1 m' HIS WF4 HR5 ZONE MAPPED).
        + cbn [ms_vm upd]. exact VMok4.
        + exact AvOK4.
        + exact UsOK4.
        + exact deads4.
      - constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd]; try reflexivity.
        + intros x Ho. unfold owned_of in *. rewrite (dom_bigA x). tauto.
        + intros a Ho _. destruct (wfree_dec (BW cv) (u a)) as [Hf | (w & Hw & Hx)]; [exact (rw_frame A1 _ _ m' RW a Hf)|].
          exfalso. apply Ho. unfold owned_of. rewrite (dom_bigA (u a)). unfold CTX_END.
          destruct (WCASE w (u a) Hw Hx) as [H | [H | H]]; [left; lia | | right; right; lia].
          right; left. replace (u a) with (m + (u a - m)) by lia. apply Mdom. lia.
        + intros q n Hq. rewrite bigA_live. exact Hq.
        + intros q n a Hq Ha. destruct (wfree_dec (BW cv) (u a)) as [Hf | (w & Hw & Hx)]; [exact (rw_frame A1 _ _ m' RW a Hf)|].
          exfalso. pose proof (live_dom A1 q n (u a) HW1 Hq Ha) as Hd.
          pose proof (dom_heap A1 (u a) HW1 Hd) as (lo & hi & Hh & Hlh). unfold heap_range in Hh.
          destruct (WCASE w (u a) Hw Hx) as [H | [H | H]].
          * lia.
          * exact (proj2 (meta_dom_nolive A1 m md (u a) HW1 Hm ltac:(lia)) q n Hq Ha).
          * apply (Hnodom (u a)); [lia | exact Hd].
        + intros a Ha. exact (rw_mapped A1 _ _ m' RW a Ha).
      - intros a. destruct (wfree_dec (BW cv) (u a)) as [Hf | (w & Hw & Hx)]; [left; exact (rw_frame A1 _ _ m' RW a Hf) | right].
        exact (WCASE w (u a) Hw Hx).
      - intros a Ha. destruct (wfree_dec (BW cv) (u a)) as [Hf | (w & Hw & Hx)].
        + rewrite (rw_frame A1 _ _ m' RW a Hf). apply Hzero. lia.
        + exfalso. destruct (WCASE w (u a) Hw Hx) as [H | [H | H]]; lia.
    Qed.
  End Cv.

  (* [comment removed for export] *)
  Lemma ts_lw_fact4w : forall (A : astate) s (m0 : word -> option byte) ws a v (k : word -> M R) (P : R -> mstate -> Prop),
    WF A -> RepW A m0 ws (ms_mem s) -> WIN s -> has A (FCT a 4 v) -> wfree_range ws a 4 -> 0 <= v ->
    tsafe (k (w32 v) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 a) ;; k x) s) P.
  Proof.
    intros A s m0 ws a v k P HW RW HWIN Hf Hfree Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3. ceil.
    destruct (repw_read_fact A m0 ws (ms_mem s) a 4 v RW Hf Hfree ltac:(lia) ltac:(cbn; lia) Hv) as (bs & Hrd & Hl & Hval).
    eapply ts_lw; [apply acc_ok_heap; [exact HWIN | lia | lia | cbn; lia] | exact Hrd |].
    rewrite (le_val_Z bs (v mod 2^32)); [| rewrite Hval; reflexivity].
    rewrite v_lw_w32 by (pose proof (Z.mod_pos_bound v (2^32)); lia). rewrite w32_mod. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Theorem big_stores_ok : forall (k : word -> M R) P,
    (forall cv m', 0 <= cv -> RepW A1 (ms_mem s1) (BW cv) m' -> tsafe (k (w32 cv) (upd s1 m' (ms_vm s1))) P) ->
    tsafe ((m_sd (at_ (Z_to_bv 64 m) 16) (Z_to_bv 64 p) ;;
            m_sd (Z_to_bv 64 p) (Z_to_bv 64 m) ;;
            m_sd (at_ (Z_to_bv 64 m) 32) (Z_to_bv 64 (L + 4064)) ;;
            m_sw (at_ (Z_to_bv 64 m) 28) w0 ;;
            m_sw (at_ (Z_to_bv 64 m) 24) w0 ;;
            c <- m_lw (at_ A_LOCK 20) ;;
            m_sw (at_ A_LOCK 20) (v_addi c 1) ;;
            ctr <- m_lw (at_ A_LOCK 20) ;; k ctr) s1) P.
  Proof.
    intros k P Hk. pose proof (ii_is HII) as HIS. pose proof HIS as [HW HRp HC HWIN HE HG].
    pose proof (repw_init A1 (ms_mem s1) HW1 HRp) as RW0.
    pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom). ceil. pose proof layout_small as LS. pose proof layout_nums as LN.
    pose proof Hhr as HR'. unfold heap_range in HR'. pose proof HL as HL0. pose proof L47 as HL47.
    pose proof (ctx_slot_range KCtr I) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    rewrite !at_Z, w0_eq. rewrite (addr_lock 20), <- caddr_KCtr_lock.
    (* [comment removed for export] *)
    eapply (ts_sd_metaW A1 HW1 s1 (ms_mem s1) [] m md 16); [exact RW0 | exact HWIN | exact Hm | lia | lia |].
    intros m1 RW1. rewrite uZ in RW1 by lia.
    (* [comment removed for export] *)
    unfold m_sd at 1.
    eapply (ts_st_mapw A1 _ (ms_mem s1) _ 8 p (Z_to_bv 64 m)); [exact RW1 | apply WIN_upd; exact HWIN | lia | | |].
    { unfold heap_bytes. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. repeat split; lia. }
    { intros j Hj. rewrite (Hzero (Z_to_bv 64 (p + j))); [discriminate | rewrite uZ by lia; cbn in Hj; lia]. }
    cbn [ms_vm upd]. intros m2 RW2. rewrite uZ in RW2 by lia. change (Z.of_nat 8) with 8 in RW2.
    (* [comment removed for export] *)
    eapply (ts_sd_metaW A1 HW1 _ (ms_mem s1) _ m md 32); [exact RW2 | apply WIN_upd; exact HWIN | exact Hm | lia | lia |].
    cbn [ms_vm upd]. intros m3 RW3. rewrite uZ in RW3 by lia.
    (* [comment removed for export] *)
    unfold m_sw at 1.
    eapply (ts_st_domW A1 HW1 _ (ms_mem s1) _ 4 (m + 28) (Z_to_bv 64 0)); [exact RW3 | apply WIN_upd; exact HWIN | lia | |].
    { intros j Hj. replace (m + 28 + j) with (m + (28 + j)) by lia. apply Mdom. cbn in Hj. lia. }
    cbn [ms_vm upd]. intros m4 RW4. rewrite uZ in RW4 by lia. change (Z.of_nat 4) with 4 in RW4.
    (* [comment removed for export] *)
    unfold m_sw at 1.
    eapply (ts_st_domW A1 HW1 _ (ms_mem s1) _ 4 (m + 24) (Z_to_bv 64 0)); [exact RW4 | apply WIN_upd; exact HWIN | lia | |].
    { intros j Hj. replace (m + 24 + j) with (m + (24 + j)) by lia. apply Mdom. cbn in Hj. lia. }
    cbn [ms_vm upd]. intros m5 RW5. rewrite uZ in RW5 by lia. change (Z.of_nat 4) with 4 in RW5.
    (* [comment removed for export] *)
    pose proof (wf_ctx_nonneg A1 HW1 KCtr) as Hc0. set (c0 := a_ctx A1 KCtr) in *.
    eapply (ts_lw_fact4w A1 _ (ms_mem s1) _ (caddr KCtr) c0); [exact HW1 | exact RW5 | apply WIN_upd; exact HWIN | left; exists KCtr; split; [exact I | reflexivity] | | exact Hc0 |].
    { unfold CTX_END in C2. repeat (apply wfree_range_cons; [cbn [f_a f_n]; lia|]). apply wfree_range_nil. }
    (* [comment removed for export] *)
    unfold m_sw at 1. set (cvw := v_addi (w32 c0) 1). pose proof (u64_range cvw) as Hcvw.
    eapply (ts_st_ctxrW A1 _ (ms_mem s1) _ 4 (caddr KCtr) cvw); [exact RW5 | apply WIN_upd; exact HWIN | rewrite caddr_KCtr_lock, CTX_lock; lia | rewrite caddr_KCtr_lock; unfold CTX_END; cbn; lia |].
    cbn [ms_vm upd]. intros m6 RW6. change (Z.of_nat 4) with 4 in RW6.
    (* [comment removed for export] *)
    eapply (ts_lw_wrw A1 _ (ms_mem s1) _ (caddr KCtr) (u cvw)); [exact RW6 | apply WIN_upd; exact HWIN | lia | unfold CTX_END in C2; lia | lia | |].
    { intros j Hj. cbn [wlook]. replace (wcov (FCT (caddr KCtr) 4 (u cvw)) (caddr KCtr + j)) with true by (symmetry; apply wcov_spec; cbn; lia).
      cbn [f_a f_v]. f_equal. f_equal. lia. }
    apply (Hk (u cvw) m6); [lia|]. unfold BW. rewrite iw32_63_1. exact RW6.
  Qed.

End BigTail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma vm_mmap_limit : forall a len h, vm_limit (vm_mmap a len h) = vm_limit h.
Proof. intros. reflexivity. Qed.
Lemma vm_mmap_maps : forall a len h, vm_maps (vm_mmap a len h) = (a, len) :: vm_maps h.
Proof. intros. reflexivity. Qed.
Lemma vm_mmap_noaccess : forall a len h, vm_noaccess (vm_mmap a len h) = vm_noaccess h.
Proof. intros. reflexivity. Qed.
Lemma vm_mmap_live_bytes : forall a len h, vm_live_bytes (vm_mmap a len h) = vm_live_bytes h + u len.
Proof. intros. unfold vm_live_bytes. cbn [vm_maps vm_mmap live_bytes]. lia. Qed.

Section BigOk.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (n : Z).
  Variables (K : word -> M R) (P : R -> mstate -> Prop).
  Hypothesis HII0 : II sp0 argv envp cb [] A s.
  Hypothesis Hxm0 : a_xmaps A = [].
  Hypothesis Hact : ACT48 A.
  Hypothesis Hn : MMAP_THRESHOLD <= n < 2^61.
  Hypothesis HL : MLeaf W sp0 argv envp cb A s n K P.
  Hypothesis HWs : W <> WFail.
  (* [comment removed for export] *)
  Variables (A5 : astate) (s6 : mstate) (p L : Z).
  Hypothesis HR5 : hrel A A5.
  Hypothesis EL : L = page_round_up_Z (n + 20).
  Hypothesis Hpal : page_aligned p.
  Hypothesis Hhr : heap_range p (p + L).
  Hypothesis Gdom : forall x, p <= x < p + L -> ~ dom A x /\ ms_mem s (Z_to_bv 64 x) = None.
  Hypothesis Gna : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true.
  Hypothesis F6lo : ms_lo s6 = ms_lo s.
  Hypothesis F6hi : ms_hi s6 = ms_hi s.
  Hypothesis F6vm : ms_vm s6 = vm_mmap (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_vm s).
  Hypothesis F6mem : forall a : word, ~ owned_of A (u a) -> ~ (p <= u a < p + L) -> ms_mem s6 a = ms_mem s a.
  Hypothesis F6live : forall q k (a : word), a_live A q = Some k -> q <= u a < q + k -> ms_mem s6 a = ms_mem s a.
  Hypothesis F6mapped : forall a : word, ms_mem s a <> None -> ms_mem s6 a <> None.
  Hypothesis F6zero : forall a : word, p <= u a < p + L -> ms_mem s6 a = Some (Z_to_bv 8 0).
  Let A6 : astate := xadd A5 p L.
  (* [comment removed for export] *)
  Variables (A1 : astate) (s1 : mstate) (m : Z).
  Hypothesis HII1 : II sp0 argv envp cb [m] A1 s1.
  Hypothesis HFR1 : FR A6 s6 A1 s1.
  Hypothesis HGM : got_meta A6 [] A1 m.
  Hypothesis HAM : AMvm A6 A1 s6 s1.
  Hypothesis Hxm1 : a_xmaps A1 = a_xmaps A6.
  Hypothesis Hsp : (0 < spare A6 /\ ms_vm s1 = ms_vm s6 /\ a_areas A1 = a_areas A6 /\ spare A1 = spare A6 - 1)
                   \/ (spare A6 = 0 /\ a_areas A1 = a_areas A6 ++ [m - 24] /\ a_ctx A1 KAmc = 100 /\ a_freelist A1 = []).
  Hypothesis HGR : am_grow (ms_vm s6) (ms_vm s1).   (* [comment removed for export] *)

  Lemma L_facts : 0 < L /\ n + 20 <= L /\ L <= n + 20 + 4095 /\ L mod 4096 = 0.
  Proof.
    destruct (page_round_up_Z_spec (n + 20) ltac:(clear - Hn; unfold MMAP_THRESHOLD in Hn; lia)) as [[B1 B2] B3]. rewrite <- EL in *.
    unfold page_size in *. clear - B1 B2 B3 Hn. unfold MMAP_THRESHOLD in Hn. repeat split; try lia.
  Qed.

  Theorem big_ok :
    tsall W ((x <- (m_sd (at_ (Z_to_bv 64 m) 16) (Z_to_bv 64 p) ;;
                    m_sd (Z_to_bv 64 p) (Z_to_bv 64 m) ;;
                    m_sd (at_ (Z_to_bv 64 m) 32) (Z_to_bv 64 (L + 4064)) ;;
                    m_sw (at_ (Z_to_bv 64 m) 28) w0 ;;
                    m_sw (at_ (Z_to_bv 64 m) 24) w0 ;;
                    c <- m_lw (at_ A_LOCK 20) ;;
                    m_sw (at_ A_LOCK 20) (v_addi c 1) ;;
                    ctr <- m_lw (at_ A_LOCK 20) ;;
                    m_unlock ;;
                    m_enframe (Z_to_bv 64 m) w0 (Z_to_bv 64 n) ctr) ;; K x) s1) P.
  Proof.
    pose proof L_facts as (HL0 & HnL & HLn & HLm).
    assert (Hnn : 0 <= n /\ n + 20 <= L /\ L <= n + 20 + 4095) by (clear - HL0 HnL HLn Hn; unfold MMAP_THRESHOLD in Hn; lia).
    pose proof (ii_is HII0) as HI0. pose proof HI0 as [HW0 HRp0 HC0 HWIN0 HE0 HG0].
    pose proof (ii_is HII1) as HI1. pose proof HI1 as [HW1 HRp1 HC1 HWIN1 HE1 HG1].
    pose proof HGM as [GMm GMlo GMhi GMdom GMdd GMfresh GMgs GMav]. destruct GMm as (md & Hm & Hr & Hz).
    pose proof HR5 as [L5 Ar5 Pg5 Mb5 Xm5 Fl5 Ac5 Bk5 M5 C5 D5].
    pose proof GMgs as [GS1 GS2 GS3 GS4 GS5 GS6].
    pose proof layout_nums as LN. pose proof layout_small as LS. pose proof Hhr as HR'. unfold heap_range in HR'.
    assert (Hxm : a_xmaps A1 = [(p, L)]) by (rewrite Hxm1; unfold A6, xadd, set_xmaps; cbn [a_xmaps]; rewrite Xm5, Hxm0; reflexivity).
    assert (Hmaps6 : vm_maps (ms_vm s6) = (Z_to_bv 64 p, Z_to_bv 64 L) :: vm_maps (ms_vm s)) by (rewrite F6vm; apply vm_mmap_maps).
    assert (Hna6 : vm_noaccess (ms_vm s6) = vm_noaccess (ms_vm s)) by (rewrite F6vm; apply vm_mmap_noaccess).
    assert (Hin6 : In (Z_to_bv 64 p, Z_to_bv 64 L) (vm_maps (ms_vm s6))) by (rewrite Hmaps6; left; reflexivity).
    assert (Hrf6 : region_free (vm_noaccess (ms_vm s6)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true) by (rewrite Hna6; exact Gna).
    assert (Hin1 : In (Z_to_bv 64 p, Z_to_bv 64 L) (vm_maps (ms_vm s1))) by exact (amv_maps _ _ _ _ HAM _ _ Hin6).
    assert (Hrf1 : region_free (vm_noaccess (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true) by exact (amv_acc _ _ _ _ HAM _ _ Hin6 Hrf6).
    assert (Hdom6 : forall x, dom A6 x <-> dom A x) by (intros x; unfold A6, xadd, set_xmaps, dom; cbn [a_areas a_meta a_pages]; apply D5).
    assert (Hnodom1 : forall x, p <= x < p + L -> ~ dom A1 x).
    { intros x Hx Hd. pose proof (proj1 (Gdom x Hx)) as Hnd.
      assert (Hn6 : ~ dom A6 x) by (intros H6; exact (proj1 (Gdom x Hx) (proj1 (Hdom6 x) H6))).
      apply (amv_newdom _ _ _ _ HAM x _ _ Hd Hn6 Hin6 Hrf6). rewrite !uZ by (clear - HR' LS HL0; lia). exact Hx. }
    assert (NOWN1 : forall x, p <= x < p + L -> ~ owned_of A1 x).
    { intros x Hx [Hc | Hd]; [pose proof ctx_block_rw as CB; clear - CB Hc Hx HR' LN; unfold CTX_END in *; lia | exact (Hnodom1 x Hx Hd)]. }
    assert (Hzero1 : forall a : word, p <= u a < p + L -> ms_mem s1 a = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite (fr_mem _ _ _ _ HFR1 a (NOWN1 (u a) Ha)) by (clear - Ha HR' LN; lia). exact (F6zero a Ha). }
    (* [comment removed for export] *)
    apply (tw_lift_leaves W _ s1 (fun x s' => tsall W (K x s') P)); [| intros x s' H; exact H].
    apply (big_stores_ok sp0 argv envp cb A1 s1 m md p L n HII1 Hm Hhr Hzero1 Hnn).
    intros cv m' Hcv RW.
    destruct (big_handover sp0 argv envp cb A1 s1 m md p L n HII1 Hm Hr Hz Hxm Hpal Hhr HLm Hin1 Hrf1 Hnodom1 Hzero1 Hnn cv Hcv m' RW)
      as (HII2 & HFR2 & MEM2 & ZERO2).
    set (B := bigA A1 m p L cv) in *. set (s2 := upd s1 m' (ms_vm s1)) in *.
    pose proof (ii_is HII2) as HI2. pose proof HI2 as [HW2 HRp2 HC2 HWIN2 HE2 HG2].
    apply ts_unlock; [exact (envok_statics _ _ _ _ HE2) | exact HWIN2 |].
    (* [comment removed for export] *)
    pose proof (slot0 p L n HLm Hnn) as [S0 E0]. pose proof (bmt_stride p L n HLm Hnn) as Hsd.
    pose proof (bmt_sc p L n HLm Hnn) as Hsc63. pose proof (bmt_last p L n HLm Hnn) as Hlast0. pose proof (bmt_maplen_pos p L n HLm Hnn) as Hmlp.
    pose proof (bmt_maplen p L n HLm Hnn) as HmlEq.
    pose proof (bigA_m A1 m p L cv) as HBm. fold B in HBm. pose proof (bmt_role p L) as Hrole. set (mt := bmt p L) in *.
    rewrite w0_eq.
    apply (tsafe_leaves_of_cps (m_enframe (Z_to_bv 64 m) (Z_to_bv 64 0) (Z_to_bv 64 n) (w32 cv)) s2). intros K' P' HK'.
    apply (enframe_II sp0 argv envp cb [] B s2 HII2 m mt (ir_aib 0 0) (ir_slots 1) 0 n (w32 cv) HBm Hrole eq_refl ltac:(lia) ltac:(rewrite Hsd; clear - HL0 HnL HLn Hn; unfold MMAP_THRESHOLD in Hn; lia) K' P').
    intros off s3 Hoff. cbv zeta. intros HII3 NF3 Hfr3 Hpay3. apply HK'. clear HK' K' P'.
    rewrite S0 in *. rewrite E0 in *. rewrite Hsd in Hoff.
    set (res := p + 16 + 16 * off) in *.
    set (A3 := slot_set B m 0 (SLive off n) (lupd (a_live B) res (Some n))) in *.
    pose proof (ii_is HII3) as HI3. pose proof HI3 as [HW3 HRp3 HC3 HWIN3 HE3 HG3].
    (* [comment removed for export] *)
    assert (A3_meta : forall x, a_meta A3 x = if Z.eq_dec x m then Some (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n])) else a_meta B x).
    { intros x. unfold A3, slot_set. rewrite HBm, Hrole. cbn [a_meta set_live ameta_upd set_meta list_set ir_slots repeat Z.to_nat Z.sub]. unfold aupd. reflexivity. }
    assert (A3_g : a_meta A3 m = Some (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n]))) by (rewrite A3_meta; destruct (Z.eq_dec m m); [reflexivity | contradiction]).
    assert (A3_other : forall x, x <> m -> a_meta A3 x = a_meta A1 x).
    { intros x Hx. rewrite A3_meta. destruct (Z.eq_dec x m); [contradiction|]. unfold B. apply (bigA_other A1 m p L cv x Hx). }
    assert (A3_eq : a_ctx A3 = a_ctx B /\ a_areas A3 = a_areas A1 /\ a_pages A3 = a_pages A1 /\ a_xmaps A3 = [] /\
                    a_freelist A3 = a_freelist A1 /\ a_active A3 = a_active A1 /\ a_live A3 = lupd (a_live A1) res (Some n)).
    { unfold A3, slot_set. rewrite HBm, Hrole. repeat split; reflexivity. }
    destruct A3_eq as (E_ctx & E_areas & E_pages & E_xm & E_fl & E_act & E_live).
    assert (Hoff16 : 0 <= 16 * off <= L - 16 - n - 4).
    { pose proof (Z.div_mod (L - 16 - n - 4) 16 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (L - 16 - n - 4) 16 ltac:(lia)) as D2.
      set (d := (L - 16 - n - 4) / 16) in *. clearbody d. set (r := (L - 16 - n - 4) mod 16) in *. clearbody r.
      clear - Hoff D1 D2. lia. }
    assert (Hres : p + 16 <= res /\ res + n + 4 <= p + L) by (subst res; clear - Hoff16; lia).
    assert (Hup : u (Z_to_bv 64 res) = res) by (apply uZ; clear - Hres HR' LS Hn; unfold MMAP_THRESHOLD in Hn; lia).
    assert (DOMB : forall x, dom B x <-> dom A1 x \/ p <= x < p + L) by (intros x; unfold B; apply (dom_bigA A1 m md p L n Hm Hr HLm Hnn cv x)).
    assert (DOM3 : forall x, dom A3 x <-> dom B x).
    { intros x. unfold dom. rewrite E_areas, E_pages. replace (a_areas B) with (a_areas A1) by reflexivity. replace (a_pages B) with (a_pages A1) by reflexivity. split; intros Hd.
      - destruct Hd as [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | Hpg]]; [left; exact Ha | right; left | right; right; exact Hpg].
        rewrite A3_meta in Hy. destruct (Z.eq_dec y m) as [-> | Hne].
        + injection Hy as <-. cbn in Hry. injection Hry as <- <-. exists m, mt, (ir_aib 0 0), (ir_slots 1). split; [exact HBm|]. split; [exact Hrole|]. exact (conj Hml Hx).
        + exists y, mty, aiby, sly. auto.
      - destruct Hd as [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | Hpg]]; [left; exact Ha | right; left | right; right; exact Hpg].
        destruct (Z.eq_dec y m) as [-> | Hne].
        + rewrite HBm in Hy. injection Hy as <-. rewrite Hrole in Hry. injection Hry as <- <-.
          eexists m, _, (ir_aib 0 0), [SLive off n]. split; [exact A3_g|]. split; [reflexivity|]. exact (conj Hml Hx).
        + exists y, mty, aiby, sly. rewrite A3_meta. destruct (Z.eq_dec y m); [contradiction|]. auto. }
    (* [comment removed for export] *)
    assert (LIVE1 : a_live A1 = a_live A) by (rewrite GS5; unfold A6, xadd, set_xmaps; cbn [a_live]; exact L5).
    assert (LIVEA : a_live A res = None).
    { destruct (a_live A res) as [k|] eqn:E; [exfalso | reflexivity].
      apply (proj1 (Gdom res ltac:(clear - Hres Hn; unfold MMAP_THRESHOLD in Hn; lia))).
      pose proof (proj1 (wf_live_map A HW0 _ _) E) as (ma & mta & aiba & sla & i & offa & Hma & Hra & Hi0 & Hi & Ep).
      pose proof (live_geom A HW0 ma mta aiba sla i offa k Hma Hra Hi0 Hi) as (q & Hq & Hk & Ho & Hfit & _ & _ & G1 & G2 & G3 & G4 & _).
      apply (grp_dom A ma mta aiba sla res HW0 Hma Hra). rewrite Ep. clear - Hk Ho Hfit G1 G2 G3 G4. lia. }
    (* [comment removed for export] *)
    assert (GRPA : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta A1 x = Some mtx /\ x <> m).
    { intros x mtx aibx slx Hx Hrx. assert (H6 : a_meta A6 x = Some mtx) by (unfold A6, xadd, set_xmaps; cbn [a_meta]; rewrite M5; exact Hx).
      pose proof (GS1 x mtx aibx slx H6 Hrx) as H1. split; [exact H1|]. intros ->. rewrite Hm in H1. injection H1 as ->. rewrite Hr in Hrx. discriminate. }
    assert (GRPB : forall x mtx aibx slx, a_meta A1 x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta A x = Some mtx).
    { intros x mtx aibx slx Hx Hrx. pose proof (GS2 x mtx aibx slx Hx Hrx) as H6. unfold A6, xadd, set_xmaps in H6. cbn [a_meta] in H6. rewrite M5 in H6. exact H6. }
    assert (OWN01 : forall x, owned_of A x -> owned_of A1 x).
    { intros x Hx. apply (fr_owned _ _ _ _ HFR1). destruct Hx as [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (Hdom6 x)). exact Hd. }
    assert (DOM01 : forall x, dom A x -> dom A1 x).
    { intros x Hd. destruct (OWN01 x (or_intror Hd)) as [Hc | Hd1]; [exfalso | exact Hd1].
      pose proof (dom_heap A x HW0 Hd) as (lo & hi & Hh & Hlh). unfold heap_range in Hh. clear - Hc Hh Hlh LN. unfold CTX_END in *. lia. }
    assert (Hvm2 : ms_vm s3 = ms_vm s1) by (rewrite (nf_vm _ _ _ NF3); reflexivity).
    assert (Hsp6 : spare A6 = spare A) by (unfold spare, A6, xadd, set_xmaps; cbn [a_ctx a_freelist]; rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5; reflexivity).
    assert (Har6 : a_areas A6 = a_areas A) by (unfold A6, xadd, set_xmaps; cbn [a_areas]; exact Ar5).
    assert (Hsp3 : spare A3 = spare A1) by (unfold spare; rewrite E_ctx, E_fl; unfold B; rewrite (bigA_ctx A1 m p L cv), (bc2_other A1 cv KAmc) by discriminate; reflexivity).
    (* [comment removed for export] *)
    pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3 & M4 & Mdom).
    assert (ZOWN : forall a : word, (LOCKA + 8 <= u a < LOCKA + 936) \/ (m <= u a < m + 40) \/ (p <= u a < p + 8) -> owned_of B (u a)).
    { intros a [Hc | [Hmm | Hp]]; [left; clear - Hc LN; unfold CTX_END; lia | right | right]; apply (proj2 (DOMB (u a))).
      - left. replace (u a) with (m + (u a - m)) by lia. apply Mdom. clear - Hmm; lia.
      - right. clear - Hp HnL Hn; unfold MMAP_THRESHOLD in Hn; lia. }
    (* [comment removed for export] *)
    apply (HL s3 A3 (Z_to_bv 64 res) HII3).
    - (* [comment removed for export] *) constructor.
      + rewrite (nf_lo _ _ _ NF3). unfold s2. cbn [ms_lo upd]. rewrite (fr_lo _ _ _ _ HFR1). exact F6lo.
      + rewrite (nf_hi _ _ _ NF3). unfold s2. cbn [ms_hi upd]. rewrite (fr_hi _ _ _ _ HFR1). exact F6hi.
      + intros x Hx. destruct (OWN01 x Hx) as [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (DOM3 x)). apply (proj2 (DOMB x)). left. exact Hd.
      + intros a Hno Herr.
        assert (HnoB : ~ owned_of B (u a)) by (intros [Hc | Hd]; apply Hno; [left; exact Hc | right; apply (proj2 (DOM3 (u a))); exact Hd]).
        assert (Hno1 : ~ owned_of A1 (u a)) by (intros [Hc | Hd]; apply HnoB; [left; exact Hc | right; apply (proj2 (DOMB (u a))); left; exact Hd]).
        assert (HnoA : ~ owned_of A (u a)) by (intros Ho; exact (Hno1 (OWN01 _ Ho))).
        assert (Hnp : ~ (p <= u a < p + L)) by (intros Hp; apply HnoB; right; apply (proj2 (DOMB (u a))); right; exact Hp).
        rewrite (nf_mem _ _ _ NF3 a HnoB). unfold s2. cbn [ms_mem upd].
        destruct (MEM2 a) as [-> | Hw]; [| exfalso; exact (HnoB (ZOWN a Hw))].
        rewrite (fr_mem _ _ _ _ HFR1 a Hno1 Herr). exact (F6mem a HnoA Hnp).
      + intros q k Hq. rewrite E_live. unfold lupd. destruct (Z.eq_dec q res) as [-> | Hne]; [rewrite LIVEA in Hq; discriminate|]. rewrite LIVE1. exact Hq.
      + intros q k a Hq Ha.
        assert (HqB : a_live B q = Some k) by (unfold B; rewrite (bigA_live A1 m p L cv), LIVE1; exact Hq).
        rewrite (nf_live _ _ _ NF3 q k a HqB Ha). unfold s2. cbn [ms_mem upd].
        pose proof (live_dom A q k (u a) HW0 Hq Ha) as Hd. pose proof (dom_heap A (u a) HW0 Hd) as (lo & hi & Hh & Hlh). unfold heap_range in Hh.
        destruct (MEM2 a) as [-> | [Hc | [Hmm | Hp]]].
        * assert (Hq6 : a_live A6 q = Some k) by (unfold A6, xadd, set_xmaps; cbn [a_live]; rewrite L5; exact Hq).
          rewrite (fr_livemem _ _ _ _ HFR1 q k a Hq6 Ha). exact (F6live q k a Hq Ha).
        * exfalso. clear - Hc Hh Hlh LN. unfold CTX_END in *. lia.
        * exfalso. rewrite <- LIVE1 in Hq. exact (proj2 (meta_dom_nolive A1 m md (u a) HW1 Hm ltac:(clear - Hmm; lia)) q k Hq Ha).
        * exfalso. exact (proj1 (Gdom (u a) ltac:(clear - Hp HnL Hn; unfold MMAP_THRESHOLD in Hn; lia)) Hd).
      + intros a Ha. apply (nf_mapped _ _ _ NF3). unfold s2. cbn [ms_mem upd]. apply (fr_mapped _ _ _ _ HFR2). apply (fr_mapped _ _ _ _ HFR1). exact (F6mapped a Ha).
      + rewrite Hvm2, (fr_limit _ _ _ _ HFR1), F6vm. apply vm_mmap_limit.
    - exact E_xm.
    - intros c Hc. rewrite E_act, (GS4 c). unfold A6, xadd, set_xmaps. cbn [a_active]. rewrite Ac5. exact (Hact c Hc).
    - exact (eo_lock _ _ _ _ HE3).
    - (* [comment removed for export] *) constructor.
      + rewrite Hvm2. apply (vm_fixed_of A B _ _ (ii_vm HII0) (ii_vm HII2)). unfold s2. cbn [ms_vm upd]. rewrite (fr_limit _ _ _ _ HFR1), F6vm. apply vm_mmap_limit.
      + intros b sz Hb. rewrite Hvm2. apply (amv_maps _ _ _ _ HAM). rewrite Hmaps6. right. exact Hb.
      + intros b sz Hb Hf. rewrite Hvm2. apply (amv_acc _ _ _ _ HAM); [rewrite Hmaps6; right; exact Hb | rewrite Hna6; exact Hf].
      + intros Hpre. rewrite Hvm2.
        assert (HL6 : vm_live_bytes (ms_vm s6) = vm_live_bytes (ms_vm s) + L) by (rewrite F6vm, vm_mmap_live_bytes, uZ by (clear - HL0 HR' LS; lia); reflexivity).
        destruct Hsp as [(_ & Evm & _ & _) | (Hsp0 & _ & _ & _)].
        * rewrite Evm, HL6. clear - Hnn. lia.
        * assert (Har0 : a_areas A6 = []) by (rewrite Har6; destruct Hpre as [E | H4]; [exact E | exfalso; rewrite Hsp6 in Hsp0; clear - H4 Hsp0; lia]).
          pose proof (amv_budget _ _ _ _ HAM Har0) as Bud. rewrite HL6 in Bud. clear - Bud Hnn. lia.
    - (* [comment removed for export] *)
      right. rewrite Hup. split; [clear - Hres HR'; lia|]. exists m, 0, off. constructor.
      + (* [comment removed for export] *) constructor.
        * intros x mtx Hx Hrx. exfalso. destruct (proj1 (ii_dd HII0 x) (ex_intro _ mtx (conj Hx Hrx))).
        * intros x Hd. apply (proj2 (DOM3 x)). apply (proj2 (DOMB x)). left. exact (DOM01 x Hd).
        * intros x Hd. apply (proj1 (DOM3 x)) in Hd. apply (proj1 (DOMB x)) in Hd. destruct Hd as [Hd | Hp].
          -- destruct Hd as [(pg & Hpg & Hx) | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | (pg & Hpg & Hx)]].
             ++ right; right. exists pg. rewrite E_areas. split; [left; exact Hpg | exact Hx].
             ++ left. right; left. exists y, mty, aiby, sly. split; [exact (GRPB y mty aiby sly Hy Hry) | auto].
             ++ right; right. exists pg. rewrite E_pages. split; [right; exact Hpg | exact Hx].
          -- right; left. exact (proj2 (Gdom x Hp)).
        * rewrite E_xm, Hxm0. reflexivity.
        * intros x mtx aibx slx Hx Hrx. destruct (GRPA x mtx aibx slx Hx Hrx) as [Hx1 Hne].
          exists mtx, aibx, slx. rewrite (A3_other x Hne). repeat split; auto.
        * intros Hpre. rewrite E_areas, Hsp3.
          destruct Hsp as [(_ & _ & Ear & Esp) | (Hsp0 & Ear & Eamc & Efl)].
          -- left. rewrite Ear, Har6, Esp, Hsp6. split; [reflexivity | clear; lia].
          -- right. rewrite Hsp6 in Hsp0. assert (Ea0 : a_areas A = []) by (destruct Hpre as [E | H4]; [exact E | exfalso; clear - H4 Hsp0; lia]).
             split; [exact Ea0|]. split; [exists (m - 24); rewrite Ear, Har6, Ea0; reflexivity|]. unfold spare. rewrite Eamc, Efl. cbn. clear; lia.
      + (* [comment removed for export] *) intros q. rewrite E_live, LIVE1. unfold lupd. reflexivity.
      + exact LIVEA.
      + (* [comment removed for export] *) eexists _, (ir_aib 0 0), [SLive off n]. split; [exact A3_g|]. split; [reflexivity|].
        split; [change (mt_last (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n]))) with (mt_last mt); rewrite Hlast0; clear; lia|].
        split; [reflexivity|]. split; [change (slot_start (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n])) 0) with (slot_start mt 0); rewrite S0; reflexivity|].
        right. change (mt_sc (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n]))) with (mt_sc mt). exact Hsc63.
      + (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (Z.eq_dec x m) as [-> | Hxg]; [right; left; reflexivity | left].
        rewrite (A3_other x Hxg) in Hx. exists mtx, aibx, slx. split; [exact (GRPB x mtx aibx slx Hx Hrx) | exact Hrx].
      + (* [comment removed for export] *) intros mtx aibx slx Hx Hrx _. rewrite A3_g in Hx. injection Hx as <-. cbn in Hrx. injection Hrx as <- <-.
        change (mt_last (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n]))) with (mt_last mt).
        change (mt_sc (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n]))) with (mt_sc mt).
        unfold grp_map_len. change (mt_maplen (MT (mt_f mt) (RGroup (ir_aib 0 0) [SLive off n]))) with (mt_maplen mt). rewrite Hlast0, Hsc63.
        split; [reflexivity|]. split; [reflexivity|].
        split; [| split; [intros _; split; [reflexivity | split; [reflexivity | split; [exact Hmlp | rewrite HmlEq, <- EL; pose proof (proj2 (Z.div_exact L 4096 ltac:(clear; lia)) HLm) as DX; clear - DX; lia]]]
                        | split; intros Hsmall; exfalso; clear - Hsmall Hn; lia]].
        intros _ x mtx aibx slx Hx Hrx Hxg. rewrite (A3_other x Hxg) in Hx. exists mtx, aibx, slx. split; [exact (GRPB x mtx aibx slx Hx Hrx) | exact Hrx].
      + (* [comment removed for export] *) intros _ a Ha. rewrite (Hpay3 a Ha). unfold s2. cbn [ms_mem upd]. apply ZERO2. clear - Ha Hres; lia.
      + (* [comment removed for export] *) intros mtx aibx slx _ _ _. rewrite E_areas, Hsp3.
        destruct Hsp as [(Hpos & _ & Ear & Esp) | (Hsp0 & Ear & Eamc & Efl)].
        * left. rewrite Ear, Har6, Esp, Hsp6. split; [reflexivity | clear; lia].
        * right. rewrite Hsp6 in Hsp0. split; [clear - Hsp0; lia|]. split; [exists (m - 24); rewrite Ear, Har6; reflexivity|]. unfold spare. rewrite Eamc, Efl. cbn. clear; lia.
    - intros HWf _. exfalso. exact (HWs HWf).
    - intros _ H0. exfalso. rewrite Hup in H0. clear - H0 Hres HR'. lia.
    - (* [comment removed for export] *)
      unfold malloc_growS. rewrite Hvm2. rewrite (malloc_db_big n (proj1 Hn)).
      assert (G6 : sgrow 1 L 0 A A6 (ms_vm s) (ms_vm s6)).
      { rewrite F6vm. apply (grow_mmap A A6 (ms_vm s) p L (ii_vm HII0)); [clear - HR'; lia | clear - HL0; lia | clear - HR' LS; lia | exact Har6 | rewrite Hsp6; apply Z.le_refl]. }
      assert (G1 : sgrow 1 8192 1 A6 A3 (ms_vm s6) (ms_vm s1)).
      { (* [comment removed for export] *)
        replace 1 with (1 + 0) by reflexivity. replace 8192 with (8192 + 0) by reflexivity.
        apply (sgrow_trans _ _ _ _ _ _ A6 A1 A3 (ms_vm s6) (ms_vm s1) (ms_vm s1) (sgrow_am A6 A1 _ _ (m - 24) HGR Hsp)).
        apply sgrow_same; [reflexivity | exact E_areas | rewrite Hsp3; apply Z.le_refl]. }
      pose proof (sgrow_trans _ _ _ _ _ _ A A6 A3 _ _ _ G6 G1) as GT.
      split; [apply (sgrow_weaken (1 + 1) (L + 8192) (0 + 1)); [exact GT | clear; lia | clear - HLn Hn; unfold MMAP_THRESHOLD in Hn; lia | clear; lia| clear; lia]|].
      (* [comment removed for export] *)
      rewrite (malloc_dp_big n (proj1 Hn)).
      apply (pgrow_weaken (L + 8192 + META_COST)); [| unfold META_COST; clear - HLn; lia].
      apply pgrow_backed1; [pose proof (sg_backed _ _ _ _ _ _ _ GT) as BK; clear - BK; lia | |].
      2: { (* [comment removed for export] *)
           rewrite Hsp3, <- Hsp6. destruct Hsp as [(_ & _ & _ & Esp) | (Hsp0 & _ & Eamc & Efl)]; [rewrite Esp; apply Z.le_refl|].
           rewrite Hsp0. unfold spare. rewrite Eamc, Efl. cbn. clear; lia. }
      rewrite (pot_keep_meta A A3 HW0); [apply Z.le_refl | |].
      + intros c _. rewrite E_act, (GS4 c). unfold A6, xadd, set_xmaps. cbn [a_active]. rewrite Ac5. reflexivity.
      + intros x mtx aibx slx Hx Hrx. destruct (GRPA x mtx aibx slx Hx Hrx) as [H1x Hxnm]. exists mtx, aibx.
        split; [rewrite (A3_other x Hxnm); exact H1x | exact Hrx].
    - intros _ H0. exfalso. rewrite Hup in H0. clear - H0 Hres HR'. lia.
  Qed.
End BigOk.

End WithLayout.
