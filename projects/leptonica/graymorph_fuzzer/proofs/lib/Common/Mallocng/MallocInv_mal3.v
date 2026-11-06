(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_vmops MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_hints MallocInv_sc
  MallocInv_enframe MallocInv_ameta_iface MallocInv_ameta5 MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_freetop MallocInv_take
  MallocInv_sc3 MallocInv_aslot_iface MallocInv_ametax_iface MallocInv_malloc_iface MallocInv_agm2 MallocInv_agm3 MallocInv_mal1 MallocInv_efII MallocSureCap MallocSureCredit MallocSurePot.
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

Definition MLeaf (W : wmode) {R : Type} (sp0 : word) (argv envp : list (list byte)) (cb : list byte)
           (A : astate) (s : mstate) (n : Z) (K : word -> M R) (P : R -> mstate -> Prop) : Prop :=
  forall s' A' (res : word),
    II sp0 argv envp cb [] A' s' -> FR A s A' s' -> a_xmaps A' = [] -> ACT48 A' ->
    (forall i, 0 <= i < 8 -> ms_mem s' (Z_to_bv 64 (LOCKA + i)) = None) ->
    malloc_vm A n s s' ->
    malloc_rel A A' n res (ms_mem s) s' ->
    (W = WFail -> u res <> 0 -> aslot_had_idle A) ->
    (W = WOk -> u res = 0 -> malloc_noroom sp0 argv envp cb A s n) ->
    (* [comment removed for export] *)
    malloc_growS n A A' s s' ->
    (W <> WFail -> u res = 0 -> malloc_noroomS sp0 argv envp cb n A s) ->
    tsall W (K res s') P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_lts_wm1_w0 : c_lts wm1 w0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vm_fixed_of : forall A A' h h', VMok A h -> VMok A' h' -> vm_limit h' = vm_limit h -> vm_fixed h h'.
Proof.
  intros A A' h h' V V' Hl. unfold vm_fixed.
  pose proof (vm_top A h V) as T. pose proof (vm_top A' h' V') as T'.
  split; [exact Hl|]. split; [congruence|]. split.
  - unfold alloc_top in T, T'. rewrite <- (Z_to_bv_bv_unsigned 64 (vm_init_sp h')), <- (Z_to_bv_bv_unsigned 64 (vm_init_sp h)). f_equal. lia.
  - rewrite (vm_res A h V), (vm_res A' h' V'). reflexivity.
Qed.

Lemma FR_of_ntframe' : forall A A' s s', ntframe A s s' -> (forall x, owned_of A x -> owned_of A' x) ->
  (forall p n, a_live A p = Some n -> a_live A' p = Some n) -> FR A s A' s'.
Proof.
  intros A A' s s' [L1 H1 V1 M1 P1 Q1] Ho Hl. constructor.
  - exact L1. - exact H1. - exact Ho.
  - intros a Hno _. apply M1. intros Hox. exact (Hno (Ho _ Hox)).
  - exact Hl. - exact P1. - exact Q1.
  - rewrite V1. reflexivity.
Qed.

Lemma nest_rank_pos : forall c, 0 < nest_rank c -> c = 15 \/ c = 19 \/ c = 23.
Proof.
  intros c H. unfold nest_rank in H.
  destruct (Z.eqb_spec c 15); [auto|]. destruct (Z.eqb_spec c 19); [auto|]. destruct (Z.eqb_spec c 23); [auto | lia].
Qed.

Lemma nest_rank_range : forall c, 0 <= nest_rank c <= 3.
Proof. intros c. unfold nest_rank. destruct (c =? 15); [lia|]. destruct (c =? 19); [lia|]. destruct (c =? 23); lia. Qed.

(* [comment removed for export] *)
Lemma malloc_keep_of_aslot : forall A A' sc m0, aslot_keep A A' sc m0 -> a_xmaps A = [] -> malloc_keep A A' m0.
Proof.
  intros A A' sc m0 K Hx. pose proof (nest_rank_range sc) as Hnr. constructor.
  - exact (ak_dead _ _ _ _ K). - exact (ak_dom _ _ _ _ K). - exact (ak_newdom _ _ _ _ K).
  - rewrite (ak_xmaps _ _ _ _ K). reflexivity.
  - exact (ak_grp _ _ _ _ K).
  - intros Hpre. destruct (ak_acct _ _ _ _ K ltac:(destruct Hpre; [left; assumption | right; lia])) as [(E & S) | (E & Hpg & S)]; [left | right].
    + split; [exact E | lia].
    + split; [exact E|]. split; [exact Hpg | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fail.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (sp : word) (n : Z).
  Variables (K : word -> M R) (P : R -> mstate -> Prop).
  Hypothesis HII : II sp0 argv envp cb [] A s.
  Hypothesis Hxm : a_xmaps A = [].
  Hypothesis Hact : ACT48 A.
  Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
  Hypothesis HL : MLeaf W sp0 argv envp cb A s n K P.
  Variables (sc : Z) (A2 : astate) (s2 : mstate).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis HII2 : II sp0 argv envp cb [] A2 s2.
  Hypothesis HFR2 : FR A s A2 s2.
  Hypothesis HAF : aslot_fail A A2 sc (ms_mem s) .
  Hypothesis HAV : aslot_vm A sc s s2.
  Hypothesis Hnoroom : W = WOk -> aslot_noroom sp0 argv envp cb A s.
  (* [comment removed for export] *)
  Hypothesis HGS : aslot_growS sc A A2 s s2.
  Hypothesis HnoroomS : W <> WFail -> aslot_noroomS sp0 argv envp cb sc A s.
  (* [comment removed for export] *)
  Hypothesis Hclsn : sc = size_to_class_z n \/ sc = size_to_class_z n + 1.

  Theorem fail_leaf :
    tsall W ((gi <- (m_unlock ;; mret (@None (word * word)%type)) ;; r <- mal_fin (Z_to_bv 64 n) gi ;; K r) s2) P.
  Proof.
    pose proof (ii_is HII2) as HI2. pose proof HI2 as [HW2 HR2 HC2 HWIN2 HE2 HG2].
    apply tsall_assoc.
    eapply (tw_det W _ s2 _ P tt s2); [intros K' P' HK'; apply ts_unlock; [exact (envok_statics _ _ _ _ HE2) | exact HWIN2 | exact HK'] |].
    apply tw_bind_ret. unfold mal_fin. apply tw_bind_ret.
    pose proof (af_keep _ _ _ _ HAF) as KP. pose proof (nest_rank_range sc) as Hnr.
    apply (HL s2 A2 w0 HII2 HFR2).
    - rewrite (ak_xmaps _ _ _ _ KP). exact Hxm.
    - intros c Hc. rewrite (ak_act _ _ _ _ KP c ltac:(clear - Hc Hsc; lia)); [apply Hact; exact Hc|].
      pose proof (nest_rank_range c). unfold nest_rank at 1. destruct (Z.eqb_spec c 15); [exfalso; clear - Hc e; lia|].
      destruct (Z.eqb_spec c 19); [exfalso; clear - Hc e; lia|]. destruct (Z.eqb_spec c 23); [exfalso; clear - Hc e; lia|]. clear - Hnr. lia.
    - exact (eo_lock _ _ _ _ HE2).
    - constructor.
      + exact (vm_fixed_of A A2 _ _ (ii_vm HII) (ii_vm HII2) (fr_limit _ _ _ _ HFR2)).
      + exact (av_maps _ _ _ _ HAV). + exact (av_acc _ _ _ _ HAV).
      + intros Hpre. pose proof (av_budget _ _ _ _ HAV ltac:(destruct Hpre; [left; assumption | right; lia])) as B.
        pose proof (proj1 (proj1 (page_round_up_Z_spec (n + 20) ltac:(clear - Hn; lia)))). clear - B Hnr H Hn. unfold MMAP_THRESHOLD in Hn. lia.
    - left. split; [reflexivity|]. constructor.
      + exact (malloc_keep_of_aslot A A2 sc _ KP Hxm).
      + exact (ak_live _ _ _ _ KP).
      + exact (af_slots _ _ _ _ HAF). + exact (af_grp_back _ _ _ _ HAF).
      + destruct (af_acct0 _ _ _ _ HAF) as [L | (S1 & Pg & S2)]; [left; exact L | right]. split; [pose proof (nest_rank_range sc) as NR; clear - S1 NR; lia|]. split; [exact Pg | exact S2].
    - intros _ H0. exfalso. apply H0. reflexivity.
    - intros HWk _. left. exact (Hnoroom HWk).
    - (* [comment removed for export] *)
      unfold malloc_growS. unfold aslot_growS in HGS. destruct HGS as [HGS0 HPS]. rewrite (malloc_db_small n (proj2 Hn)).
      pose proof (malloc_cap_cls n sc Hclsn) as Hcap.
      split; [apply (sgrow_weaken _ _ _ _ _ _ _ _ _ _ HGS0); clear - Hnr Hn Hcap; lia|].
      exact (pgrow_weaken _ _ _ _ _ _ HPS (malloc_dp_cls n sc (proj2 Hn) Hclsn)).
    - (* [comment removed for export] *)
      intros HWnf _. unfold malloc_noroomS. pose proof (HnoroomS HWnf) as X. unfold aslot_noroomS in X. rewrite (malloc_db_small n (proj2 Hn)).
      pose proof (malloc_cap_cls n sc Hclsn) as Hcap.
      apply (snoroom_weaken _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X); clear - Hnr Hn Hcap; lia.
  Qed.
End Fail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ACT48_keep : forall A A' sc m0, 0 <= sc < 48 -> aslot_keep A A' sc m0 -> ACT48 A -> ACT48 A'.
Proof.
  intros A A' sc m0 Hsc KP Hact c Hc. rewrite (ak_act _ _ _ _ KP c ltac:(clear - Hc Hsc; lia)); [apply Hact; exact Hc|].
  pose proof (nest_rank_range sc) as Hnr. unfold nest_rank at 1.
  destruct (Z.eqb_spec c 15); [exfalso; clear - Hc e; lia|]. destruct (Z.eqb_spec c 19); [exfalso; clear - Hc e; lia|].
  destruct (Z.eqb_spec c 23); [exfalso; clear - Hc e; lia|]. clear - Hnr. lia.
Qed.

Section Ok.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (n : Z).
  Variables (K : word -> M R) (P : R -> mstate -> Prop).
  Hypothesis HII : II sp0 argv envp cb [] A s.
  Hypothesis Hxm : a_xmaps A = [].
  Hypothesis Hact : ACT48 A.
  Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
  Hypothesis HL : MLeaf W sp0 argv envp cb A s n K P.
  Variables (sc : Z) (A2 : astate) (s2 : mstate) (g idx : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hfit : n + 4 <= 16 * size_class sc.
  Hypothesis HII2 : II sp0 argv envp cb [] A2 s2.
  Hypothesis HFR2 : FR A s A2 s2.
  Hypothesis HAO : aslot_ok A A2 sc n g idx (ms_mem s) s2.
  Hypothesis HAV : aslot_vm A sc s s2.
  Hypothesis HGS : aslot_growS sc A A2 s s2.   (* [comment removed for export] *)
  Hypothesis Hmt : a_meta A2 g = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hgsc : mt_sc mt = sc.
  Hypothesis Hidx : 0 <= idx <= mt_last mt.
  Hypothesis Hslot : nth_error slots (Z.to_nat idx) = Some STaken.
  Hypothesis Hreq4 : n + 4 <= mt_stride mt.
  Hypothesis Hstr : 16 * size_class sc <= mt_stride mt \/ (mt_last mt = 0 /\ 0 < mt_maplen mt /\ mt_stride mt + 16 = page_round_up_Z (n + 20)).
  Hypothesis Hidle0 : forall mt0 aib0 sl0, a_meta A g = Some mt0 -> mt_role mt0 = RGroup aib0 sl0 -> nth_error sl0 (Z.to_nat idx) = Some SIdle.
  Hypothesis Hhook : W = WFail -> aslot_had_idle A.
  (* [comment removed for export] *)
  Hypothesis Hstc : 32 <= size_to_class_z n -> sc = size_to_class_z n.
  (* [comment removed for export] *)
  Hypothesis Hclsn : sc = size_to_class_z n \/ sc = size_to_class_z n + 1.

  Let KP := ao_keep _ _ _ _ _ _ _ _ HAO.

  Lemma ok_geom : 16 <= mt_stride mt < 2^20 /\ (exists q, mt_stride mt = 16 * q) /\ 0x1000 + 16 <= slot_start mt idx /\
                  slot_end mt idx + 4 <= alloc_ceiling /\ slot_end mt idx = slot_start mt idx + mt_stride mt - 4 /\ alloc_ceiling < 2^64 - 4096.
  Proof.
    pose proof (ii_is HII2) as [HW2 _ _ _ _ _].
    destruct (wf_grp A2 HW2 g mt aib slots Hmt Hr) as (Hw32 & _ & Hscx & Hlen & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _ & Hce & _).
    pose proof (stride_ge16 mt ltac:(lia) Hscx) as HS. pose proof (wf_stride20 A2 HW2 g mt aib slots Hmt Hr ltac:(rewrite Hgsc; clear - Hsc; lia)) as HS20.
    destruct (stride_16 mt) as [q Hq]. pose proof alloc_ceiling_val as HCV.
    assert (Hic : idx + 1 <= mt_cnt mt) by (unfold mt_cnt; clear - Hidx; lia).
    assert (GG : 0 <= idx * mt_stride mt /\ idx * mt_stride mt + mt_stride mt <= mt_cnt mt * mt_stride mt) by (clear - Hidx Hic HS; nia).
    unfold slot_start, slot_end, slot_start_g, slot_end_g. repeat split; try (clear - HS HS20 Hq GG Hmem Hce HCV; lia). exists q. exact Hq.
  Qed.

  Theorem ok_leaf : tsall W ((r <- mal_fin (Z_to_bv 64 n) (Some (Z_to_bv 64 g, Z_to_bv 64 idx)) ;; K r) s2) P.
  Proof.
    pose proof (ii_is HII2) as HI2. pose proof HI2 as [HW2 HR2 HC2 HWIN2 HE2 HG2]. pose proof (ii_is HII) as [HW _ _ _ _ _].
    pose proof ok_geom as (HS & (q & Hq) & Glo & Ghi & Ese & HCV).
    pose proof (nest_rank_range sc) as Hnr.
    unfold mal_fin. apply tsall_assoc. rewrite (addr_lock 20), <- caddr_KCtr_lock.
    pose proof (wf_ctx_nonneg A2 HW2 KCtr) as Hc0.
    eapply (tw_det W _ s2 _ P (w32 (a_ctx A2 KCtr)) s2).
    { intros K' P' HK'. apply (ts_lw_fact4 A2 s2 (caddr KCtr) (a_ctx A2 KCtr) K' P' HW2 HR2 HWIN2); [left; exists KCtr; split; [exact I | reflexivity] | exact Hc0 | exact HK']. }
    apply tsall_assoc.
    eapply (tw_det W _ s2 _ P tt s2); [intros K' P' HK'; apply ts_unlock; [exact (envok_statics _ _ _ _ HE2) | exact HWIN2 | exact HK'] |].
    (* [comment removed for export] *)
    eapply (tw_lift W (m_enframe (Z_to_bv 64 g) (Z_to_bv 64 idx) (Z_to_bv 64 n) (w32 (a_ctx A2 KCtr))) s2
              (fun x s3 => exists off, 0 <= off <= (mt_stride mt - n - 4) / 16 /\ x = Z_to_bv 64 (slot_start mt idx + 16 * off) /\
                 II sp0 argv envp cb [] (slot_set A2 g idx (SLive off n) (lupd (a_live A2) (slot_start mt idx + 16 * off) (Some n))) s3 /\
                 ntframe A2 s2 s3 /\ (forall a : word, u a < slot_start mt idx - 3 \/ slot_end mt idx <= u a -> ms_mem s3 a = ms_mem s2 a) /\
                 (forall a : word, slot_start mt idx + 16 * off <= u a < slot_start mt idx + 16 * off + n -> ms_mem s3 a = ms_mem s2 a))).
    { intros K' P' HK'. apply (enframe_II sp0 argv envp cb [] A2 s2 HII2 g mt aib slots idx n (w32 (a_ctx A2 KCtr)) Hmt Hr Hslot ltac:(clear - Hidx; lia) ltac:(clear - Hn Hreq4 HS; lia) K' P').
      intros off s3 Hoff. cbv zeta. intros HII3 NF3 Hfr3 Hpay3. apply HK'. exists off. auto 10. }
    intros x s3 (off & Hoff & -> & HII3 & NF3 & Hfr3 & Hpay3).
    set (p := slot_start mt idx + 16 * off) in *.
    set (A3 := slot_set A2 g idx (SLive off n) (lupd (a_live A2) p (Some n))) in *.
    set (sl3 := list_set slots (Z.to_nat idx) (SLive off n)).
    assert (Hilt : (Z.to_nat idx < length slots)%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hslot; discriminate).
    assert (A3_meta : forall x, a_meta A3 x = if Z.eq_dec x g then Some (MT (mt_f mt) (RGroup aib sl3)) else a_meta A2 x).
    { intros x. unfold A3, slot_set. rewrite Hmt, Hr. cbn [a_meta set_live ameta_upd set_meta]. unfold aupd. reflexivity. }
    assert (A3_g : a_meta A3 g = Some (MT (mt_f mt) (RGroup aib sl3))) by (rewrite A3_meta; destruct (Z.eq_dec g g); [reflexivity | contradiction]).
    assert (A3_other : forall x, x <> g -> a_meta A3 x = a_meta A2 x) by (intros x Hx; rewrite A3_meta; destruct (Z.eq_dec x g); [contradiction | reflexivity]).
    assert (A3_eq : a_ctx A3 = a_ctx A2 /\ a_areas A3 = a_areas A2 /\ a_pages A3 = a_pages A2 /\ a_mblocks A3 = a_mblocks A2 /\ a_xmaps A3 = a_xmaps A2 /\
                    a_freelist A3 = a_freelist A2 /\ a_active A3 = a_active A2 /\ a_live A3 = lupd (a_live A2) p (Some n)).
    { unfold A3, slot_set. rewrite Hmt, Hr. repeat split; reflexivity. }
    destruct A3_eq as (E_ctx & E_areas & E_pages & E_mb & E_xm & E_fl & E_act & E_live).
    assert (Hoff16 : 0 <= 16 * off <= mt_stride mt - n - 4 /\ 16 * off <= mt_stride mt - 16).
    { pose proof (Z.div_mod (mt_stride mt - n - 4) 16 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (mt_stride mt - n - 4) 16 ltac:(lia)) as D2.
      set (d := (mt_stride mt - n - 4) / 16) in *. clearbody d. set (r := (mt_stride mt - n - 4) mod 16) in *. clearbody r.
      clear - Hoff D1 D2 Hq Hn Hreq4. subst. lia. }
    assert (Hp : 0x1000 <= p /\ p + n <= slot_end mt idx /\ p + 16 <= slot_end mt idx + 4 /\ p < 2^64) by (subst p; clear - Hoff16 Glo Ghi Ese HCV Hn; lia).
    assert (Hup : u (Z_to_bv 64 p) = p) by (apply uZ; clear - Hp; lia).
    (* [comment removed for export] *)
    assert (FRESH : a_live A2 p = None).
    { destruct (a_live A2 p) as [k|] eqn:E; [exfalso | reflexivity].
      apply (proj1 (wf_live_map A2 HW2 p k)) in E. destruct E as (g' & mt' & aib' & sl' & j' & off' & Hg' & Hr' & Hj0' & Hj' & Ep).
      destruct (live_in_span_unique A2 g' mt' aib' sl' j' off' k g mt aib slots idx STaken HW2 Hg' Hr' Hj0' Hj' Hmt Hr ltac:(clear - Hidx; lia) Hslot
                 ltac:(intros ch; discriminate) ltac:(rewrite <- Ep; subst p; clear - Hoff16 Ese HS; lia)) as [-> ->].
      rewrite Hmt in Hg'. injection Hg' as <-. rewrite Hr in Hr'. injection Hr' as <- <-. rewrite Hslot in Hj'. discriminate. }
    assert (LIVEA : a_live A p = None) by (rewrite <- (ak_live _ _ _ _ KP); exact FRESH).
    assert (DOM3 : forall x, dom A3 x <-> dom A2 x).
    { intros x. unfold dom. rewrite E_areas, E_pages. split; intros Hd.
      - destruct Hd as [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | Hpg]]; [left; exact Ha | right; left | right; right; exact Hpg].
        rewrite A3_meta in Hy. destruct (Z.eq_dec y g) as [-> | Hne].
        + injection Hy as <-. cbn in Hry. injection Hry as <- <-. exists g, mt, aib, slots. auto.
        + exists y, mty, aiby, sly. auto.
      - destruct Hd as [Ha | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | Hpg]]; [left; exact Ha | right; left | right; right; exact Hpg].
        destruct (Z.eq_dec y g) as [-> | Hne].
        + rewrite Hmt in Hy. injection Hy as <-. rewrite Hr in Hry. injection Hry as <- <-. eexists g, _, aib, sl3. split; [exact A3_g|]. split; [reflexivity|]. exact (conj Hml Hx).
        + exists y, mty, aiby, sly. rewrite (A3_other y Hne). auto. }
    (* [comment removed for export] *)
    apply (HL s3 A3 (Z_to_bv 64 p) HII3).
    - (* [comment removed for export] *) apply (FR_trans A s A2 s2 A3 s3 HFR2). apply (FR_of_ntframe' A2 A3 s2 s3 NF3).
      + intros x [Hc | Hd]; [left; exact Hc | right; apply (proj2 (DOM3 x)); exact Hd].
      + intros q0 k Hq0. rewrite E_live. unfold lupd. destruct (Z.eq_dec q0 p) as [-> | Hne]; [rewrite FRESH in Hq0; discriminate | exact Hq0].
    - rewrite E_xm, (ak_xmaps _ _ _ _ KP). exact Hxm.
    - intros c Hc. rewrite E_act. exact (ACT48_keep A A2 sc _ Hsc KP Hact c Hc).
    - exact (eo_lock _ _ _ _ (is_env _ _ _ _ _ _ (ii_is HII3))).
    - (* [comment removed for export] *) constructor.
      + rewrite (nf_vm _ _ _ NF3). exact (vm_fixed_of A A2 _ _ (ii_vm HII) (ii_vm HII2) (fr_limit _ _ _ _ HFR2)).
      + intros b sz Hb. rewrite (nf_vm _ _ _ NF3). exact (av_maps _ _ _ _ HAV b sz Hb).
      + intros b sz Hb Hf. rewrite (nf_vm _ _ _ NF3). exact (av_acc _ _ _ _ HAV b sz Hb Hf).
      + intros Hpre. rewrite (nf_vm _ _ _ NF3). pose proof (av_budget _ _ _ _ HAV ltac:(destruct Hpre; [left; assumption | right; lia])) as B.
        pose proof (proj1 (proj1 (page_round_up_Z_spec (n + 20) ltac:(clear - Hn; lia)))). clear - B Hnr H Hn. unfold MMAP_THRESHOLD in Hn. lia.
    - (* [comment removed for export] *)
      right. rewrite Hup. split; [clear - Hp; lia|]. exists g, idx, off. constructor.
      + (* [comment removed for export] *) constructor.
        * intros x mtx Hx Hrx. pose proof (ak_dead _ _ _ _ KP x mtx Hx Hrx) as Hx2. rewrite (A3_other x); [exact Hx2|].
          intros ->. rewrite Hmt in Hx2. injection Hx2 as ->. rewrite Hr in Hrx. discriminate.
        * intros x Hd. apply (proj2 (DOM3 x)). exact (ak_dom _ _ _ _ KP x Hd).
        * intros x Hd. rewrite E_areas, E_pages. exact (ak_newdom _ _ _ _ KP x (proj1 (DOM3 x) Hd)).
        * rewrite E_xm. exact (ak_xmaps _ _ _ _ KP).
        * intros x mt0 aib0 sl0 Hx0 Hr0. destruct (ak_grp _ _ _ _ KP x mt0 aib0 sl0 Hx0 Hr0) as (mt2 & aib2 & sl2 & Hx2 & Hr2 & W2 & M2 & L2 & K2).
          destruct (Z.eq_dec x g) as [-> | Hne].
          -- rewrite Hmt in Hx2. injection Hx2 as <-. rewrite Hr in Hr2. injection Hr2 as <- <-.
             eexists _, aib, sl3. split; [exact A3_g|]. split; [reflexivity|]. split; [exact W2|]. split; [exact M2|].
             split; [unfold sl3; rewrite list_set_length; exact L2|].
             intros j st Hj Hst. unfold sl3. destruct (Nat.eq_dec (Z.to_nat idx) j) as [<- | Hnj].
             ++ exfalso. rewrite (Hidle0 mt0 aib0 sl0 Hx0 Hr0) in Hj. injection Hj as <-. exact (Hst eq_refl).
             ++ rewrite list_set_nth_other by exact Hnj. exact (K2 j st Hj Hst).
          -- exists mt2, aib2, sl2. rewrite (A3_other x Hne). auto 10.
        * intros Hpre. assert (Esp : spare A3 = spare A2) by (unfold spare; rewrite E_ctx, E_fl; reflexivity). rewrite E_areas, Esp.
          destruct (ak_acct _ _ _ _ KP ltac:(destruct Hpre; [left; assumption | right; clear - H Hnr; lia])) as [(E & S) | (E & Hpg & S)]; [left | right].
          -- split; [exact E | clear - S Hnr; lia].
          -- split; [exact E|]. split; [exact Hpg | clear - S Hnr; lia].
      + (* [comment removed for export] *) intros q0. rewrite E_live, (ak_live _ _ _ _ KP). unfold lupd. reflexivity.
      + exact LIVEA.
      + (* [comment removed for export] *) eexists _, aib, sl3. split; [exact A3_g|]. split; [reflexivity|]. split; [exact Hidx|].
        split; [unfold sl3; apply list_set_nth_same; exact Hilt|]. split; [reflexivity|]. left. change (mt_sc mt < 48). rewrite Hgsc. clear - Hsc; lia.
      + (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (Z.eq_dec x g) as [-> | Hxg]; [right; left; reflexivity|].
        rewrite (A3_other x Hxg) in Hx.
        destruct (ao_grp_back _ _ _ _ _ _ _ _ HAO x mtx aibx slx Hx Hrx) as [Hold | [E | (Hne & H48 & Hrk)]]; [left; exact Hold | exfalso; exact (Hxg E) | right; right].
        split; [exact Hne|]. apply nest_rank_pos. clear - Hrk Hnr. lia.
      + (* [comment removed for export] *) intros mtx aibx slx Hx Hrx Hnew. rewrite A3_g in Hx. injection Hx as <-. cbn in Hrx. injection Hrx as <- <-.
        destruct (ao_gfresh _ _ _ _ _ _ _ _ HAO mt aib slots Hmt Hr Hnew) as [-> Esl].
        split; [reflexivity|]. split.
        { unfold sl3. rewrite Esl. change (mt_last (MT (mt_f mt) (RGroup aib (list_set slots (Z.to_nat 0) (SLive off n))))) with (mt_last mt). reflexivity. }
        split; [| split; [intros Hbig; exfalso; clear - Hbig Hn; lia | split; [intros _ H32; change (mt_sc (MT (mt_f mt) (RGroup aib sl3))) with (mt_sc mt); rewrite Hgsc; exact (Hstc H32) |]]].
        * intros Hnn x mtx aibx slx Hx Hrx Hxg. rewrite (A3_other x Hxg) in Hx.
          destruct Hnn as [Hbig | Hsz]; [exfalso; clear - Hbig Hn; lia|]. change (mt_sc (MT (mt_f mt) (RGroup aib sl3))) with (mt_sc mt) in Hsz. rewrite Hgsc in Hsz.
          exact (ao_nonest _ _ _ _ _ _ _ _ HAO Hsz x mtx aibx slx Hx Hrx Hxg).
        * change (mt_sc (MT (mt_f mt) (RGroup aib sl3))) with (mt_sc mt). change (mt_last (MT (mt_f mt) (RGroup aib sl3))) with (mt_last mt).
          change (mt_maplen (MT (mt_f mt) (RGroup aib sl3))) with (mt_maplen mt). change (mt_stride (MT (mt_f mt) (RGroup aib sl3))) with (mt_stride mt). rewrite Hgsc.
          intros _ H38 Hm4 Hus Hlen. exact (ao_single _ _ _ _ _ _ _ _ HAO mt aib slots Hmt Hr Hnew H38 Hm4 Hus Hlen).
      + (* [comment removed for export] *) intros (ma & mta & aiba & sla & j & offa & na & Hma & Hra & Hj0 & Hja & Ep & Hz) a Ha.
        (* [comment removed for export] *)
        assert (Eg : ma = g /\ j = idx).
        { destruct (live_slot_unique A3 ma mta aiba sla j offa na g (MT (mt_f mt) (RGroup aib sl3)) aib sl3 idx off n
                      (is_wf _ _ _ _ _ _ (ii_is HII3)) Hma Hra Hj0 Hja A3_g eq_refl ltac:(clear - Hidx; lia)
                      ltac:(unfold sl3; apply list_set_nth_same; exact Hilt) ltac:(rewrite <- Ep; reflexivity)) as [E1 E2]. auto. }
        destruct Eg as [-> ->]. rewrite A3_g in Hma. injection Hma as <-.
        destruct Hz as [H48 | Hshort]; [exfalso; change (mt_sc (MT (mt_f mt) (RGroup aib sl3))) with (mt_sc mt) in H48; rewrite Hgsc in H48; clear - H48 Hsc; lia|].
        change (mt_stride (MT (mt_f mt) (RGroup aib sl3)) < 16 * size_class (mt_sc (MT (mt_f mt) (RGroup aib sl3)))) with (mt_stride mt < 16 * size_class (mt_sc mt)) in Hshort.
        rewrite Hgsc in Hshort.
        destruct Hstr as [Hge | (L0 & Mlen & Est)]; [exfalso; clear - Hge Hshort; lia|].
        assert (Hi0 : idx = 0) by (clear - Hidx L0; lia).
        rewrite (Hpay3 a) by (subst p; exact Ha).
        apply (ao_zero _ _ _ _ _ _ _ _ HAO mt aib slots Hmt Hr Hshort a).
        subst p. clear - Ha Hoff16 Ese Hn Hi0. subst idx. lia.
      + (* [comment removed for export] *) intros mtx aibx slx Hx Hrx Hcls. rewrite A3_g in Hx. injection Hx as <-.
        change (mt_sc (MT (mt_f mt) (RGroup aib sl3))) with (mt_sc mt) in Hcls. rewrite Hgsc in Hcls.
        destruct Hcls as [Hbig | Hsz]; [exfalso; clear - Hbig Hn; lia|].
        assert (Esp : spare A3 = spare A2) by (unfold spare; rewrite E_ctx, E_fl; reflexivity). rewrite E_areas, Esp.
        destruct (ao_acct1 _ _ _ _ _ _ _ _ HAO Hsz) as [L | (S1 & Pg & S2)]; [left; exact L | right].
        split; [pose proof (nest_rank_range sc) as NR; clear - S1 NR; lia|]. split; [exact Pg | exact S2].
    - intros HWf _. exact (Hhook HWf).
    - intros _ H0. exfalso. rewrite Hup in H0. clear - H0 Hp. lia.
    - (* [comment removed for export] *)
      unfold malloc_growS. unfold aslot_growS in HGS. destruct HGS as [HGS0 HPS]. rewrite (malloc_db_small n (proj2 Hn)).
      pose proof (malloc_cap_cls n sc Hclsn) as Hcap.
      split.
      { apply (sgrow_weaken (5 - nest_rank sc + 0) ((4 - nest_rank sc) * 8192 + grp_cap sc + 0) (4 - nest_rank sc + 0));
          [| clear - Hnr; lia | clear - Hnr Hcap; lia | clear - Hnr; lia| clear - Hnr; lia].
        apply (sgrow_trans _ _ _ _ _ _ A A2 A3 _ _ _ HGS0).
        apply sgrow_same; [exact (nf_vm _ _ _ NF3) | exact E_areas | unfold spare; rewrite E_ctx, E_fl; apply Z.le_refl]. }
      (* [comment removed for export] *)
      apply (pgrow_weaken (acostS sc + 0)); [| pose proof (malloc_dp_cls n sc (proj2 Hn) Hclsn) as HD; clear - HD; lia].
      apply (pgrow_trans _ _ A A2 A3 _ _ _ HPS). apply pgrow_pot; [exact (nf_vm _ _ _ NF3) | | unfold spare; rewrite E_ctx, E_fl; apply Z.le_refl].
      rewrite (pot_keep A2 A3 HW2 (fun c _ => f_equal (fun f => f c) E_act)); [apply Z.le_refl|].
      intros x mtx aibx slx Hx Hrx. destruct (Z.eq_dec x g) as [-> | Hxg].
      + rewrite Hmt in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
        rewrite (slots_of_grp A3 g _ aib sl3 A3_g eq_refl). unfold sl3.
        apply (count_idle_set_same slots (Z.to_nat idx) STaken); [exact Hslot | discriminate | discriminate].
      + unfold slots_of. rewrite (A3_other x Hxg), Hx, Hrx. reflexivity.
    - intros _ H0. exfalso. rewrite Hup in H0. clear - H0 Hp. lia.
  Qed.
End Ok.

End WithLayout.
