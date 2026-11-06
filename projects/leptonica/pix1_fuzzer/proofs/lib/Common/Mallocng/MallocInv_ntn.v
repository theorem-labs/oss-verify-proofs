(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf5 MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_tryavail MallocInv_ameta_base MallocInv_ameta_iface
  MallocInv_vmops MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_nt1 MallocInv_ntok MallocInv_usage
  MallocInv_ntfm MallocInv_ntd MallocInv_ntk MallocInv_ntg.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Lemma list_set_set : forall {T} (l : list T) k (a b : T), list_set (list_set l k a) k b = list_set l k b.
Proof. intros T l. induction l as [|x l IH]; intros k a b; [reflexivity|]. destruct k; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FgNested.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A1 : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D A1 s1.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A1 ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hidle : forall j st, nth_error slots j = Some st -> st = SIdle \/ st = STaken.
  Hypothesis Hnotact : forall c, ~ In ma (a_active A1 c).
  Hypothesis Hml : mt_maplen mt = 0.
  Hypothesis Hact48 : ACT48 A1.
  (* [comment removed for export] *)
  Variable rec : word -> word -> M (word * word).
  Hypothesis Hrec : forall D' A' s' pa pm paib psl j,
    II sp0 argv envp cb D' A' s' -> ACT48 A' -> a_meta A' pa = Some pm -> mt_role pm = RGroup paib psl ->
    nth_error psl (Z.to_nat j) = Some STaken -> 0 <= j -> (nfuel pm < nfuel mt)%nat ->
    tsafe (rec (Z_to_bv 64 pa) (Z_to_bv 64 j) s') (ntpost sp0 argv envp cb D' A' s' pa psl j).

  Let W := mt_w32 mt.
  Let sc := mt_sc mt.
  Let cnt := mt_cnt mt.
  Let mem := mt_mem mt.

  Lemma NW : WF A1. Proof. exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma Ngrp : 0 <= W < 2^64 /\ sc < 48 /\ 1 <= cnt <= 32 /\ cnt = W mod 32 + 1 /\ 0x1000 <= mem /\ 0 <= sc < 64 /\
    mem + 16 + cnt * mt_stride mt <= alloc_ceiling /\ 16 <= mt_stride mt.
  Proof.
    destruct (wf_grp A1 NW ma mt aib slots Hma Hr) as (H1 & _ & H3 & _ & _ & _ & _ & _ & _ & _ & _ & Hal & Hmem & Hfit & Hce & Hpg).
    pose proof (w_last_range (mt_w32 mt)) as Hl. pose proof (w_sc_range (mt_w32 mt)) as Hs.
    pose proof (stride_ge16 mt ltac:(lia) H3) as HS.
    assert (Hsc48 : mt_sc mt < 48) by (destruct H3 as [H3 | (_ & _ & H3)]; [exact H3 | lia]).
    unfold W, sc, cnt, mem in *. unfold mt_cnt, mt_last, mt_sc, w_last in *.
    repeat split; lia.
  Qed.

  Lemma ma_notin_D : ~ In ma D.
  Proof.
    intros Hin. destruct (proj2 (ii_dd HII ma) Hin) as (mtx & Hx & Hrl). rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrl. discriminate.
  Qed.

  Lemma usage_now : a_ctx A1 (KUsage sc) = usage_of A1 sc /\ cnt <= usage_of A1 sc < 2^47.
  Proof.
    pose proof Ngrp as (_ & Hsc & _). pose proof NW as HW. pose proof (ii_us HII sc ltac:(pose proof Ngrp; lia)) as HU.
    (* [comment removed for export] *)
    destruct (proj1 (wf_meta_dom A1 HW ma) ltac:(rewrite Hma; discriminate)) as (pg0 & k0 & Hpg0 & Hk0 & Ema).
    set (A0 := ameta_upd A1 ma (MT (mt_f mt) RDead)).
    assert (U0 : usage_of A0 sc = usage_of A1 sc - cnt).
    { apply (usage_of_point A1 A0 sc ma pg0 k0 cnt HW eq_refl Hpg0 Hk0 Ema).
      - intros x Hx. unfold meta_usage, A0, ameta_upd, set_meta. cbn [a_meta]. rewrite aupd_other by exact Hx. reflexivity.
      - unfold meta_usage, A0, ameta_upd, set_meta. cbn [a_meta]. rewrite aupd_same, Hma, Hr. cbn [mt_role MT]. unfold sc, cnt. rewrite Z.eqb_refl. lia. }
    assert (MU0 : forall x, 0 <= meta_usage A0 sc x).
    { intros x. unfold meta_usage. destruct (a_meta A0 x) as [mtx|]; [| lia]. destruct (mt_role mtx); try lia.
      destruct (mt_sc mtx =? sc); [| lia]. unfold mt_cnt, mt_last. pose proof (w_last_range (mt_w32 mtx)). lia. }
    assert (AU0 : forall pg, 0 <= area_usage A0 sc pg) by (intros pg; unfold area_usage; apply sumk_nonneg; intros k Hk; apply MU0).
    assert (R0 : 0 <= usage_of A0 sc).
    { unfold usage_of. generalize (a_areas A0) as l. induction l as [|pg l IH]; cbn [fold_right]; [lia|]. pose proof (AU0 pg). lia. }
    pose proof (usage_of_range A1 sc HW). split; [exact HU | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma Npar : exists pa pm paib psl j, a_meta A1 pa = Some pm /\ mt_role pm = RGroup paib psl /\ 0 <= j /\
    nth_error psl (Z.to_nat j) = Some (SNested ma) /\ mem = slot_start pm j /\ pa <> ma /\ j < 32 /\
    (nfuel pm < nfuel mt)%nat.
  Proof.
    pose proof NW as HW.
    destruct (wf_nested_parent A1 HW ma mt aib slots Hma Hr Hml) as (pa & pm & paib & psl & j & Hpa & Hpr & Hj0 & Hj).
    destruct (wf_nested A1 HW pa pm paib psl j ma Hpa Hpr Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & _ & Hmemc & _).
    rewrite Hma in Hmc. injection Hmc as <-.
    exists pa, pm, paib, psl, j. split; [exact Hpa|]. split; [exact Hpr|]. split; [exact Hj0|]. split; [exact Hj|]. split; [exact Hmemc|].
    split. { intros ->. rewrite Hma in Hpa. injection Hpa as <-. rewrite Hr in Hpr. injection Hpr as <- <-. destruct (Hidle _ _ Hj); discriminate. }
    split. { destruct (wf_grp A1 HW pa pm paib psl Hpa Hpr) as (_ & _ & _ & Hlen & _). pose proof (w_last_range (mt_w32 pm)).
             assert (Hjlt : (Z.to_nat j < length psl)%nat) by (apply (proj1 (nth_error_Some psl (Z.to_nat j))); rewrite Hj; discriminate).
             unfold mt_cnt, mt_last in Hlen. lia. }
    exact (nfuel_parent A1 HW ma mt aib slots pa pm paib psl j Hma Hr Hml Hpa Hpr Hj0 Hj).
  Qed.

  (* [comment removed for export] *)
  Lemma hdr_clear : forall B pa pm paib psl j f x,
    WF B -> a_meta B ma = Some mt -> (forall x mtx, a_meta B x = Some mtx -> exists mtx1, a_meta A1 x = Some mtx1 /\ mt_role mtx1 = mt_role mtx /\ mt_w32 mtx1 = mt_w32 mtx /\ mt_mem mtx1 = mt_mem mtx) ->
    a_meta B pa = Some pm -> mt_role pm = RGroup paib psl -> nth_error psl (Z.to_nat j) = Some (SNested ma) ->
    has (dnA B ma mt pa pm paib psl j) f -> f_a f <= x < f_a f + f_n f -> ~ (mem <= x < mem + 8).
  Proof.
    intros B pa pm paib psl j f x HWB HmaB Hback Hpa Hpr Hj Hf Hfx Hx.
    pose proof Ngrp as (_ & _ & Hcnt & _ & _ & _ & _ & HS16).
    assert (HCS : 16 <= cnt * mt_stride mt) by (clear - Hcnt HS16; nia).
    assert (GEXT : gext_lo mt = mem /\ mem + 28 <= gext_hi mt) by (unfold gext_lo, gext_hi, mem, cnt in *; split; [reflexivity | lia]).
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - destruct (other_fact_clear B HWB ma mt aib slots HmaB Hr f (or_introl Hc)) as (_ & _ & [Dc | (jj & ch & Hjj & _)]); [lia | destruct (Hidle _ _ Hjj); discriminate].
    - destruct (other_fact_clear B HWB ma mt aib slots HmaB Hr f (or_intror (or_introl Har))) as (_ & _ & [Dc | (jj & ch & Hjj & _)]); [lia | destruct (Hidle _ _ Hjj); discriminate].
    - destruct Hm as (y & mty & fl & Hy & ->). cbn [f_a f_n] in Hfx. pose proof (mfield_range fl) as Hfl.
      destruct (Z.eq_dec y ma) as [-> | Hne].
      + pose proof (meta_clear_of_gext B HWB ma mt aib slots HmaB Hr) as MC. lia.
      + assert (Hy1 : exists mty1, a_meta B y = Some mty1).
        { destruct (dn_meta_inv B ma mt pa pm paib psl j y mty Hy) as [(-> & ->) | [(E & _) | (_ & _ & H)]]; [exists pm; exact Hpa | exfalso; exact (Hne E) | exists mty; exact H]. }
        destruct Hy1 as (mty1 & Hy1).
        destruct (other_fact_clear B HWB ma mt aib slots HmaB Hr (FCT (y + moff fl) (mlen fl) (mt_f mty1 fl))) as (_ & _ & [Dc | (jj & ch & Hjj & _)]);
          [right; right; left; exists y, mty1, fl; auto | cbn [f_a f_n] in Dc; lia | destruct (Hidle _ _ Hjj); discriminate].
    - destruct Hg as (y & mty & aiby & sly & Hy & Hry & Hin).
      destruct (dn_group_back B ma mt aib slots HmaB Hr Hidle pa pm paib psl j Hpa Hpr Hj y mty aiby sly Hy Hry)
        as (mt0 & sl0 & Hy0 & Hr0 & Hne & Ef & Ew & Em & Es & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsl & _).
      assert (ORIG : In f (grp_hdr_fields y mt0 aiby) \/ exists jj st, nth_error sl0 jj = Some st /\ In f (slot_fields mt0 (Z.of_nat jj) st) \/
                     (y = pa /\ In f (slot_fields mt0 (Z.of_nat (Z.to_nat j)) STaken))).
      { destruct Hin as [Hh | (jj & st & Hjj & Hfin)].
        - left. unfold grp_hdr_fields in *. rewrite Em in Hh. exact Hh.
        - unfold slot_fields in *. rewrite Em, Es in Hfin. destruct (Hsl _ _ Hjj) as [H0 | (-> & -> & -> & H0)].
          + right. exists jj, st. auto.
          + right. exists (Z.to_nat j), STaken. right. split; [reflexivity | exact Hfin]. }
      assert (CLR : forall g, (In g (grp_hdr_fields y mt0 aiby) \/ exists jj st, nth_error sl0 jj = Some st /\ In g (slot_fields mt0 (Z.of_nat jj) st)) ->
                f_a g <= x < f_a g + f_n g -> False).
      { intros g Hg Hgx. destruct (other_fact_clear B HWB ma mt aib slots HmaB Hr g) as (_ & _ & [Dc | (jj & ch & Hjj & _)]);
          [right; right; right; exists y, mt0, aiby, sl0; auto | lia | destruct (Hidle _ _ Hjj); discriminate]. }
      destruct ORIG as [Hh | (jj & st & [(Hjj & Hfin) | (-> & Hfin)])].
      + exact (CLR f (or_introl Hh) Hfx).
      + exact (CLR f (or_intror (ex_intro _ jj (ex_intro _ st (conj Hjj Hfin)))) Hfx).
      + (* [comment removed for export] *)
        rewrite Hpa in Hy0. injection Hy0 as E0. subst mt0. rewrite Hpr in Hr0. injection Hr0 as E1 E2. subst sl0.
        apply (CLR f); [| exact Hfx]. right. exists (Z.to_nat j), (SNested ma). split; [exact Hj|].
        unfold slot_fields, slot_fields_g in *. apply in_app_iff in Hfin. apply in_app_iff. destruct Hfin as [Hfin | []]. left. exact Hfin.
  Qed.

  Theorem ts_nt_fg_nested : forall (K : word * word -> M R) P,
    (forall s' A' r, II sp0 argv envp cb D A' s' -> ntframe A1 s1 s' -> fgrel A1 A' ma -> nt_res A1 A' (ms_vm s1) r -> tsafe (K r s') P) ->
    tsafe ((r <- nt_fg rec (Z_to_bv 64 ma) ;; K r) s1) P.
  Proof.
    intros K P HK. pose proof NW as HW. pose proof (is_rep _ _ _ _ _ _ (ii_is HII)) as HR. pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof Ngrp as (HW64 & Hsc & Hcnt & Ecnt & Hmem & Hsc64 & Hce & HS16).
    assert (HCS : 16 <= cnt * mt_stride mt) by (clear - Hcnt HS16; nia).
    pose proof (meta_facts A1 ma mt HW Hma) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    destruct usage_now as [EU HU].
    destruct Npar as (pa & pm & paib & psl & j & Hpa & Hpr & Hj0 & Hj & Emem & Hpane & Hj32 & Hfuel).
    pose proof (repw_init A1 (ms_mem s1) HW HR) as RW0.
    unfold nt_fg. reassoc. rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_metaW A1 HW s1 (ms_mem s1) [] ma mt FW32); [exact RW0 | exact HWIN | exact Hma | reflexivity | apply wfree_range_nil | change (mt_f mt FW32) with W; lia |].
    change (mt_f mt FW32) with W. cbv zeta. unfold W. rewrite (wsc_eq mt) by lia. fold W. change (mt_sc mt) with sc.
    reassoc.
    eapply (ts_nt_usage A1 HW s1 (ms_mem s1) [] ma mt W sc); [exact RW0 | exact HWIN | exact Hma | reflexivity | lia | lia | apply wfree_range_nil | | intros; lia |].
    { intros _. split; [apply wfree_range_nil|]. rewrite EU. lia. }
    intros _ m2 RW2. unfold W at 1. rewrite (wmaplen_eq mt), Hml by lia. change (is0 (Z_to_bv 64 0)) with true. cbn [negb].
    (* [comment removed for export] *)
    set (cu := cupd (a_ctx A1) (KUsage sc) (a_ctx A1 (KUsage sc) - cnt)).
    set (A1u := set_ctx A1 cu).
    assert (Hheur : forall k, ctx_heur k \/ cu k = a_ctx A1 k).
    { intros k. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hne]; [left; exact I | right; unfold cu; apply cupd_other; exact Hne]. }
    assert (Hnn : forall k, 0 <= cu k).
    { intros k. unfold cu. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hne]; [rewrite cupd_same; lia | rewrite cupd_other by exact Hne; apply (wf_ctx_nonneg A1 HW)]. }
    pose proof (WF_ctx_heur A1 HW cu Hheur Hnn) as HWu. fold A1u in HWu.
    pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    assert (WOu : writes_ok A1 [FCT (caddr (KUsage sc)) 8 (a_ctx A1 (KUsage sc) - (W mod 32 + 1))]).
    { apply (writes_ok_ctxr A1 _ HW). intros w x [<- | []] Hx. cbn [f_a f_n] in Hx. exists (KUsage sc). cbn [clen]. split; [cbn; lia | lia]. }
    assert (HRu : Rep A1u m2).
    { apply (commit_heur A1 cu (ms_mem s1) _ m2 HW Hheur Hnn RW2).
      - intros x b Hw. destruct (wlook_some_cov _ _ _ Hw) as (w & [<- | []] & Hxw). cbn [f_a f_n] in Hxw.
        rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia). injection Hw as <-. cbn [f_v f_a]. exists (KUsage sc). cbn [clen].
        split; [cbn; lia|]. split; [lia|]. unfold cu. rewrite cupd_same. rewrite <- Ecnt. reflexivity.
      - intros k Hk Hne x Hx. unfold cu in Hne. destruct (cslot_eq_dec k (KUsage sc)) as [-> | Hk2]; [| rewrite cupd_other in Hne by exact Hk2; exfalso; exact (Hne eq_refl)].
        apply (wlook_cov_some _ (FCT (caddr (KUsage sc)) 8 (a_ctx A1 (KUsage sc) - (W mod 32 + 1))) x); [left; reflexivity | cbn [f_a f_n clen] in *; lia]. }
    pose proof (IS_commit sp0 argv envp cb A1 A1u s1 _ m2 (ii_is HII) RW2 WOu HWu HRu) as HISu.
    pose proof (ntframe_commit A1 s1 _ m2 HW RW2 WOu) as HFu.
    set (s2 := upd s1 m2 (ms_vm s1)) in HISu, HFu |- *.
    assert (Au_meta : forall x, a_meta A1u x = a_meta A1 x) by (intros x; reflexivity).
    assert (Hmau : a_meta A1u ma = Some mt) by (rewrite Au_meta; exact Hma).
    assert (Hpau : a_meta A1u pa = Some pm) by (rewrite Au_meta; exact Hpa).
    assert (Hnotactu : forall c, ~ In ma (a_active A1u c)) by (intros c; exact (Hnotact c)).
    (* [comment removed for export] *)
    unfold nt_fg_nested. reassoc. rewrite at_Z. change (ma + 16) with (ma + moff FMem).
    eapply (ts_ld_meta A1u HWu); [exact HRu | exact HWIN | exact Hmau | reflexivity | change (mt_f mt FMem) with mem; lia |].
    change (mt_f mt FMem) with mem. reassoc.
    apply (get_meta_ok A1u s2 HWu HRu HWIN (eo_rodata _ _ _ _ (is_env _ _ _ _ _ _ HISu)) pa pm paib psl j (SNested ma) 0 mem Hpau Hpr Hj Hj0
             ltac:(right; exists ma; auto) ltac:(rewrite Emem; lia)).
    reassoc. eapply (ts_ld_meta A1u HWu); [exact HRu | exact HWIN | exact Hmau | reflexivity | change (mt_f mt FMem) with mem; lia |].
    change (mt_f mt FMem) with mem. reassoc. rewrite at_Z.
    destruct (slot_hdr_facts A1u HWu pa pm paib psl j (SNested ma) 0 mem Hpau Hpr Hj Hj0 ltac:(right; exists ma; auto) ltac:(rewrite Emem; lia)) as (c6 & Hc6 & _ & F3 & _).
    replace (mem + -3) with (mem - 3) by lia.
    eapply (ts_lbu_fact A1u HWu); [exact HRu | exact HWIN | exact F3 | lia |].
    rewrite v_andi_Z, land_31 by lia. replace ((j + 32 * c6) mod 32) with j by (rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    reassoc.
    pose proof (repw_init A1u m2 HWu HRu) as RWu0.
    assert (Hdom8 : forall k, 0 <= k < Z.of_nat 8 -> dom A1u (mem + k)).
    { intros k Hk. apply (grp_dom A1u ma mt aib slots (mem + k) HWu Hmau Hr). unfold gext_lo, gext_hi, mem, cnt in *. lia. }
    eapply (ts_st_domW A1u HWu s2 m2 [] 8 mem); [exact RWu0 | exact HWIN | lia | exact Hdom8 |].
    intros m3 RW3. change (bv_unsigned w0) with 0 in RW3. change (Z.of_nat 8) with 8 in RW3.
    set (A2 := dnA A1u ma mt pa pm paib psl j).
    pose proof (WF_dissolve_nested A1u HWu ma mt aib slots Hmau Hr Hml Hidle Hnotactu pa pm paib psl j Hpau Hpr Hj0 Hj) as HW2. fold A2 in HW2.
    assert (WO2 : writes_ok A1u [FCT mem 8 0]).
    { intros w x [<- | []] Hx. cbn [f_a f_n] in Hx. split; [left; apply (grp_dom A1u ma mt aib slots x HWu Hmau Hr); unfold gext_lo, gext_hi, mem, cnt in *; lia|].
      intros p n Hp Hpx. rewrite (live_same_ctx A1 cu) in Hp || change (a_live A1u p) with (a_live A1 p) in Hp.
      apply (proj1 (wf_live_map A1 HW p n)) in Hp. destruct Hp as (y & mty & aiby & sly & jj & off & Hy & Hry & Hjj0 & Hjj & ->).
      destruct (live_geom A1 HW y mty aiby sly jj off n Hy Hry Hjj0 Hjj) as (q & _ & Hn & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
      pose proof (round16_ge n).
      (* [comment removed for export] *)
      destruct (Z.eq_dec y ma) as [-> | Hne].
      { rewrite Hma in Hy. injection Hy as <-. rewrite Hr in Hry. injection Hry as <- <-. destruct (Hidle _ _ Hjj); discriminate. }
      assert (Fz : has A1 (FCT (slot_start mty jj - 4) 1 0)).
      { right; right; right. exists y, mty, aiby, sly. split; [exact Hy|]. split; [exact Hry|]. right. exists (Z.to_nat jj), (SLive off n). split; [exact Hjj|].
        rewrite Z2Nat.id by lia. unfold slot_fields, slot_fields_g. left. reflexivity. }
      destruct (other_fact_clear A1 HW ma mt aib slots Hma Hr (FCT (slot_start mty jj - 4) 1 0)) as (_ & _ & [Dc | (j2 & ch & Hj2 & _)]);
        [| cbn [f_a f_n] in Dc | destruct (Hidle _ _ Hj2); discriminate].
      { right; right; right. exists y, mty, aiby, sly. split; [exact Hne|]. split; [exact Hy|]. split; [exact Hry|]. right. exists (Z.to_nat jj), (SLive off n).
        split; [exact Hjj|]. rewrite Z2Nat.id by lia. unfold slot_fields, slot_fields_g. left. reflexivity. }
      (* [comment removed for export] *)
      assert (Fe : has A1 (FCT (slot_end mty jj) 1 0)).
      { right; right; right. exists y, mty, aiby, sly. split; [exact Hy|]. split; [exact Hry|]. right. exists (Z.to_nat jj), (SLive off n). split; [exact Hjj|].
        rewrite Z2Nat.id by lia. unfold slot_fields, slot_fields_g. right. left. reflexivity. }
      destruct (other_fact_clear A1 HW ma mt aib slots Hma Hr (FCT (slot_end mty jj) 1 0)) as (_ & _ & [De | (j2 & ch & Hj2 & _)]);
        [| cbn [f_a f_n] in De | destruct (Hidle _ _ Hj2); discriminate].
      { right; right; right. exists y, mty, aiby, sly. split; [exact Hne|]. split; [exact Hy|]. split; [exact Hry|]. right. exists (Z.to_nat jj), (SLive off n).
        split; [exact Hjj|]. rewrite Z2Nat.id by lia. unfold slot_fields, slot_fields_g. right. left. reflexivity. }
      (* [comment removed for export] *)
      destruct (wf_laminar A1 HW ma mt aib slots y mty aiby sly Hma Hr Hy Hry ltac:(intros E; exact (Hne (eq_sym E)))) as [L1 | [L2 | [(j3 & ch3 & _ & Hj3 & _) | (j3 & ch3 & Hj30 & Hj3 & Hlo3 & Hhi3)]]].
      - unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g, mem, cnt in *. lia.
      - unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g, mem, cnt in *. lia.
      - destruct (Hidle _ _ Hj3); discriminate.
      - (* [comment removed for export] *)
        assert (Hj3ne : j3 <> jj) by (intros ->; rewrite Hjj in Hj3; discriminate).
        destruct (wf_grp A1 HW y mty aiby sly Hy Hry) as (Hyw & _ & Hysc & _). pose proof (stride_ge16 mty ltac:(lia) Hysc) as HSy.
        destruct (Z.lt_ge_cases j3 jj) as [Hlt | Hge].
        + pose proof (slots_disjoint (mt_mem mty) (mt_stride mty) j3 jj HSy Hj30 ltac:(lia) Hlt) as SD.
          unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g, mem, cnt in *. lia.
        + pose proof (slots_disjoint (mt_mem mty) (mt_stride mty) jj j3 HSy ltac:(lia) Hj30 ltac:(lia)) as SD.
          unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g, mem, cnt in *. lia. }
    (* [comment removed for export] *)
    assert (HR2 : Rep A2 m3).
    { apply (repw_commit2 A1u A2 m2 [FCT mem 8 0] m3 HW2 RW3).
      - intros f Hf. left. exact (has_dnA A1u ma mt aib slots Hmau Hr Hidle pa pm paib psl j Hpau Hpr Hj f Hf).
      - intros x b Hw. right; right. destruct (wlook_some_cov _ _ _ Hw) as (w & [<- | []] & Hxw). cbn [f_a f_n] in Hxw.
        intros f Hf Hfx. refine (hdr_clear A1u pa pm paib psl j f x HWu Hmau _ Hpau Hpr Hj Hf Hfx ltac:(lia)).
        intros y mty Hy. rewrite Au_meta in Hy. exists mty. auto.
      - intros x Hx. apply (proj1 (dom_dnA A1u ma mt aib slots Hmau Hr Hml Hidle pa pm paib psl j Hpau Hpr Hj x)). exact Hx. }
    pose proof (IS_commit sp0 argv envp cb A1u A2 s2 [FCT mem 8 0] m3 HISu RW3 WO2 HW2 HR2) as HIS2.
    pose proof (ntframe_commit A1u s2 [FCT mem 8 0] m3 HWu RW3 WO2) as HF2.
    set (s3 := upd s2 m3 (ms_vm s2)) in HIS2, HF2 |- *.
    assert (DOM2 : forall x, dom A2 x <-> dom A1 x).
    { intros x. unfold A2. rewrite (dom_dnA A1u ma mt aib slots Hmau Hr Hml Hidle pa pm paib psl j Hpau Hpr Hj x). reflexivity. }
    assert (Hma2 : a_meta A2 ma = Some (mtDn mt)) by (unfold A2; apply (dn_meta_ma A1u ma mt aib slots Hmau Hr Hidle pa pm paib psl j Hpau Hpr Hj)).
    assert (Hpa2 : a_meta A2 pa = Some (pm' pm paib psl j)) by (unfold A2; apply dn_meta_pa).
    destruct (proj1 (wf_meta_dom A1 HW ma) ltac:(rewrite Hma; discriminate)) as (pg0 & k0 & Hpg0 & Hk0 & Ema).
    assert (HUS2 : forall c, usage_of A2 c = usage_of A1 c - (if sc =? c then cnt else 0)).
    { intros c. rewrite <- (usage_of_ext A1 A1u c eq_refl ltac:(intros x; unfold meta_usage; rewrite Au_meta; reflexivity)).
      apply (usage_of_point A1u A2 c ma pg0 k0 _ HWu eq_refl Hpg0 Hk0 Ema).
      - intros x Hx. unfold meta_usage. destruct (Z.eq_dec x pa) as [-> | Hxp].
        + rewrite Hpa2, Hpau, Hpr. cbn [mt_role pm' MT]. unfold mt_sc, mt_cnt, mt_last. rewrite (pm'_w32 pm paib psl j). reflexivity.
        + unfold A2. rewrite (dn_old A1u ma mt pa pm paib psl j x) || idtac.
          destruct (a_meta A1u x) as [mtx|] eqn:Ex.
          * rewrite (dn_old A1u ma mt pa pm paib psl j x mtx Ex Hxp Hx). reflexivity.
          * destruct (a_meta (dnA A1u ma mt pa pm paib psl j) x) as [mtx'|] eqn:Ex'; [| reflexivity].
            destruct (dn_meta_inv A1u ma mt pa pm paib psl j x mtx' Ex') as [(E & _) | [(E & _) | (_ & _ & H)]]; [contradiction | contradiction | rewrite Ex in H; discriminate].
      - unfold meta_usage. rewrite Hma2, Hmau, Hr. cbn [mt_role mtDn MT]. unfold sc, cnt. destruct (mt_sc mt =? c); lia. }
    assert (HII2 : II sp0 argv envp cb (ma :: D) A2 s3).
    { apply II_intro; [exact HIS2 | | | |].
      - unfold s3, s2. cbn [ms_vm upd]. unfold A2. apply (VMok_dnA A1u ma mt aib slots Hmau Hr Hml Hidle pa pm paib psl j Hpau Hpr Hj).
        unfold A1u. apply (VMok_ctx_heur A1 cu Hheur). exact (ii_vm HII).
      - apply (AvOK_transfer A1 A2 (ii_av HII)); [reflexivity | unfold A2, A1u, dnA, set_ctx; cbn [a_ctx]; unfold cu; apply cupd_other; discriminate |].
        intros x mt' Hx Hrl. destruct (dn_meta_inv A1u ma mt pa pm paib psl j x mt' Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]]; [cbn in Hrl; discriminate | cbn in Hrl; discriminate |].
        rewrite Au_meta in H. exists mt'. auto.
      - intros c Hc. rewrite HUS2. change (a_ctx A2 (KUsage c)) with (cu (KUsage c)). unfold cu.
        destruct (Z.eqb_spec sc c) as [<- | Hne]; [rewrite cupd_same; lia | rewrite cupd_other by (intros E; injection E; lia)]. rewrite (ii_us HII c Hc). lia.
      - intros x. split.
        + intros (mt' & Hx & Hrl). destruct (dn_meta_inv A1u ma mt pa pm paib psl j x mt' Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]]; [cbn in Hrl; discriminate | left; reflexivity | right].
          rewrite Au_meta in H. apply (proj1 (ii_dd HII x)). exists mt'. auto.
        + intros [<- | Hin]; [exists (mtDn mt); split; [exact Hma2 | reflexivity] |].
          destruct (proj2 (ii_dd HII x) Hin) as (mt' & Hx & Hrl). exists mt'. split; [| exact Hrl].
          unfold A2. apply dn_old; [rewrite Au_meta; exact Hx | | intros ->; exact (ma_notin_D Hin)].
          intros ->. rewrite Hpa in Hx. injection Hx as <-. rewrite Hpr in Hrl. discriminate. }
    (* [comment removed for export] *)
    replace (mem + 0) with mem by lia || idtac.
    reassoc. apply (ts_bind_split _ _ s3 P (ntpost sp0 argv envp cb (ma :: D) A2 s3 pa (psl' psl j) j)).
    { apply (Hrec (ma :: D) A2 s3 pa (pm' pm paib psl j) paib (psl' psl j) j HII2 ltac:(intros c Hc; exact (Hact48 c Hc)) Hpa2 eq_refl); [| exact Hj0 |].
      - unfold psl'. apply list_set_nth_same. apply (proj1 (nth_error_Some psl (Z.to_nat j))). rewrite Hj. discriminate.
      - exact Hfuel. }
    intros r s4 (A4 & HII4 & HF4 & HR4 & HRes4).
    (* [comment removed for export] *)
    destruct (proj2 (ii_dd HII4 ma) (or_introl eq_refl)) as (md & Hmd & Hrd).
    reassoc. apply (ts_free_meta sp0 argv envp cb D A4 s4 ma md HII4 ma_notin_D Hmd Hrd).
    intros s5 HII5 HF5. apply ts_bind_ret.
    set (A5 := fmA A4 ma (a_freelist A4) (hd ma (a_freelist A4)) (last (a_freelist A4) ma)) in HII5.
    pose proof (fmrel sp0 argv envp cb D A4 s4 ma md HII4 Hmd Hrd) as (L5 & Ar5 & P5 & B5 & X5 & Ac5 & C5 & G5 & Gi5 & D5). fold A5 in L5, Ar5, P5, B5, X5, Ac5, C5, G5, Gi5, D5.
    destruct HR4 as [L4 Ar4 P4 B4 C4 Q4 G4 D4 FL4].
    assert (OWNu : forall x, owned_of A1u x -> owned_of A1 x) by (intros x Hx; exact Hx).
    assert (OWN2 : forall x, owned_of A2 x -> owned_of A1u x) by (intros x [Hx | Hx]; [left; exact Hx | right; apply (proj1 (DOM2 x)); exact Hx]).
    assert (OWN4 : forall x, owned_of A4 x -> owned_of A2 x) by (intros x [Hx | Hx]; [left; exact Hx | right; exact (D4 x Hx)]).
    assert (HF15 : ntframe A1 s1 s5).
    { apply (ntframe_trans A1 A4 s1 s4 s5); [| exact HF5 | intros x Hx; apply OWNu, OWN2, OWN4; exact Hx | rewrite L4; reflexivity].
      apply (ntframe_trans A1 A2 s1 s3 s4); [| exact HF4 | intros x Hx; apply OWNu, OWN2; exact Hx | reflexivity].
      apply (ntframe_trans A1 A1u s1 s2 s3); [exact HFu | exact HF2 | exact OWNu | reflexivity]. }
    pose proof (nf_vm _ _ _ HF4) as Hvm4. unfold s3, s2 in Hvm4. cbn [ms_vm upd] in Hvm4.
    apply (HK s5 A5 r HII5 HF15).
    - (* [comment removed for export] *) constructor.
      + rewrite L5, L4. reflexivity. + rewrite Ar5, Ar4. reflexivity. + rewrite P5, P4. reflexivity. + rewrite B5, B4. reflexivity.
      + intros k Hk. rewrite C5 by (destruct k; cbn in Hk; try discriminate; try (intros c; discriminate); destruct Hk).
        rewrite (C4 k Hk). change (a_ctx A2 k) with (cu k). unfold cu. rewrite cupd_other by (destruct k; try discriminate; destruct Hk). reflexivity.
      + intros c Hc. rewrite Ac5, (Q4 c Hc). reflexivity.
      + intros x mtx aibx slx Hx Hrx. pose proof (Gi5 x mtx aibx slx Hx Hrx) as Hx4.
        destruct (G4 x mtx aibx slx Hx4 Hrx) as (mt2 & sl2 & Hx2 & Hr2 & W2 & Mm2 & K2).
        destruct (dn_group_inv A1u ma mt pa pm paib psl j x mt2 aibx sl2 Hx2 Hr2) as [(-> & -> & -> & ->) | (Hxp & Hxm & Hx0)].
        * (* [comment removed for export] *)
          split; [exact (pa_ne_ma A1u ma mt aib slots Hmau Hr Hidle pa pm paib psl j Hpau Hpr Hj)|].
          exists pm, psl. split; [exact Hpa|]. split; [exact Hpr|]. rewrite pm'_w32 in W2. rewrite pm'_mem in Mm2. split; [exact W2|]. split; [exact Mm2|].
          right. exists (Z.to_nat j), ma. split; [exact Hj|].
          destruct K2 as [(_ & ->) | (Hbad & _)]; [| exfalso; exact (Hbad eq_refl)].
          unfold psl'. rewrite list_set_set. reflexivity.
        * split; [exact Hxm|]. exists mt2, sl2. split; [exact Hx0|]. split; [exact Hr2|]. split; [exact W2|]. split; [exact Mm2|].
          destruct K2 as [(E & _) | (_ & HK2)]; [exfalso; exact (Hxp E) | exact HK2].
      + intros x Hx. apply (proj1 (DOM2 x)). apply D4. apply D5. exact Hx.
      + destruct FL4 as [l4 E4]. exists (l4 ++ [ma]). unfold A5. rewrite fmA_freelist, E4. change (a_freelist A2) with (a_freelist A1). rewrite <- app_assoc. reflexivity.
    - (* [comment removed for export] *)
      assert (XS : forall xs, VMok (set_xmaps A4 xs) (vm_munmap (fst r) (snd r) (ms_vm s1)) -> VMok (set_xmaps A5 xs) (vm_munmap (fst r) (snd r) (ms_vm s1))).
      { intros xs HV. unfold A5.
        change (set_xmaps (fmA A4 ma (a_freelist A4) (hd ma (a_freelist A4)) (last (a_freelist A4) ma)) xs)
          with (fmA (set_xmaps A4 xs) ma (a_freelist (set_xmaps A4 xs)) (hd ma (a_freelist (set_xmaps A4 xs))) (last (a_freelist (set_xmaps A4 xs)) ma)).
        apply (VMok_fmA (set_xmaps A4 xs) ma md); [exact Hmd | exact Hrd | exact HV]. }
      destruct HRes4 as [(-> & X4 & Dk4) | (B & L & -> & HL & HBal & HLm & Hhr & X4 & Hin & Diff & Nod & Hav & WFx & VMx)].
      + left. split; [reflexivity|]. split; [rewrite X5, X4; reflexivity|]. intros x Hx. apply D5. apply Dk4. apply (proj2 (DOM2 x)). exact Hx.
      + right. exists B, L. split; [reflexivity|]. split; [exact HL|]. split; [exact HBal|]. split; [exact HLm|]. split; [exact Hhr|].
        split; [rewrite X5, X4; reflexivity|]. split; [unfold s3, s2 in Hin; cbn [ms_vm upd] in Hin; exact Hin|].
        split. { intros x. rewrite <- (DOM2 x), (Diff x). split; (intros [H|H]; [left | right; exact H]); [apply (proj2 (D5 x)) | apply (proj1 (D5 x))]; exact H. }
        split. { intros x Hx Hd. exact (Nod x Hx (proj1 (D5 x) Hd)). }
        split. { intros f x Hf Hfx.
          pose proof (is_wf _ _ _ _ _ _ (ii_is HII4)) as HW4.
          destruct (has_fmA A4 HW4 ma md (a_freelist A4) _ _ Hmd Hrd eq_refl eq_refl eq_refl f Hf) as [Hf4 | [-> | [(fld & ->) | (_ & Hc)]]].
          - exact (Hav f x Hf4 Hfx).
          - cbn [f_a f_n] in Hfx. unfold heap_range in Hhr. pose proof (ctx_slot_range KFmh I) as (K1 & K2 & K3). cbn [clen] in K2. pose proof layout_nums. unfold CTX_END in *. lia.
          - cbn [f_a f_n] in Hfx. pose proof (mfield_range fld). pose proof (meta_facts A4 ma md HW4 Hmd) as (_ & _ & _ & _ & Mdm).
            intros Hr'. apply (Nod x Hr'). replace x with (ma + (x - ma)) by lia. apply Mdm. lia.
          - assert (FL : forall y, In y (a_freelist A4) -> exists mty, a_meta A4 y = Some mty) by (intros y Hy; destruct (proj1 (wf_fl_mem A4 HW4 y) Hy) as (mty & Hmy & _); exists mty; exact Hmy).
            assert (MD : forall y mty, a_meta A4 y = Some mty -> y <= x < y + 40 -> ~ (B <= x < B + L)).
            { intros y mty Hy Hyx Hr'. apply (Nod x Hr'). pose proof (meta_facts A4 y mty HW4 Hy) as (_ & _ & _ & _ & Mdy). replace x with (y + (x - y)) by lia. apply Mdy. lia. }
            destruct Hc as [-> | ->]; cbn [f_a f_n] in Hfx.
            + destruct (a_freelist A4) as [|y l] eqn:El; cbn [hd] in Hfx |- *; [exact (MD ma md Hmd ltac:(lia))|].
              destruct (FL y (or_introl eq_refl)) as (mty & Hy). exact (MD y mty Hy ltac:(lia)).
            + destruct (list_eq_dec Z.eq_dec (a_freelist A4) []) as [El | El]; [rewrite El in Hfx; cbn in Hfx; exact (MD ma md Hmd ltac:(lia))|].
              destruct (FL _ (last_In_ne _ ma El)) as (mty & Hy). exact (MD _ mty Hy ltac:(lia)). }
        split. { apply WF_set_xmaps. exact (is_wf _ _ _ _ _ _ (ii_is HII5)). }
        change (a_xmaps A1) with (a_xmaps A2). apply (XS (a_xmaps A2)). unfold s3, s2 in VMx. cbn [ms_vm upd] in VMx. exact VMx.
  Qed.
End FgNested.
End WithLayout.
