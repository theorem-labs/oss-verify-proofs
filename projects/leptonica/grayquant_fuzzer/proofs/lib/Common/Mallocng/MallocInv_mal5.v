(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger LibMaskBits.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf6 MallocInv_wf7 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_vmops MallocInv_vmfree
  MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_hints MallocInv_sc
  MallocInv_enframe MallocInv_ameta_iface MallocInv_ameta5 MallocInv_ametax_iface MallocInv_ametax MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_freetop MallocInv_free
  MallocInv_sc3 MallocInv_aslot_iface MallocInv_malloc_iface MallocInv_agm2 MallocInv_agm3 MallocInv_agtail MallocInv_agroot MallocInv_mal1 MallocInv_efII MallocInv_mal3 MallocInv_mal2
  MallocSureLedger MallocSureInv MallocSureGrow MallocSureCap MallocSureCredit MallocSurePot.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mul_pow2_low : forall t c k, 0 <= t -> 0 <= k -> 0 <= c < 2^k -> Z.land (2^k * t) c = 0.
Proof.
  intros t c k Ht Hk Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hlt | Hge].
  - rewrite Z.mul_comm, Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high k c i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_disjoint_add : forall a b, Z.land a b = 0 -> Z.lor a b = a + b.
Proof. intros a b Hd. pose proof (Z.add_lor_land a b). lia. Qed.

(* [comment removed for export] *)
Lemma bigw32_word : forall n, 0 <= n -> n + 4115 < 2^64 ->
  v_or (v_andi (v_addi (v_add (Z_to_bv 64 n) (wlit 4064)) 51) (-2048)) (wlit 4064) = Z_to_bv 64 (page_round_up_Z (n + 20) + 4064).
Proof.
  intros n Hn Hn64. unfold wlit. rewrite v_add_Z, v_addi_Z. replace (n + 4064 + 51) with (n + 4115) by lia.
  rewrite v_andi_negZ by lia. replace (2 ^ 64 + -2048) with (2^64 - 2^11) by reflexivity.
  rewrite land_high_mask by lia.
  unfold page_round_up_Z, page_size. replace (n + 20 + 4096 - 1) with (n + 4115) by lia.
  set (X := n + 4115) in *.
  pose proof (Z.div_mod X (2^11) ltac:(lia)) as D1. pose proof (Z.mod_pos_bound X (2^11) ltac:(lia)) as D2.
  set (q := X / 2^11) in *.
  pose proof (Z.div_mod q 2 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as D4.
  set (r := q / 2) in *. set (b := q mod 2) in *.
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (Hr : 0 <= r) by (subst r; apply Z.div_pos; lia).
  assert (Er : X / 4096 = r).
  { subst r q. change 4096 with (2^11 * 2). rewrite <- Z.div_div by lia. reflexivity. }
  rewrite Er. replace (X - X mod 2^11) with (2^11 * q) by lia.
  rewrite v_or_Z by lia.
  assert (Ex : 2^11 * q = Z.lor (2^12 * r) (2^11 * b)).
  { rewrite lor_disjoint_add; [lia|]. apply (land_mul_pow2_low r (2^11 * b) 12); lia. }
  assert (Hland : Z.land (2^11 * q) 4064 = 2048 * b).
  { rewrite Ex, Z.land_lor_distr_l. rewrite (land_mul_pow2_low r 4064 12) by lia. rewrite Z.lor_0_l.
    assert (Hb : b = 0 \/ b = 1) by lia. destruct Hb as [E | E]; rewrite E; reflexivity. }
  pose proof (Z.add_lor_land (2^11 * q) 4064) as AL.
  f_equal. lia.
Qed.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

Lemma vm_munmap_live_le : forall a len h, In (a, len) (vm_maps h) -> vm_live_bytes (vm_munmap a len h) + u len <= vm_live_bytes h.
Proof. intros a len h Hin. unfold vm_live_bytes. rewrite vm_munmap_maps. apply live_bytes_remove_entry. exact Hin. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BigFail.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (n : Z).
  Variables (K : word -> M R) (P : R -> mstate -> Prop).
  Hypothesis HII0 : II sp0 argv envp cb [] A s.
  Hypothesis Hxm0 : a_xmaps A = [].
  Hypothesis Hact : ACT48 A.
  Hypothesis Hn : MMAP_THRESHOLD <= n < 2^61.
  Hypothesis HL : MLeaf W sp0 argv envp cb A s n K P.
  (* [comment removed for export] *)
  Variables (A5 : astate) (s6 : mstate) (p L : Z).
  Hypothesis HR5 : hrel A A5.
  Hypothesis EL : L = page_round_up_Z (n + 20).
  Hypothesis Hpal : page_aligned p.
  Hypothesis Hhr : heap_range p (p + L).
  Hypothesis Gdom : forall x, p <= x < p + L -> ~ dom A x /\ ms_mem s (Z_to_bv 64 x) = None.
  Hypothesis Gna : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true.
  Hypothesis Gdisj : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> p + L <= u b \/ u b + u sz <= p.
  Hypothesis F6lo : ms_lo s6 = ms_lo s.
  Hypothesis F6hi : ms_hi s6 = ms_hi s.
  Hypothesis F6vm : ms_vm s6 = vm_mmap (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_vm s).
  Hypothesis F6mem : forall a : word, ~ owned_of A (u a) -> ~ (p <= u a < p + L) -> ms_mem s6 a = ms_mem s a.
  Hypothesis F6live : forall q k (a : word), a_live A q = Some k -> q <= u a < q + k -> ms_mem s6 a = ms_mem s a.
  Hypothesis F6mapped : forall a : word, ms_mem s a <> None -> ms_mem s6 a <> None.
  Let A6 : astate := xadd A5 p L.
  (* [comment removed for export] *)
  Variables (A1 : astate) (s1 : mstate).
  Hypothesis HII6 : II sp0 argv envp cb [] A6 s6.
  Hypothesis HII1 : II sp0 argv envp cb [] A1 s1.
  Hypothesis HFR1 : FR A6 s6 A1 s1.
  Hypothesis HGS : gsame A6 A1.
  Hypothesis HAM : AMvm A6 A1 s6 s1.
  Hypothesis Hxm1 : a_xmaps A1 = a_xmaps A6.
  Hypothesis Hsp0 : spare A6 = 0.
  Hypothesis Har : a_areas A1 = a_areas A6.
  Hypothesis HWOk : W = WOk -> ~ am_budget A6 s6.
  (* [comment removed for export] *)
  Hypothesis HGR : am_grow (ms_vm s6) (ms_vm s1).
  Hypothesis HroomS : W <> WFail -> ~ am_room A6 s6.

  Lemma L_facts' : 0 < L /\ n + 20 <= L /\ L <= n + 20 + 4095 /\ L mod 4096 = 0.
  Proof.
    destruct (page_round_up_Z_spec (n + 20) ltac:(clear - Hn; unfold MMAP_THRESHOLD in Hn; lia)) as [[B1 B2] B3]. rewrite <- EL in *.
    unfold page_size in *. clear - B1 B2 B3 Hn. unfold MMAP_THRESHOLD in Hn. repeat split; try lia.
  Qed.

  Theorem big_fail :
    tsall W ((x <- (m_unlock ;; r <- sys_munmap (Z_to_bv 64 p) (Z_to_bv 64 (n + 20)) ;; mret w0) ;; K x) s1) P.
  Proof.
    pose proof L_facts' as (HL0 & HnL & HLn & HLm).
    pose proof (ii_is HII0) as HI0. pose proof HI0 as [HW0 HRp0 HC0 HWIN0 HE0 HG0].
    pose proof (ii_is HII1) as HI1. pose proof HI1 as [HW1 HRp1 HC1 HWIN1 HE1 HG1].
    pose proof HR5 as [L5 Ar5 Pg5 Mb5 Xm5 Fl5 Ac5 Bk5 M5 C5 D5]. pose proof HGS as [GS1 GS2 GS3 GS4 GS5 GS6].
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
    assert (OWN01 : forall x, owned_of A x -> owned_of A1 x).
    { intros x Hx. apply (fr_owned _ _ _ _ HFR1). destruct Hx as [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (Hdom6 x)). exact Hd. }
    assert (HuP : u (Z_to_bv 64 p) = p) by (apply uZ; clear - HR' LS; lia).
    assert (HuL : u (Z_to_bv 64 (n + 20)) = n + 20) by (apply uZ; clear - Hn; unfold MMAP_THRESHOLD in Hn; lia).
    assert (Hpr : page_round_up (Z_to_bv 64 (n + 20)) = Z_to_bv 64 L) by (unfold page_round_up; rewrite HuL, <- EL; reflexivity).
    (* [comment removed for export] *)
    apply tsall_assoc.
    eapply (tw_det W _ s1 _ P tt s1); [intros K' P' HK'; apply ts_unlock; [exact (envok_statics _ _ _ _ HE1) | exact HWIN1 | exact HK'] |].
    (* [comment removed for export] *)
    apply tsall_assoc.
    set (m' := unfill (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_mem s1)). set (h' := vm_munmap (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_vm s1)).
    eapply (tw_det W _ s1 _ P (Z_to_bv 64 0) (upd s1 m' h')).
    { intros K' P' HK'. eapply ts_sys_munmap; [rewrite HuP; exact Hpal | rewrite HuL; clear - Hn; unfold MMAP_THRESHOLD in Hn; lia | | |].
      - rewrite HuP, HuL, <- EL. rewrite (vm_top A1 _ (ii_vm HII1)). clear - HR'; lia.
      - rewrite Hpr. apply in_map_has. exact Hin1.
      - rewrite Hpr. exact HK'. }
    apply tw_bind_ret.
    (* [comment removed for export] *)
    assert (M'in : forall a : word, p <= u a < p + L -> m' a = None) by (intros a Ha; unfold m'; apply unfill_in; rewrite HuP, uZ by (clear - HL0 HR' LS; lia); exact Ha).
    assert (M'out : forall a : word, ~ (p <= u a < p + L) -> m' a = ms_mem s1 a) by (intros a Ha; unfold m'; apply unfill_out; rewrite HuP, uZ by (clear - HL0 HR' LS; lia); clear - Ha; lia).
    set (A2 := set_xmaps A1 []).
    assert (HI2 : IS sp0 argv envp cb A2 (upd s1 m' h')).
    { apply IS_set_xmaps. apply (IS_region sp0 argv envp cb A1 s1 m' h' p L HI1).
      - intros a. destruct (Z.lt_ge_cases (u a) p) as [H1|H1]; [left; apply M'out; clear - H1; lia|].
        destruct (Z.lt_ge_cases (u a) (p + L)) as [H2|H2]; [right; clear - H1 H2; lia | left; apply M'out; clear - H2; lia].
      - clear - HR'; lia. - clear - HR'; lia. - clear - HR'; lia.
      - intros x Hd Hx. exact (Hnodom1 x Hx Hd).
      - intros a Hm Hout Hc. unfold h'. rewrite vm_munmap_maps. pose proof (ii_vm HII1) as HV1.
        apply (mcov_remove (vm_maps (ms_vm s1)) (Z_to_bv 64 p) (Z_to_bv 64 L) (u a) 1 (vm_pw A1 _ HV1) Hin1 ltac:(rewrite uZ by (clear - HL0 HR' LS; lia); exact HL0)
                 (fun b sz Hb => proj1 (vm_maps_wf A1 _ HV1 b sz Hb)) Hc ltac:(clear; lia)).
        + right; right. exists (u a). split; [clear; lia|]. rewrite HuP, uZ by (clear - HL0 HR' LS; lia). exact Hout.
        + intros y Hy. rewrite HuP, uZ by (clear - HL0 HR' LS; lia). replace y with (u a) by (clear - Hy; lia). exact Hout.
      - intros a Ha Hm. exfalso. exact (Hm (M'in a Ha)). }
    assert (HV2 : VMok A2 h').
    { unfold A2, h'. apply (VMok_munmap_xmap A1 (ms_vm s1) p L [] HW1 (ii_vm HII1) Hxm); [clear - HR'; lia | exact HL0 | clear - HR' LS; lia | exact Hin1 | exact Hrf1 | exact Hnodom1]. }
    assert (HII2 : II sp0 argv envp cb [] A2 (upd s1 m' h')).
    { apply II_intro; [exact HI2 | exact HV2 | | |].
      - apply (AvOK_transfer A1 A2 (ii_av HII1)); [reflexivity | reflexivity | intros x mt' Hx Hrl; exists mt'; split; [exact Hx | exact Hrl]].
      - apply (UsOK_transfer A1 A2 (ii_us HII1)); [reflexivity | intros; reflexivity | intros; reflexivity].
      - apply (deads_transfer A1 A2 [] (ii_dd HII1)). intros x. unfold A2, set_xmaps. cbn [a_meta]. tauto. }
    pose proof (ii_is HII2) as [_ _ _ _ HE2 _].
    assert (LIVE1 : a_live A1 = a_live A) by (rewrite GS5; unfold A6, xadd, set_xmaps; cbn [a_live]; exact L5).
    (* [comment removed for export] *)
    apply (HL (upd s1 m' h') A2 w0 HII2).
    - (* [comment removed for export] *) constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd].
      + rewrite (fr_lo _ _ _ _ HFR1). exact F6lo.
      + rewrite (fr_hi _ _ _ _ HFR1). exact F6hi.
      + intros x Hx. exact (OWN01 x Hx).
      + intros a Hno Herr. change (~ owned_of A1 (u a)) in Hno.
        assert (HnoA : ~ owned_of A (u a)) by (intros Ho; exact (Hno (OWN01 _ Ho))).
        destruct (Z.lt_ge_cases (u a) p) as [H1|H1]; [| destruct (Z.lt_ge_cases (u a) (p + L)) as [H2|H2]].
        * rewrite M'out by (clear - H1; lia). rewrite (fr_mem _ _ _ _ HFR1 a Hno Herr). apply F6mem; [exact HnoA | clear - H1; lia].
        * rewrite M'in by (clear - H1 H2; lia). symmetry. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (Gdom (u a) ltac:(clear - H1 H2; lia))).
        * rewrite M'out by (clear - H2; lia). rewrite (fr_mem _ _ _ _ HFR1 a Hno Herr). apply F6mem; [exact HnoA | clear - H2; lia].
      + intros q k Hq. change (a_live A1 q = Some k). rewrite LIVE1. exact Hq.
      + intros q k a Hq Ha. pose proof (live_dom A q k (u a) HW0 Hq Ha) as Hd.
        assert (Hout : ~ (p <= u a < p + L)) by (intros Hp; exact (proj1 (Gdom (u a) Hp) Hd)).
        rewrite (M'out a Hout). assert (Hq6 : a_live A6 q = Some k) by (unfold A6, xadd, set_xmaps; cbn [a_live]; rewrite L5; exact Hq).
        rewrite (fr_livemem _ _ _ _ HFR1 q k a Hq6 Ha). exact (F6live q k a Hq Ha).
      + intros a Ha. assert (Hout : ~ (p <= u a < p + L)).
        { intros Hp. apply Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (Gdom (u a) Hp)). }
        rewrite (M'out a Hout). apply (fr_mapped _ _ _ _ HFR1). exact (F6mapped a Ha).
      + unfold h'. rewrite vm_munmap_limit, (fr_limit _ _ _ _ HFR1), F6vm. reflexivity.
    - reflexivity.
    - intros c Hc. change (a_active A1 c = []). rewrite (GS4 c). unfold A6, xadd, set_xmaps. cbn [a_active]. rewrite Ac5. exact (Hact c Hc).
    - exact (eo_lock _ _ _ _ HE2).
    - (* [comment removed for export] *) constructor; cbn [ms_vm upd].
      + apply (vm_fixed_of A A2 _ _ (ii_vm HII0) HV2). unfold h'. rewrite vm_munmap_limit, (fr_limit _ _ _ _ HFR1), F6vm. reflexivity.
      + intros b sz Hb. unfold h'. rewrite vm_munmap_maps. apply (proj2 (in_map_remove _ _ _)). split; [apply (amv_maps _ _ _ _ HAM); rewrite Hmaps6; right; exact Hb|].
        cbn [fst]. intros E. pose proof (proj1 (vm_maps_wf A _ (ii_vm HII0) b sz Hb)) as Hsz. destruct (Gdisj b sz Hb) as [X|X]; rewrite E, HuP in X; clear - X Hsz HL0; lia.
      + intros b sz Hb Hf. unfold h'. rewrite vm_munmap_noaccess. apply maps_subtract_free; [exact (vm_na_nw A1 _ (ii_vm HII1))|].
        apply (amv_acc _ _ _ _ HAM); [rewrite Hmaps6; right; exact Hb | rewrite Hna6; exact Hf].
      + intros Hpre. pose proof (vm_munmap_live_le (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_vm s1) Hin1) as LE. fold h' in LE. rewrite uZ in LE by (clear - HL0 HR' LS; lia).
        assert (HL6 : vm_live_bytes (ms_vm s6) = vm_live_bytes (ms_vm s) + L) by (rewrite F6vm, vm_mmap_live_bytes, uZ by (clear - HL0 HR' LS; lia); reflexivity).
        assert (Hsp6 : spare A6 = spare A) by (unfold spare, A6, xadd, set_xmaps; cbn [a_ctx a_freelist]; rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5; reflexivity).
        assert (Har0 : a_areas A6 = []).
        { unfold A6, xadd, set_xmaps. cbn [a_areas]. rewrite Ar5. destruct Hpre as [E | H4]; [exact E | exfalso; rewrite Hsp6 in Hsp0; clear - H4 Hsp0; lia]. }
        pose proof (amv_budget _ _ _ _ HAM Har0) as Bud. rewrite HL6 in Bud. pose proof (proj1 (proj1 (page_round_up_Z_spec (n + 20) ltac:(clear - Hn; unfold MMAP_THRESHOLD in Hn; lia)))).
        clear - LE Bud H HL0 Hn. unfold MMAP_THRESHOLD in Hn. lia.
    - (* [comment removed for export] *)
      left. split; [reflexivity|].
      assert (GRPA : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta A1 x = Some mtx).
      { intros x mtx aibx slx Hx Hrx. apply (GS1 x mtx aibx slx); [| exact Hrx]. unfold A6, xadd, set_xmaps. cbn [a_meta]. rewrite M5. exact Hx. }
      assert (GRPB : forall x mtx aibx slx, a_meta A1 x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta A x = Some mtx).
      { intros x mtx aibx slx Hx Hrx. pose proof (GS2 x mtx aibx slx Hx Hrx) as H6. unfold A6, xadd, set_xmaps in H6. cbn [a_meta] in H6. rewrite M5 in H6. exact H6. }
      assert (DOM01 : forall x, dom A x -> dom A1 x).
      { intros x Hd. destruct (OWN01 x (or_intror Hd)) as [Hc | Hd1]; [exfalso | exact Hd1].
        pose proof (dom_heap A x HW0 Hd) as (lo & hi & Hh & Hlh). unfold heap_range in Hh. clear - Hc Hh Hlh LN. unfold CTX_END in *. lia. }
      assert (DOM10 : forall x, dom A1 x -> dom A x \/ (exists pg, (In pg (a_areas A1) \/ In pg (a_pages A1)) /\ pg <= x < pg + 4096)).
      { intros x [(pg & Hpg & Hx) | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | (pg & Hpg & Hx)]].
        - right. exists pg. auto.
        - left. right; left. exists y, mty, aiby, sly. split; [exact (GRPB y mty aiby sly Hy Hry) | auto].
        - right. exists pg. auto. }
      constructor.
      + (* [comment removed for export] *) constructor.
        * intros x mtx Hx Hrx. exfalso. destruct (proj1 (ii_dd HII0 x) (ex_intro _ mtx (conj Hx Hrx))).
        * intros x Hd. exact (DOM01 x Hd).
        * intros x Hd. change (dom A1 x) in Hd. destruct (DOM10 x Hd) as [H0 | Hpg]; [left; exact H0 | right; right; exact Hpg].
        * rewrite Hxm0. reflexivity.
        * intros x mtx aibx slx Hx Hrx. exists mtx, aibx, slx. split; [exact (GRPA x mtx aibx slx Hx Hrx)|]. repeat split; auto.
        * intros Hpre. left. change (a_areas A1 = a_areas A /\ spare A - 4 <= spare A2).
          split; [rewrite Har; unfold A6, xadd, set_xmaps; cbn [a_areas]; exact Ar5|].
          unfold spare. pose proof (wf_ctx_nonneg A2 (is_wf _ _ _ _ _ _ HI2) KAmc). pose proof (wf_ctx_nonneg A HW0 KAmc).
          assert (Hsp6 : spare A6 = spare A) by (unfold spare, A6, xadd, set_xmaps; cbn [a_ctx a_freelist]; rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5; reflexivity).
          unfold spare in Hsp6, Hsp0. clear - H H0 Hsp6 Hsp0 Hpre. destruct Hpre as [_ | H4]; lia.
      + change (a_live A1 = a_live A). exact LIVE1.
      + intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [exact (GRPA x mtx aibx slx Hx Hrx) | exact Hrx].
      + intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [exact (GRPB x mtx aibx slx Hx Hrx) | exact Hrx].
      + (* [comment removed for export] *) left. split; [change (a_areas A1 = a_areas A); rewrite Har; unfold A6, xadd, set_xmaps; cbn [a_areas]; exact Ar5|].
        assert (Hsp6 : spare A6 = spare A) by (unfold spare, A6, xadd, set_xmaps; cbn [a_ctx a_freelist]; rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5; reflexivity).
        pose proof (wf_ctx_nonneg A1 HW1 KAmc) as K0. unfold spare in Hsp6, Hsp0 |- *. unfold A2. cbn [a_ctx a_freelist set_xmaps]. clear - K0 Hsp6 Hsp0. lia.
    - intros HWf H0. exfalso. apply H0. reflexivity.
    - (* [comment removed for export] *)
      intros HWk _. right; right. split; [clear - Hn; lia|].
      set (mu := unfill (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_mem s6)).
      assert (MUin : forall a : word, p <= u a < p + L -> mu a = None) by (intros a Ha; unfold mu; apply unfill_in; rewrite HuP, uZ by (clear - HL0 HR' LS; lia); exact Ha).
      assert (MUout : forall a : word, ~ (p <= u a < p + L) -> mu a = ms_mem s6 a) by (intros a Ha; unfold mu; apply unfill_out; rewrite HuP, uZ by (clear - HL0 HR' LS; lia); clear - Ha; lia).
      pose proof (ii_is HII6) as HI6.
      assert (HI6u : IS sp0 argv envp cb A6 (upd s6 mu (ms_vm s6))).
      { apply (IS_region sp0 argv envp cb A6 s6 mu (ms_vm s6) p L HI6).
        - intros a. destruct (Z.lt_ge_cases (u a) p) as [H1|H1]; [left; apply MUout; clear - H1; lia|].
          destruct (Z.lt_ge_cases (u a) (p + L)) as [H2|H2]; [right; clear - H1 H2; lia | left; apply MUout; clear - H2; lia].
        - clear - HR'; lia. - clear - HR'; lia. - clear - HR'; lia.
        - intros x Hd Hx. exact (proj1 (Gdom x Hx) (proj1 (Hdom6 x) Hd)).
        - intros a _ _ Hc. exact Hc.
        - intros a Ha Hm. exfalso. exact (Hm (MUin a Ha)). }
      exists A6, (upd s6 mu (ms_vm s6)). split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
      + pose proof HII6 as [_ V6 Av6 Us6 Dd6]. apply II_intro; [exact HI6u | exact V6 | exact Av6 | exact Us6 | exact Dd6].
      + constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd].
        * exact F6lo. * exact F6hi.
        * intros x [Hc | Hd]; [left; exact Hc | right; apply (proj2 (Hdom6 x)); exact Hd].
        * intros a Hno _. assert (HnoA : ~ owned_of A (u a)) by (intros [Hc | Hd]; apply Hno; [left; exact Hc | right; apply (proj2 (Hdom6 (u a))); exact Hd]).
          destruct (Z.lt_ge_cases (u a) p) as [H1|H1]; [| destruct (Z.lt_ge_cases (u a) (p + L)) as [H2|H2]].
          -- rewrite MUout by (clear - H1; lia). apply F6mem; [exact HnoA | clear - H1; lia].
          -- rewrite MUin by (clear - H1 H2; lia). symmetry. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (Gdom (u a) ltac:(clear - H1 H2; lia))).
          -- rewrite MUout by (clear - H2; lia). apply F6mem; [exact HnoA | clear - H2; lia].
        * intros q k Hq. unfold A6, xadd, set_xmaps. cbn [a_live]. rewrite L5. exact Hq.
        * intros q k a Hq Ha. pose proof (live_dom A q k (u a) HW0 Hq Ha) as Hd.
          assert (Hout : ~ (p <= u a < p + L)) by (intros Hp; exact (proj1 (Gdom (u a) Hp) Hd)).
          rewrite (MUout a Hout). exact (F6live q k a Hq Ha).
        * intros a Ha. assert (Hout : ~ (p <= u a < p + L)).
          { intros Hp. apply Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (proj2 (Gdom (u a) Hp)). }
          rewrite (MUout a Hout). exact (F6mapped a Ha).
        * rewrite F6vm. apply vm_mmap_limit.
      + cbn [ms_vm upd]. intros b sz Hb. rewrite Hmaps6. right. exact Hb.
      + cbn [ms_vm upd]. rewrite F6vm, vm_mmap_live_bytes, uZ, <- EL by (clear - HL0 HR' LS; lia). clear; lia.
      + unfold A6, xadd, set_xmaps. cbn [a_areas]. exact Ar5.
      + unfold spare, A6, xadd, set_xmaps. cbn [a_ctx a_freelist]. rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5. reflexivity.
      + intros Hb. apply (HWOk HWk). unfold am_budget in *. cbn [ms_vm upd] in Hb. exact Hb.
      + intros x. unfold A6, xadd, set_xmaps. cbn [a_meta]. apply M5.
      + exists p. unfold A6, xadd, set_xmaps. cbn [a_xmaps]. rewrite Xm5, Hxm0, <- EL. reflexivity.
    - (* [comment removed for export] *)
      unfold malloc_growS. cbn [ms_vm upd]. rewrite (malloc_db_big n (proj1 Hn)).
      assert (Hsp6 : spare A6 = spare A).
      { unfold spare, A6, xadd, set_xmaps. cbn [a_ctx a_freelist]. rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5. reflexivity. }
      assert (G6 : sgrow 1 L 0 A A6 (ms_vm s) (ms_vm s6)).
      { rewrite F6vm. apply (grow_mmap A A6 (ms_vm s) p L (ii_vm HII0)); [clear - HR'; lia | clear - HL0; lia | clear - HR' LS; lia | | rewrite Hsp6; apply Z.le_refl].
        unfold A6, xadd, set_xmaps. cbn [a_areas]. exact Ar5. }
      assert (G1 : sgrow 1 8192 0 A6 A1 (ms_vm s6) (ms_vm s1)).
      { exact (sgrow_am_fail A6 A1 _ _ HGR Hsp0 Har (spare_nn A1 (is_wf _ _ _ _ _ _ (ii_is HII1)))). }
      assert (G2 : sgrow (-1) 0 0 A1 A2 (ms_vm s1) h') by (unfold h'; apply (grow_munmap A1 A2 (ms_vm s1) _ _ (ii_vm HII1) Hin1); [reflexivity | apply Z.le_refl]).
      pose proof (sgrow_trans _ _ _ _ _ _ A A1 A2 _ _ _ (sgrow_trans _ _ _ _ _ _ A A6 A1 _ _ _ G6 G1) G2) as GT.
      split; [apply (sgrow_weaken (1 + 1 + -1) (L + 8192 + 0) (0 + 0 + 0)); [exact GT | clear; lia | clear - HLn Hn; unfold MMAP_THRESHOLD in Hn; lia | clear; lia| clear; lia]|].
      (* [comment removed for export] *)
      rewrite (malloc_dp_big n (proj1 Hn)).
      apply pgrow_backed; [pose proof (sg_backed _ _ _ _ _ _ _ GT) as BK; clear - BK HLn; lia | |].
      2: { (* [comment removed for export] *)
           rewrite <- Hsp6, Hsp0. change (0 <= spare A1). exact (spare_nn A1 (is_wf _ _ _ _ _ _ (ii_is HII1))). }
      rewrite (pot_keep_meta A A2 HW0); [apply Z.le_refl | |].
      + intros c _. change (a_active A1 c = a_active A c). rewrite (GS4 c). unfold A6, xadd, set_xmaps. cbn [a_active]. rewrite Ac5. reflexivity.
      + intros x mtx aibx slx Hx Hrx. exists mtx, aibx. split; [| exact Hrx]. change (a_meta A1 x = Some mtx).
        apply (GS1 x mtx aibx slx); [| exact Hrx]. unfold A6, xadd, set_xmaps. cbn [a_meta]. rewrite M5. exact Hx.
    - (* [comment removed for export] *)
      intros HWnf _. unfold malloc_noroomS. rewrite (malloc_db_big n (proj1 Hn)). exists [], A6, s6. split; [exact HII6|].
      split.
      { apply (sgrow_weaken 1 L 0); [| clear; lia | clear - HLn; lia | clear; lia| clear; lia].
        rewrite F6vm. apply (grow_mmap A A6 (ms_vm s) p L (ii_vm HII0)); [clear - HR'; lia | clear - HL0; lia | clear - HR' LS; lia | |].
        - unfold A6, xadd, set_xmaps. cbn [a_areas]. exact Ar5.
        - unfold spare, A6, xadd, set_xmaps. cbn [a_ctx a_freelist]. rewrite (C5 KAmc I ltac:(cbn; tauto)), Fl5. apply Z.le_refl. }
      split; [| left; exact (HroomS HWnf)].
      unfold A6, xadd, set_xmaps. cbn [a_xmaps lsum]. rewrite Xm5, Hxm0. cbn [lsum]. clear - HLn HL0. lia.
  Qed.
End BigFail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BigTop.
  Context {R : Type}.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (sp : word) (n : Z).
  Variables (K : word -> M R) (P : R -> mstate -> Prop).
  Hypothesis HII : II sp0 argv envp cb [] A s.
  Hypothesis Hxm : a_xmaps A = [].
  Hypothesis Hact : ACT48 A.
  Hypothesis Hn : MMAP_THRESHOLD <= n < 2^61.
  Hypothesis HL : MLeaf W sp0 argv envp cb A s n K P.

  Theorem mal_big_ok : tsall W ((r <- mal_big sp (Z_to_bv 64 n) ;; K r) s) P.
  Proof.
    pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG]. ceil.
    pose proof layout_nums as LN. pose proof layout_small as LS.
    assert (Hn0 : 0 <= n < 2^61) by (clear - Hn; unfold MMAP_THRESHOLD in Hn; lia).
    unfold mal_big. cbv zeta. rewrite v_addi_Z.
    set (L := page_round_up_Z (n + 20)).
    destruct (page_round_up_Z_spec (n + 20) ltac:(clear - Hn0; lia)) as [[B1 B2] B3]. fold L in B1, B2, B3. unfold page_size in *.
    assert (HuL : u (Z_to_bv 64 (n + 20)) = n + 20) by (apply uZ; clear - Hn0; lia).
    assert (Hpr : page_round_up (Z_to_bv 64 (n + 20)) = Z_to_bv 64 L) by (unfold page_round_up; rewrite HuL; reflexivity).
    assert (HmmL : mm_len (Z_to_bv 64 (n + 20)) = L) by (unfold mm_len; rewrite HuL; reflexivity).
    apply tsall_assoc.
    eapply tw_sys_mmap04; [rewrite HuL; clear - Hn0; lia | rewrite HuL; clear - Hn0; lia | |].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      intros Hnone. assert (HWf : W <> WOk \/ forall a0, mmap_grant_ok MMrw (ms_vm s) a0 (mm_len (Z_to_bv 64 (n + 20))) = false) by (right; exact Hnone).
      eapply tw_set_errno; [exact HWIN|]. cbv beta.
      unfold MAP_FAILED at 1. rewrite wm1_eq, c_eq_Z by (clear; lia). rewrite Z.eqb_refl. cbv iota.
      apply tw_bind_ret.
      set (se := upd s (errno_mem (ms_mem s) ENOMEM) (ms_vm s)).
      pose proof (II_errno sp0 argv envp cb [] A s ENOMEM HII) as HIIe. fold se in HIIe. pose proof (ii_is HIIe) as [_ _ _ _ HEe _].
      apply (HL se A w0 HIIe).
      + apply FR_errno. exact HW.
      + exact Hxm.
      + exact Hact.
      + exact (eo_lock _ _ _ _ HEe).
      + constructor; unfold se; cbn [ms_vm upd].
        * apply (vm_fixed_of A A _ _ (ii_vm HII) (ii_vm HII)). reflexivity.
        * auto. * auto.
        * intros _. clear - B1 Hn0. lia.
      + left. split; [reflexivity|]. constructor; [constructor | reflexivity | | | left; split; [reflexivity | clear; lia]].
        * intros x mt Hx Hr. exact Hx.
        * intros x Hd. exact Hd.
        * intros x Hd. left. exact Hd.
        * reflexivity.
        * intros x mt aib sl Hx Hr. exists mt, aib, sl. repeat split; auto.
        * intros _. left. split; [reflexivity | clear; lia].
        * intros x mt aib sl Hx Hr. exists mt, aib. auto.
        * intros x mt aib sl Hx Hr. exists mt, aib. auto.
      + intros _ H0. exfalso. apply H0. reflexivity.
      + intros HWk _. right; left. split; [clear - Hn; lia|]. destruct HWf as [HWf | Hall]; [exfalso; exact (HWf HWk)|].
        intros a. specialize (Hall a). rewrite HmmL in Hall. exact Hall.
      + (* [comment removed for export] *) unfold malloc_growS, se. cbn [ms_vm upd]. rewrite (malloc_db_big n (proj1 Hn)).
        split; [apply (sgrow_weaken 0 0 0); [apply sgrow_refl | clear; lia | clear - Hn0; lia | clear; lia| clear; lia]|].
        rewrite (malloc_dp_big n (proj1 Hn)). apply (pgrow_weaken 0); [apply pgrow_refl | clear - Hn0; lia].
      + (* [comment removed for export] *)
        intros HWnf _. unfold malloc_noroomS. rewrite (malloc_db_big n (proj1 Hn)). exists [], A, s. split; [exact HII|].
        split; [apply (sgrow_weaken 0 0 0); [apply sgrow_refl | clear; lia | clear - Hn0; lia | clear; lia| clear; lia]|].
        split; [clear - Hn0; lia|]. right. exists L.
        split; [clear - B1 B2 Hn0; unfold page_size in *; lia|]. split; [exact B3|].
        split; [clear - B1 B2 Hn0; unfold page_size in *; lia|].
        intros a. specialize (Hnone a). rewrite HmmL in Hnone. exact Hnone.
    - (* [comment removed for export] *)
      intros HWs a Hg. cbn [mmap_grant_ok] in Hg. rewrite HmmL in Hg.
      pose proof (VMok_core A _ (ii_vm HII)) as HVc.
      destruct (mmap_grant_facts sp0 argv envp cb A s a (Z_to_bv 64 (n + 20)) HI HVc ltac:(rewrite HuL; clear - Hn0; lia) ltac:(rewrite HuL; clear - Hn0; lia) ltac:(rewrite HuL; exact Hg))
        as (EnZ & _ & G1 & Glo & Gce & Gimg & Gm & Gna & Gdom & Gdisj & _).
      destruct (mmap_rw_ok sp0 argv envp cb A s a (Z_to_bv 64 (n + 20)) HI (ii_vm HII) ltac:(rewrite HuL; clear - Hn0; lia) ltac:(rewrite HuL; clear - Hn0; lia) ltac:(rewrite HuL; exact Hg)) as [HI3 HV3].
      rewrite HuL in *. rewrite Hpr in *. fold L in Glo, Gce, Gimg, Gdom, Gdisj, HI3, HV3, Gm, Gna.
      pose proof (u64_range a) as Ha. set (p := u a) in *. change (page_aligned p) in G1.
      assert (Ea : a = Z_to_bv 64 p) by (subst p; symmetry; apply Z_to_bv_bv_unsigned).
      set (A3 := xadd A p L) in *. set (s3 := upd s (zfill a (Z_to_bv 64 L) (ms_mem s)) (vm_mmap a (Z_to_bv 64 L) (ms_vm s))) in *.
      assert (HII3 : II sp0 argv envp cb [] A3 s3).
      { apply II_intro; [exact HI3 | exact HV3 | | |].
        - apply (AvOK_transfer A A3 (ii_av HII)); [reflexivity | reflexivity | intros x mt' Hx Hrl; exists mt'; split; [exact Hx | exact Hrl]].
        - apply (UsOK_transfer A A3 (ii_us HII)); [reflexivity | intros; reflexivity | intros; reflexivity].
        - apply (deads_transfer A A3 [] (ii_dd HII)). intros x. unfold A3, xadd, set_xmaps. cbn [a_meta]. tauto. }
      pose proof (ii_is HII3) as HI3'. pose proof HI3' as [HW3 HRp3 _ HWIN3 HE3 _]. pose proof (repw_init A3 (ms_mem s3) HW3 HRp3) as RW30.
      cbv beta. rewrite wm1_eq, (c_eq_u a (2^64 - 1)) by (clear; lia). fold p.
      replace (p =? 2^64 - 1) with false by (symmetry; apply Z.eqb_neq; clear - Gce B1 Hn0 LN; lia). cbv iota.
      (* [comment removed for export] *)
      apply tsall_assoc. eapply (tw_det W _ s3 _ P (Z_to_bv 64 0) s3); [intros K' P' HK'; apply ts_needlocks; [exact (envok_statics _ _ _ _ HE3) | exact HWIN3 | exact HK'] |].
      cbv beta. apply tsall_assoc. apply tw_assert; [reflexivity|].
      (* [comment removed for export] *)
      apply tsall_assoc. rewrite (addr_lock 920), <- caddr_KSeq_lock.
      eapply (tw_det W _ s3 _ P (Z_to_bv 64 (a_ctx A3 KSeq mod 256)) s3).
      { intros K' P' HK'. eapply (ts_lbu_ctxW_m A3 HW3 s3 (ms_mem s3) [] KSeq); [exact RW30 | exact HWIN3 | exact I | reflexivity | apply wfree_range_nil | exact HK']. }
      pose proof (Z.mod_pos_bound (a_ctx A3 KSeq) 256 ltac:(clear; lia)) as Hsqv. set (sqv := a_ctx A3 KSeq mod 256) in *. clearbody sqv.
      apply tsall_assoc.
      eapply (tw_lift W (ag_seq (Z_to_bv 64 sqv)) s3
                (fun sq' s4 => exists (sqn : Z) (reset : bool), sq' = Z_to_bv 64 sqn /\ 1 <= sqn <= 256 /\
                   RepW A3 (ms_mem s3) (reset_writes reset) (ms_mem s4) /\ WIN s4 /\ ms_vm s4 = ms_vm s3 /\ ms_lo s4 = ms_lo s3 /\ ms_hi s4 = ms_hi s3)).
      { intros K' P' HK'. apply (ag_seq_ok A3 s3 (ms_mem s3) [] sqv K' P' RW30 HWIN3 ltac:(clear - Hsqv; lia)).
        intros s4 sq' reset Hsq RW4 HWIN4 Hvm4 Hlo4 Hhi4. apply HK'. exists sq', reset. rewrite app_nil_r in RW4. auto 10. }
      intros sq' s4 (sqn & reset & -> & Hsqn & RW4 & HWIN4 & Hvm4 & Hlo4 & Hhi4).
      apply tsall_assoc.
      eapply (tw_lift W (m_sb (Z_to_bv 64 (caddr KSeq)) (Z_to_bv 64 sqn)) s4
                (fun _ s5 => exists m5, s5 = upd s3 m5 (ms_vm s3) /\
                   II sp0 argv envp cb [] (set_ctx A3 (c_w A3 (FCT (caddr KSeq) 1 sqn :: reset_writes reset))) s5 /\ ntframe A3 s3 s5)).
      { intros K' P' HK'. eapply (ts_sb_ctxW A3 s4 (ms_mem s3) (reset_writes reset) KSeq); [exact RW4 | exact HWIN4 | exact I | reflexivity |].
        intros m5 RW5. rewrite uZ in RW5 by (clear - Hsqn; lia).
        destruct (heur_commit sp0 argv envp cb [] A3 s3 _ m5 HII3 RW5 (seq_writes_slots sqn reset)) as (HII5 & NF5 & HR5).
        rewrite (upd_eq s3 s4 m5 (ms_vm s4) Hlo4 Hhi4), Hvm4. apply HK'. exists m5. split; [reflexivity|]. split; [exact HII5 | exact NF5]. }
      intros x5 s5 (m5 & Es5 & HII5 & NF5). clear x5.
      set (cw := c_w A3 (FCT (caddr KSeq) 1 sqn :: reset_writes reset)) in *.
      pose proof (c_w_heur A3 (FCT (caddr KSeq) 1 sqn :: reset_writes reset)) as Hcw. fold cw in Hcw.
      set (A5 := set_ctx A cw). set (A6 := set_ctx A3 cw) in *.
      assert (EA6 : A6 = xadd A5 p L) by reflexivity.
      assert (HR5' : hrel A A5) by (apply hrel_set_ctx; intros k; destruct (Hcw k) as [Hh | Hk]; [left; exact Hh | right; exact Hk]).
      (* [comment removed for export] *)
      assert (ZOUT : forall a0 : word, ~ (p <= u a0 < p + L) -> zfill a (Z_to_bv 64 L) (ms_mem s) a0 = ms_mem s a0).
      { intros a0 Ha0. apply zfill_out. rewrite uZ by (clear - B1 Gce LN Hn0 Glo; lia). fold p.
        destruct (Z.lt_ge_cases (u a0) p) as [H1 | H1]; [left; exact H1 | right].
        destruct (Z.lt_ge_cases (u a0) (p + L)) as [H2 | H2]; [exfalso; apply Ha0; split; assumption | exact H2]. }
      assert (ZIN : forall a0 : word, p <= u a0 < p + L -> zfill a (Z_to_bv 64 L) (ms_mem s) a0 = Some (Z_to_bv 8 0)).
      { intros a0 Ha0. apply zfill_in. rewrite uZ by (clear - B1 Gce LN Hn0 Glo; lia). exact Ha0. }
      assert (Hown3 : forall x, owned_of A3 x <-> owned_of A x) by (intros x; reflexivity).
      assert (F6lo : ms_lo s5 = ms_lo s) by (rewrite (nf_lo _ _ _ NF5); reflexivity).
      assert (F6hi : ms_hi s5 = ms_hi s) by (rewrite (nf_hi _ _ _ NF5); reflexivity).
      assert (F6vm : ms_vm s5 = vm_mmap (Z_to_bv 64 p) (Z_to_bv 64 L) (ms_vm s)) by (rewrite (nf_vm _ _ _ NF5), <- Ea; reflexivity).
      assert (F6mem : forall a0 : word, ~ owned_of A (u a0) -> ~ (p <= u a0 < p + L) -> ms_mem s5 a0 = ms_mem s a0).
      { intros a0 Hno Hout. rewrite (nf_mem _ _ _ NF5 a0) by (intros Ho; exact (Hno (proj1 (Hown3 _) Ho))). unfold s3. cbn [ms_mem upd]. exact (ZOUT a0 Hout). }
      assert (F6live : forall q k (a0 : word), a_live A q = Some k -> q <= u a0 < q + k -> ms_mem s5 a0 = ms_mem s a0).
      { intros q k a0 Hq Hin. rewrite (nf_live _ _ _ NF5 q k a0); [| exact Hq | exact Hin]. unfold s3. cbn [ms_mem upd]. apply ZOUT.
        intros Hx. exact (proj1 (Gdom (u a0) Hx) (live_dom A q k (u a0) HW Hq Hin)). }
      assert (F6mapped : forall a0 : word, ms_mem s a0 <> None -> ms_mem s5 a0 <> None).
      { intros a0 Ha0. apply (nf_mapped _ _ _ NF5 a0). unfold s3. cbn [ms_mem upd].
        destruct (Z.lt_ge_cases (u a0) p) as [H1 | H1]; [rewrite ZOUT by (intros [X _]; clear - X H1; lia); exact Ha0|].
        destruct (Z.lt_ge_cases (u a0) (p + L)) as [H2 | H2]; [rewrite ZIN by (split; assumption); discriminate|].
        rewrite ZOUT by (intros [_ X]; clear - X H2; lia). exact Ha0. }
      assert (F6zero : forall a0 : word, p <= u a0 < p + L -> ms_mem s5 a0 = Some (Z_to_bv 8 0)).
      { intros a0 Ha0. rewrite (nf_mem _ _ _ NF5 a0).
        - unfold s3. cbn [ms_mem upd]. exact (ZIN a0 Ha0).
        - intros [Hc | Hd]; [pose proof ctx_block_rw as CB; clear - CB Hc Ha0 Gimg LN; unfold CTX_END in *; lia | exact (proj1 (Gdom (u a0) Ha0) Hd)]. }
      assert (Hhr : heap_range p (p + L)) by (unfold heap_range; repeat split; [exact Glo | clear - B1 Hn0; lia | exact Gce | exact Gimg]).
      assert (Gna' : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 L) = true) by (rewrite <- Ea; exact Gna).
      rewrite Es5 in HII5. fold A6 in HII5. rewrite EA6 in HII5.
      assert (HII6 : II sp0 argv envp cb [] (xadd A5 p L) s5) by (rewrite Es5; exact HII5).
      (* [comment removed for export] *)
      apply tsall_assoc.
      apply (alloc_meta_okX W R sp0 argv envp cb [] (xadd A5 p L) s5 (at_ sp (-64)) _ P HII6).
      + (* [comment removed for export] *)
        intros s1 A1 HII1 HFR1 HGS1 HAM1 Hxm1 Hdom1 Hsp0 Har1 HWOk HGR1 HroomS1. cbv beta. rewrite is0_Z by (clear; lia). cbv iota.
        rewrite Ea.
        apply (big_fail W sp0 argv envp cb A s n K P HII Hxm Hact Hn HL A5 s5 p L HR5' eq_refl G1 Hhr Gdom Gna' Gdisj F6lo F6hi F6vm F6mem F6live F6mapped
                 A1 s1 HII6 HII1 HFR1 HGS1 HAM1 Hxm1 Hsp0 Har1 HWOk HGR1 HroomS1).
      + (* [comment removed for export] *)
        intros s1 A1 m HII1 HFR1 HGM HAM1 Hxm1 Hdelta Hsp HGR1. cbv beta.
        pose proof (gm_lo _ _ _ _ HGM) as Hmlo. pose proof (gm_hi _ _ _ _ HGM) as Hmhi.
        rewrite is0_Z by (clear - Hmlo Hmhi LS; lia). replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hmlo; lia). cbv iota.
        rewrite Ea. rewrite (bigw32_word n) by (clear - Hn0; lia). fold L.
        apply (big_ok W sp0 argv envp cb A s n K P HII Hxm Hact Hn HL HWs A5 s5 p L HR5' eq_refl G1 Hhr Gdom Gna' F6lo F6hi F6vm F6mem F6live F6mapped F6zero
                 A1 s1 m HII1 HFR1 HGM HAM1 Hxm1 Hsp HGR1).
  Qed.
End BigTop.

End WithLayout.
