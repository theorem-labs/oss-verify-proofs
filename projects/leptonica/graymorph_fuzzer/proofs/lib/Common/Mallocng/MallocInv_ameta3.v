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
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_vmops MallocInv_ameta_base MallocInv_ameta_iface MallocInv_ameta2 MallocInv_free.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Local Ltac llia ::= first [ solve [LiaFast.flia2] | pose proof layout_small; lia | pose proof layout_nums; lia | lia ].   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


Local Notation u := bv_unsigned (only parsing).

Ltac cside := cbn [f_a f_n f_v caddr clen]; unfold C_AM, C_AMC, C_FMH, C_INIT, C_SECRET, C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_SHIFT, C_BRK; llia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wlook_none_wfree : forall ws x, wlook ws x = None -> wfree ws x.
Proof using Type. pu_keep tt.
  induction ws as [|w ws IH]; intros x H; [apply wfree_nil|].
  cbn [wlook] in H. destruct (wcov w x) eqn:E; [discriminate H|].
  apply wfree_cons; [exact (wcov_false w x E) | apply IH; exact H].
Qed.

(* [comment removed for export] *)
Lemma repw_commit3 : forall A A' m0 ws m,
  RepW A m0 ws m ->
  (forall x b, facts A' x b -> facts A x b \/ wlook ws x <> None \/ (mbyte m0 x = Some b /\ 0 <= x < 2^64)) ->
  (forall x b, facts A' x b -> wlook ws x <> None -> wlook ws x = Some b) ->
  (forall x, dom A' x -> dom A x \/ m0 (Z_to_bv 64 x) <> None) ->
  Rep A' m.
Proof using Type. pu_keep tt.
  intros A A' m0 ws m HR H1 H2 Hd. constructor.
  - intros x b Hf. destruct (wlook ws x) as [b'|] eqn:E.
    + apply (rw_wr A m0 ws m HR). apply H2; [exact Hf | rewrite E; discriminate].
    + destruct (H1 x b Hf) as [H | [H | [H Hx]]].
      * apply (rw_fact A m0 ws m HR); assumption.
      * exfalso. apply H. exact E.
      * rewrite <- H. apply mbyte_ext. rewrite <- (uZ x) in E by llia.
        apply (rw_frame A m0 ws m HR). apply wlook_none_wfree. exact E.
  - intros x Hx. destruct (Hd x Hx) as [H | H].
    + apply (rw_dom A m0 ws m HR). exact H.
    + apply (rw_mapped A m0 ws m HR). exact H.
Qed.

Section MappedStore.
  Context {R : Type}.
  Variable A : astate.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop) (ws : list fct).

  (* [comment removed for export] *)
  Lemma ts_st_mappedw : forall s (m0 : word -> option byte) ws (n : nat) a v (k : unit -> M R) P,
    RepW A m0 ws (ms_mem s) -> WIN s -> (0 < n)%nat -> 0x1000 <= a -> a + Z.of_nat n <= alloc_ceiling ->
    (a + Z.of_nat n <= IMG_LO \/ IMG_HI <= a) ->
    (forall j, 0 <= j < Z.of_nat n -> m0 (Z_to_bv 64 (a + j)) <> None) ->
    tsafe (k tt (upd s (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)) (ms_vm s))) P ->
    tsafe ((x <- m_st n (Z_to_bv 64 a) v ;; k x) s) P.
  Proof using MLok. pu_keep (MLok).
    intros s m0 ws n a v k P HR HWn Hn Hlo Hce Himg Hm Hk. pose proof alloc_ceiling_val as HCV.
    eapply ts_st.
    - apply acc_ok_heap; [exact HWn | llia | llia | llia].
    - apply st_zone_heap; llia.
    - apply store_ok_of_all; [rewrite u_lit by llia; llia|].
      intros y Hy. rewrite u_lit in Hy by llia. unfold wview.
      pose proof (rw_mapped A m0 ws _ HR (Z_to_bv 64 (a + (u y - a))) (Hm (u y - a) ltac:(llia))) as Hy'.
      replace (a + (u y - a)) with (u y) in Hy' by llia. rewrite Z_to_bv_bv_unsigned in Hy'.
      destruct (ms_mem s y); [discriminate | exfalso; apply Hy'; reflexivity].
    - exact Hk.
  Qed.

  Lemma repw_st_mapped : forall s (m0 : word -> option byte) ws (n : nat) a v,
    RepW A m0 ws (ms_mem s) -> 0x1000 <= a -> a + Z.of_nat n <= alloc_ceiling ->
    (a + Z.of_nat n <= IMG_LO \/ IMG_HI <= a) ->
    RepW A m0 (FCT a (Z.of_nat n) (bv_unsigned v) :: ws) (wbytes (ms_mem s) (Z_to_bv 64 a) (word_to_le_bytes n v)).
  Proof using Type. pu_keep tt.
    intros s m0 ws n a v HR Hlo Hce Himg. pose proof alloc_ceiling_val as HCV.
    apply repw_store; [exact HR | llia | llia | unfold wzone; cbn; llia].
  Qed.
End MappedStore.

(* [comment removed for export] *)
Lemma usage_fold_app : forall (f : Z -> Z) l p,
  fold_right (fun pg acc => f pg + acc) 0 (l ++ [p]) = fold_right (fun pg acc => f pg + acc) 0 l + f p.
Proof using Type. pu_keep tt.
  intros f l p. induction l as [|a l IH]; cbn [fold_right app]; [llia|]. rewrite IH. llia.
Qed.

Lemma usage_fold_ext : forall (f g : Z -> Z) l, (forall x, f x = g x) ->
  fold_right (fun pg acc => f pg + acc) 0 l = fold_right (fun pg acc => g pg + acc) 0 l.
Proof using Type. pu_keep tt.
  intros f g l H. induction l as [|a l IH]; cbn [fold_right]; [reflexivity|]. rewrite IH, H. reflexivity.
Qed.

Lemma byte_of_mod64 : forall v k, 0 <= k < 8 -> byte_of (v mod 2^64) k = byte_of v k.
Proof using Type. pu_keep tt.
  intros v k Hk. apply Z.bits_inj'. intros j Hj. rewrite !MallocInv_free.byte_of_testbit by llia.
  destruct (j <? 8) eqn:E; [apply Z.ltb_lt in E | reflexivity].
  apply Z.mod_pow2_bits_low. llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Commit.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Variable p : Z.
  Hypothesis HI : IS sp0 argv envp cb A s.
  Hypothesis HVc : VMcore A (ms_vm s).
  Hypothesis HVall : VMall A (ms_vm s).
  Hypothesis HAV : AvOK A.
  Hypothesis HUS : UsOK A.
  Hypothesis HD : deads A D.
  Hypothesis Hinit : a_ctx A KInit = 1.
  Hypothesis Hamc : a_ctx A KAmc = 0.
  Hypothesis Hfl : a_freelist A = [].
  Hypothesis Hbrk : a_ctx A KBrk <> 0.
  Hypothesis Haac : 1 <= a_ctx A KAac.
  Hypothesis Hal : page_aligned p.
  Hypothesis Hheap : heap_range p (p + 4096).
  Hypothesis Hpdom : forall x, p <= x < p + 4096 -> ~ dom A x.
  Hypothesis Hzero : forall x, p <= x < p + 4096 -> ms_mem s (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Hypothesis Hcov : mcov (vm_maps (ms_vm s)) p 4096.
  Hypothesis Hnafree : region_free (vm_noaccess (ms_vm s)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true.
  (* [comment removed for export] *)
  Hypothesis HbrkOK : a_ctx A KBrk = 2^64 - 1 \/
     (a_ctx A KBrk = u (vm_brk (ms_vm s)) /\ 0 < u (vm_brk (ms_vm s)) /\
      u (vm_start_brk (ms_vm s)) <= u (vm_brk (ms_vm s)) /\ page_aligned (u (vm_brk (ms_vm s)))).
  Hypothesis Hres : a_ctx A KAac - 1 > 0 ->
     (p + 4096) + 4096 * (a_ctx A KAac - 1) <= alloc_ceiling /\
     map_contains (vm_maps (ms_vm s)) (Z_to_bv 64 (p + 4096)) (Z_to_bv 64 (4096 * (a_ctx A KAac - 1))) = true /\
     map_contains (vm_noaccess (ms_vm s)) (Z_to_bv 64 (p + 4096)) (Z_to_bv 64 (4096 * (a_ctx A KAac - 1))) = true.
  Hypothesis Hspan : u (vm_brk (ms_vm s)) - u (vm_start_brk (ms_vm s)) <= 4096 * (Z.of_nat (length (a_areas A)) + 2).
  Implicit Types (P : R -> mstate -> Prop).

  Let aac := a_ctx A KAac.
  Let m := p + 24.
  Definition cmA : astate := aaA A p (aac - 1) (p + 4096).

  Lemma HWc : WF A. Proof using HI. pu_keep (HI). exact (is_wf _ _ _ _ _ _ HI). Qed.

  Lemma p_disj_area : forall pg, In pg (a_areas A) -> pg + 4096 <= p \/ p + 4096 <= pg.
  Proof using HI Hal Hpdom. pu_keep (HI, Hal, Hpdom).
    intros pg Hpg. destruct (wf_areas_al A HWc pg Hpg) as [Halp _]. unfold page_aligned in *.
    destruct (Z.eq_dec pg p) as [-> | Hne]; [exfalso; apply (Hpdom p); [llia | left; exists p; split; [exact Hpg | llia]]|].
    destruct (pages_disj pg p Halp Hal Hne); llia.
  Qed.
  Lemma p_disj_grp : forall ma mt aib sl, a_meta A ma = Some mt -> mt_role mt = RGroup aib sl ->
    0 < mt_maplen mt -> p + 4096 <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= p.
  Proof using HI Hbrk HbrkOK Hpdom. pu_keep (HI, Hbrk, HbrkOK, Hpdom).
    intros ma mt aib sl Hma Hr Hml.
    destruct (wf_grp A HWc ma mt aib sl Hma Hr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hce & Hpg).
    destruct (Hpg Hml) as [Halg _]. unfold page_aligned, grp_map_len in *.
    destruct (Z.lt_ge_cases (p + 4096) (mt_mem mt + 1)) as [L|L]; [left; llia|].
    destruct (Z.lt_ge_cases (mt_mem mt + mt_maplen mt * 4096) (p + 1)) as [L2|L2]; [right; llia|].
    exfalso. destruct (Z.lt_ge_cases p (mt_mem mt)) as [L3|L3].
    - apply (Hpdom (mt_mem mt)); [llia|]. right; left. exists ma, mt, aib, sl. unfold grp_map_len. repeat split; auto; llia.
    - apply (Hpdom p); [llia|]. right; left. exists ma, mt, aib, sl. unfold grp_map_len. repeat split; auto; llia.
  Qed.
  Lemma p_disj_page : forall pg, In pg (a_pages A) -> pg + 4096 <= p \/ p + 4096 <= pg.
  Proof using HI Hal Hpdom. pu_keep (HI, Hal, Hpdom).
    intros pg Hpg. destruct (wf_pages_al A HWc pg Hpg) as [Halp _]. unfold page_aligned in *.
    destruct (Z.eq_dec pg p) as [-> | Hne]; [exfalso; apply (Hpdom p); [llia | right; right; exists p; split; [exact Hpg | llia]]|].
    destruct (pages_disj pg p Halp Hal Hne); llia.
  Qed.

  Lemma WF_cmA : WF cmA.
  Proof using HI Haac Hal Hbrk HbrkOK Hheap Hinit Hpdom. pu_keep (HI, Haac, Hal, Hbrk, HbrkOK, Hheap, Hinit, Hpdom).
    unfold cmA. apply (WF_add_area A HWc p (aac - 1) (p + 4096) Hal Hheap p_disj_area p_disj_grp p_disj_page Hinit Hbrk); unfold aac; [llia| |llia].
    destruct Hheap as (H1 & _). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma no_avail : forall x mt, a_meta A x = Some mt -> mt_role mt <> RAvail.
  Proof using HAV Hamc m. pu_keep (HAV, Hamc, m). intros x mt Hx Hr. destruct (HAV x mt Hx Hr) as (k & Hk & _). rewrite Hamc in Hk. llia. Qed.

  (* [comment removed for export] *)
  Lemma p_slot_fresh : forall k, 0 <= k < 101 -> a_meta A (meta_addr p k) = None.
  Proof using HI Hal Hbrk Hpdom. pu_keep (HI, Hal, Hbrk, Hpdom).
    intros k Hk. destruct (a_meta A (meta_addr p k)) as [mt|] eqn:E; [| reflexivity]. exfalso.
    destruct (proj1 (wf_meta_dom A HWc (meta_addr p k)) ltac:(rewrite E; discriminate)) as (pg & k' & Hpg & Hk' & Ek).
    pose proof (meta_addr_range p k Hk). pose proof (meta_addr_range pg k' Hk'). destruct (p_disj_area pg Hpg); llia.
  Qed.

  Lemma areas_tl : (a_areas A = [] /\ a_ctx A KAtail = 0) \/ (a_areas A <> [] /\ a_ctx A KAtail = last (a_areas A) 0 /\ In (last (a_areas A) 0) (a_areas A) /\ 0x1000 <= last (a_areas A) 0).
  Proof using HI Hspan. pu_keep (HI, Hspan).
    rewrite (wf_atail A HWc). destruct (a_areas A) as [|a l] eqn:E; [left; auto | right].
    assert (Hin : In (last (a :: l) 0) (a :: l)) by (apply last_in; discriminate).
    rewrite <- E in Hin |- *. destruct (wf_areas_al A HWc _ Hin) as [_ (H1 & _)].
    split; [rewrite E; discriminate|]. auto.
  Qed.

  (* [comment removed for export] *)
  Definition cmCH (x : Z) : Prop :=
    (C_AAC <= x < C_AAC + 8) \/ (C_AAREAS <= x < C_AAREAS + 8) \/ (a_areas A = [] /\ C_AHEAD <= x < C_AHEAD + 8) \/
    (C_ATAIL <= x < C_ATAIL + 8) \/ (C_AM <= x < C_AM + 8) \/ (C_AMC <= x < C_AMC + 8) \/
    (p <= x < p + 40) \/ (a_areas A <> [] /\ last (a_areas A) 0 + 8 <= x < last (a_areas A) 0 + 16).

  Lemma cmA_meta_usage : forall sc x, meta_usage cmA sc x = meta_usage A sc x.
  Proof using HI Hal Hbrk Hpdom. pu_keep (HI, Hal, Hbrk, Hpdom).
    intros sc x. unfold meta_usage, cmA, aaA, aa_meta. cbn [a_meta].
    destruct (meta_index p x) as [k|] eqn:E; [| reflexivity].
    destruct (proj1 (meta_index_spec p x k) E) as [Hk ->]. rewrite (p_slot_fresh k Hk). cbn. destruct (k =? 0); reflexivity.
  Qed.

  Lemma cmA_ctx : forall k, a_ctx cmA k = aa_ctx A p (aac - 1) (p + 4096) k.
  Proof using Type. pu_keep tt. reflexivity. Qed.

  Lemma usage_of_cmA : forall sc, usage_of cmA sc = usage_of A sc.
  Proof using HI Hal Hbrk Hpdom. pu_keep (HI, Hal, Hbrk, Hpdom).
    intros sc. unfold usage_of. change (a_areas cmA) with (a_areas A ++ [p]).
    rewrite (usage_fold_ext (area_usage cmA sc) (area_usage A sc)) by (intros x; unfold area_usage; apply sumk_ext; intros k Hk; apply cmA_meta_usage).
    rewrite usage_fold_app.
    assert (Z0 : area_usage A sc p = 0).
    { unfold area_usage. rewrite (sumk_ext _ (fun _ => 0)) by (intros k Hk; unfold meta_usage; rewrite p_slot_fresh by llia; reflexivity). reflexivity. }
    rewrite Z0. llia.
  Qed.

  Lemma commit_finish : forall (K : word -> M R) P m9 ws,
    (forall s', II sp0 argv envp cb (m :: D) cmA s' -> FR A s cmA s' -> got_meta A D cmA m -> ms_vm s' = ms_vm s ->
       tsafe (K (Z_to_bv 64 m) s') P) ->
    RepW A (ms_mem s) ws m9 ->
    (forall x, wlook ws x <> None -> cmCH x) ->
    (forall x, C_AAC <= x < C_AAC + 8 -> wlook ws x = Some (byte_of (aac - 1) (x - C_AAC))) ->
    (forall x, C_AAREAS <= x < C_AAREAS + 8 -> wlook ws x = Some (byte_of (p + 4096) (x - C_AAREAS))) ->
    (a_areas A = [] -> forall x, C_AHEAD <= x < C_AHEAD + 8 -> wlook ws x = Some (byte_of p (x - C_AHEAD))) ->
    (a_areas A <> [] -> forall x, C_AHEAD <= x < C_AHEAD + 8 -> wlook ws x = None) ->
    (forall x, C_ATAIL <= x < C_ATAIL + 8 -> wlook ws x = Some (byte_of p (x - C_ATAIL))) ->
    (forall x, C_AM <= x < C_AM + 8 -> wlook ws x = Some (byte_of (m + 40) (x - C_AM))) ->
    (forall x, C_AMC <= x < C_AMC + 8 -> wlook ws x = Some (byte_of 100 (x - C_AMC))) ->
    (forall x, p <= x < p + 8 -> wlook ws x = Some (byte_of (a_ctx A KSecret) (x - p))) ->
    (forall x, p + 24 <= x < p + 40 -> wlook ws x = Some 0) ->
    (forall x, p + 40 <= x < p + 4096 -> wlook ws x = None) ->
    (forall a : word, m9 a = ms_mem s a \/ cmCH (bv_unsigned a)) ->
    (forall a : word, ms_mem s a <> None -> m9 a <> None) ->
    tsafe (K (Z_to_bv 64 m) (upd s m9 (ms_vm s))) P.
  Proof using HAV HD HI HUS HVall HVc Haac Hal Hamc Hbrk HbrkOK Hcov Hheap Hinit Hnafree Hpdom Hres Hspan Hzero MLok. pu_keep (HAV, HD, HI, HUS, HVall, HVc, Haac, Hal, Hamc, Hbrk, HbrkOK, Hcov, Hheap, Hinit, Hnafree, Hpdom, Hres, Hspan, Hzero, MLok).
    intros K P m9 ws HK RW HCH Vaac Vaar Vhd1 Vhd2 Vtl Vam Vamc Vsec Vlnk Vfree FRM KEEP.
    pose proof HI as [HW HR HC HWIN HE HG]. pose proof alloc_ceiling_val as HCV. pose proof WF_cmA as HW2.
    destruct Hheap as (Hp1 & _ & Hp2 & Hp3).
    pose proof (meta_addr_range p) as MAR.
    assert (Hpg_new : In p (a_areas cmA)) by (unfold cmA, aaA; cbn [a_areas]; apply in_or_app; right; left; reflexivity).
    assert (Hm0 : a_meta cmA m = Some (mzero RDead)).
    { unfold cmA, aaA, m. cbn [a_meta]. replace (p + 24) with (meta_addr p 0) by (unfold meta_addr; llia). rewrite (aa_meta_new A p 0) by llia. reflexivity. }
    (* [comment removed for export] *)
    assert (HR2 : Rep cmA m9).
    { apply (repw_commit3 A cmA (ms_mem s) ws m9 RW).
      - intros x b (f & Hf & Hfb).
        destruct (has_aaA_inv A HW p (aac - 1) (p + 4096) f Hf) as [(k & Hk & ->) | [-> | [(k & fl & Hk & ->) | (Hold & Hnc)]]].
        + destruct Hfb as [Hx ->]. cbn [f_a f_n f_v] in Hx |- *.
          assert (DEC : forall k', cvalid k' -> {k = k'} + {k <> k'}) by (intros k' _; apply cslot_eq_dec).
          destruct (cslot_eq_dec k KAac) as [-> | N1]; [right; left; cbn [caddr clen] in Hx; rewrite Vaac by (unfold C_AAC in *; cbn in Hx; llia); discriminate|].
          destruct (cslot_eq_dec k KAareas) as [-> | N2]; [right; left; cbn [caddr clen] in Hx; rewrite Vaar by (unfold C_AAREAS in *; cbn in Hx; llia); discriminate|].
          destruct (cslot_eq_dec k KAtail) as [-> | N3]; [right; left; cbn [caddr clen] in Hx; rewrite Vtl by (unfold C_ATAIL in *; cbn in Hx; llia); discriminate|].
          destruct (cslot_eq_dec k KAm) as [-> | N4]; [right; left; cbn [caddr clen] in Hx; rewrite Vam by (unfold C_AM in *; cbn in Hx; llia); discriminate|].
          destruct (cslot_eq_dec k KAmc) as [-> | N5]; [right; left; cbn [caddr clen] in Hx; rewrite Vamc by (unfold C_AMC in *; cbn in Hx; llia); discriminate|].
          destruct (cslot_eq_dec k KAhead) as [-> | N6].
          * destruct (a_areas A) as [|a0 l0] eqn:Ear.
            -- right; left. cbn [caddr clen] in Hx. rewrite (Vhd1 eq_refl) by (unfold C_AHEAD in *; cbn in Hx; llia). discriminate.
            -- left. exists (FCT (caddr KAhead) (clen KAhead) (a_ctx A KAhead)). split; [left; exists KAhead; split; [exact I|]|].
               ++ cbn [aa_ctx]. rewrite ?Ear. reflexivity.
               ++ split; [exact Hx|]. cbn [f_a f_v aa_ctx]. rewrite ?Ear. reflexivity.
          * left. exists (FCT (caddr k) (clen k) (a_ctx A k)). split; [left; exists k; split; [exact Hk | reflexivity]|].
            split; [exact Hx|]. cbn [f_a f_v]. destruct k; try reflexivity; exfalso; congruence.
        + right; left. destruct Hfb as [Hx ->]. cbn in Hx. rewrite Vsec by llia. discriminate.
        + destruct Hfb as [Hx ->]. cbn [f_a f_n f_v] in Hx |- *. pose proof (mfield_range fl) as Hflr. pose proof (MAR k Hk) as Hmk.
          destruct (Z.lt_ge_cases (meta_addr p k + moff fl) (p + 40)) as [Hlo40 | Hhi40].
          * right; left. assert (k = 0) by (unfold meta_addr in *; lnia). subst k.
            assert (Hfl01 : moff fl + mlen fl <= 16) by (unfold meta_addr in Hlo40; destruct fl; cbn in *; llia).
            rewrite Vlnk by (unfold meta_addr in *; llia). discriminate.
          * right; right. rewrite byte_of_zero. split; [| llia].
            rewrite (mbyte_overlay (ms_mem s) x (Z_to_bv 8 0)); [reflexivity | llia | apply Hzero; llia].
        + left. exists f. split; [exact Hold | exact Hfb].
      - intros x b (f & Hf & [Hx ->]) Hw. pose proof (HCH x Hw) as C.
        (* [comment removed for export] *)
        assert (CTXCASE : forall k v, cvalid k -> clen k = 8 -> caddr k <= x < caddr k + 8 -> aa_ctx A p (aac - 1) (p + 4096) k = v ->
                  wlook ws x = Some (byte_of v (x - caddr k)) -> wlook ws x = Some (byte_of (f_v f) (x - f_a f))).
        { intros k v Hk Hlen Hkx Ev Ew. pose proof (fact_at_ctx cmA HW2 f k x Hf Hk Hx ltac:(rewrite Hlen; exact Hkx)) as ->.
          cbn [f_a f_v]. rewrite cmA_ctx, Ev. exact Ew. }
        destruct C as [Cx | [Cx | [(Ear & Cx) | [Cx | [Cx | [Cx | [Cx | (Hne & Cx)]]]]]]].
        + apply (CTXCASE KAac (aac - 1) I eq_refl); [cbn; unfold C_AAC in *; llia | reflexivity | cbn [caddr]; apply Vaac; exact Cx].
        + apply (CTXCASE KAareas (p + 4096) I eq_refl); [cbn; unfold C_AAREAS in *; llia | reflexivity | cbn [caddr]; apply Vaar; exact Cx].
        + apply (CTXCASE KAhead p I eq_refl); [cbn; unfold C_AHEAD in *; llia | cbn [aa_ctx]; rewrite Ear; reflexivity | cbn [caddr]; apply (Vhd1 Ear); exact Cx].
        + apply (CTXCASE KAtail p I eq_refl); [cbn; unfold C_ATAIL in *; llia | reflexivity | cbn [caddr]; apply Vtl; exact Cx].
        + apply (CTXCASE KAm (m + 40) I eq_refl); [cbn; unfold C_AM in *; llia | cbn [aa_ctx]; unfold m, meta_addr; llia | cbn [caddr]; apply Vam; exact Cx].
        + apply (CTXCASE KAmc 100 I eq_refl); [cbn; unfold C_AMC in *; llia | reflexivity | cbn [caddr]; apply Vamc; exact Cx].
        + (* [comment removed for export] *)
          destruct (Z.lt_ge_cases x (p + 24)) as [L24 | G24].
          * destruct (fact_at_area_hdr cmA HW2 f p x Hf Hpg_new Hx ltac:(llia)) as [-> L8]. cbn [f_a f_v].
            rewrite cmA_ctx. cbn [aa_ctx]. apply Vsec. llia.
          * destruct (Z.lt_ge_cases x (p + 32)) as [L32 | G32].
            -- pose proof (fact_at_meta cmA HW2 f m (mzero RDead) FPrev x Hf Hm0 Hx ltac:(unfold m; cbn; llia)) as ->.
               cbn [f_a f_v]. rewrite mt_f_mzero, byte_of_zero. apply Vlnk. llia.
            -- pose proof (fact_at_meta cmA HW2 f m (mzero RDead) FNext x Hf Hm0 Hx ltac:(unfold m; cbn; llia)) as ->.
               cbn [f_a f_v]. rewrite mt_f_mzero, byte_of_zero. apply Vlnk. llia.
        + (* [comment removed for export] *)
          exfalso. assert (Hin : In (last (a_areas A) 0) (a_areas cmA)).
          { unfold cmA, aaA. cbn [a_areas]. apply in_or_app. left. apply last_in. exact Hne. }
          destruct (fact_at_area_hdr cmA HW2 f (last (a_areas A) 0) x Hf Hin Hx ltac:(llia)) as [_ L8]. llia.
      - intros x Hx. destruct (proj1 (dom_aaA A HW p (aac - 1) (p + 4096) p_disj_area x) Hx) as [Hd | Hpx]; [left; exact Hd | right].
        rewrite Hzero by exact Hpx. discriminate. }
    (* [comment removed for export] *)
    assert (CHW : forall x, cmCH x -> (LOCKA <= x < CTX_END) \/ (p <= x < p + 4096) \/
              (dom A x /\ exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096)).
    { intros x [C|[C|[(_ & C)|[C|[C|[C|[C|(Hne & C)]]]]]]]; unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC, LOCKA, CTX_END in *; try (left; llia).
      - right; left. llia.
      - right; right. pose proof (last_in (a_areas A) 0 Hne) as Hin. split; [left; exists (last (a_areas A) 0); split; [exact Hin | llia]|].
        exists (last (a_areas A) 0). split; [exact Hin | llia]. }
    assert (HAV2 : AvOK cmA).
    { intros x mt Hx Hr. unfold cmA, aaA in Hx. cbn [a_meta] in Hx.
      destruct (aa_meta_inv A p x mt Hx) as [Hold | (k & Hk & -> & ->)]; [exfalso; exact (no_avail x mt Hold Hr)|].
      destruct (Z.eq_dec k 0) as [Ek | Hk0]; [exfalso; subst k; cbn in Hr; discriminate Hr|].
      exists k. unfold cmA, aaA. cbn [a_ctx a_areas aa_ctx]. rewrite last_app1. split; [llia | reflexivity]. }
    assert (HDD2 : deads cmA (m :: D)).
    { intros x. unfold cmA, aaA. cbn [a_meta]. split.
      - intros (mt & Hx & Hr). destruct (aa_meta_inv A p x mt Hx) as [Hold | (k & Hk & -> & ->)].
        + right. apply (proj1 (HD x)). exists mt. auto.
        + left. destruct (Z.eq_dec k 0) as [Ek | Hk0]; [subst k; unfold m, meta_addr; llia | exfalso; rewrite (proj2 (Z.eqb_neq k 0) Hk0) in Hr; cbn in Hr; discriminate Hr].
      - intros [<- | Hin].
        + exists (mzero RDead). split; [| reflexivity]. unfold m. replace (p + 24) with (meta_addr p 0) by (unfold meta_addr; llia). apply aa_meta_new. llia.
        + destruct (proj2 (HD x) Hin) as (mt & Hx & Hr). exists mt. split; [exact (aa_meta_old A HW p p_disj_area x mt Hx) | exact Hr]. }
    assert (GS : gsame A cmA).
    { constructor; unfold cmA, aaA; cbn [a_meta a_active a_live a_ctx]; auto.
      - intros x mt aib sl Hx Hr. exact (aa_meta_old A HW p p_disj_area x mt Hx).
      - intros x mt aib sl Hx Hr. exact (aa_group_inv A p x mt aib sl Hx Hr).
      - intros x mt Hx Hr. exact (aa_meta_old A HW p p_disj_area x mt Hx).
      - intros k Hk _. destruct k; cbn in Hk; try contradiction; reflexivity. }
    apply (HK (upd s m9 (ms_vm s))).
    - (* [comment removed for export] *) constructor; cbn [ms_mem ms_vm upd].
      + (* [comment removed for export] *) apply (IS_mem sp0 argv envp cb A cmA s m9 HI HW2 HR2).
        * intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. destruct (CHW _ X) as [Hc | [Hp | (Hd & _)]].
          -- unfold mzone, LOCKA, CTX, CTX_END in *.
             (* [comment removed for export] *)
             destruct X as [C|[C|[(_ & C)|[C|[C|[C|[C|(Hne & C)]]]]]]]; unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC in *; try llia.
             pose proof (last_in (a_areas A) 0 Hne) as Hin. destruct (wf_areas_al A HW _ Hin) as [_ (R1 & R2 & R3 & R4)]. llia.
          -- unfold mzone. llia.
          -- destruct (dom_heap A (bv_unsigned a) HW Hd) as (lo & hi & Hh & Hx). unfold heap_range in Hh. unfold mzone. llia.
        * intros a Ha. destruct (FRM a) as [E | X]; [left; rewrite <- E; exact Ha|]. destruct (CHW _ X) as [Hc | [Hp | (Hd & _)]].
          -- right; left. unfold LOCKA, CTX_END in Hc. llia.
          -- left. rewrite <- (Z_to_bv_bv_unsigned 64 a). rewrite Hzero by exact Hp. discriminate.
          -- left. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom A _ HR). exact Hd.
      + (* [comment removed for export] *) apply VMcore_ok.
        * apply (VMcore_restate A cmA (ms_vm s) HVc); unfold cmA, aaA; cbn [a_meta a_areas a_pages].
          -- intros x mt aib sl Hx Hr Hml. exists mt, aib, sl. split; [exact (aa_group_inv A p x mt aib sl Hx Hr) | auto].
          -- intros pg Hpg. apply in_app_or in Hpg. destruct Hpg as [Hpg | [<- | []]]; [left; exact Hpg | right]. split; [exact Hcov | exact Hnafree].
          -- intros pg Hpg. left. exact Hpg.
        * intros b sz Hin. destruct (HVall b sz Hin) as [(x & mtx & aibx & slx & Hx & Hrx & R0) | [Hbr | Hbl]]; [left | right; left; exact Hbr | right; right; exact Hbl].
          exists x, mtx, aibx, slx. split; [exact (aa_meta_old A HW p p_disj_area x mtx Hx) | split; [exact Hrx | exact R0]].
        * unfold cmA, aaA. cbn [a_ctx a_areas aa_ctx]. split; [intros E; exfalso; exact (Hbrk E)|].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. llia.
        * unfold cmA, aaA. cbn [a_ctx aa_ctx]. destruct HbrkOK as [E | E]; [right; left; exact E | right; right; exact E].
        * unfold cmA, aaA. cbn [a_ctx aa_ctx]. intros Hgt. destruct (Hres Hgt) as (R1 & R2 & R3).
          split; [unfold page_aligned in *; rewrite <- Zplus_mod_idemp_l, Hal; reflexivity|]. split; [llia|]. split; [exact R2 | exact R3].
      + exact HAV2.
      + (* [comment removed for export] *) intros sc Hsc. change (a_ctx cmA (KUsage sc)) with (a_ctx A (KUsage sc)). rewrite (HUS sc Hsc). symmetry. apply usage_of_cmA.
      + exact HDD2.
    - (* [comment removed for export] *) constructor; cbn [ms_mem ms_vm ms_lo ms_hi upd]; auto.
      + intros x [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (dom_aaA A HW p (aac - 1) (p + 4096) p_disj_area x)). left. exact Hd.
      + intros a Hown Herr. destruct (FRM a) as [E | X]; [exact E | exfalso]. destruct (CHW _ X) as [Hc | [Hp | (Hd & _)]].
        * apply Hown. left. exact Hc.
        * apply Hown. right. apply (proj2 (dom_aaA A HW p (aac - 1) (p + 4096) p_disj_area _)). right. exact Hp.
        * apply Hown. right. apply (proj2 (dom_aaA A HW p (aac - 1) (p + 4096) p_disj_area _)). left. exact Hd.
      + intros q n a Hq Ha. destruct (FRM a) as [E | X]; [exact E | exfalso]. destruct (CHW _ X) as [Hc | [Hp | (Hd & pg & Hpg & Hx)]].
        * destruct (live_heap A q n HW Hq) as (Hn & H1 & H2 & H3 & _). pose proof (MallocInv_live.round16_ge n). unfold LOCKA, CTX_END in Hc. llia.
        * destruct (live_heap A q n HW Hq) as (Hn & H1 & H2 & H3 & Hd). pose proof (MallocInv_live.round16_ge n).
          apply (Hpdom (bv_unsigned a)); [exact Hp | apply Hd; llia].
        * exact (area_not_live A pg (bv_unsigned a) q n HW Hpg Hx Hq Ha).
    - (* [comment removed for export] *) constructor.
      + exists (mzero RDead). split; [exact Hm0|]. split; [reflexivity|]. intros fl; rewrite mt_f_mzero; reflexivity.
      + unfold m. llia.
      + unfold m. llia.
      + intros j Hj. apply (proj2 (dom_aaA A HW p (aac - 1) (p + 4096) p_disj_area _)). right. unfold m in *. llia.
      + exact HDD2.
      + intros Hin. destruct (proj2 (HD m) Hin) as (mt & Hx & _). unfold m in Hx.
        replace (p + 24) with (meta_addr p 0) in Hx by (unfold meta_addr; llia). rewrite (p_slot_fresh 0) in Hx by llia. discriminate Hx.
      + exact GS.
      + exact HAV2.
    - reflexivity.
  Qed.

  Theorem commit_ok : forall (K : word -> M R) P,
    (forall s', II sp0 argv envp cb (m :: D) cmA s' -> FR A s cmA s' -> got_meta A D cmA m -> ms_vm s' = ms_vm s ->
       tsafe (K (Z_to_bv 64 m) s') P) ->
    tsafe ((x <- (aac3 <- m_ld A_AVAIL_AREA_CNT ;;
                  tl <- m_ld A_AREA_TAIL ;;
                  m_sd A_AVAIL_AREA_CNT (v_addi aac3 (-1)) ;;
                  m_sd A_AVAIL_AREAS (v_add (Z_to_bv 64 p) (wlit 4096)) ;;
                  (if is0 tl then m_sd A_AREA_HEAD (Z_to_bv 64 p) else m_sd (at_ tl 8) (Z_to_bv 64 p)) ;;
                  sec <- m_ld A_CTX ;;
                  m_sd A_AREA_TAIL (Z_to_bv 64 p) ;;
                  m_sd (Z_to_bv 64 p) sec ;;
                  t1 <- m_ld A_AREA_TAIL ;;
                  m_sw (at_ t1 16) (wlit 101) ;;
                  t2 <- m_ld A_AREA_TAIL ;;
                  let mm := at_ t2 24 in
                  m_sd A_AVAIL_META (at_ mm 40) ;;
                  m_sd A_AVAIL_META_CNT (wlit 100) ;;
                  m_sd (at_ mm 8) w0 ;; m_sd mm w0 ;;
                  mret mm) ;; K x) s) P.
  Proof using HAV HD HI HUS HVall HVc Haac Hal Hamc Hbrk HbrkOK Hcov Hheap Hinit Hnafree Hpdom Hres Hspan Hzero MLok. pu_keep (HAV, HD, HI, HUS, HVall, HVc, Haac, Hal, Hamc, Hbrk, HbrkOK, Hcov, Hheap, Hinit, Hnafree, Hpdom, Hres, Hspan, Hzero, MLok).
    intros K P HK. pose proof HI as [HW HR HC HWIN HE HG]. pose proof alloc_ceiling_val as HCV.
    destruct Hheap as (Hp1 & _ & Hp2 & Hp3).
    assert (Haac_hi : aac < 2^40).
    { unfold aac. destruct (Z.eq_dec (a_ctx A KAac - 1) 0) as [E|E]; [llia|]. destruct (Hres ltac:(unfold aac in *; llia)) as (R1 & _). llia. }
    pose proof (repw_init A _ HW HR) as RW0.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite ?A_AVAIL_AREA_CNT_eq.
    eapply (ts_ld_ctx A); [exact HR | exact HWIN | exact I | reflexivity | unfold aac in *; llia |]. fold aac.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite ?A_AREA_TAIL_eq.
    pose proof (wf_ctx_nonneg A HW KAtail) as Htl0.
    assert (Htl_hi : a_ctx A KAtail < 2^64).
    { destruct areas_tl as [(_ & ->) | (_ & -> & Hin & _)]; [llia|]. destruct (wf_areas_al A HW _ Hin) as [_ (_ & _ & H3 & _)]. llia. }
    eapply (ts_ld_ctx A); [exact HR | exact HWIN | exact I | reflexivity | llia |].
    (* [comment removed for export] *)
    apply ts_assoc. unfold m_sd at 1. rewrite v_addi_Z.
    eapply (ts_st_ctxw A s (ms_mem s) []); [exact RW0 | exact HWIN | exact I |].
    pose proof (repw_st_ctx A s (ms_mem s) [] KAac (Z_to_bv 64 (aac + -1)) RW0 I) as RW1.
    set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (caddr KAac)) (word_to_le_bytes (Z.to_nat (clen KAac)) (Z_to_bv 64 (aac + -1)))) in RW1 |- *.
    cbn [ms_mem ms_vm upd].
    (* [comment removed for export] *)
    apply ts_assoc. rewrite ?A_AVAIL_AREAS_eq. unfold m_sd at 1. rewrite v_add_Z.
    eapply (ts_st_ctxw A (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
    pose proof (repw_st_ctx A (upd s m1 (ms_vm s)) (ms_mem s) _ KAareas (Z_to_bv 64 (p + 4096)) RW1 I) as RW2. cbn [ms_mem upd] in RW2.
    set (m2 := wbytes m1 (Z_to_bv 64 (caddr KAareas)) (word_to_le_bytes (Z.to_nat (clen KAareas)) (Z_to_bv 64 (p + 4096)))) in RW2 |- *.
    (* [comment removed for export] *)
    assert (Hfsec : has A (FCT (caddr KSecret) 8 (a_ctx A KSecret))) by (left; exists KSecret; split; [exact I | reflexivity]).
    pose proof (wf_ctx_nonneg A HW KSecret) as Hsec0.
    apply ts_assoc. rewrite is0_Z by llia.
    destruct areas_tl as [(Ear & Etl) | (Hne & Etl & Hlast_in & Hlast_lo)].
    - (* [comment removed for export] *)
      rewrite Etl, Z.eqb_refl. rewrite ?A_AREA_HEAD_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m2 (ms_vm s)) (ms_mem s) _ KAhead (Z_to_bv 64 p) RW2 I) as RW3. cbn [ms_mem upd] in RW3.
      set (m3 := wbytes m2 (Z_to_bv 64 (caddr KAhead)) (word_to_le_bytes (Z.to_nat (clen KAhead)) (Z_to_bv 64 p))) in RW3 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_CTX_eq.
      eapply (ts_ld_factw A HW (upd s m3 (ms_vm s)) (ms_mem s) _ (caddr KSecret) (a_ctx A KSecret)); [exact RW3 | apply WIN_upd; exact HWIN | exact Hfsec | | exact Hsec0 |].
      { repeat (apply wfree_range_cons; [cside|]). apply wfree_range_nil. }
      cbv beta.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_AREA_TAIL_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m3 (ms_vm s)) (ms_mem s)); [exact RW3 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m3 (ms_vm s)) (ms_mem s) _ KAtail (Z_to_bv 64 p) RW3 I) as RW4. cbn [ms_mem upd] in RW4.
      set (m4 := wbytes m3 (Z_to_bv 64 (caddr KAtail)) (word_to_le_bytes (Z.to_nat (clen KAtail)) (Z_to_bv 64 p))) in RW4 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_mappedw A (upd s m4 (ms_vm s)) (ms_mem s)); [exact RW4 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m4 (ms_vm s)) (ms_mem s) _ 8 p (Z_to_bv 64 (a_ctx A KSecret)) RW4 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW5. cbn [ms_mem upd] in RW5.
      set (m5 := wbytes m4 (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (a_ctx A KSecret)))) in RW5 |- *.
      (* [comment removed for export] *)
      apply ts_assoc.
      eapply (ts_ld_wrw A (upd s m5 (ms_vm s)) (ms_mem s) _ (caddr KAtail) p); [exact RW5 | apply WIN_upd; exact HWIN | cside | cside | llia | |].
      { intros j Hj. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_ATAIL. rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. repeat f_equal; llia. }
      (* [comment removed for export] *)
      apply ts_assoc. rewrite at_Z. unfold m_sw.
      eapply (ts_st_mappedw A (upd s m5 (ms_vm s)) (ms_mem s)); [exact RW5 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m5 (ms_vm s)) (ms_mem s) _ 4 (p + 16) (wlit 101) RW5 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW6. cbn [ms_mem upd] in RW6.
      set (m6 := wbytes m5 (Z_to_bv 64 (p + 16)) (word_to_le_bytes 4 (wlit 101))) in RW6 |- *.
      (* [comment removed for export] *)
      apply ts_assoc.
      eapply (ts_ld_wrw A (upd s m6 (ms_vm s)) (ms_mem s) _ (caddr KAtail) p); [exact RW6 | apply WIN_upd; exact HWIN | cside | cside | llia | |].
      { intros j Hj. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_ATAIL. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. repeat f_equal; llia. }
      cbv beta zeta. rewrite !at_Z.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_AVAIL_META_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m6 (ms_vm s)) (ms_mem s)); [exact RW6 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m6 (ms_vm s)) (ms_mem s) _ KAm (Z_to_bv 64 (p + 24 + 40)) RW6 I) as RW7. cbn [ms_mem upd] in RW7.
      set (m7 := wbytes m6 (Z_to_bv 64 (caddr KAm)) (word_to_le_bytes (Z.to_nat (clen KAm)) (Z_to_bv 64 (p + 24 + 40)))) in RW7 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_AVAIL_META_CNT_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m7 (ms_vm s)) (ms_mem s)); [exact RW7 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m7 (ms_vm s)) (ms_mem s) _ KAmc (wlit 100) RW7 I) as RW8. cbn [ms_mem upd] in RW8.
      set (m8 := wbytes m7 (Z_to_bv 64 (caddr KAmc)) (word_to_le_bytes (Z.to_nat (clen KAmc)) (wlit 100))) in RW8 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_mappedw A (upd s m8 (ms_vm s)) (ms_mem s)); [exact RW8 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m8 (ms_vm s)) (ms_mem s) _ 8 (p + 24 + 8) w0 RW8 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW9. cbn [ms_mem upd] in RW9.
      set (m9 := wbytes m8 (Z_to_bv 64 (p + 24 + 8)) (word_to_le_bytes 8 w0)) in RW9 |- *.
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_mappedw A (upd s m9 (ms_vm s)) (ms_mem s)); [exact RW9 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m9 (ms_vm s)) (ms_mem s) _ 8 (p + 24) w0 RW9 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW10. cbn [ms_mem upd] in RW10.
      set (m10 := wbytes m9 (Z_to_bv 64 (p + 24)) (word_to_le_bytes 8 w0)) in RW10 |- *.
      apply ts_bind_ret. fold m.
      (* [comment removed for export] *)
      apply (commit_finish K P m10 _ HK RW10).
      all: cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]; unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC in *.
      + intros x Hw. unfold cmCH. unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC.
        assert (DQrng : p <= x < (p + 40) \/ (LOCKA + 32) <= x < (LOCKA + 56) \/ (LOCKA + 64) <= x < (LOCKA + 88) \/
                       (~ (p <= x < (p + 40)) /\ ~ ((LOCKA + 32) <= x < (LOCKA + 56)) /\ ~ ((LOCKA + 64) <= x < (LOCKA + 88)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | DQrng]]];
          [ do 6 right; left; llia
          | destruct (Z.lt_ge_cases x (LOCKA + 40)); [do 4 right; left; llia | destruct (Z.lt_ge_cases x (LOCKA + 48)); [do 5 right; left; llia | left; llia]]
          | destruct (Z.lt_ge_cases x (LOCKA + 72)); [right; right; left; split; [exact Ear | llia] | destruct (Z.lt_ge_cases x (LOCKA + 80)); [right; right; right; left; llia | right; left; llia]] |].
         
        exfalso; apply Hw; rewrite !wlook_skip by (cbn [f_a f_n]; llia); reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. repeat f_equal; llia.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. reflexivity.
      + intros _ x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. reflexivity.
      + intros Hne. exfalso. exact (Hne Ear).
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. unfold m. repeat f_equal; llia.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ_mod, byte_of_mod64 by llia. reflexivity.
      + intros x Hx. destruct (Z.lt_ge_cases x (p + 32)).
        * rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
        * rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). reflexivity.
      + intros a. pose proof (u64_range a). unfold cmCH. unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC.
        assert (DQrng : p <= (u a) < (p + 40) \/ (LOCKA + 32) <= (u a) < (LOCKA + 56) \/ (LOCKA + 64) <= (u a) < (LOCKA + 88) \/
                       (~ (p <= (u a) < (p + 40)) /\ ~ ((LOCKA + 32) <= (u a) < (LOCKA + 56)) /\ ~ ((LOCKA + 64) <= (u a) < (LOCKA + 88)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | DQrng]]];
          [ right; do 6 right; left; llia
          | destruct (Z.lt_ge_cases (u a) (LOCKA + 40)); [right; do 4 right; left; llia | destruct (Z.lt_ge_cases (u a) (LOCKA + 48)); [right; do 5 right; left; llia | right; left; llia]]
          | destruct (Z.lt_ge_cases (u a) (LOCKA + 72)); [right; right; right; left; split; [exact Ear | llia] | destruct (Z.lt_ge_cases (u a) (LOCKA + 80)); [right; right; right; right; left; llia | right; right; left; llia]] |].
         
        left; unfold m10, m9, m8, m7, m6, m5, m4, m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat]; unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC;
        rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; llia); reflexivity.
      + intros a Ha. unfold m10, m9, m8, m7, m6, m5, m4, m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat]. unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC.
        repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by llia; llia|]). exact Ha.
    - (* [comment removed for export] *)
      set (tl := last (a_areas A) 0) in *.
      destruct (wf_areas_al A HW tl Hlast_in) as [Htl_al (Ht1 & Ht2 & Ht3 & Ht4)]. pose proof (p_disj_area tl Hlast_in) as Htl_p.
      assert (Hdom_tl : forall j, 0 <= j < 4096 -> dom A (tl + j)) by (intros j Hj; left; exists tl; split; [exact Hlast_in | llia]).
      rewrite Etl. replace (tl =? 0) with false by (symmetry; apply Z.eqb_neq; llia). rewrite at_Z. unfold m_sd at 1.
      eapply (ts_st_domw A HW (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (tl + 8 + j) with (tl + (8 + j)) by llia; apply Hdom_tl; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m2 (ms_vm s)) (ms_mem s) _ 8 (tl + 8) (Z_to_bv 64 p) RW2 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (tl + 8 + j) with (tl + (8 + j)) by llia; apply Hdom_tl; llia)) as RW3.
      cbn [ms_mem upd] in RW3. rewrite uZ in RW3 by llia.
      set (m3 := wbytes m2 (Z_to_bv 64 (tl + 8)) (word_to_le_bytes 8 (Z_to_bv 64 p))) in RW3 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_CTX_eq.
      eapply (ts_ld_factw A HW (upd s m3 (ms_vm s)) (ms_mem s) _ (caddr KSecret) (a_ctx A KSecret)); [exact RW3 | apply WIN_upd; exact HWIN | exact Hfsec | | exact Hsec0 |].
      { repeat (apply wfree_range_cons; [cside|]). apply wfree_range_nil. }
      cbv beta.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_AREA_TAIL_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m3 (ms_vm s)) (ms_mem s)); [exact RW3 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m3 (ms_vm s)) (ms_mem s) _ KAtail (Z_to_bv 64 p) RW3 I) as RW4. cbn [ms_mem upd] in RW4.
      set (m4 := wbytes m3 (Z_to_bv 64 (caddr KAtail)) (word_to_le_bytes (Z.to_nat (clen KAtail)) (Z_to_bv 64 p))) in RW4 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_mappedw A (upd s m4 (ms_vm s)) (ms_mem s)); [exact RW4 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m4 (ms_vm s)) (ms_mem s) _ 8 p (Z_to_bv 64 (a_ctx A KSecret)) RW4 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW5. cbn [ms_mem upd] in RW5.
      set (m5 := wbytes m4 (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (a_ctx A KSecret)))) in RW5 |- *.
      (* [comment removed for export] *)
      apply ts_assoc.
      eapply (ts_ld_wrw A (upd s m5 (ms_vm s)) (ms_mem s) _ (caddr KAtail) p); [exact RW5 | apply WIN_upd; exact HWIN | cside | cside | llia | |].
      { intros j Hj. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_ATAIL. rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. repeat f_equal; llia. }
      (* [comment removed for export] *)
      apply ts_assoc. rewrite at_Z. unfold m_sw.
      eapply (ts_st_mappedw A (upd s m5 (ms_vm s)) (ms_mem s)); [exact RW5 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m5 (ms_vm s)) (ms_mem s) _ 4 (p + 16) (wlit 101) RW5 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW6. cbn [ms_mem upd] in RW6.
      set (m6 := wbytes m5 (Z_to_bv 64 (p + 16)) (word_to_le_bytes 4 (wlit 101))) in RW6 |- *.
      (* [comment removed for export] *)
      apply ts_assoc.
      eapply (ts_ld_wrw A (upd s m6 (ms_vm s)) (ms_mem s) _ (caddr KAtail) p); [exact RW6 | apply WIN_upd; exact HWIN | cside | cside | llia | |].
      { intros j Hj. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]. unfold C_ATAIL. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. repeat f_equal; llia. }
      cbv beta zeta. rewrite !at_Z.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_AVAIL_META_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m6 (ms_vm s)) (ms_mem s)); [exact RW6 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m6 (ms_vm s)) (ms_mem s) _ KAm (Z_to_bv 64 (p + 24 + 40)) RW6 I) as RW7. cbn [ms_mem upd] in RW7.
      set (m7 := wbytes m6 (Z_to_bv 64 (caddr KAm)) (word_to_le_bytes (Z.to_nat (clen KAm)) (Z_to_bv 64 (p + 24 + 40)))) in RW7 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. rewrite ?A_AVAIL_META_CNT_eq. unfold m_sd at 1.
      eapply (ts_st_ctxw A (upd s m7 (ms_vm s)) (ms_mem s)); [exact RW7 | apply WIN_upd; exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m7 (ms_vm s)) (ms_mem s) _ KAmc (wlit 100) RW7 I) as RW8. cbn [ms_mem upd] in RW8.
      set (m8 := wbytes m7 (Z_to_bv 64 (caddr KAmc)) (word_to_le_bytes (Z.to_nat (clen KAmc)) (wlit 100))) in RW8 |- *.
      (* [comment removed for export] *)
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_mappedw A (upd s m8 (ms_vm s)) (ms_mem s)); [exact RW8 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m8 (ms_vm s)) (ms_mem s) _ 8 (p + 24 + 8) w0 RW8 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW9. cbn [ms_mem upd] in RW9.
      set (m9 := wbytes m8 (Z_to_bv 64 (p + 24 + 8)) (word_to_le_bytes 8 w0)) in RW9 |- *.
      apply ts_assoc. unfold m_sd at 1.
      eapply (ts_st_mappedw A (upd s m9 (ms_vm s)) (ms_mem s)); [exact RW9 | apply WIN_upd; exact HWIN | cbv; llia | llia | cbn; llia | cbn; llia | intros j Hj; cbn in Hj; rewrite Hzero by llia; discriminate |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_mapped A (upd s m9 (ms_vm s)) (ms_mem s) _ 8 (p + 24) w0 RW9 ltac:(llia) ltac:(cbn; llia) ltac:(cbn; llia)) as RW10. cbn [ms_mem upd] in RW10.
      set (m10 := wbytes m9 (Z_to_bv 64 (p + 24)) (word_to_le_bytes 8 w0)) in RW10 |- *.
      apply ts_bind_ret. fold m.
      (* [comment removed for export] *)
      apply (commit_finish K P m10 _ HK RW10).
      all: cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat]; unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC in *.
      + intros x Hw. unfold cmCH. unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC.
        assert (DQrng : p <= x < (p + 40) \/ (LOCKA + 32) <= x < (LOCKA + 56) \/ (LOCKA + 72) <= x < (LOCKA + 88) \/ (tl + 8) <= x < (tl + 16) \/
                       (~ (p <= x < (p + 40)) /\ ~ ((LOCKA + 32) <= x < (LOCKA + 56)) /\ ~ ((LOCKA + 72) <= x < (LOCKA + 88)) /\ ~ ((tl + 8) <= x < (tl + 16)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | [DQrng | DQrng]]]];
          [ do 6 right; left; llia
          | destruct (Z.lt_ge_cases x (LOCKA + 40)); [do 4 right; left; llia | destruct (Z.lt_ge_cases x (LOCKA + 48)); [do 5 right; left; llia | left; llia]]
          | destruct (Z.lt_ge_cases x (LOCKA + 80)); [right; right; right; left; llia | right; left; llia]
          | do 7 right; split; [exact Hne | llia] |].
         
        exfalso; apply Hw; rewrite !wlook_skip by (cbn [f_a f_n]; llia); reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. repeat f_equal; llia.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. reflexivity.
      + intros Ear. exfalso. exact (Hne Ear).
      + intros _ x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ by llia. unfold m. repeat f_equal; llia.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. rewrite uZ_mod, byte_of_mod64 by llia. reflexivity.
      + intros x Hx. destruct (Z.lt_ge_cases x (p + 32)).
        * rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
        * rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
      + intros x Hx. rewrite !wlook_skip by (cbn [f_a f_n]; llia). reflexivity.
      + intros a. pose proof (u64_range a). unfold cmCH. unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC.
        assert (DQrng : p <= (u a) < (p + 40) \/ (LOCKA + 32) <= (u a) < (LOCKA + 56) \/ (LOCKA + 72) <= (u a) < (LOCKA + 88) \/ (tl + 8) <= (u a) < (tl + 16) \/
                       (~ (p <= (u a) < (p + 40)) /\ ~ ((LOCKA + 32) <= (u a) < (LOCKA + 56)) /\ ~ ((LOCKA + 72) <= (u a) < (LOCKA + 88)) /\ ~ ((tl + 8) <= (u a) < (tl + 16)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | [DQrng | DQrng]]]];
          [ right; do 6 right; left; llia
          | destruct (Z.lt_ge_cases (u a) (LOCKA + 40)); [right; do 4 right; left; llia | destruct (Z.lt_ge_cases (u a) (LOCKA + 48)); [right; do 5 right; left; llia | right; left; llia]]
          | destruct (Z.lt_ge_cases (u a) (LOCKA + 80)); [right; right; right; right; left; llia | right; right; left; llia]
          | right; do 7 right; split; [exact Hne | llia] |].
         
        left; unfold m10, m9, m8, m7, m6, m5, m4, m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat]; unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC;
        rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; llia); reflexivity.
      + intros a Ha. unfold m10, m9, m8, m7, m6, m5, m4, m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat]. unfold C_AAC, C_AAREAS, C_AHEAD, C_ATAIL, C_AM, C_AMC.
        repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by llia; llia|]). exact Ha.
  Qed.
End Commit.

End WithLayout.
