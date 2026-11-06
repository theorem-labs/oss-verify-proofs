(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_wf6 MallocInv_wf7 MallocInv_wf8 MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm
  MallocInv_coh MallocInv_ops MallocInv_usage MallocInv_live MallocInv_free MallocInv_freetop MallocInv_enframe MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq
  MallocInv_nt1 MallocInv_aspieces MallocInv_agtail MallocInv_agroot MallocInv_agm2 MallocInv_agm3 MallocInv_agnest.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.
Local Notation u := bv_unsigned (only parsing).

Section NestRest2.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A1 : astate) (s1 : mstate).
  Variables (sc m : Z) (md : meta_rec) (j gj : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (idx cnt1 : Z).
  Hypothesis HII : II sp0 argv envp cb (m :: D) A1 s1.
  Hypothesis Hm : a_meta A1 m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis Hmd0 : forall fl, mt_f md fl = 0.
  Hypothesis HmD : ~ In m D.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A1 sc = [].
  Hypothesis Hj : 0 <= j < 48.
  Hypothesis Hgj : a_ctx A1 (KActive j) = gj.
  Hypothesis Hmt : a_meta A1 gj = Some mt.
  Hypothesis Hrl : mt_role mt = RGroup aib slots.
  Hypothesis Hscj : mt_sc mt = j.
  Hypothesis Hidx : 0 <= idx <= mt_last mt.
  Hypothesis Hslot : nth_error slots (Z.to_nat idx) = Some STaken.
  Hypothesis Hstride : mt_stride mt = 16 * size_class j.
  Hypothesis Hcnt1 : 2 <= cnt1 <= 32.
  Hypothesis Hfitj : 16 * size_class sc * cnt1 + 16 <= 16 * size_class j.
  Hypothesis Hsmall : 16 * size_class sc * cnt1 + 16 <= 2048.

  Let HW1 : WF A1 := is_wf _ _ _ _ _ _ (ii_is HII).

  (* [comment removed for export] *)
  Local Notation P0 := (p0 mt idx).
  Local Notation NE := (ne mt idx).
  Local Notation NN := (nn j).
  Local Notation NSZ := (nsize sc).
  Local Notation NA2 := (nA2 A1 j gj mt aib slots idx).
  Local Notation NA3 := (nA3 A1 j gj mt aib slots idx).
  Local Notation NESTA := (nestA A1 sc m j gj mt aib slots idx cnt1).
  Local Notation PRE_WS := (pre_ws sc m mt idx cnt1).

  Let WF3 : WF NA3 := WF_nA3 sp0 argv envp cb D A1 s1 sc m j gj mt aib slots idx HII Hsc Hj Hmt Hrl Hidx Hslot Hstride.
  Let M3 : a_meta NA3 m = Some md := nA3_m A1 m md j gj mt aib slots idx Hm Hr Hmt Hrl Hscj Hidx Hstride.

  Lemma Rep_nA3 : forall m2, Rep NA2 m2 -> Rep NA3 m2.
  Proof using HII Hcnt1 Hidx Hj Hmt Hrl Hsc Hslot Hstride. pu_keep (HII, Hcnt1, Hidx, Hj, Hmt, Hrl, Hsc, Hslot, Hstride).
    intros m2 R2. rewrite <- (nA3_eq A1 j gj mt aib slots idx).
    apply (Rep_slot_set NA2 gj (mt2 j mt aib slots idx) aib (list_set slots (Z.to_nat idx) (SLive 0 NN)) idx STaken
             (nA2_gj A1 j gj mt aib slots idx) (mt2_role j mt aib slots idx) ltac:(lia) (a_live A1) m2 R2).
    intros f x b Hf Hfb. apply (rep_facts NA2 m2 R2). exists f. split; [| exact Hfb].
    destruct (nA3_end_facts A1 sc j gj mt aib slots idx Hsc Hj Hidx Hslot) as [Fe F4].
    pose proof (nA2_hdr_facts A1 sc j gj mt aib slots idx cnt1 Hsc Hj Hidx Hslot Hstride Hcnt1) as (_ & _ & Fe2 & F42).
    unfold slot_fields, slot_fields_g in Hf. cbn [In app] in Hf.
    change (slot_start_g (mt_mem (mt2 j mt aib slots idx)) (mt_stride (mt2 j mt aib slots idx)) idx) with P0 in Hf.
    change (slot_end_g (mt_mem (mt2 j mt aib slots idx)) (mt_stride (mt2 j mt aib slots idx)) idx) with NE in Hf.
    destruct Hf as [<- | [<- | []]]; [exact F42 | exact Fe2].
  Qed.

  (* [comment removed for export] *)
  Theorem ts_nest_rest : forall (K : word -> M R) P,
    (forall ab s', 0 <= ab < 256 ->
       ms_vm s' = ms_vm s1 ->
       II sp0 argv envp cb D (NESTA ab) s' -> FR A1 s1 (NESTA ab) s' ->
       tsafe (K (Z_to_bv 64 0) s') P) ->
    tsafe ((r <- nest_rest (Z_to_bv 64 sc) (Z_to_bv 64 NSZ) (Z_to_bv 64 m) (Z_to_bv 64 cnt1)
                           (Z_to_bv 64 (LOCKA + 8 * sc)) (Z_to_bv 64 (caddr (KActive sc)))
                           (Z_to_bv 64 j) (Z_to_bv 64 idx) ;; K r) s1) P.
  Proof using HW1 Hact Hcnt1 Hfitj Hgj HmD Hmd0 Hsmall M3 MLok WF3. pu_keep (HW1, Hact, Hcnt1, Hfitj, Hgj, HmD, Hmd0, Hsmall, M3, MLok, WF3).
    intros K P HK. pose proof (ii_is HII) as HIS. pose proof HIS as [HW HRp HC HWIN HE HG].
    pose proof (meta_facts A1 m md HW1 Hm) as (M1 & M2 & M3' & M4 & Mdom). ceil. pose proof layout_small as LS.
    pose proof (envok_rodata _ _ _ _ HE) as HRO.
    pose proof (szj_rng j Hj) as SZJ. pose proof (szc_rng sc Hsc) as SZC.
    pose proof (ne_eq sc j mt idx Hsc Hj Hstride) as NEQ.
    pose proof (idx_facts sp0 argv envp cb D A1 s1 sc m j gj mt aib slots idx HII Hsc Hj Hmt Hrl Hidx Hslot) as (C & S16g & I32).
    pose proof (span_heap sp0 argv envp cb D A1 s1 sc m j gj mt aib slots idx HII Hsc Hj Hmt Hrl Hidx Hslot) as (SH1 & SH2 & SH3).
    pose proof (span_dom sp0 argv envp cb D A1 s1 sc m j gj mt aib slots idx HII Hsc Hj Hmt Hrl Hidx Hslot) as SD.
    pose proof (p0_m_apart sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx HII Hm Hsc Hj Hmt Hrl Hidx Hslot Hstride) as Hpm.
    pose proof (span_m_apart sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx HII Hm Hsc Hj Hmt Hrl Hidx Hslot Hstride) as Hspm.
    pose proof (nn_facts sc j mt Hsc Hj Hstride) as (N1 & N2 & N3 & N4).
    pose proof (usage_now sp0 argv envp cb D A1 s1 sc m HII Hsc) as [EU HU].
    pose proof (act0 sp0 argv envp cb D A1 s1 sc m HII Hsc Hact) as Hact0.
    pose proof (meta_facts A1 gj mt HW1 Hmt) as (G1 & G2 & G3 & G4 & Gdom).
    assert (Ep0 : mt_mem mt + 16 + idx * mt_stride mt = P0) by (unfold p0, slot_start, slot_start_g; lia).
    assert (Ene : P0 + mt_stride mt - 4 = NE) by (unfold ne, p0, slot_end, slot_start, slot_end_g, slot_start_g; lia).
    unfold nest_rest.
    (* [comment removed for export] *)
    reassoc.
    replace (v_add A_SIZE_CLASSES (v_slli (Z_to_bv 64 j) 1)) with (Z_to_bv 64 (T_SIZE_CLASSES + 2 * j))
      by (rewrite A_SIZE_CLASSES_eq, v_slli_Z, v_add_Z by lia; f_equal; change (2^1) with 2; lia).
    eapply ts_lhu_size_class; [exact HRO | exact HWIN | exact Hj |].
    (* [comment removed for export] *)
    reassoc.
    replace (at_ (v_add A_LOCK (v_slli (Z_to_bv 64 j) 3)) 88) with (Z_to_bv 64 (caddr (KActive j)))
      by (rewrite A_LOCK_eq, v_slli_Z, v_add_Z, at_Z by lia; rewrite caddr_active; f_equal; change (2^3) with 8; lia).
    eapply (ts_ld_ctx A1 s1 (KActive j)); [exact HRp | exact HWIN | cbn; lia | reflexivity | rewrite Hgj; lia |]. rewrite Hgj.
    (* [comment removed for export] *)
    reassoc. rewrite (at_lock 20), <- caddr_KCtr_lock.
    eapply (ts_lw_fact4 A1 s1 (caddr KCtr) (a_ctx A1 KCtr)); [exact HW1 | exact HRp | exact HWIN | left; exists KCtr; split; [exact I | reflexivity] | apply (wf_ctx_nonneg A1 HW1) |].
    (* [comment removed for export] *)
    reassoc.
    replace (v_addi (v_slli (Z_to_bv 64 (size_class j)) 4) (-4)) with (Z_to_bv 64 NN)
      by (rewrite v_slli_Z, v_addi_Z by lia; f_equal; unfold nn; change (2^4) with 16; lia).
    eapply (enframe_ok A1 s1 gj mt aib slots idx NN _ HW1 HRp HWIN HRO Hmt Hrl Hslot ltac:(lia) ltac:(split; [lia | split; lia])).
    unfold enframe_post. cbv zeta. intros off s2 Hoff HW2 HR2 HWIN2 Hvm2 Hlo2 Hhi2 HRO2 Hfr2 Hpay2.
    assert (Hoff0 : off = 0) by (rewrite N4 in Hoff; lia). subst off.
    rewrite Ep0 in *. rewrite Z.mul_0_r, Z.add_0_r in *.
    pose proof (nA2_eq A1 j gj mt aib slots idx Hmt Hrl) as E2. unfold nL2 in E2. rewrite E2 in HW2, HR2. clear E2.
    rewrite Ene in Hfr2.
    pose proof (Rep_nA3 (ms_mem s2) HR2) as R3.
    destruct s2 as [m2 vm2 lo2 hi2]. cbn [ms_mem ms_vm ms_lo ms_hi] in *. subst vm2 lo2 hi2.
    set (s2 := {| ms_mem := m2; ms_vm := ms_vm s1; ms_lo := ms_lo s1; ms_hi := ms_hi s1 |}) in *.
    assert (HWIN2' : WIN s2) by exact HWIN2.
    (* [comment removed for export] *)
    reassoc. rewrite (at_Z m 32). change (Z_to_bv 64 (m + 32)) with (Z_to_bv 64 (m + moff FW32)) at 1.
    eapply (ts_ld_metaW NA3 WF3 s2 m2 [] m md FW32); [apply repw_init; [exact WF3 | exact R3] | exact HWIN2' | exact M3 | reflexivity | apply wfree_range_nil | rewrite (Hmd0 FW32); lia |].
    rewrite (Hmd0 FW32).
    reassoc. replace (v_srli (v_slli (Z_to_bv 64 0) 52) 52) with (Z_to_bv 64 0) by (rewrite v_slli_Z, Z.mul_0_l, v_srli_Z by lia; reflexivity).
    unfold m_sd at 1.
    eapply (ts_st_domW NA3 WF3 s2 m2 [] 8 (m + 32) (Z_to_bv 64 0)); [apply repw_init; [exact WF3 | exact R3] | exact HWIN2' | lia | |].
    { intros jj Hjj. apply (proj2 (dom_nA3 A1 j gj mt aib slots idx Hmt Hrl (m + 32 + jj))). rewrite <- Z.add_assoc. apply Mdom. lia. }
    intros m3 RW3. rewrite uZ in RW3 by lia.
    (* [comment removed for export] *)
    reassoc. rewrite (at_Z P0 (-3)). replace (P0 + -3) with (P0 - 3) by lia.
    assert (Hb3 : mbyte m2 (P0 - 3) = Some idx).
    { pose proof (nA2_hdr_facts A1 sc j gj mt aib slots idx cnt1 Hsc Hj Hidx Hslot Hstride Hcnt1) as (F3 & _ & _ & _).
      transitivity (Some (byte_of idx 0)); [| f_equal; rewrite byte_of_0; apply Z.mod_small; lia].
      apply (rep_facts NA2 m2 HR2). exists (FCT (P0 - 3) 1 idx). split; [exact F3|]. split; [cbn; lia | cbn [f_v f_a]; rewrite Z.sub_diag; reflexivity]. }
    eapply (ts_lbu_m0w NA3 _ m2 _ (P0 - 3) idx); [exact RW3 | apply WIN_upd; exact HWIN2' | lia | lia | apply wfree_cons; [cbn; lia | apply wfree_nil] | exact Hb3 |].
    reassoc.
    replace (v_addi (v_andi (Z_to_bv 64 idx) 31) 192) with (Z_to_bv 64 (idx + 192))
      by (rewrite v_andi_Z by lia; rewrite land_31 by lia; rewrite Z.mod_small by lia; rewrite v_addi_Z; reflexivity).
    unfold m_sb at 1.
    eapply (ts_st_domW NA3 WF3 _ m2 _ 1 (P0 - 3) (Z_to_bv 64 (idx + 192))); [exact RW3 | apply WIN_upd; exact HWIN2' | lia | |].
    { intros jj Hjj. apply (proj2 (dom_nA3 A1 j gj mt aib slots idx Hmt Hrl _)). apply SD. lia. }
    intros m4 RW4. rewrite uZ in RW4 by lia.
    (* [comment removed for export] *)
    reassoc. rewrite (at_Z P0 12). rewrite uZ by lia. replace (P0 + 12) with (P0 + 12 + 0 * NSZ) by lia.
    cbn [ms_vm ms_mem upd].
    eapply (ts_zl sp0 argv envp cb D A1 s1 sc m j gj mt aib slots idx cnt1 HII Hsc Hj Hmt Hrl Hidx Hslot Hstride Hcnt1 Hfitj
              (S (Z.to_nat cnt1)) 0 _ _ _ P m2); [exact RW4 | apply WIN_upd; exact HWIN2' | lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia |].
    intros m9 RW9. cbn [ms_vm ms_mem upd].
    assert (RW9' : RepW NA3 m2 PRE_WS m9) by exact RW9. clear RW9.
    destruct (pre_commit sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr Hmd0 Hsc Hj Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 Hfitj m2 m9 HR2 R3 RW9')
      as (R9 & Z9 & B3 & B2a & B2b & FR9).
    (* [comment removed for export] *)
    cbv zeta. rewrite (v_addi_Z cnt1 (-1)). replace (cnt1 + -1) with (cnt1 - 1) by lia.
    assert (Hact3 : a_ctx NA3 (KActive sc) = 0) by (rewrite (nA3_ctx A1 j gj mt aib slots idx); exact Hact0).
    assert (Hus3 : a_ctx NA3 (KUsage sc) + cnt1 < 2^63) by (rewrite (nA3_ctx A1 j gj mt aib slots idx), EU; lia).
    assert (HPB : heap_bytes P0 16) by (unfold heap_bytes; lia).
    eapply (ts_as_tail NA3 m md sc cnt1 (cnt1 - 1) P0 0 WF3 M3 (Hmd0 FPrev) (Hmd0 FNext) (Hmd0 FW32) ltac:(lia) ltac:(reflexivity)
              Hsc Hact3 ltac:(lia) ltac:(lia) Hus3 HPB Hpm _ m9 []);
      [apply repw_init; [exact WF3 | exact R9] | apply WIN_upd; exact HWIN2' | | apply wfree_range_nil | apply wfree_range_nil | apply wfree_range_nil | apply wfree_range_nil |].
    { intros jj Hjj. apply (rep_dom NA3 m9 R9). apply (proj2 (dom_nA3 A1 j gj mt aib slots idx Hmt Hrl _)). apply SD. lia. }
    intros m' ab av1 fr av2 Hab Hav1 Hfr Hav2 Q1 Q2 Q3 RW. rewrite app_nil_r in RW. cbn [ms_vm ms_mem upd].
    pose proof (nest_commit sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr Hmd0 Hsc Hact Hj Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 Hfitj Hsmall
                  ab Hab m2 m9 m' av1 fr av2 HR2 R3 RW9' Hav1 Hfr Hav2 Q1 Q2 Q3 RW) as HR7.
    change (upd s2 m' (ms_vm s1)) with (upd s1 m' (ms_vm s1)).
    (* [comment removed for export] *)
    pose proof (ctx_slot_range (KUsage sc) ltac:(cbn; lia)) as (U1 & U2 & U3). pose proof (ctx_slot_range (KActive sc) ltac:(cbn; lia)) as (C1 & C2 & C3).
    cbn [clen] in U2, U3, C2, C3. unfold CTX_END in U2, C2.
    set (TW := tail_ws NA3 m sc cnt1 (cnt1 - 1) P0 0 ab av1 fr av2) in RW.
    assert (WCASE : forall w x, In w TW -> f_a w <= x < f_a w + f_n w ->
      (LOCKA + 8 <= x < LOCKA + 936) \/ (m <= x < m + 40) \/ (P0 - 4 <= x < NE + 1)).
    { intros w x Hw Hx. unfold TW, tail_ws in Hw. cbn [In] in Hw.
      clear - Hw Hx U1 U2 C1 C2 Ene S16g;   (* [comment removed for export] *)
        destruct Hw as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]]]; cbn [f_a f_n] in Hx; lia. }
    set (BAD := fun x => (LOCKA + 8 <= x < LOCKA + 936) \/ (m <= x < m + 40) \/ (P0 - 4 <= x < NE + 1)) in WCASE.
    assert (OUT : forall a : word, ~ BAD (u a) -> m' a = ms_mem s1 a).
    { intros a Hn. subst BAD. cbn beta in Hn, WCASE.
      transitivity (m9 a).
      { apply (rw_frame NA3 m9 TW m' RW). destruct (wfree_dec TW (u a)) as [Hf | (w & Hw & Hx)]; [exact Hf | exfalso; exact (Hn (WCASE w (u a) Hw Hx))]. }
      transitivity (m2 a); [apply FR9; [| intros Hx; apply Hn]; lia | apply Hfr2; lia]. }
    assert (MOVED : forall a : word, m' a = ms_mem s1 a \/
      ((LOCKA + 8 <= u a < LOCKA + 936) \/ (m <= u a < m + 40) \/ (P0 - 4 <= u a < NE + 1))).
    { intros a. specialize (OUT a). subst BAD. cbn beta in OUT. set (x := u a) in *. clearbody x. clear -OUT x.
      destruct (Z_lt_le_dec x (LOCKA + 8)); destruct (Z_lt_le_dec x (LOCKA + 936)); destruct (Z_lt_le_dec x m);
      destruct (Z_lt_le_dec x (m + 40)); destruct (Z_lt_le_dec x (P0 - 4)); destruct (Z_lt_le_dec x (NE + 1));
      first [right; lia | left; apply OUT; lia]. }
    clear OUT. subst BAD. cbn beta in WCASE.
    assert (ZONE : forall a : word, m' a = ms_mem s1 a \/ mzone (u a)).
    { intros a. destruct (MOVED a) as [E | Hz]; [left; exact E | right]. unfold mzone, CTX, CTX_END.
      clear - Hz M1 M2 M3' SH1 SH2 SH3; destruct Hz as [H | [H | H]]; lia.   (* [comment removed for export] *) }
    assert (OWN : forall a : word, m' a = ms_mem s1 a \/ owned_of A1 (u a)).
    { intros a. destruct (MOVED a) as [E | Hz]; [left; exact E | right]. unfold owned_of, CTX_END.
      destruct Hz as [H | [H | H]]; [left; lia | right | right; apply SD; lia].
      replace (u a) with (m + (u a - m)) by lia. apply Mdom. lia. }
    assert (MAPPED : forall a : word, m' a <> None -> ms_mem s1 a <> None \/ (IMG_LO <= u a < IMG_HI) \/ mcov (vm_maps (ms_vm s1)) (u a) 1).
    { intros a Ha. destruct (OWN a) as [E | [Hc | Hd]]; [left; rewrite <- E; exact Ha | right; left; unfold CTX_END in Hc; clear - Hc LS; lia | left].
      rewrite <- (Z_to_bv_bv_unsigned 64 a). exact (rep_dom A1 (ms_mem s1) HRp (u a) Hd). }
    apply (HK ab (upd s1 m' (ms_vm s1)) Hab eq_refl).
    - apply II_intro.
      + exact (IS_mem sp0 argv envp cb A1 (NESTA ab) s1 m' HIS
                 (WF7n sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr Hsc Hact Hj Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 Hfitj Hsmall ab Hab)
                 HR7 ZONE MAPPED).
      + cbn [ms_vm upd]. exact (VMok7n sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr Hsc Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 ab Hab).
      + exact (AvOK7n sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr Hsc Hact Hj Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 Hfitj Hsmall ab Hab).
      + exact (UsOK7n sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr Hsc Hact Hj Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 Hfitj Hsmall ab Hab).
      + exact (deads7n sp0 argv envp cb D A1 s1 sc m md j gj mt aib slots idx cnt1 HII Hm Hr HmD Hact Hmt Hrl Hscj Hidx Hstride ab).
    - constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd]; try reflexivity.
      + intros x Ho. unfold owned_of in *. rewrite (dom_nestA A1 sc m md j gj mt aib slots idx cnt1 Hm Hr Hsc Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 ab Hab x). exact Ho.
      + intros a Ho _. destruct (OWN a) as [E | Hown]; [exact E | exfalso; apply Ho].
        unfold owned_of in *. rewrite (dom_nestA A1 sc m md j gj mt aib slots idx cnt1 Hm Hr Hsc Hmt Hrl Hscj Hidx Hslot Hstride Hcnt1 ab Hab (u a)). exact Hown.
      + intros q n Hq. rewrite (nestA_live A1 sc m j gj mt aib slots idx cnt1 ab). exact Hq.
      + intros q n a Hq Ha. destruct (MOVED a) as [E | Hz]; [exact E | exfalso].
        pose proof (live_dom A1 q n (u a) HW1 Hq Ha) as Hd.
        pose proof (dom_heap A1 (u a) HW1 Hd) as (lo & hi & Hh & Hlh). unfold heap_range in Hh.
        destruct Hz as [H | [H | H]].
        * clear - H Hh Hlh LS; lia.
        * exact (proj2 (meta_dom_nolive A1 m md (u a) HW1 Hm ltac:(lia)) q n Hq Ha).
        * apply (taken_span_nolive A1 gj mt aib slots idx HW1 Hmt Hrl ltac:(lia) Hslot (u a) q n); [| exact Hq | exact Ha].
          unfold p0, ne in H. lia.
      + intros a Ha. apply (rw_mapped NA3 m9 TW m' RW). apply (rw_mapped NA3 m2 PRE_WS m9 RW9').
        destruct (Z_lt_le_dec (u a) (P0 - 3)) as [L5|L5]; [rewrite (Hfr2 a (or_introl L5)); exact Ha|].
        destruct (Z_lt_le_dec (u a) NE) as [L6|L6]; [| rewrite (Hfr2 a (or_intror L6)); exact Ha].
        rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom NA3 m2 R3). apply (proj2 (dom_nA3 A1 j gj mt aib slots idx Hmt Hrl _)). apply SD. lia.
  Qed.
End NestRest2.

End WithLayout.
